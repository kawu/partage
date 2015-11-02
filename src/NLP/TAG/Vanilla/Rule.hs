{-# LANGUAGE RecordWildCards #-}


module NLP.TAG.Vanilla.Rule where


import           Control.Monad.Trans.Class (lift)
import qualified Control.Monad.State.Strict   as E

import qualified Data.Set as S
import           Data.List (intercalate)

import qualified Pipes as P

import           NLP.TAG.Vanilla.Core
import qualified NLP.TAG.Vanilla.Tree as G


----------------------
-- Grammar compilation
----------------------


-- | Compile the given grammar into the list of rules.
-- No structure sharing takes place here.
compile
    :: (Monad m, Ord n, Ord t)
    => [ Either
        (G.Tree n t)
        (G.AuxTree n t) ]
    -> m (S.Set (Rule n t))
compile ts =
    flip E.execStateT S.empty $ runRM $ P.runEffect $
        P.for rules $ \rule -> do
            lift . lift $ E.modify $ S.insert rule
  where
    rules = mapM_ getRules ts
    getRules (Left t)  = treeRules True t
    getRules (Right t) = auxRules  True t


----------------------
-- Initial Trees
----------------------


-- | Label is one of the following:
-- * A non-terminal
-- * A terminal
-- * A root of an auxiliary tree
-- * A foot node of an auxiliary tree
-- * A vertebra of the spine of the auxiliary tree
--
-- TODO: could simplify directly to the form proposed in the
-- paper.
-- 
-- TODO: note that the Eq and Ord instances are not reused in the
-- Eq/Ord instances of rules.  But this is "problem" of rules,
-- not ours, isn't it?
--
data Lab n t
    = NonT
        { nonTerm   :: n
        , labID     :: Maybe SymID }
    | Term t
    | AuxRoot
        { nonTerm   :: n }
    | AuxFoot
        { nonTerm   :: n }
    | AuxVert
        { nonTerm   :: n
        , symID     :: SymID }
    deriving (Show, Eq, Ord)


-- | Show full info about the label.
viewLab :: (View n, View t) => Lab n t -> String
viewLab lab = case lab of
    NonT{..}    -> "N(" ++ view nonTerm
        ++ ( case labID of
                Nothing -> ""
                Just i  -> ", " ++ view i ) ++ ")"
    Term t      -> "T(" ++ view t ++ ")"
    AuxRoot{..} -> "A(" ++ view nonTerm ++ ")"
    AuxFoot x   -> "F(" ++ view x ++ ")"
    AuxVert{..} -> "V(" ++ view nonTerm ++ ", " ++ view symID ++ ")"


-- -- | Show the label.
-- viewLab :: (View n, View t) => Lab n t -> String
-- viewLab (NonT s) = "N" ++ viewSym s
-- viewLab (Term t) = "T(" ++ view t ++ ")"
-- viewLab (Foot s) = "F" ++ viewSym s


-- | A rule for an elementary tree.
data Rule n t = Rule {
    -- | The head of the rule.  TODO: should not be allowed to be
    -- a terminal or a foot.
      headR :: Lab n t
    -- | The body of the rule
    , bodyR :: [Lab n t]
    } deriving (Show, Eq, Ord)


-- | Print the rule.
printRule
    :: ( View n, View t )
    => Rule n t -> IO ()
printRule Rule{..} = do
    putStr $ viewLab headR
    putStr " -> "
    putStr $ intercalate " " $ map viewLab bodyR


--------------------------
-- Rule generation monad
--------------------------


-- | Identifier generation monad.
-- type RM n t i f a = RWS.RWS () [Rule n t i f a] Int
type RM n t m = P.Producer (Rule n t) (E.StateT Int m)


-- | Pull the next identifier.
nextSymID :: Monad m => RM n t m SymID
nextSymID = E.state $ \i -> (i, i + 1)


-- | Save the rule in the writer component of the monad.
keepRule :: Monad m => Rule n t -> RM n t m ()
keepRule = P.yield


-- | Evaluate the state part of the RM monad.
-- runRM :: Monad m => P.Effect (E.StateT Int m) a -> m a
-- runRM = flip E.evalStateT 0 . P.runEffect
runRM :: Monad m => E.StateT Int m a -> m a
runRM = flip E.evalStateT 0


-----------------------------------------
-- Tree Factorization
-----------------------------------------


-- instance (ToString a, ToString b) => ToString (Either a b) where
--     toString (Left x)  = "L " ++ toString x
--     toString (Right x) = "R " ++ toString x


-- | Take an initial tree and factorize it into a list of rules.
treeRules
    :: (Monad m)
    => Bool         -- ^ Is it a top level tree?  `True' for
                    -- an entire initial tree, `False' otherwise.
    -> G.Tree n t   -- ^ The tree itself
    -> RM n t m (Lab n t)
treeRules isTop G.INode{..} = case (subTrees, isTop) of
    ([], _) -> return $ NonT
        -- Foot or substitution node:
        { nonTerm = labelI
        , labID   = Nothing }
    (_, True) -> do
        -- Root node:
        let x = NonT
              { nonTerm = labelI
              , labID   = Nothing }
        xs <- mapM (treeRules False) subTrees
        keepRule $ Rule x xs
        return x
    (_, False) -> do
        -- Internal node; top and bottom feature structures
        -- are split between different rules, dummy attributes
        -- have to be added in order to preserve relations between
        -- tree-local variables.
        i <- nextSymID
        -- First compute the set of all identifiers which occur
        -- in the `botFS` and the sub-trees.  These IDs will be
        -- kept as special attribute values in `rootTopFS`.
--         let is = S.unions
--                 $ idsIn botFS
--                 : map idsInTree subTrees
        -- Compute the map from identifiers (occuring in the `botFS`
        -- and the sub-trees) to their addresses.  These IDs will be
        -- kept as special attribute values in `rootTopFS`.
        let x0 = NonT 
                { nonTerm = labelI
                , labID   = Just i }
        xs <- mapM (treeRules False) subTrees
        keepRule $ Rule x0 xs
        return x0
treeRules _ G.FNode{..} = return $ Term labelF


-----------------------------------------
-- Auxiliary Tree Factorization
-----------------------------------------


-- | Convert an auxiliary tree to a lower-level auxiliary
-- representation and a list of corresponding rules which
-- represent the "substitution" trees on the left and on the
-- right of the spine.
auxRules
    :: (Monad m)
    => Bool
    -> G.AuxTree n t
    -> RM n t m (Lab n t)
auxRules b G.AuxTree{..} =
    doit b auxTree auxFoot
  where
    doit _ G.INode{..} [] = return $
        AuxFoot {nonTerm = labelI}
    doit isTop G.INode{..} (k:ks) = do
        let (ls, bt, rs) = split k subTrees
        ls' <- mapM (treeRules False) ls
        bt' <- doit False bt ks
        rs' <- mapM (treeRules False) rs
        -- In case of an internal node `xt` and `xb` are slighly
        -- different; for a root, they are the same:
        x0 <- if isTop
            then do
                return $ AuxRoot
                        { nonTerm = labelI }
            else nextSymID >>= \i -> do
                return $ AuxVert
                        { nonTerm = labelI
                        , symID   = i }
        keepRule $ Rule x0 $ ls' ++ (bt' : rs')
        return x0
    doit _ _ _ = error "auxRules: incorrect path"



split :: Int -> [a] -> ([a], a, [a])
split =
    doit []
  where
    doit acc 0 (x:xs) = (reverse acc, x, xs)
    doit acc k (x:xs) = doit (x:acc) (k-1) xs
    doit _ _ [] = error "auxRules.split: index to high"
