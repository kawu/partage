{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | TAG conversion into flat production rules.


module NLP.TAG.Vanilla.Rule.Internal
(
-- * Rule
  Rule (..)
, Lab (..)

-- * Grammar flattening
, compile
, compileWeights

-- * Internal
, runRM
, treeRules
, auxRules
) where


import           Control.Monad.Trans.Class (lift)
import qualified Control.Monad.State.Strict   as E

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Tree as T

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
        P.for rules $ \rule ->
            lift . lift $ E.modify $ S.insert rule
  where
    rules = mapM_ getRules ts
    getRules (Left t)  = treeRules t
    getRules (Right t) = auxRules  t


-- | Compile the given probabilistic grammar into the list of rules.  No
-- structure sharing takes place.  Weights are evenly distributed over all
-- rules representing the corresponding elementary trees.
compileWeights
    :: (Monad m, Ord n, Ord t)
    => [ Either
        (G.Tree n t, Cost)
        (G.AuxTree n t, Cost) ]
    -> m (M.Map (Rule n t) Cost)
compileWeights ts =
    flip E.execStateT M.empty $ runRM $ P.runEffect $
        P.for rules $ \(rule, cost) ->
            lift . lift $ E.modify $ M.insert rule cost
  where
    rules = mapM_ getRules ts
    getRules (Left (t, c0))  = do
        labTree <- lift $ labelTree True t
        keepRules labTree c0
        return $ T.rootLabel labTree
    getRules (Right (t, c0)) = do
        labTree <- lift $ labelAux True t
        keepRules labTree c0
        return $ T.rootLabel labTree
    keepRules labTree c0 = do
        let rs = collect labTree
            c = c0 / fromIntegral (length rs)
        mapM_ keepRule [ (r, c) | r <- rs ]


----------------------
-- Initial Trees
----------------------


-- | A label is a data type over which flat production rules are
-- constructed.  In particular, it describes what information is
-- stored in the heads of rules, as well as in the elements of the
-- their bodies.
data Lab n t
    = NonT
        { nonTerm   :: n
        , labID     :: Maybe SymID }
    -- ^ A non-terminal symbol originating from a branching,
    -- non-spine node, optionally marked with a `SymID` if
    -- originating from an internal (non-root, non-leaf) node
    | Term t
    -- ^ A terminal symbol
    | AuxRoot
        { nonTerm   :: n }
    -- ^ A non-terminal originating from a /root/ of an auxiliary tree
    | AuxFoot
        { nonTerm   :: n }
    -- ^ A non-terminal originating from a /foot/ of an auxiliary tree
    | AuxVert
        { nonTerm   :: n
        , symID     :: SymID }
    -- ^ A non-terminal originating from a /spine/ of an auxiliary
    -- tree (unless root or foot)
    deriving (Show, Eq, Ord)


-- -- | Show full info about the label.
-- viewLab :: (View n, View t) => Lab n t -> String
-- viewLab lab = case lab of
--     NonT{..}    -> "N(" ++ view nonTerm
--         ++ ( case labID of
--                 Nothing -> ""
--                 Just i  -> ", " ++ view i ) ++ ")"
--     Term t      -> "T(" ++ view t ++ ")"
--     AuxRoot{..} -> "A(" ++ view nonTerm ++ ")"
--     AuxFoot x   -> "F(" ++ view x ++ ")"
--     AuxVert{..} -> "V(" ++ view nonTerm ++ ", " ++ view symID ++ ")"
--
--
-- -- -- | Show the label.
-- -- viewLab :: (View n, View t) => Lab n t -> String
-- -- viewLab (NonT s) = "N" ++ viewSym s
-- -- viewLab (Term t) = "T(" ++ view t ++ ")"
-- -- viewLab (Foot s) = "F" ++ viewSym s


-- | A production rule, responsible for recognizing a specific
-- (unique) non-trivial (of height @> 0@) subtree of an elementary
-- grammar tree.  Due to potential subtree sharing, a single rule can
-- be responsible for recognizing a subtree common to many different
-- elementary trees.
--
-- Invariants:
--
--  * `headR` is neither `Term` nor `AuxFoot`
data Rule n t = Rule {
    -- | Head of the rule
      headR :: Lab n t
    -- | Body of the rule
    , bodyR :: [Lab n t]
    } deriving (Show, Eq, Ord)


-- -- | Print the rule.
-- printRule
--     :: ( View n, View t )
--     => Rule n t -> IO ()
-- printRule Rule{..} = do
--     putStr $ viewLab headR
--     putStr " -> "
--     putStr . unwords $ map viewLab bodyR


--------------------------
-- Rule generation monad
--------------------------


-- | Identifier generation monad.
type ID m = E.StateT Int m


-- | Generating rules in a pipe.
type RM r m = P.Producer r (ID m)


-- | Pull the next identifier.
nextSymID :: E.MonadState SymID m => m SymID
nextSymID = E.state $ \i -> (i, i + 1)


-- | Save the rule in the writer component of the monad.
keepRule :: Monad m => r -> RM r m ()
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
    => G.Tree n t   -- ^ The tree itself
    -> RM (Rule n t) m (Lab n t)
treeRules t = do
    labTree <- lift $ labelTree True t
    mapM_ keepRule $ collect labTree
    return $ T.rootLabel labTree


-- | Take an initial tree and factorize it into a tree of labels.
labelTree
    :: (Monad m)
    => Bool         -- ^ Is it a top level tree?  `True' for
                    -- an entire initial tree, `False' otherwise.
    -> G.Tree n t   -- ^ The tree itself
    -> ID m (T.Tree (Lab n t))
labelTree isTop G.Branch{..} = case (subTrees, isTop) of
    -- Foot or substitution node:
    ([], _) -> return . flip T.Node [] $ NonT
        { nonTerm = labelI
        , labID   = Nothing }
    -- Root node:
    (_, True) -> do
        let x = NonT
              { nonTerm = labelI
              , labID   = Nothing }
        xs <- mapM (labelTree False) subTrees
        return $ T.Node x xs
    -- Internal node:
    (_, False) -> do
        i <- nextSymID
        let x = NonT
                { nonTerm = labelI
                , labID   = Just i }
        xs <- mapM (labelTree False) subTrees
        return $ T.Node x xs
labelTree _ G.Leaf{..} = return $ T.Node (Term labelF) []


-----------------------------------------
-- Auxiliary Tree Factorization
-----------------------------------------


-- | Take an auxiliary tree and factorize it into a tree of labels.
auxRules
    :: (Monad m)
    => G.AuxTree n t
    -> RM (Rule n t) m (Lab n t)
auxRules t = do
    labTree <- lift $ labelAux True t
    mapM_ keepRule $ collect labTree
    return $ T.rootLabel labTree


-- | Take an auxiliary tree and factorize it into a tree of labels.
labelAux
    :: (Monad m)
    => Bool
    -> G.AuxTree n t
    -> ID m (T.Tree (Lab n t))
labelAux b G.AuxTree{..} =
    doit b auxTree auxFoot
  where
    doit _ G.Branch{..} [] = return . flip T.Node [] $
        AuxFoot {nonTerm = labelI}
    doit isTop G.Branch{..} (k:ks) = do
        let (ls, bt, rs) = split k subTrees
        ls' <- mapM (labelTree False) ls
        bt' <- doit False bt ks
        rs' <- mapM (labelTree False) rs
        -- In case of an internal node `xt` and `xb` are slighly
        -- different; for a root, they are the same:
        x0 <- if isTop
            then return AuxRoot
                        { nonTerm = labelI }
            else nextSymID >>= \i ->
                 return AuxVert
                        { nonTerm = labelI
                        , symID   = i }
        -- keepRule $ Rule x0 $ ls' ++ (bt' : rs')
        -- return x0
        return $ T.Node x0 $ ls' ++ (bt' : rs')
    doit _ _ _ = error "auxRules: incorrect path"


-----------------------------------------
-- Utils
-----------------------------------------


-- | Split the given list on the given position.
split :: Int -> [a] -> ([a], a, [a])
split =
    doit []
  where
    doit acc 0 (x:xs) = (reverse acc, x, xs)
    doit acc k (x:xs) = doit (x:acc) (k-1) xs
    doit _ _ [] = error "auxRules.split: index to high"


-- | Collect rules present in the tree produced by `labelTree`.
collect :: T.Tree (Lab n t) -> [Rule n t]
collect T.Node{..} = case subForest of
    [] -> []
    -- WARNING! It is crucial for substructure-sharing (at least in
    -- the current implementation, that indexes (SymIDs) are
    -- generated in the ascending order.  This stems from the fact
    -- that `Data.Partition.rep` returns the minimum element of the
    -- given partition, thus making it impossible to choose a custom
    -- representant of the given partition.
    --
    -- Note that this solution should be changed and that
    -- substructure sharing should be implemented differently.
    -- The current solution seems too error prone.
    _  ->  concatMap collect subForest
        ++ [ Rule rootLabel
            (map T.rootLabel subForest) ]
