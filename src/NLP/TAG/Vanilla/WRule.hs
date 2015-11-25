{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | Rules in weights in terminals.


module NLP.TAG.Vanilla.WRule where


import           Control.Monad.Trans.Class (lift)
import qualified Control.Monad.State.Strict   as E

import qualified Data.Set as S
-- import qualified Data.Map.Strict as M
import qualified Data.Tree as T

import qualified Pipes as P

import           NLP.TAG.Vanilla.Core
import qualified NLP.TAG.Vanilla.Tree as G
import qualified NLP.TAG.Vanilla.Rule as R


----------------------
-- Grammar compilation
----------------------


-- -- | Compile the given grammar into the list of rules.
-- -- No structure sharing takes place here.
-- compile
--     :: (Monad m, Ord n, Ord t)
--     => [ Either
--         (G.Tree n t)
--         (G.AuxTree n t) ]
--     -> m (S.Set (Rule n t))
-- compile ts =
--     flip E.execStateT S.empty $ runRM $ P.runEffect $
--         P.for rules $ \rule ->
--             lift . lift $ E.modify $ S.insert rule
--   where
--     rules = mapM_ getRules ts
--     getRules (Left t)  = treeRules t
--     getRules (Right t) = auxRules  t


-- | Compile the given probabilistic grammar into the list of rules.  No
-- structure sharing takes place.  Weights are evenly distributed over all
-- terminals in the corresponding elementary trees.
compileWeights
    :: (Monad m, Ord n, Ord t)
    => [ Either
        (G.Tree n t, Cost)
        (G.AuxTree n t, Cost) ]
    -> m (S.Set (Rule n t))
compileWeights ts =
    flip E.execStateT S.empty $ runRM $ P.runEffect $
        P.for rules $ \rule ->
            lift . lift $ E.modify $ S.insert rule
  where
    rules = mapM_ getRules ts
    getRules (Left (t, c0))  = do
        let termNum = fromIntegral $ countTerms t
        labTree <- lift $ labelTree True (c0 / termNum) t
        keepRules labTree
        return $ T.rootLabel labTree
    getRules (Right (t, c0)) = do
        let termNum = fromIntegral $ countTerms $ G.auxTree t
        labTree <- lift $ labelAux True (c0 / termNum) t
        keepRules labTree
        return $ T.rootLabel labTree
    keepRules labTree = do
        let rs = collect labTree
        mapM_ keepRule rs


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
    | Term
        { term      :: t
        , termCost  :: Cost }
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
    Term{..}    -> "T(" ++ view term ++ ", " ++ show termCost ++ ")"
    AuxRoot{..} -> "A(" ++ view nonTerm ++ ")"
    AuxFoot x   -> "F(" ++ view x ++ ")"
    AuxVert{..} -> "V(" ++ view nonTerm ++ ", " ++ view symID ++ ")"


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
    putStr . unwords $ map viewLab bodyR


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
    => Cost         -- ^ Cost of scanning a terminal
    -> G.Tree n t   -- ^ The tree itself
    -> RM (Rule n t) m (Lab n t)
treeRules cost t = do
    labTree <- lift $ labelTree True cost t
    mapM_ keepRule $ collect labTree
    return $ T.rootLabel labTree


-- | Take an initial tree and factorize it into a tree of labels.
labelTree
    :: (Monad m)
    => Bool         -- ^ Is it a top level tree?  `True' for
                    -- an entire initial tree, `False' otherwise.
    -> Cost         -- ^ Cost of scanning a terminal
    -> G.Tree n t   -- ^ The tree itself
    -> ID m (T.Tree (Lab n t))
labelTree isTop termPrice G.INode{..} = case (subTrees, isTop) of
    -- Foot or substitution node:
    ([], _) -> return . flip T.Node [] $ NonT
        { nonTerm = labelI
        , labID   = Nothing }
    -- Root node:
    (_, True) -> do
        let x = NonT
              { nonTerm = labelI
              , labID   = Nothing }
        xs <- mapM (labelTree False termPrice) subTrees
        return $ T.Node x xs
    -- Internal node:
    (_, False) -> do
        i <- nextSymID
        let x = NonT
                { nonTerm = labelI
                , labID   = Just i }
        xs <- mapM (labelTree False termPrice) subTrees
        return $ T.Node x xs
labelTree _ termPrice G.FNode{..} = return $ T.Node (Term labelF termPrice) []


-----------------------------------------
-- Auxiliary Tree Factorization
-----------------------------------------


-- | Take an auxiliary tree and factorize it into a tree of labels.
auxRules
    :: (Monad m)
    => Cost         -- ^ Cost of scanning a terminal
    -> G.AuxTree n t
    -> RM (Rule n t) m (Lab n t)
auxRules cost t = do
    labTree <- lift $ labelAux True cost t
    mapM_ keepRule $ collect labTree
    return $ T.rootLabel labTree


-- | Take an auxiliary tree and factorize it into a tree of labels.
labelAux
    :: (Monad m)
    => Bool
    -> Cost         -- ^ Cost of scanning a terminal
    -> G.AuxTree n t
    -> ID m (T.Tree (Lab n t))
labelAux b termPrice G.AuxTree{..} =
    doit b auxTree auxFoot
  where
    doit _ G.INode{..} [] = return . flip T.Node [] $
        AuxFoot {nonTerm = labelI}
    doit isTop G.INode{..} (k:ks) = do
        let (ls, bt, rs) = split k subTrees
        ls' <- mapM (labelTree False termPrice) ls
        bt' <- doit False bt ks
        rs' <- mapM (labelTree False termPrice) rs
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
    -- WARNING! It is crucial for substructure-sharing (at least in the current
    -- implementation, that indexes (SymIDs) are generated in the ascending
    -- order.  This stems from the fact that `Data.Partition.rep` returns the
    -- minimum element of the given partition, thus making it impossible to
    -- choose a custom representant of the given partition.
    --
    -- Note that this solution should be changed and that substructure sharing
    -- should be implemented differently.  The current solution is too error
    -- prone.
    _  ->  concatMap collect subForest
        ++ [ Rule rootLabel
            (map T.rootLabel subForest) ]


-- | Count the number of terminals in the given tree.
countTerms :: G.Tree n t -> Int
countTerms G.FNode{} = 1
countTerms G.INode{..} = sum $ map countTerms subTrees


-----------------------------------------
-- Conversion
-----------------------------------------


-- | Make a weighted rule from a regular rule.
weighRule :: Cost -> R.Rule n t -> Rule n t
weighRule c R.Rule{..} = Rule
    (weighLab c headR)
    (map (weighLab c) bodyR)


-- | Make a weighted label from a regular rule.
weighLab :: Cost -> R.Lab n t -> Lab n t
weighLab _ R.NonT{..}    = NonT nonTerm labID
weighLab c (R.Term t)    = Term t c
weighLab _ R.AuxRoot{..} = AuxRoot nonTerm
weighLab _ R.AuxFoot{..} = AuxFoot nonTerm
weighLab _ R.AuxVert{..} = AuxVert nonTerm symID


-- | Remove weights from a weighted rule.
unWeighRule :: Rule n t -> R.Rule n t
unWeighRule Rule{..} = R.Rule
    (unWeighLab headR)
    (map unWeighLab bodyR)


-- \ Remove weight from the label.
unWeighLab :: Lab n t -> R.Lab n t
unWeighLab NonT{..}    = R.NonT nonTerm labID
unWeighLab Term{..}    = R.Term term
unWeighLab AuxRoot{..} = R.AuxRoot nonTerm
unWeighLab AuxFoot{..} = R.AuxFoot nonTerm
unWeighLab AuxVert{..} = R.AuxVert nonTerm symID
