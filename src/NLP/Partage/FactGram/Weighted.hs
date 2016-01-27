{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


-- | TAG conversion into flat production rules with subtree sharing
-- enabled.  To each elementary tree a non-negative weight (score)
-- can be assigned.


module NLP.Partage.FactGram.Weighted
(
-- -- * Grammar flattening
--   flattenWithWeights
) where


import           Control.Applicative ((<$>))
import qualified Control.Monad.State.Strict as E
import           Control.Monad.Trans.Maybe (MaybeT (..))

import qualified Data.List as L
import           Data.Ord (comparing)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.MemoCombinators as Memo

import qualified Data.Tree as R
-- import qualified NLP.Partage.Tree.Other as G


----------------------
-- DAGs
----------------------


-- | Node identifier in the `DAG`.  Invariant: non-negative
-- (see `newID`).
type ID = Int


-- | Cost assigned to a given edge in the DAG.
type Weight = Double


-- | A DAG representation of a tree forest in which identical
-- subtrees are shared, i.e. a subtree common to several trees is
-- represented by a single subgraph in the DAG.
--
-- Type @a@ represents values of DAG nodes, type @b@ -- values of
-- DAG edges.
data DAG a b = DAG
    { rootSet   :: S.Set ID
    -- ^ The set of roots of the DAG
    , nodeMap   :: M.Map ID (Node a b)
    -- ^ The set of nodes in the DAG
    }


-- | A single node of the `DAG`.
data Node a b = Node
    { nodeLabel :: a
    , nodeEdges :: [(ID, b)]
    -- ^ Note that IDs on the `nodeEdges` list can be repeated.
    } deriving (Show, Eq, Ord)


-- | Edges outgoing from the given node.
edges :: ID -> DAG a b -> [(ID, b)]
edges i DAG{..} =
    maybe [] nodeEdges
        (M.lookup i nodeMap)


-- | The list of children IDs for the given node ID.
children :: ID -> DAG a b -> [ID]
children i = map fst . edges i


-- | The set of descendant IDs for the given ID.
-- The argument ID is not included in the resulting set.
descendants :: ID -> DAG a b -> S.Set ID
descendants = undefined


-- | The set of all IDs in the DAG.
setIDs :: DAG a b -> S.Set ID
setIDs dag = S.fromList
    [ i
    | r <- S.toList (rootSet dag)
    , i <- r : S.toList (descendants r dag) ]


-- TODO: Similar instance already inferred in the "Gen" module.
deriving instance (Ord a) => (Ord (R.Tree a))


---------------------------
-- Convertion with Weights
---------------------------


-- | Transform the given weighted grammar into a `DAG`.
-- Common subtrees are shared in the resulting `DAG`.
dagFromWeightedForest
    :: (Ord a)
    => [(R.Tree a, Weight)]
    -> DAG a Weight
dagFromWeightedForest forestWeights =
    let (forest, weights) = unzip forestWeights
        (rootList, nodeMapI) = runDagM (mapM fromTree forest)
        dag0 = DAG
            { rootSet = S.fromList rootList
            , nodeMap = revMap nodeMapI }
     in weighDAG dag0 $
            M.fromListWith min (zip rootList weights)


-- | Weigh the DAG given a mapping from root nodes to weights.
-- Each node represents a tree of the input forest, those the
-- weights are in fact assigned to the input trees.
--
-- We assume that if a weight for a given root is not provided, then
-- it's equal to @0@.
weighDAG
    :: DAG a ()         -- ^ The DAG
    -> M.Map ID Weight  -- ^ Weights assigned to DAG roots
    -> DAG a Weight     -- ^ Weighted DAG
weighDAG dag rootWeightMap =
    flip E.execState dagw0 $
        mapM_ (relax parMap) allIDs
  where
    parMap  = parentMap dag
    distFun = rootDistFun dag parMap
    dagw0   = weighDAG0 dag rootWeightMap
    -- list of IDs to relax, ordered according to the corresponding
    -- distances to roots provided by `distFun`
    allIDs  = L.sortBy (comparing distFun) $ S.toList
        (setIDs dag `S.difference` rootSet dag)


---------------------------
-- Relax monad: BEG
---------------------------


-- | The relaxation monad which works on the uderlying weighted DAG.
type RelaxM a = E.State (DAG a Weight)


-- | Relax the given node, i.e. try to move weights from the
-- ingoing edges to the outgoing edges
relax :: ParentMap -> ID -> RelaxM a ()
relax parMap i = do
    -- TODO: don't relax if leaf node!

    -- Find the minimal weight amongst the ingoing edges
    w0 <- minim 0 . concat <$> sequence
        [ edgeWeight j i
        | j <- S.toList $ parents i parMap ]

    -- Substract the minimal weight from the ingoing edges
    sequence_
        [ modEdgeWeight (\w -> w - w0) j i
        | j <- S.toList $ parents i parMap ]

    -- Add the minimal weight to the outgoing edges
    dag <- E.get
    sequence_
        [ modEdgeWeight (\w -> w + w0) i j
        -- below we don't care about the order of children;
        -- note that we have to remove duplicates, otherwise
        -- weights could be modified for a specific pair
        -- multiple times
        | j <- setNub (children i dag) ]


-- | Get the weight of the edges connecting the two IDs.
edgeWeight :: ID -> ID -> RelaxM a [Weight]
edgeWeight i j = runError "edgeWeight: invalid ID" $ do
    Node{..} <- may =<< E.gets (M.lookup i . nodeMap)
    return $ snd <$> L.filter (\e -> fst e == j) nodeEdges


-- | Modify the weight of the edges connecting the two IDs.
modEdgeWeight :: (Weight -> Weight) -> ID -> ID -> RelaxM a ()
modEdgeWeight f i j = runError "edgeWeight: invalid ID" $ do
    Node{..} <- may =<< E.gets (M.lookup i . nodeMap)
    let insert i n dag = dag
            {nodeMap = M.insert i n (nodeMap dag)}
    E.modify' . insert i $ Node
        { nodeLabel = nodeLabel
        , nodeEdges =
            [ if j == k
                then (k, f w)
                else (k, w)
            | (k, w) <- nodeEdges ] }


---------------------------
-- Relax monad: END
---------------------------


-- | Assign root weights to edges outgoing from individual roots.
--
-- We assume that if a weight for a given root is not provided, then
-- it's equal to @0@.
weighDAG0
    :: DAG a ()         -- ^ The DAG
    -> M.Map ID Weight  -- ^ Weights assigned to DAG roots
    -> DAG a Weight     -- ^ Weighted DAG
weighDAG0 dag rootWeightMap = undefined


-- | A map from nodes to their parent IDs.
type ParentMap = M.Map ID (S.Set ID)


-- | Compute the reverse DAG representation: a map from an ID @i@
-- to the set of IDs of the nodes from which an edge leading to @i@
-- exists.  In simpler words, for each ID, a set of its parent IDs.
parentMap :: DAG a b -> ParentMap
parentMap dag = M.fromListWith S.union
    [ (j, S.singleton i)
    | i <- S.toList (setIDs dag)
    -- below we don't care about the order of children
    , j <- setNub $ children i dag ]


-- | List of parents for the given node ID.
-- Empty if ID not present in the map.
parents :: ID -> ParentMap -> S.Set ID
parents i = maybe S.empty id . M.lookup i


-- | A map which, for a given node, provides a minimal distance from
-- this node to some DAG root.  Returns @0@ for IDs not present in
-- the underlying DAG (as well as for its roots, of course).
type DistFun = ID -> Int


-- | Compute the minimal distance from each node to a root in the
-- DAG.
rootDistFun
    :: DAG a b      -- ^ The DAG
    -> ParentMap    -- ^ Parent map of the DAG
    -> DistFun
rootDistFun dag parMap =
    dist
  where
    dist = Memo.integral dist'
    dist' i =
        (minim 0 . map dist)
            (S.toList $ parents i parMap)


----------------------
-- Basic Convertion
----------------------


-- | Transform the given weighted grammar into a `DAG`.
-- Common subtrees are shared in the resulting `DAG`.
dagFromForest :: (Ord a) => [R.Tree a] -> DAG a ()
dagFromForest ts =
    let (rootList, nodeMapI) = runDagM (mapM fromTree ts)
     in DAG
        { rootSet = S.fromList rootList
        , nodeMap = revMap nodeMapI }


-- | Type of the monad used to create DAGs from trees.
type DagM a b = E.State (M.Map (Node a b) ID)


-- | Run the DagM monad.
runDagM :: DagM a b c -> (c, M.Map (Node a b) ID)
runDagM = flip E.runState M.empty


-- | Create a DAG node from a tree.
fromTree :: (Ord a) => R.Tree a -> DagM a () ID
fromTree t = do
    childrenIDs <- mapM fromTree (R.subForest t)
    addNode $ Node
        { nodeLabel = R.rootLabel t
        , nodeEdges = zip childrenIDs $ repeat () }


-- | Add a node (unless already exists) to the underlying
-- DAG and return its ID.
addNode :: (Ord a, Ord b) => Node a b -> DagM a b ID
addNode x = do
    mayID <- getNode x
    case mayID of
        Nothing -> do
            i <- newID
            putNode i x
            return i
        Just i ->
            return i


-- | Get the node from the underlying map.
getNode :: (Ord a, Ord b) => Node a b -> DagM a b (Maybe ID)
getNode = E.gets . M.lookup


-- | Get the node from the underlying map.
putNode :: (Ord a, Ord b) => ID -> Node a b -> DagM a b ()
putNode i x = E.modify' $ M.insert x i


-- | Retrieve new, unused node identifier.
newID :: DagM a b ID
newID = E.gets M.size


---------------------------
-- Error with MaybeT
---------------------------


-- | Print error if result is `Nothing`.
runError :: Monad m => String -> MaybeT m a -> m a
runError errMsg m = do
    mayVal <- runMaybeT m
    case mayVal of
         Nothing    -> error errMsg
         Just x     -> return x


-- | Embed `Maybe` withing `MaybeT`.
may :: Monad m => Maybe a -> MaybeT m a
may = MaybeT . return


----------------------
-- Misc
----------------------


-- | Reverse map.
revMap :: (Ord b) => M.Map a b -> M.Map b a
revMap =
    let swap (x, y) = (y, x)
     in M.fromList . map swap . M.toList


-- | A version of `minimum` which the value specified for the case
-- where the input list is empty.
minim :: Ord a => a -> [a] -> a
minim x0 xs = case xs of
             [] -> x0
             _  -> minimum xs


-- | Change list to a set, but still represented by a list...
-- Similar to `L.nub`, but the order of elements may change.
setNub :: Ord a => [a] -> [a]
setNub = S.toList . S.fromList
