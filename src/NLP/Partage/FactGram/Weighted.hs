{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


-- | TAG conversion into flat production rules with subtree sharing
-- enabled.  To each elementary tree a non-negative weight (score)
-- can be assigned.


module NLP.Partage.FactGram.Weighted
(
-- * DAG
-- ** Types
  Weight
-- ** Utils
-- ** Parent Map
, parents
, parentMap

-- * Ensemble
, Gram (..)
, mkGram

-- * Conversion
, dagFromWeightedForest
-- ** Flattening
, flattenWithWeights
) where


import           Control.Applicative        ((<$>))
import           Control.Arrow              (first)
import qualified Control.Monad.State.Strict as E
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import           Prelude                    hiding (lookup)

import qualified Data.List                  as L
import qualified Data.Map.Strict            as M
import qualified Data.MemoCombinators       as Memo
import           Data.Ord                   (comparing)
import qualified Data.Set                   as S
import qualified Data.Tree                  as R

import           NLP.Partage.FactGram.DAG   hiding (Gram (..), mkGram)
-- import           NLP.Partage.FactGram.Internal (Lab (..), Rule (..))
import qualified NLP.Partage.Tree           as T
import qualified NLP.Partage.Tree.Other     as O


----------------------
-- Weight
----------------------


-- | Weight assigned to a given edge in the DAG.
type Weight = Double


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
        (rootList, dagSt) = runDagM (mapM (fromTree True) forest)
        dag0 = DAG
            { rootSet = S.fromList rootList
            , nodeMap = M.union
                (revMap (rootMap dagSt))
                (revMap (normMap dagSt)) }
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
    -> M.Map DID Weight -- ^ Weights assigned to DAG roots
    -> DAG a Weight     -- ^ Weighted DAG
weighDAG dag rootWeightMap =
    flip E.execState dagw0 $
        mapM_ tryRelax allIDs
  where
    parMap  = parentMap dag
    sizeFun = subSizeFun dag
    distFun = rootDistFun parMap
    dagw0   = weighDAG0 dag sizeFun rootWeightMap
    -- relax the node only if not a leaf
    tryRelax i = if isLeaf i dag
                    then return ()
                    else relax parMap sizeFun i
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
relax :: ParentMap -> SizeFun -> DID -> RelaxM a ()
relax parMap sizeFun i = do
    -- Find the minimal weight amongst the ingoing edges
    w0 <- minim 0 . concat <$> sequence
        [ edgeWeight j i
        | j <- S.toList $ parents i parMap ]

    -- Substract the minimal weight from the ingoing edges
    sequence_
        [ modEdgeWeight (\w -> w - w0) j i
        | j <- S.toList $ parents i parMap ]

    -- Spread the weight over the outgoing edges, according to the
    -- sizes of the corresponding subtrees (see also `weighDAG0`)
    dag <- E.get
    let sizeList = map (fromIntegral . sizeFun) (children i dag)
        sizeSum  = sum sizeList
        weights  = [w0 * size / sizeSum | size <- sizeList]
    setWeights weights i


-- | Get the weight of the edges connecting the two IDs.
edgeWeight :: DID -> DID -> RelaxM a [Weight]
edgeWeight i j = runError "edgeWeight: invalid ID" $ do
    Node{..} <- may =<< E.gets (M.lookup i . nodeMap)
    return $ snd <$> L.filter (\e -> fst e == j) nodeEdges


-- Set the weights of the edges outgoing from the given ID.
setWeights :: [Weight] -> DID -> RelaxM a ()
setWeights ws i = runError "multWeights: invalid ID" $ do
    dag <- E.get
    n <- may (lookup i dag)
    E.modify' . insert i $ n
        { nodeEdges =
            [ (j, w)
            | (j, w) <- zip (children i dag) ws ] }


-- | Modify the weight of the edges connecting the two IDs.
modEdgeWeight :: (Weight -> Weight) -> DID -> DID -> RelaxM a ()
modEdgeWeight f i j = runError "modEdgeWeight: invalid ID" $ do
    Node{..} <- may =<< E.gets (M.lookup i . nodeMap)
    E.modify' . insert i $ Node
        { nodeLabel = nodeLabel
        , nodeValue = 0
        , nodeEdges =
            [ if j == k
                then (k, f w)
                else (k, w)
            | (k, w) <- nodeEdges ] }


---------------------------
-- Relax monad: END
---------------------------


-- | Spread root weights over edges outgoing from individual roots.
--
-- We assume that if a weight for a given root is not provided, then
-- it's equal to @0@.
weighDAG0
    :: DAG a ()         -- ^ The DAG
    -> SizeFun          -- ^ `SizeFun` of the DAG
    -> M.Map DID Weight -- ^ Weights assigned to DAG roots
    -> DAG a Weight     -- ^ Weighted DAG
weighDAG0 dag sizeFun rootWeightMap = DAG
    { rootSet = rootSet dag
    , nodeMap = M.fromList
        [ (i, updateNode i n)
        | (i, n) <- M.toList (nodeMap dag) ] }
  where
    updateNode i n = n
      { nodeValue = 0
      , nodeEdges =
          [ (j, w0 * size / sizeSum)
          | (j, size) <- zip (children i dag) sizeList ] }
      where
        sizeList = map
            -- -- The version with (+1) would make sense if
            -- -- `sizeFun` would really compute the size of
            -- -- the subtree, and not the number of leaves.
            -- (fromIntegral . (+1) . sizeFun)
            (fromIntegral . sizeFun)
            (children i dag)
        sizeSum  = sum sizeList
        w0 = case M.lookup i rootWeightMap of
                  Nothing -> 0
                  Just w  -> w
--                  Just w0    -> w0 /
--                     let size = fromIntegral . length
--                      in size (nodeEdges n)


-- | A map from nodes to their parent IDs.
type ParentMap = M.Map DID (S.Set DID)


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
parents :: DID -> ParentMap -> S.Set DID
parents i = maybe S.empty id . M.lookup i


-- | A map which, for a given node, provides a minimal distance from
-- this node to some DAG root.  Returns @0@ for IDs not present in
-- the underlying DAG (as well as for its roots, of course).
type DistFun = DID -> Int


-- | Compute the minimal distance from each node to a root.
rootDistFun
    :: ParentMap    -- ^ Parent map of the DAG
    -> DistFun
rootDistFun parMap =
    dist
  where
    dist = Memo.wrap DID unDID Memo.integral dist'
    dist' i =
        (maxim 0 . map ((+1).dist))
            (S.toList $ parents i parMap)


-- | A map which, for a given node, gives the number of /leaves/ in
-- the corresponding /subtree/ (@0@ by default).  Note that the
-- corresponding sub-DAG is treated as a subtree, and not a sub-DAG,
-- thus some leaves in the sub-DAG can be included multiple times in
-- the result.
type SizeFun = DID -> Int


-- | Compute `SizeFun`.
subSizeFun
    :: DAG a b    -- ^ The DAG
    -> SizeFun
subSizeFun dag =
    size
  where
    size = Memo.wrap DID unDID Memo.integral size'
    size' i
        | isLeaf i dag = 1
        | otherwise =
            (sum . map size)
                (children i dag)


-- -- | Compute `SizeFun` (version which computes the number of all
-- -- edges).
-- subSizeFun
--     :: DAG a b    -- ^ The DAG
--     -> SizeFun
-- subSizeFun dag =
--     size
--   where
--     size = Memo.integral size'
--     size' i =
--         (sum . map ((+1).size))
--             (children i dag)


----------------------
-- Grammar Flattening
----------------------


-- | Flatten the given weighted grammar.
flattenWithWeights
    :: (Ord n, Ord t)
    => [(O.SomeTree n t, Weight)]   -- ^ Weighted grammar
    -> M.Map Rule Weight
flattenWithWeights
    = rulesMapFromDAG
    . dagFromWeightedForest
    . map (first O.encode)


-- | Extract rules from the grammar DAG.
rulesMapFromDAG :: DAG a Weight -> M.Map Rule Weight
rulesMapFromDAG dag = M.fromList
    [ let (is, ws) = unzip (edges i dag)
      in  (Rule i is, sum ws)
    | i <- M.keys (nodeMap dag)
    , not (isLeaf i dag) ]


-- -- | A function which tells whether the given node is a spine node.
-- isSpine :: DAG (O.Node n t) w -> ID -> Bool
-- isSpine dag =
--     spine
--   where
--     spine = Memo.integral spine'
--     spine' i
--         | isFoot i dag = True
--         | otherwise    = or . map spine . children i $ dag
--
--
-- -- | Is it a foot node?
-- isFoot :: ID -> DAG (O.Node n t) w -> Bool
-- isFoot i dag = case lookup i dag of
--     Nothing -> False
--     Just n  -> case nodeLabel n of
--         O.Foot _  -> True
--         _         -> False


----------------------
-- Ensemble
----------------------


-- | The datatype which contains the grammar in its different forms
-- needed for parsing.
data Gram n t = Gram
    { dagGram  :: DAG (O.Node n t) ()
    -- ^ Grammar as a DAG (with subtree sharing)
    , factGram :: M.Map Rule Weight
    -- ^ Factorized (flattened) form of the grammar
    , termWei  :: M.Map t Weight
    -- ^ The lower bound estimates on reading terminal weights.
    -- Based on the idea that weights of the elementary trees are
    -- evenly distributed over its terminals.
    }


-- | Construct `Gram` based on the given weighted grammar.
mkGram
    :: (Ord n, Ord t)
    => [(O.Tree n t, Weight)]   -- ^ Weighted grammar
    -> Gram n t
mkGram ts = Gram
    { dagGram   = fmap (const ()) dagGram_
    , factGram  = rulesMapFromDAG dagGram_
    , termWei   = mkTermWei (map (first O.decode) ts) }
  where
    dagGram_
        = dagFromWeightedForest
        -- . map (first O.encode)
        $ ts


-- | Compute the lower bound estimates on reading terminal weights.
-- Based on the idea that weights of the elementary trees are evenly
-- distributed over its terminals.
mkTermWei
    :: (Ord n, Ord t)
    => [(O.SomeTree n t, Weight)]   -- ^ Weighted grammar
    -> M.Map t Weight
mkTermWei ts = M.fromListWith min
    [ (x, w / fromIntegral n)
    | (t, w) <- ts
    , let terms = listTerms t
          n = length terms
    , x <- terms ]


-- | List the terminal leaves of the tree.
listTerms :: O.SomeTree n t -> [t]
listTerms (Left t) = T.project t
listTerms (Right a) = T.project (T.auxTree a)


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


-- | A version of `minimum` which the value specified for the case
-- where the input list is empty.
maxim :: Ord a => a -> [a] -> a
maxim x0 xs = case xs of
             [] -> x0
             _  -> maximum xs


-- | Change list to a set, but still represented by a list...
-- Similar to `L.nub`, but the order of elements may change.
setNub :: Ord a => [a] -> [a]
setNub = S.toList . S.fromList
