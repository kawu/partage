{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


-- | Directed acyclic graph (DAG) representation of TAG grammars.
--
-- The input TAG can be seen as a set of elementary (initial and auxiliary)
-- grammar trees. This module provides an alternative, more compact
-- representation in which common subtrees are shared among the corresponding
-- elementary trees. In this representation the grammar takes for form of a DAG
-- which allows to represent sharing in a natural way.


module NLP.Partage.DAG
(
-- * DAG
  DAG
, DID(..)
, Weight
-- ** Mapping
, nmap
-- ** Identifiers
, rootSet
, nodeSet
-- ** Predicates
, isRoot
, isLeaf
, isFoot
, isSpine
-- ** Querying
, label
, value
, edges
, children
, descendants
-- -- ** Nodes
-- , Node(..)
-- , lookup
-- , insert
-- ** Parent map
-- $parent-map
, ParentMap
, parentMap
, parents

-- * Ensemble
, Gram (..)
, mkGram
-- , mkFreqGram
, mkDummy

-- * Conversion
-- $rule
-- ** Rule
, Rule(..)
-- ** Plain
, dagFromForest
, rulesFromDAG
-- ** Weighted
, dagFromWeightedForest
, rulesMapFromDAG
-- ** Dummy
, dummyFromWeightedForest

-- * Tree
, toTree

-- -- * Low-level internal
-- -- (Use on your own responsibility)
-- , DagSt(..)
-- , runDagM
-- , fromTree
) where


-- import           Control.Arrow              (first)
import           Control.Monad              (forM)
import qualified Control.Monad.State.Strict as E
import           Prelude                    hiding (lookup)

import           Data.Maybe                 (catMaybes)
import qualified Data.Map.Strict            as M
import qualified Data.MemoCombinators       as Memo
import qualified Data.Set                   as S
import qualified Data.Tree                  as R
import qualified Data.List                  as L

-- import qualified NLP.Partage.Tree           as T
import qualified NLP.Partage.Tree.Other     as O

-- import Debug.Trace (trace)

----------------------
-- DAGs
----------------------


-- | Weight assigned to a given node or edge in the DAG.
type Weight = Double


-- | `DAG` node identifier.
newtype DID = DID { unDID :: Int }
    deriving (Show, Eq, Ord)


-- | A DAG representation of a tree forest in which identical
-- subtrees are shared, i.e. a subtree common to several trees is
-- represented by a single subgraph in the DAG.
--
-- Type @a@ represents values stored in DAG nodes, type @b@ --
-- values kept in DAG edges.
data DAG a b = DAG
    { rootSet :: S.Set DID
    -- ^ The set of roots of the DAG
    , nodeMap :: M.Map DID (Node a b)
    -- ^ The set of nodes in the DAG
    } deriving (Functor)


-- | A single node of the `DAG`.
data Node a b = Node
    { nodeLabel :: a
    , nodeValue :: b
    , nodeEdges :: [(DID, b)]
    -- ^ Note that IDs on the `nodeEdges` list can be repeated.
    } deriving (Show, Eq, Ord, Functor)


-- | Empty DAG.
empty :: DAG a b
empty = DAG S.empty M.empty


-- | Lookup the ID in the DAG.
lookup :: DID -> DAG a b -> Maybe (Node a b)
lookup i dag = M.lookup i (nodeMap dag)


-- -- | Insert the node to the DAG.
-- insert :: DID -> Node a b -> DAG a b -> DAG a b
-- insert i n dag = dag
--     {nodeMap = M.insert i n (nodeMap dag)}


-- | Retrieve the label of the DAG node.
label :: DID -> DAG a b -> Maybe a
label i dag = nodeLabel <$> lookup i dag


-- | Retrieve the weight of the DAG node.
value :: DID -> DAG a b -> Maybe b
value i dag = nodeValue <$> lookup i dag


-- | Edges outgoing from the given node.
edges :: DID -> DAG a b -> [(DID, b)]
edges i DAG{..} =
    maybe [] nodeEdges
        (M.lookup i nodeMap)


-- | The list of children IDs for the given node ID.
children :: DID -> DAG a b -> [DID]
children i = map fst . edges i


-- | Check whether the given node is a root.
isRoot :: DID -> DAG a b -> Bool
isRoot i dag = S.member i (rootSet dag)


-- | A function which tells whether the given node is a spine node.
-- The function employs memoization once it is supplied with its first
-- argument (the grammar DAG).
isSpine :: DAG (O.Node n t) w -> DID -> Bool
isSpine dag =
    spine
  where
    spine = Memo.wrap DID unDID Memo.integral spine'
    spine' i
        | isFoot i dag = True
        | otherwise    = or . map spine . children i $ dag


-- | Is it a foot node?
isFoot :: DID -> DAG (O.Node n t) w -> Bool
isFoot i dag = case lookup i dag of
    Nothing -> False
    Just n  -> case nodeLabel n of
        O.Foot _  -> True
        _         -> False


-- | Check whether the given node is a leaf.
isLeaf :: DID -> DAG a b -> Bool
isLeaf i = null . edges i


-- | The set of descendant IDs for the given ID.
-- The argument ID is not included in the resulting set.
descendants :: DID -> DAG a b -> S.Set DID
descendants i dag = S.unions
    [ S.insert j (descendants j dag)
    | j <- children i dag ]


-- | The set of all node IDs in the DAG.
nodeSet :: DAG a b -> S.Set DID
nodeSet dag = S.fromList
    [ i
    | r <- S.toList (rootSet dag)
    , i <- r : S.toList (descendants r dag) ]


-- TODO: Similar instance already inferred in the "Gen" module.
deriving instance (Ord a) => (Ord (R.Tree a))


----------------------
-- Mapping
----------------------


-- | Map over node values.
--
-- NOTE: This does not touch edge values!
--
nmap :: (DID -> b -> b) -> DAG a b -> DAG a b
nmap f dag = dag
  { nodeMap = M.fromList $ do
      (did, node) <- M.toList (nodeMap dag)
      return (did, updateNode did node)
  }
  where
    updateNode did node = node
      { nodeValue = f did (nodeValue node)
      }


----------------------
-- Concat
----------------------


-- | Concatenate two DAGs (without any subtree sharing).  
concatDAG :: DAG a b -> DAG a b -> DAG a b
concatDAG l r0 = DAG
  { rootSet = S.union (rootSet l) (rootSet r)
  , nodeMap = M.union (nodeMap l) (nodeMap r)
  } where
    m = M.size (nodeMap l)
    -- n = M.size (nodeMap r)
    r = mapDID (+m) r0


-- | Concatenate several DAGs (without any subtree sharing).
concatDAGs :: [DAG a b] -> DAG a b
concatDAGs = L.foldl' concatDAG empty


-- | Map a function over node IDs.
mapDID :: (Int -> Int) -> DAG a b -> DAG a b
mapDID f dag = DAG
  { rootSet =
      S.fromList . map g . S.toList $ rootSet dag
  , nodeMap = M.fromList
      [ (g nodeID, mapNodeID node)
      | (nodeID, node) <- M.toList (nodeMap dag)
      ]
  } where
    g (DID k) = DID (f k)
    mapNodeID node = node
      { nodeEdges =
          [ (g did, v)
          | (did, v) <- nodeEdges node
          ] 
      }


----------------------
-- Basic Convertion
----------------------


-- | Transform the given TAG into a `DAG`.  Common subtrees are
-- implicitely shared in the resulting `DAG`.
dagFromForest :: (Ord a) => [R.Tree a] -> DAG a ()
dagFromForest ts =
    let (rootList, dagSt) = runDagM (mapM (fromTree True) ts)
     in DAG
        { rootSet = S.fromList rootList
        , nodeMap = M.union
            (revMap (rootMap dagSt))
            (revMap (normMap dagSt)) }


-- | Type of the monad used to create DAGs from trees.
type DagM a b = E.State (DagSt a b)


-- | State underlying `DagM`.
-- Invariant: sets of IDs in `rootMap` and `normMap`
-- are disjoint.
--
-- TODO: Does it make sense to allow b \= () here?
--
-- TODO: At the moment, it seems that it doesn't make sense
--   to distinguish root from normal nodes!
--
data DagSt a b = DagSt
    { rootMap :: M.Map (Node a b) DID
    -- ^ Map for top-level nodes
    , normMap :: M.Map (Node a b) DID
    -- ^ Map for other nodes.
    }


-- | Run the DagM monad.
runDagM :: DagM a b c -> (c, DagSt a b)
runDagM = flip E.runState (DagSt M.empty M.empty)


-- | Create a DAG node from a tree.
fromTree :: (Ord a) => Bool -> R.Tree a -> DagM a () DID
fromTree topLevel t = do
    childrenIDs <- mapM (fromTree False) (R.subForest t)
    addNode topLevel $ Node
        { nodeLabel = R.rootLabel t
        , nodeValue = ()
        , nodeEdges = zip childrenIDs $ repeat () }


-- | Add a node (unless already exists) to the underlying
-- DAG and return its ID.
addNode :: (Ord a, Ord b) => Bool -> Node a b -> DagM a b DID
addNode topLevel x = do
    mayID <- getNode topLevel x
    case mayID of
        Nothing -> do
            i <- newID
            putNode topLevel i x
            return i
        Just i ->
            return i


-- | Get the node from the underlying map.
getNode :: (Ord a, Ord b) => Bool -> Node a b -> DagM a b (Maybe DID)
getNode topLevel n =
    let selectMap = if topLevel then rootMap else normMap
     in E.gets (M.lookup n . selectMap)


-- | Put the node in the underlying map.
putNode :: (Ord a, Ord b) => Bool -> DID -> Node a b -> DagM a b ()
putNode True i x = E.modify' $ \s -> s
    {rootMap = M.insert x i (rootMap s)}
putNode False i x = E.modify' $ \s -> s
    {normMap = M.insert x i (normMap s)}


-- | Retrieve new, unused node identifier.
newID :: DagM a b DID
newID = E.gets $ \DagSt{..} -> DID $ M.size rootMap + M.size normMap


----------------------
-- Weighted Convertion
----------------------


-- | A version of `dagFromWeightedForest` which takes a list of forests,
-- creates a separate DAG for each of them, and concatenates the resulting DAGs
-- in the end.
dagFromWeightedForests
    :: (Ord a)
    => [[(R.Tree a, Weight)]]
    -> DAG a Weight
dagFromWeightedForests = concatDAGs . map dagFromWeightedForest


-- | Transform the given weighted grammar into a `DAG`.  Common subtrees are
-- shared in the resulting `DAG`, while weights are assigned to the DAG roots
-- corresponding to the individual elementary trees.
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
            M.fromListWith min
                (zip rootList weights)


-- | Weigh the DAG given a mapping from root nodes to weights.
-- Each node represents a tree from the input forest, thus the
-- weights are in fact assigned to the input trees.
--
-- We assume that if a weight for a given root is not provided, then
-- it's equal to @0@.
weighDAG
    :: DAG a ()         -- ^ The DAG
    -> M.Map DID Weight -- ^ Weights assigned to DAG roots
    -> DAG a Weight     -- ^ Weighted DAG
weighDAG dag rootWeightMap = DAG
    { rootSet = rootSet dag
    , nodeMap = M.fromList
        [ (i, updateNode i n)
        | (i, n) <- M.toList (nodeMap dag) ] }
   where
     updateNode i n = mkNode i n $
       case M.lookup i rootWeightMap of
         Nothing -> 0
         Just x  -> x
     mkNode i n w = n
       { nodeValue = w
       , nodeEdges = [(j, 0) | j <- children i dag] }


----------------------
-- Dummy Convertion
----------------------


-- | Transform the given weighted grammar into a dummy `DAG`.  No subtree
-- sharing takes place.
dummyFromWeightedForest
    :: [(R.Tree a, Weight)]
    -> DAG a Weight
dummyFromWeightedForest forestWeights =
    let (forest, weights) = unzip forestWeights
        (rootList, dag0) = flip E.runState empty . forM forest $ \t -> do
          i <- dummyTree t
          saveRoot i
          return i
     in weighDAG dag0 $
            M.fromListWith min
                (zip rootList weights)


-- | Put the node in the underlying map.
saveRoot :: DID -> E.State (DAG a b) ()
saveRoot i = E.modify' $ \s -> s
    {rootSet = S.insert i (rootSet s)}


-- | Create a DAG node from a tree.
dummyTree :: R.Tree a -> E.State (DAG a ()) DID
dummyTree t = do
    childrenIDs <- mapM dummyTree (R.subForest t)
    addDummyNode $ Node
        { nodeLabel = R.rootLabel t
        , nodeValue = ()
        , nodeEdges = zip childrenIDs $ repeat () }


-- | Add a node (unless already exists) to the underlying
-- DAG and return its ID.
addDummyNode :: Node a b -> E.State (DAG a b) DID
addDummyNode x = do
    i <- dummyID
    putDummy i x
    return i


-- | Put the node in the underlying map.
putDummy :: DID -> Node a b -> E.State (DAG a b) ()
putDummy i x = E.modify' $ \s -> s
    {nodeMap = M.insert i x (nodeMap s)}


-- | Retrieve new, unused node identifier.
dummyID :: E.State (DAG a b) DID
dummyID = E.gets $ \DAG{..} -> DID $ M.size nodeMap


----------------------
-- Grammar Flattening
----------------------


{- $rule
  The Earley-style TAG parser (see `NLP.Partage.Earley`) assumes that
  the grammar is represented by a set of flat production grammar rules.
  Each rule serves to recognize a specific subtree of some elementary grammar
  tree.  Since common subtrees are shared in the DAG representation of the grammar,
  single rule can actually serve to recognize a specific subtree common to many
  different elementary trees.
-}


-- | A production rule, responsible for recognizing a specific
-- (unique) non-trivial (of height @> 0@) subtree of an elementary
-- grammar tree.  Due to potential subtree sharing, a single rule can
-- be responsible for recognizing a subtree common to many different
-- elementary trees.
data Rule = Rule {
    -- | Head of the rule
      headR :: DID
    -- | Body of the rule
    , bodyR :: [DID]
    } deriving (Show, Eq, Ord)


-- | Extract rules from the grammar DAG.
rulesFromDAG :: DAG a w -> S.Set Rule
rulesFromDAG dag = S.fromList
    [ Rule i (children i dag)
    | i <- M.keys (nodeMap dag)
    , not (isLeaf i dag) ]


-- | Extract rules and the corresponding weights from the weighted grammar DAG.
rulesMapFromDAG :: DAG a Weight -> M.Map Rule Weight
rulesMapFromDAG dag = M.fromList
    [ let (is, ws) = unzip (edges i dag)
          w = maybe 0 id (value i dag)
      in  (Rule i is, w + sum ws)
    | i <- M.keys (nodeMap dag)
    , not (isLeaf i dag) ]


----------------------
-- Parent map
----------------------


{- $parent-map
  A `ParentMap` is a map from node IDs to the IDs of their parents.
-}


-- | A map from nodes to their parent IDs.
type ParentMap = M.Map DID (S.Set DID)


-- | Compute the reverse DAG representation: a map from an ID @i@
-- to the set of IDs of the nodes from which an edge leading to @i@
-- exists.  In simpler words, for each ID, a set of its parent IDs.
parentMap :: DAG a b -> ParentMap
parentMap dag = M.fromListWith S.union
    [ (j, S.singleton i)
    | i <- S.toList (nodeSet dag)
    -- below we don't care about the order of children
    , j <- setNub $ children i dag ]


-- | List of parents for the given node ID.
-- Empty if ID not present in the map.
parents :: DID -> ParentMap -> S.Set DID
parents i = maybe S.empty id . M.lookup i


----------------------
-- Ensemble
----------------------


-- | A datatype which contains the grammar in its various forms needed for
-- parsing. The main component is the `dagGram` DAG, from which the other two
-- elements (`factGram` and `termWei`) can be derived.
data Gram n t = Gram
    { dagGram  :: DAG (O.Node n (Maybe t)) Weight
    -- ^ Grammar as a DAG.
    , factGram :: M.Map Rule Weight
    -- ^ Grammar as a set of production rules, with a weight assigned to each
    -- rule.
    , termWei  :: M.Map t Weight
    -- ^ The lower bound estimates on reading terminal weights. Based on the
    -- idea that weights of the elementary trees can be evenly distributed over
    -- their terminals which, in turn, can serve to compute the lower bound
    -- estimates on the cost of parsing the remaining part of an input sentence.
    }


-- | Construct `Gram` from the given weighted grammar.
-- 
-- The behaviour of this function depends on some compile-time flags.
--
mkGram
    :: (Ord n, Ord t)
    => [(O.Tree n (Maybe t), Weight)]
    -> Gram n t
#if Compression
mkGram ts = Gram
    { dagGram   = 
        -- trace ("dag size: " ++ show (M.size $ nodeMap dagGram_))
        dagGram_
    , factGram  =
        -- trace ("ruleMap size: " ++ show (M.size ruleMap))
        ruleMap
    , termWei   = mkTermWei ts }
  where
    ruleMap = rulesMapFromDAG dagGram_
#if ExtraCompression
    dagGram_ = dagFromWeightedForest ts
#else
    dagGram_ = dagFromWeightedForests $ M.elems byTerm
    byTerm = M.fromListWith (++)
      [ (termSet t, [(t, w)])
      | (t, w) <- ts ]
    termSet = S.fromList . catMaybes . O.project
#endif
#else
mkGram = mkDummy
#endif


-- | Construct a dummy `Gram` (no subtree sharing) from the given weighted
-- grammar.
mkDummy
    :: (Ord t)
    => [(O.Tree n (Maybe t), Weight)]
    -> Gram n t
mkDummy ts = Gram
    { dagGram   = dagGram_
    , factGram  = rulesMapFromDAG dagGram_
    -- , termWei   = mkTermWei (map (first O.decode) ts) }
    , termWei   = mkTermWei ts }
  where
    dagGram_ = dummyFromWeightedForest ts


-- | Compute the lower bound estimates on reading terminal weights.
--
-- Based on the idea that weights of the elementary trees are evenly distributed
-- over their terminals.
mkTermWei
    :: (Ord t)
    => [(O.Tree n (Maybe t), Weight)]   -- ^ Weighted grammar
    -> M.Map t Weight
mkTermWei ts = M.fromListWith min
    [ (x, w / fromIntegral n)
    | (t, w) <- ts
    , let terms = catMaybes (O.project t)
          n = length terms
    , x <- terms ]


----------------------
-- Convertion to tree
----------------------


-- | Retrieve a tree rooted in the given DAG node.
-- Node and edge values will be discarded.
-- Raises an exception for an invalid node ID.
toTree :: DID -> DAG a b -> Maybe (R.Tree a)
toTree i dag = do
  x <- label i dag
  let js = children i dag
  ts <- mapM (flip toTree dag) js
  return $ R.Node x ts


----------------------
-- Misc
----------------------


-- -- | List the terminal leaves of the tree.
-- listTerms :: O.SomeTree n t -> [t]
-- listTerms (Left t)  = T.project t
-- listTerms (Right a) = T.project (T.auxTree a)


-- | Reverse map.
revMap :: (Ord b) => M.Map a b -> M.Map b a
revMap =
    let swap (x, y) = (y, x)
     in M.fromList . map swap . M.toList


-- | Change list to a set, but still represented by a list...
-- Similar to `L.nub`, but the order of elements may change.
setNub :: Ord a => [a] -> [a]
setNub = S.toList . S.fromList
