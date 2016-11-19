{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


-- | DAG representation of TAG grammars.
--
-- The input TAG can be seen as a set of elementary (initial and auxiliary)
-- grammar trees. This module provides an alternative, more compact
-- representation in which common subtrees are shared amongst the corresponding
-- elementary trees. In this representation the grammar takes for form of a
-- directed acyclic graph (DAG) which allows to represent sharing in a natural
-- way.


module NLP.Partage.DAG
(
-- * DAG
  DAG
, empty
, DID (..)
-- ** Identifiers
, rootMap
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
-- ** Parent map
-- $parent-map
, ParentMap
, parentMap
, parents

-- * Ensemble
, Gram (..)
, mkGram

-- * Conversion
, dagFromForest
, rulesFromDAG
-- ** Rule
-- $rule
, Rule(..)

-- * Tree
, toTree
) where


import qualified Control.Monad.State.Strict as E
import           Prelude                    hiding (lookup)

import qualified Data.Map.Strict            as M
import qualified Data.MemoCombinators       as Memo
import qualified Data.Set                   as S
import qualified Data.Tree                  as R

import qualified NLP.Partage.Tree.Other     as O


----------------------
-- DAGs
----------------------


-- | `DAG` node identifier.
newtype DID = DID { unDID :: Int }
    deriving (Show, Eq, Ord)


-- | A DAG representation of a tree forest in which identical
-- subtrees are shared, i.e. a subtree common to several trees is
-- represented by a single subgraph in the DAG.
--
-- Type @a@ represents values stored in DAG nodes, type @b@ --
-- additional values kept in DAG *root* nodes only.
data DAG a b = DAG
    { rootMap :: M.Map DID b
    -- ^ The set of roots of the DAG, together with the accompanying values
    , nodeMap :: M.Map DID (Node a)
    -- ^ The set of nodes in the DAG
    } deriving (Functor)


-- | A single node of the `DAG`.
data Node a = Node
    { nodeLabel :: a
    , nodeEdges :: [DID]
    -- ^ Note that IDs on the `nodeEdges` list can be repeated.
    } deriving (Show, Eq, Ord, Functor)


-- | Empty DAG.
empty :: DAG a b
empty = DAG M.empty M.empty


-- | Lookup the ID in the DAG.
lookup :: DID -> DAG a b -> Maybe (Node a)
lookup i dag = M.lookup i (nodeMap dag)


-- | Retrieve the label of the given DAG node.
-- Returns `Nothing` in case of invalid `DID`.
label :: DID -> DAG a b -> Maybe a
label i dag = nodeLabel <$> lookup i dag


-- | Lookup the value assigned to the root in the DAG.
-- Returns `Nothing` in case of invalid `DID`.
value :: DID -> DAG a b -> Maybe b
value i dag = M.lookup i (rootMap dag)


-- | Edges outgoing from the given node.
edges :: DID -> DAG a b -> [DID]
edges i DAG{..} =
    maybe [] nodeEdges
        (M.lookup i nodeMap)


-- | The list of children IDs for the given node ID.
children :: DID -> DAG a b -> [DID]
-- children i = map fst . edges i
children = edges
{-# INLINE edges #-}


-- | Check whether the given node is a root.
isRoot :: DID -> DAG a b -> Bool
isRoot i dag = M.member i (rootMap dag)


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
    | r <- M.keys (rootMap dag)
    , i <- r : S.toList (descendants r dag) ]


-- TODO: Similar instance already inferred in the "Gen" module.
deriving instance (Ord a) => (Ord (R.Tree a))


----------------------
-- Basic Convertion
----------------------


-- dagFromForest :: (Ord a) => [R.Tree a] -> DAG a ()
-- dagFromForest ts =
--   let (rootList, dagSt) = runDagM (mapM fromTree ts)
--   in DAG
--      { rootMap = M.fromList . zip rootList $ repeat ()
--      , nodeMap = revMap dagSt }



-- | Transform the given TAG into a `DAG`.  Common subtrees are
-- implicitely shared in the resulting `DAG`.
dagFromForest
    :: (Ord a)
    => [(R.Tree a, b)]
    -> DAG a b
dagFromForest forestVals =
  let (forest, vals) = unzip forestVals
      (rootList, dagMap) = runDagM (mapM fromTree forest)
  in DAG
     { rootMap = M.fromList $ zip rootList vals
     , nodeMap = revMap dagMap }


-- | Type of the monad used to create DAGs from trees.
type DagM a = E.State (DagSt a)


-- | State underlying `DagM`.
-- Invariant: sets of IDs in `rootMap` and `otherMap`
-- are disjoint.
type DagSt a = M.Map (Node a) DID


-- | Run the DagM monad.
runDagM :: DagM a b -> (b, DagSt a)
runDagM = flip E.runState M.empty


-- | Create a DAG node from a tree.
fromTree :: (Ord a) => R.Tree a -> DagM a DID
fromTree t = do
    childrenIDs <- mapM fromTree (R.subForest t)
    addNode $ Node
        { nodeLabel = R.rootLabel t
        , nodeEdges = childrenIDs }


-- | Add a node (unless already exists) to the underlying
-- DAG and return its ID.
addNode :: (Ord a) => Node a -> DagM a DID
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
getNode :: (Ord a) => Node a -> DagM a (Maybe DID)
getNode = E.gets . M.lookup


-- | Put the node in the underlying map.
putNode :: (Ord a) => DID -> Node a -> DagM a ()
putNode i x = E.modify' $ M.insert x i


-- | Retrieve new, unused node identifier.
newID :: DagM a DID
newID = E.gets $ \m -> DID $ M.size m


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
-- parsing. The main component is the `dagGram` DAG, from which `factGram` is
-- derived.
data Gram n t w = Gram
    { dagGram  :: DAG (O.Node n t) w
    -- ^ Grammar as a DAG.
    , factGram :: S.Set Rule
    }


-- | Construct `Gram` from the given weighted grammar.
mkGram
    :: (Ord n, Ord t)
    => [(O.Tree n t, w)]
    -> Gram n t w
mkGram ts = Gram
    { dagGram   = dagGram_
    , factGram  = rulesFromDAG dagGram_ }
  where
    dagGram_ = dagFromForest ts


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


-- | Reverse map.
revMap :: (Ord b) => M.Map a b -> M.Map b a
revMap =
    let swap (x, y) = (y, x)
     in M.fromList . map swap . M.toList


-- | Change list to a set, but still represented by a list...
-- Similar to `L.nub`, but the order of elements may change.
setNub :: Ord a => [a] -> [a]
setNub = S.toList . S.fromList
