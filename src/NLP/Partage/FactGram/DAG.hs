{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


-- | TAG conversion into a DAG.


module NLP.Partage.FactGram.DAG
(
-- * DAG
-- ** Types
  DAG (..)
, Node(..)
, DID(..)
-- ** Utils
, setIDs
, isRoot
, isLeaf
, isFoot
, isSpine
, edges
, children
, descendants
, label
, value
, lookup
, insert
-- -- ** Parent Map
-- , parents
-- , parentMap

-- * Ensemble
, Gram (..)
, mkGram

-- * Conversion
, Rule(..)
, dagFromForest
, rulesFromDAG

-- * Low-level internal
-- (Use on your own responsibility)
, DagSt(..)
, runDagM
, fromTree
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


-- | Node identifier in the `DAG`.  Invariant: non-negative
-- (see `newID`).
newtype DID = DID { unDID :: Int }
    deriving (Show, Eq, Ord)


-- | A DAG representation of a tree forest in which identical
-- subtrees are shared, i.e. a subtree common to several trees is
-- represented by a single subgraph in the DAG.
--
-- Type @a@ represents values of DAG nodes, type @b@ -- values of
-- DAG edges.
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


-- | Lookup the ID in the DAG.
lookup :: DID -> DAG a b -> Maybe (Node a b)
lookup i dag = M.lookup i (nodeMap dag)


-- | Insert the node to the DAG.
insert :: DID -> Node a b -> DAG a b -> DAG a b
insert i n dag = dag
    {nodeMap = M.insert i n (nodeMap dag)}


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
-- Memoization turned on.
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


-- | The set of all IDs in the DAG.
setIDs :: DAG a b -> S.Set DID
setIDs dag = S.fromList
    [ i
    | r <- S.toList (rootSet dag)
    , i <- r : S.toList (descendants r dag) ]


-- TODO: Similar instance already inferred in the "Gen" module.
deriving instance (Ord a) => (Ord (R.Tree a))


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
-- Grammar Flattening
----------------------


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
-- Ensemble
----------------------


-- | The datatype which contains the grammar in its different forms
-- needed for parsing.
data Gram n t = Gram
    { dagGram  :: DAG (O.Node n t) ()
    -- ^ Grammar as a DAG (with subtree sharing)
    , factGram :: S.Set Rule
    -- ^ Factorized (flattened) form of the grammar
    }


-- | Construct `Gram` based on the given weighted grammar.
mkGram :: (Ord n, Ord t) => [O.Tree n t] -> Gram n t
mkGram ts = Gram
    { dagGram   = theDag
    , factGram  = rulesFromDAG theDag }
  where
    theDag = dagFromForest ts


----------------------
-- Misc
----------------------


-- | Reverse map.
revMap :: (Ord b) => M.Map a b -> M.Map b a
revMap =
    let swap (x, y) = (y, x)
     in M.fromList . map swap . M.toList
