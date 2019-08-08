{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types      #-}


-- | A* heuristic.
--
-- Note that, while the heuristic is built from a weighted automaton, it actually
-- requires that the automaton contains no reentrancies, i.e. that the automaton
-- is, in fact, a trie.
--
-- While, in theory, the module functions could work directly on tries, it is easier
-- to assume the same automaton abstraction as in the parsing module.


module NLP.Partage.AStar.HeuristicNew
(
-- * Bag
  Bag
, pocket
, bagEmpty
, bagAdd
, bagDiff
, bagFromList

-- * Heuristic
, Esti(..)
, mkEsti
) where


import qualified Control.Arrow                   as Arr
-- import           Data.Hashable (Hashable)
-- import qualified Data.HashTable.IO          as H
import           Data.Maybe                      (catMaybes)
import qualified Data.List                       as L
import qualified Data.Map.Strict                 as M
import qualified Data.MemoCombinators            as Memo
import qualified Data.Set                        as S

import           Data.DAWG.Ord                   (ID)

import           NLP.Partage.SOrd                (SOrd)
-- import qualified NLP.Partage.AStar.Auto          as I
import           NLP.Partage.AStar.Heuristic.Bag
import qualified NLP.Partage.AStar.Base          as B
import qualified NLP.Partage.Auto                as A
import qualified NLP.Partage.DAG                 as D
import qualified NLP.Partage.Tree.Other          as O
-- import qualified NLP.Partage.Earley.AutoAP     as E

import Debug.Trace (trace)


--------------------------------
-- Heuristic, part 1
--------------------------------


-- | Distance estimation heuristic.
data Esti t = Esti
  { dagAmort :: D.DID -> D.Weight
  -- ^ Amortized weight of the dag node
  , trieAmort :: ID -> D.Weight
  -- ^ Amortized weight of the trie node
  , prefEsti :: Int -> D.Weight
  -- ^ Prefix cost estimation
  , suffEsti :: Int -> D.Weight
  -- ^ Suffix cost estimation
  , minDepEsti  :: Int -> D.Weight
  -- ^ Minimal dependency cost of a token on a given position
  }


-- | Create `Esti` based on several basic pieces of information.
mkEsti
  :: (SOrd t, Ord n)
  => Memo.Memo t        -- ^ Memoization strategy for terminals
  -> D.Gram n t         -- ^ The underlying grammar
  -> A.WeiGramAuto n t  -- ^ The underlying automaton
  -> B.Input t          -- ^ Input sentence
  -> M.Map t Int        -- ^ Position map
  -> M.Map Int (M.Map Int D.Weight)
                        -- ^ Head map
  -> Esti t
mkEsti _memoElem D.Gram{..} autoGram input posMap hedMap = Esti
  { dagAmort = amortDag
  , trieAmort = amortTrie
  , prefEsti = \p -> maybe 0 id (M.lookup p prefSum)
  , suffEsti = \q -> maybe 0 id (M.lookup q suffSum)
  , minDepEsti = depCost
  }
  where
    -- sentence length
    sent = B.inputSent input
    sentLen = length sent

    -- DAG enriched with minimal dependency weights
    dag = addMinDepWeights posMap depCostMap dagGram

    -- cost of the given node
    nodeCost i = case labelValue i dag of
      Nothing -> error "nodeCost: incorrect ID"
      Just (_, v) -> v

    -- cost of the outer part, enriched with the cost of the node itself
    supCostDag = supCost dag
    -- costDag i = fmap (+nodeCost i) (supCostDag i)
    costDag = supCostDag

    -- DAG amortized cost
    amortDag i = minimumInf
      [ w - termBagCost bag
      | (bag, w) <- M.toList (costDag i) ]

    -- trie amortized cost
    amortTrie i = minimumInf
      [ w - termBagCost bag
      | (bag, w) <- M.toList (costTrie i) ]
    -- TODO: make sure that the `trieCost` of the "almost root"
    -- accounts for the root node cost!
    costTrie = trieCost dag autoGram

    -- minimal supertagging + dependency cost of the given bag
    termBagCost = minCost termWei posMap depCostMap

    -- miminal dependency cost for the individual positions
    depCost dep = maybe 0 id
      (M.lookup dep depCostMap)
    depCostMap = M.fromList
      [ (dep, minimumInf (M.elems heds))
      | (dep, heds) <- M.toList hedMap ]

    -- miminal supertagging cost for a given terminal
    termCost t = maybe 0 id
      (M.lookup t termWei)

    -- partial sums
    prefSum = M.fromList . sums $
      (0, 0) :
      [ (dep, depCost (dep-1) + termCost (B.terminal tok))
      | (dep, tok) <- zip [1..] sent ]
    suffSum = M.fromList . sums $
      (sentLen, 0) :
      [ (dep, depCost dep + termCost (B.terminal tok))
      | (dep, tok) <- reverse $ zip [0..] sent ]


-- | Calculate partial sums over the `snd` elements.
sums :: [(a, Double)] -> [(a, Double)]
sums =
  go 0
    where
      go acc ((k, x) : xs) =
        let acc' = acc + x
        in  (k, acc') : go acc' xs
      go _ [] = []


-- | Minimal cost of scanning the terminals in the given bag.
minCost
  :: (Ord t)
  => M.Map t D.Weight   -- ^ Minimal terminal scanning weights
  -> M.Map t Int        -- ^ Position map
  -> M.Map Int D.Weight -- ^ Minimal dependency weight map
  -> Bag t              -- ^ Bag of terminals
  -> D.Weight
minCost termWei posMap headWei bag =
  sum
    [ (w1 + w2) * fromIntegral n
    | (t, n) <- M.toList bag 
    , let w1 = maybe 0 id $ M.lookup t termWei
    , let w2 = maybe 0 id $ do
                  k <- M.lookup t posMap
                  M.lookup k headWei
    ]


-- | Enrich the DAG with the minimal dep weights.
addMinDepWeights
  :: (Ord t)
  => M.Map t Int        -- ^ Position map
  -> M.Map Int D.Weight -- ^ Minimal dependency weight map
  -> D.DAG (O.Node n (Maybe t)) D.Weight
  -> D.DAG (O.Node n (Maybe t)) D.Weight
addMinDepWeights posMap depMap dag0 =
  D.nmap f dag0
  where
    terminals = catMaybes . O.project
    f did w0
      | D.isRoot did dag0 = maybe err (w0+) $ do
          tree <- D.toTree did dag0
          [t] <- return (terminals tree)
          k <- M.lookup t posMap
          M.lookup k depMap
--           v <- M.lookup k depMap
--           return $ if v < 0
--              then trace ("negative final root val: " ++ show v) v
--              else v
      | w0 /= 0 =
          error "addMinDepWeights: non-root weight /= 0!"
      | otherwise = w0
    err = error "addMinDepWeights: something wrong!"


--------------------------------
-- Heuristic: Tree Cost
--------------------------------


-- | Compute the weight of the grammar subtree corresponding to the
-- given DAG node.  Return also the corresponding bag of terminals
-- stored in leaves of the subtree.
subCost
    :: (Ord n, Ord t, Num w)
    => D.DAG (O.Node n (Maybe t)) w     -- ^ Grammar DAG
    -> D.DID                            -- ^ ID of the DAG node
    -> (Bag t, w)
subCost dag =
    cost
  where
    cost = Memo.wrap D.DID D.unDID Memo.integral cost'
    cost' i = case labelValue i dag of
      Nothing -> error "subCost: incorrect ID"
      Just (x, v) -> case x of
        O.Term (Just t) -> (pocket t, v)
        _  -> L.foldl' add2 (bagEmpty, v)
          [ Arr.second (+w) (cost j)
          | (j, w) <- D.edges i dag ]


--------------------------------
-- Heuristic: Super Tree Cost
--------------------------------


-- | Compute the bags of terminals and the corresponding (minimal) weights
-- for the individual super-trees surrounding the given DAG node.
--
-- WARNING: the implementation is currently tweaked so that the weight of the
-- root is equal to the weight of the corresponding ET (theoretically it should
-- be 0).  See the line:
--
--    \i -> fmap (+nodeCost i) (sup i)
--
-- Note also that this impacts roots only because non-root nodes do not have
-- weights assigned.
--
supCost
    :: (Ord n, Ord t, Num w, Ord w)
    => D.DAG (O.Node n (Maybe t)) w     -- ^ Grammar DAG
    -> D.DID                            -- ^ ID of the DAG node
    -> M.Map (Bag t) w
supCost dag =
  -- sup
  \i -> fmap (+nodeCost i) (sup i)
  where
    sup = Memo.wrap D.DID D.unDID Memo.integral sup'
    sup' i
      | D.isRoot i dag = M.singleton bagEmpty 0
      | otherwise = M.fromListWith min
          [ (sup_j `add2` sub j) `sub2` sub i
          -- above, we can be sure that (sub i) is a subset
          -- of (sup_j `add2` sub j); note that, otherwise,
          -- the `sub2` operation would be unsafe, given that
          -- it relies on the `bagDiff` function
          | j <- S.toList (D.parents i parMap)
          , sup_j <- M.toList (sup j) ]
    sub = subCost dag
    parMap = D.parentMap dag
    -- cost of the given node
    nodeCost i = case labelValue i dag of
      Nothing -> error "nodeCost: incorrect ID"
      Just (_, v) -> v


--------------------------------
-- Heuristic: Super Tree Cost
--------------------------------


-- | Compute the bags of terminals and the corresponding
-- (minimal) weights which still need to be scanned before
-- some full elementary tree is parsed starting from the
-- given automaton state.
--
-- Note that for final automaton states (at the moment it is
-- guaranteed that such states are also leaves) the function
-- returns the empty map, even though we could possibly compute
-- and return 'sup' for such states.
trieCost
    :: (Ord n, Ord t)
    => D.DAG (O.Node n (Maybe t)) D.Weight  -- ^ Grammar DAG
    -> A.WeiGramAuto n t            -- ^ The weighted automaton
    -> ID                           -- ^ ID of the *automaton* node
    -> M.Map (Bag t) D.Weight
trieCost dag wei@A.WeiAuto{..} =
  cost
  where
    cost = Memo.integral cost'
    cost' i =
      if null (edgesWei i)
         then sup (prevEdge i)
         else M.fromListWith min
              [ Arr.second (+w) (bag_e `add2` bag_j)
              | (e, w, j) <- edgesWei i
              , bag_j <- M.toList (cost j)
              , bag_e <- M.toList (edge e) ]
    -- find the index of the edge preceding the given state ID;
    -- works under the assumption that the automaton is a trie and
    -- that each final node has precisely one incoming head edge.
    -- NOTE: it's also the reason for which we need to store
    -- identifiers in all edges: in particular, in edges
    -- which represent roots of elementary trees.
    -- Recall that in the previous solution, such head edges
    -- did not contain information about the corresponding
    -- DAG node (they had no index).
    prevEdge ai = head [di | A.Head di <- S.toList (ing ai)]
    edge e = case e of
      A.Head _ -> M.singleton bagEmpty 0
      A.Body i ->
        let (k, v) = sub i
        in M.singleton k v
    sub = subCost dag
    sup = supCost dag
    ing = incoming wei


-- | Build a map which, for a given automaton ID, returns
-- the set of incoming edges.
incoming :: A.WeiGramAuto n t -> ID -> S.Set (A.Edge D.DID)
incoming wei =
  go
  where
    go i = maybe S.empty id (M.lookup i m)
    auto = A.fromWei wei
    m = M.fromListWith S.union
      [ (j, S.singleton x)
      | (_, x, j) <- A.allEdges auto ]


--------------------------------
-- Misc
--------------------------------


-- | Add two bags enriched with weights.
add2 :: (Ord a, Num w) => (Bag a, w) -> (Bag a, w) -> (Bag a, w)
add2 (b1, w1) (b2, w2) = (bagAdd b1 b2, w1 + w2)


-- | Substract two bags enriched with weights.
sub2 :: (Ord a, Num w) => (Bag a, w) -> (Bag a, w) -> (Bag a, w)
sub2 (b1, w1) (b2, w2) = (bagDiff b1 b2, w1 - w2)


-- | Returns the label and the value of the node.
labelValue :: D.DID -> D.DAG a b -> Maybe (a, b)
labelValue i dag = do
  x <- D.label i dag
  y <- D.value i dag
  return (x, y)


-- | Infinite value.
infinity :: Double
infinity = read "Infinity"


-- | Mininum in the list or the infinite value for empty list.
minimumInf :: [Double] -> Double
minimumInf [] = infinity
minimumInf xs = minimum xs
