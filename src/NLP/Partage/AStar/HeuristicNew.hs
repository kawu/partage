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

-- import Debug.Trace (trace)


--------------------------------
-- Heuristic, part 1
--------------------------------


-- | Distance estimation heuristic.
data Esti t = Esti
  { termEsti :: Bag t -> D.Weight
  , trieEsti :: ID -> Bag t -> D.Weight
  -- , dagEsti  :: D.DID -> M.Map (Bag t) D.Weight
  , dagEsti  :: D.DID -> Bag t -> D.Weight
  -- ^ Bags of terminals and the corresponding (minimal) weights
  -- for the individual super-trees surrounding the given DAG node.
  , dagAmort :: D.DID -> D.Weight
  -- ^ Amortized weight of the dag node

  -- <<NEW 12.2018>>

  , trieAmort :: ID -> D.Weight
  -- ^ Amortized weight of the trie node

  , depPrefEsti :: Int -> D.Weight
  -- ^ Dependency related cost estimation (prefix)
  , depSuffEsti :: Int -> D.Weight
  -- ^ Dependency related cost estimation (suffix)
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
  { termEsti = estiTerm
  , trieEsti = estiCost2 autoGram dagGram estiTerm
  , dagEsti  = estiNode
  , dagAmort = amortDag 
  , trieAmort = amortTrie 
  , depPrefEsti = \p -> maybe 0 id (M.lookup p prefDepSum)
  , depSuffEsti = \q -> maybe 0 id (M.lookup q suffDepSum)
  , prefEsti = \p -> maybe 0 id (M.lookup p prefSum)
  , suffEsti = \q -> maybe 0 id (M.lookup q suffSum)
  , minDepEsti = depCost
  }
  where
    -- sentence length
    sent = B.inputSent input
    sentLen = length sent

    estiTerm = estiCost1 termWei
--     estiNode i bag = minimumInf
--       [ estiTerm (bag `bagDiff` bag') + w
--       | (bag', w) <- M.toList (cost i)
--       , bag' `bagSubset` bag ]
    estiNode i bag = amortDag i + estiTerm bag
    amortDag i = minimumInf
      [ w - estiTerm bag
      | (bag, w) <- M.toList (costDag i) ]
    costDag = supCost dagGram

    -- trie amortized cost
    amortTrie i = minimumInf
      [ w - estiTerm bag
      | (bag, w) <- M.toList (costTrie i) ]
    costTrie = trieCost dagGram autoGram

    -- miminal dependency cost for the individual positions
    depCost dep = maybe 0 id
      (M.lookup dep depCostMap)
    depCostMap = M.fromList
      [ (dep, minimumInf (M.elems heds))
      | (dep, heds) <- M.toList hedMap ]

    -- miminal supertagging cost for a given terminal
    termCost t = maybe 0 id
      (M.lookup t termWei)

    -- partial dependency sums
    prefDepSum = M.fromList . sums $
      [ (dep, depCost (dep-1))
      | dep <- [0..sentLen] ]
    suffDepSum = M.fromList . sums $
      [ (dep, depCost dep)
      | dep <- reverse [0..sentLen] ]

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


-- -- | Heuristic: lower bound estimate on the cost (weight) remaining
-- -- to fully parse the given input sentence.
-- estiCost1
--     :: (Ord t)
--     => Memo.Memo t      -- ^ Memoization strategy for terminals
--     -> M.Map t D.Weight -- ^ The lower bound estimates
--                         --   on terminal weights
--     -> Bag t            -- ^ Bag of terminals
--     -> D.Weight
-- estiCost1 memoElem termWei =
--     esti
--   where
--     esti = memoBag memoElem esti'
--     esti' bag = sum
--         [ maybe 0
--             (* fromIntegral n)
--             (M.lookup t termWei)
--         | (t, n) <- M.toList bag ]


-- | Heuristic: lower bound estimate on the cost (weight) remaining
-- to fully parse the given input sentence.
estiCost1
    :: (Ord t)
    => M.Map t D.Weight -- ^ The lower bound estimates
                        --   on terminal weights
    -> Bag t            -- ^ Bag of terminals
    -> D.Weight
estiCost1 termWei bag =
  sum
    [ maybe 0
        (* fromIntegral n)
        (M.lookup t termWei)
    | (t, n) <- M.toList bag ]


--------------------------------
-- Heuristic, part 2
--------------------------------


-- -- | Heuristic: lower bound estimate on the cost (weight) remaining
-- -- to fully parse the given input sentence.
-- --
-- -- NOTE: This function works on any weithed automaton representations,
-- -- but in reality it works correctly only on prefix trees!
-- estiCost2
--     :: (Ord n, Ord t)
--     => Memo.Memo t                  -- ^ Memoization strategy for terminals
--     -> A.WeiGramAuto n t            -- ^ The weighted automaton
--     -> D.DAG (O.Node n t) D.Weight  -- ^ The corresponding grammar DAG
--     -> (Bag t -> D.Weight)          -- ^ `estiCost1`
--     -> ID                           -- ^ ID of the automaton node
--     -> Bag t                        -- ^ Bag of terminals
--     -> D.Weight
-- estiCost2 memoElem weiAuto@A.WeiAuto{..} weiDag estiTerm =
--     esti
--   where
--     esti = Memo.memo2 Memo.integral (memoBag memoElem) esti'
--     esti' i bag = minimumInf
--       [ estiTerm (bag `bagDiff` bag') + w
--       | (bag', w) <- M.toList (cost i)
--       , bag' `bagSubset` bag ]
--     cost = trieCost weiDag weiAuto


-- | Heuristic: lower bound estimate on the cost (weight) remaining
-- to fully parse the given input sentence.
--
-- NOTE: This function works on any weithed automaton representations,
-- but in reality it works correctly only on prefix trees!
estiCost2
    :: (Ord n, SOrd t)
    => A.WeiGramAuto n t            -- ^ The weighted automaton
    -> D.DAG (O.Node n t) D.Weight  -- ^ The corresponding grammar DAG
    -> (Bag t -> D.Weight)          -- ^ `estiCost1`
    -> ID                           -- ^ ID of the automaton node
    -> Bag t                        -- ^ Bag of terminals
    -> D.Weight
estiCost2 weiAuto@A.WeiAuto{..} weiDag estiTerm =
    esti
  where
--     esti i bag = minimumInf
--       [ estiTerm (bag `bagDiff` bag') + w
--       | (bag', w) <- M.toList (cost i)
--       , bag' `bagSubset` bag ]
    esti i bag = amortDag i + estiTerm bag
--     esti i bag = trace 
--       (show (i, bag, amortDag i, cost i, estiTerm bag))
--       (amortDag i + estiTerm bag)
    amortDag i = minimumInf
      [ w - estiTerm bag
      | (bag, w) <- M.toList (cost i) ]
    cost = trieCost weiDag weiAuto


--------------------------------
-- Heuristic: Tree Cost
--------------------------------


-- | Compute the weight of the grammar subtree corresponding to the
-- given DAG node.  Return also the corresponding bag of terminals
-- stored in leaves of the subtree.
subCost
    :: (Ord n, Ord t, Num w)
    => D.DAG (O.Node n t) w     -- ^ Grammar DAG
    -> D.DID                    -- ^ ID of the DAG node
    -> (Bag t, w)
subCost dag =
    cost
  where
    cost = Memo.wrap D.DID D.unDID Memo.integral cost'
    cost' i = case labelValue i dag of
      Nothing -> error "subCost: incorrect ID"
      Just (x, v) -> case x of
        O.Term t -> (pocket t, v)
        _  -> L.foldl' add2 (bagEmpty, v)
          [ Arr.second (+w) (cost j)
          | (j, w) <- D.edges i dag ]


--------------------------------
-- Heuristic: Super Tree Cost
--------------------------------


-- | Compute the bags of terminals and the corresponding (minimal) weights
-- for the individual super-trees surrounding the given DAG node.
supCost
    :: (Ord n, Ord t, Num w, Ord w)
    => D.DAG (O.Node n t) w     -- ^ Grammar DAG
    -> D.DID                    -- ^ ID of the DAG node
    -> M.Map (Bag t) w
supCost dag =
    sup
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
    => D.DAG (O.Node n t) D.Weight  -- ^ Grammar DAG
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
