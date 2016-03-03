{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}


module NLP.Partage.Earley.Tmp
(
-- * Bag
  Bag
, pocket
, bagEmpty
, bagAdd
, bagDiff
, bagFromList

-- * Heuristic
, estiCost1
, estiCost2
, estiCost3

-- * Tmp
, treeCost
) where


import qualified Control.Arrow as Arr
-- import           Data.Hashable (Hashable)
-- import qualified Data.HashTable.IO          as H
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.MemoCombinators as Memo

import           Data.DAWG.Ord (ID)

import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.FactGram.Internal as I
import qualified NLP.Partage.FactGram.Weighted as W
-- import qualified NLP.Partage.Auto.WeiTrie as W
import qualified NLP.Partage.Auto as A
import qualified NLP.Partage.Earley.AutoAP as E


-- type WeiFactGram n t = M.Map (Rule n t) Weight


-- -- | Perform the earley-style computation given the grammar and
-- -- the input sentence.
-- earley
--     :: (Hashable t, Ord t, Hashable n, Ord n)
--     => W.WeiFactGram n t            -- ^ The grammar (map from rules to weights)
--     -> W.DAG (O.Node n t) W.Weight  -- ^
--     -> E.Input t                    -- ^ Input sentence
--     -> IO (E.Hype n t)
-- earley gram input = do
--     auto <- mkAuto (D.fromGram gram)
--     earleyAuto auto input


--------------------------------
-- Bag of words
--------------------------------


-- | Bag of elements (or multiset).
type Bag a = M.Map a Int


-- | Empty bag.
bagEmpty :: Bag a
bagEmpty = M.empty


-- | Single element bag.
pocket :: (Ord a) => a -> Bag a
pocket x = M.singleton x 1


-- | Add two bags.
bagAdd :: (Ord a) => Bag a -> Bag a -> Bag a
bagAdd = M.unionWith (+)


-- | Difference between the two bags:
-- `bagDiff b1 b2` = b1 \ b2
bagDiff :: (Ord a) => Bag a -> Bag a -> Bag a
bagDiff =
    let x `minus` y
            | x > y     = Just (x - y)
            | otherwise = Nothing
     in M.differenceWith minus


-- | Create a bag form a list of objects.
bagFromList :: (Ord a) => [a] -> Bag a
bagFromList = M.fromListWith (+) . map (,1)


-- | Memoization combinator.
memoBag :: (Ord a) => Memo.Memo a -> Memo.Memo (Bag a)
memoBag memoElem =
    let memoList = Memo.list $ Memo.pair
            memoElem Memo.integral
    in  Memo.wrap M.fromAscList M.toAscList memoList


--------------------------------
-- Heuristic, part 1
--------------------------------


-- | Heuristic: lower bound estimate on the cost (weight) remaining
-- to fully parse the given input sentence.
estiCost1
    :: (Ord t)
    => Memo.Memo t      -- ^ Memoization strategy for terminals
    -> M.Map t W.Weight -- ^ The lower bound estimates
                        --   on terminal weights
    -> Bag t            -- ^ Bag of terminals
    -> W.Weight
estiCost1 memoElem termWei =
    esti
  where
    esti = memoBag memoElem esti'
    esti' bag = sum
        [ maybe 0
            (* fromIntegral n)
            (M.lookup t termWei)
        | (t, n) <- M.toList bag ]


--------------------------------
-- Heuristic, part 2
--------------------------------


-- | Heuristic: lower bound estimate on the cost (weight) remaining
-- to fully parse the given input sentence.
estiCost2
    :: (Ord n, Ord t)
    => Memo.Memo t                  -- ^ Memoization strategy for terminals
    -> A.WeiGramAuto n t            -- ^ The weighted automaton
    -> W.DAG (O.Node n t) W.Weight  -- ^ The corresponding grammar DAG
    -> (Bag t -> W.Weight)          -- ^ `estiCost1`
    -> ID                           -- ^ ID of the automaton node
    -> Bag t                        -- ^ Bag of terminals
    -> W.Weight
estiCost2 memoElem A.WeiAuto{..} weiDag estiTerm =
    esti
  where
    -- estiTerm = estiCost1 memoElem termWei
    esti = Memo.memo2 Memo.integral (memoBag memoElem) esti'
    esti' i bag = if null (edgesWei i)
        then estiTerm bag
        else minimum
            [ w + wS + esti j (bag `bagDiff` bagS)
            | (x, w, j) <- edgesWei i
            , let (bagS, wS) = cost x ]
    cost = labCost weiDag


--------------------------------
-- Heuristic, part 3
--------------------------------


-- | Heuristic: lower bound estimate on the cost (weight) remaining
-- to fully parse the given input sentence.
estiCost3
    :: (Ord n, Ord t)
    => Memo.Memo t                  -- ^ Memoization strategy for terminals
    -> A.WeiGramAuto n t            -- ^ The weighted automaton
    -> W.DAG (O.Node n t) W.Weight  -- ^ The corresponding grammar DAG
    -> (Bag t -> W.Weight)          -- ^ `estiCost1`
    -> ID                           -- ^ ID of the automaton node
    -> Bag t                        -- ^ Bag of terminals
    -> W.Weight
estiCost3 memoElem weiAuto@A.WeiAuto{..} weiDag estiTerm =
    esti
  where
    esti = Memo.memo2 Memo.integral (memoBag memoElem) esti'
    esti' i bag = minimum
      [ estiTerm (bag `bagDiff` bag') + w
      | (bag', w) <- M.toList (cost i) ]
    cost = treeCost weiDag weiAuto


--------------------------------
-- Heuristic: Tree Cost
--------------------------------


-- | Compute the weight of the grammar subtree corresponding to the
-- given DAG node.  Return also the corresponding bag of terminals
-- stored in leaves of the subtree.
subCost
    :: (Ord n, Ord t, Num w)
    => W.DAG (O.Node n t) w     -- ^ Grammar DAG
    -> W.ID                     -- ^ ID of the DAG node
    -> (Bag t, w)
subCost dag =
    cost
  where
    cost = Memo.integral cost'
    cost' i = case W.label i dag of
        Nothing -> error "subCost: incorrect ID"
        Just v  -> case v of
            O.Term t -> (pocket t, 0)
            _  -> L.foldl' add2 (bagEmpty, 0)
                [ Arr.second (+w) (cost j)
                | (j, w) <- W.edges i dag ]


-- | Like `subCost` but works for a specific grammar label.
-- For non-internal nodes (roots or leaves) returns
-- `(bagEmpty, 0)`.
labCost
    :: (Ord n, Ord t, Num w)
    => W.DAG (O.Node n t) w     -- ^ Grammar DAG
    -> A.Edge (I.Lab n t)       -- ^ Automaton transition label
    -> (Bag t, w)
-- TODO: can we move `x` before the equation sign?
labCost dag = \x -> case x of
    A.Body y -> case y of
      I.NonT _ (Just i) -> cost i
      I.AuxVert _ i     -> cost i
      _                 -> (bagEmpty, 0)
    A.Head _ -> (bagEmpty, 0)
  where
    cost = subCost dag


--------------------------------
-- Heuristic: Super Tree Cost
--------------------------------


-- | Compute the bags of terminals and the corresponding (minimal) weights
-- for the individual super-trees surrounding the given DAG node.
supCost
    :: (Ord n, Ord t, Num w, Ord w)
    => W.DAG (O.Node n t) w     -- ^ Grammar DAG
    -> W.ID                     -- ^ ID of the DAG node
    -> M.Map (Bag t) w
supCost dag =
    sup
  where
    sup = Memo.integral sup'
    sup' i
      -- | W.isRoot i dag = M.empty
      | W.isRoot i dag = M.singleton bagEmpty 0
      | otherwise = M.fromListWith min
          [ (sup_j `add2` sub j) `sub2` sub i
          | j <- S.toList (W.parents i parMap)
          , sup_j <- M.toList (sup j) ]
    sub = subCost dag
    parMap = W.parentMap dag


--------------------------------
-- Heuristic: Super Tree Cost
--------------------------------


-- | Compute the bags of terminals and the corresponding
-- (minimal) weights which still need to be scanned before
-- some full elementary tree is parsed starting from the
-- given DAG node.
treeCost
    :: (Ord n, Ord t)
    => W.DAG (O.Node n t) W.Weight  -- ^ Grammar DAG
    -> A.WeiGramAuto n t            -- ^ The weighted automaton
    -> ID                           -- ^ ID of the *automaton*(!) node
    -> M.Map (Bag t) W.Weight
treeCost dag A.WeiAuto{..} =
  cost
  where
    cost = Memo.integral cost'
    cost' i =
      if null (edgesWei i)
      then sup i    -- WRONG!!!!
      else M.fromListWith min
           [ Arr.second (+w) (bag_x `add2` bag_j)
           | (x, w, j) <- edgesWei i
           , bag_j <- M.toList (cost j)
           , let bag_x = sub x ]
    sub = labCost dag
    sup = supCost dag


--------------------------------
-- Misc
--------------------------------


-- | Add two bags enriched with weights.
add2 :: (Ord a, Num w) => (Bag a, w) -> (Bag a, w) -> (Bag a, w)
add2 (b1, w1) (b2, w2) = (bagAdd b1 b2, w1 + w2)


-- | Substract two bags enriched with weights.
sub2 :: (Ord a, Num w) => (Bag a, w) -> (Bag a, w) -> (Bag a, w)
sub2 (b1, w1) (b2, w2) = (bagDiff b1 b2, w1 - w2)
