{-# LANGUAGE TupleSections   #-}


module NLP.Partage.AStar.Heuristic.Bag
(
-- * Bag
  Bag
, pocket
, bagEmpty
, bagAdd
, bagDiff
, bagFromList
, bagSubset

-- ** Memoization
, memoBag
) where


import qualified Data.MemoCombinators            as Memo
import qualified Data.Map.Strict                 as M


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
--
-- Note that this function doesn't check if `b2` is a subset of `b1`,
-- which you sould ensure yourself (using e.g. `bagSubset`).
-- Otherwise, the function fails with error.
bagDiff :: (Ord a) => Bag a -> Bag a -> Bag a
bagDiff =
    let x `minus` y
            | x > y     = Just (x - y)
            | x == y    = Nothing
            | otherwise = error "bagDiff: not a subset"
     in M.differenceWith minus


-- | Check whether the first argument is a sub-multiset of the second one.
bagSubset :: (Ord a) => Bag a -> Bag a -> Bool
bagSubset =
  let m `check` n
        | m <= n    = True
        | otherwise = False
   in M.isSubmapOfBy check


-- | Create a bag form a list of objects.
bagFromList :: (Ord a) => [a] -> Bag a
bagFromList = M.fromListWith (+) . map (,1)


-- | Memoization combinator.
memoBag :: (Ord a) => Memo.Memo a -> Memo.Memo (Bag a)
memoBag memoElem =
    let memoList = Memo.list $ Memo.pair
            memoElem Memo.integral
    in  Memo.wrap M.fromAscList M.toAscList memoList
