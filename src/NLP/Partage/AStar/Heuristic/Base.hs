{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE RecordWildCards #-}


-- | A* base heuristic, independent from the currently parsed
-- elementary tree (of trees).
--
-- WARNING: This heuristic is actually not correct!
-- UPDATE 12/07/2016: Is it really?
--
-- Let x, y be two graph nodes connected by arc with weight c(x, y).
-- Let c(x, y) represent scanning of terminal t with minw(t) > 0.
-- The cost of scanning is always zero (i.e., \beta(x) = \beta(y)),
-- thus c(x, y) = 0.
--
-- For a heuristic to be monotone, the following formula must be satisfied:
--
--   h(x) <= c(x, y) + h(y)
--
-- However, in this particular case, c(x, y) = 0 and h(y) < h(x), the latter
-- because of minw(t) > 0, which together imply h(x) > c(x, y) + h(y).  QED.


module NLP.Partage.AStar.Heuristic.Base
(
-- * Heuristic
  Esti(..)
, mkEsti
, module NLP.Partage.AStar.Heuristic.Bag
) where


import qualified Data.Map.Strict                 as M
import qualified Data.MemoCombinators            as Memo

import           Data.DAWG.Ord                   (ID)

import           NLP.Partage.AStar.Heuristic.Bag
import qualified NLP.Partage.Auto                as A
import qualified NLP.Partage.DAG                 as D


-- | Distance estimation heuristic.
data Esti t = Esti
  { termEsti :: Bag t -> D.Weight
  , trieEsti :: ID -> Bag t -> D.Weight
  -- , dagEsti  :: D.DID -> M.Map (Bag t) D.Weight
  , dagEsti  :: D.DID -> Bag t -> D.Weight
  -- ^ Bags of terminals and the corresponding (minimal) weights
  -- for the individual super-trees surrounding the given DAG node.
  }


-- | Create `Esti` based on several basic pieces of information.
mkEsti
  :: (Ord t, Ord n)
  => Memo.Memo t      -- ^ Memoization strategy for terminals
  -> D.Gram n t         -- ^ The underlying grammar
  -> A.WeiGramAuto n t  -- ^ The underlying automaton
  -> Esti t
mkEsti _memoElem D.Gram{..} _autoGram = Esti
  { termEsti = estiTerm termWei
  , trieEsti = const (estiTerm termWei)
  , dagEsti  = const (estiTerm termWei) }


-- | Heuristic: lower bound estimate on the cost (weight) remaining
-- to fully parse the given input sentence.
estiTerm
    :: (Ord t)
    => M.Map t D.Weight -- ^ The lower bound estimates
                        --   on terminal weights
    -> Bag t            -- ^ Bag of terminals
    -> D.Weight
estiTerm termWei bag =
  sum
    [ maybe 0
        (* fromIntegral n)
        (M.lookup t termWei)
    | (t, n) <- M.toList bag ]
