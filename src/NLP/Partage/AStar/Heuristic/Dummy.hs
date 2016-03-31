{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types      #-}


-- | A* dumm heuristic (always 0).


module NLP.Partage.AStar.Heuristic.Dummy
(
-- * Heuristic
  Esti(..)
, mkEsti
, module NLP.Partage.AStar.Heuristic.Bag
) where


import qualified Data.MemoCombinators     as Memo

import           Data.DAWG.Ord            (ID)

import qualified NLP.Partage.DAG as D
import qualified NLP.Partage.AStar.Auto   as I
import           NLP.Partage.AStar.Heuristic.Bag


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
  -> I.Auto n t       -- ^ The underlying automaton
  -> Esti t
mkEsti _memoElem I.Auto{..} = Esti
  { termEsti = \_ -> 0
  , trieEsti = \_ _ -> 0
  , dagEsti  = \_ _ -> 0 }
