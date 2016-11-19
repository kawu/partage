-- | Core types and functions related to the Earley monad.


module NLP.Partage.Earley.Monad
( 
-- * Earley monad
  Earley
, readInput

-- * Active items
, isProcessedA
, saveActive
, hasActiveTrav

-- * Passive items
, isProcessedP
, savePassive
, hasPassiveTrav
) where


import qualified Control.Monad.RWS.Strict   as RWS
import qualified Pipes                      as P
import qualified Data.Vector                as V
import qualified Data.Set                   as S
import           Data.Maybe (maybeToList)

import           NLP.Partage.Earley.Base
import qualified NLP.Partage.Earley.Chart as Chart
import           NLP.Partage.Earley.Hypergraph (Hype(..))
import           NLP.Partage.Earley.Item
import qualified NLP.Partage.Earley.ExtWeight as Ext


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | Earley parser monad.  Contains the input sentence (reader)
-- and the state of the computation `Hype'.
type Earley n t = RWS.RWST (Input t) () (Hype n t) IO


-- | Read word from the given position of the input.
readInput :: Pos -> P.ListT (Earley n t) t
readInput i = do
    -- ask for the input
    sent <- RWS.asks inputSent
    -- just a safe way to retrieve the i-th element
    -- each $ take 1 $ drop i xs
    xs <- some $ sent V.!? i
    each $ S.toList xs


--------------------
-- Active items
--------------------


-- | Check if the active item is not already processed.
isProcessedA :: (Ord n, Ord t) => Active -> Earley n t Bool
isProcessedA p = Chart.isProcessedA p . chart <$> RWS.get


-- | Mark the active item as processed (`done').
saveActive
    :: (Ord t, Ord n)
    => Active
    -> S.Set (Ext.Trav n t)
    -> Earley n t ()
saveActive p ts =
  RWS.modify' $ \h -> h {chart = Chart.saveActive p ts (chart h)}


-- | Check if, for the given active item, the given transitions are already
-- present in the hypergraph.
hasActiveTrav
    :: (Ord t, Ord n)
    => Active
    -> S.Set (Ext.Trav n t)
    -> Earley n t Bool
hasActiveTrav p travSet =
  Chart.hasActiveTrav p travSet . chart <$> RWS.get


--------------------
-- Passive items
--------------------


-- | Check if the passive item is not already processed.
isProcessedP :: (Ord n, Ord t) => Passive n t -> Earley n t Bool
isProcessedP p = do
  h <- RWS.get
  return $ Chart.isProcessedP p (automat h) (chart h)


-- | Mark the passive item as processed (`done').
savePassive
    :: (Ord t, Ord n)
    => Passive n t
    -> S.Set (Ext.Trav n t)
    -> Earley n t ()
savePassive p ts =
  -- RWS.state $ \s -> ((), s {donePassive = newDone s})
  RWS.modify' $ \h ->
    h {chart = Chart.savePassive p ts (automat h) (chart h)}


-- | Check if, for the given active item, the given transitions are already
-- present in the hypergraph.
hasPassiveTrav
    :: (Ord t, Ord n)
    => Passive n t
    -> S.Set (Ext.Trav n t)
    -> Earley n t Bool
hasPassiveTrav p travSet = do
  h <- RWS.get
  return $ Chart.hasPassiveTrav p travSet (automat h) (chart h)


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | ListT from a maybe.
some :: Monad m => Maybe a -> P.ListT m a
some = each . maybeToList


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each
