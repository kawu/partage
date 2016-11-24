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

-- -- * Top-passive items
-- , isProcessedT
-- , saveTopPassive
-- -- , hasTopPassiveTrav
) where


import qualified Control.Monad.RWS.Strict   as RWS
import qualified Pipes                      as P
import qualified Data.Vector                as V
import qualified Data.Set                   as S
-- import qualified Data.Map.Strict            as M
import           Data.Maybe (maybeToList)

import           NLP.Partage.Earley.Base
import qualified NLP.Partage.Earley.Chart as Chart
import           NLP.Partage.Earley.Hypergraph (Hype(..))
import           NLP.Partage.Earley.Item
import qualified NLP.Partage.Earley.Trav as Ext


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | Earley parser monad.  Contains the input sentence (reader)
-- and the state of the computation `Hype'.
type Earley n t v = RWS.RWST (Input t v) () (Hype n t v) IO


-- | Read word from the given position of the input.
readInput :: Pos -> P.ListT (Earley n t v) (Tok t, v)
readInput i = do
    -- ask for the input
    sent <- RWS.asks inputSent
    -- just a safe way to retrieve the i-th element
    -- each $ take 1 $ drop i xs
    xs <- some $ sent V.!? i
    let mkTok (t, v) = (Tok i t, v)
    each . map mkTok $ S.toList xs


--------------------
-- Active items
--------------------


-- | Check if the active item is not already processed.
isProcessedA :: (Ord v) => Active v -> Earley n t v Bool
isProcessedA p = Chart.isProcessedA p . chart <$> RWS.get


-- | Mark the active item as processed (`done').
saveActive
    :: (Ord n, Ord v)
    => Active v
    -> S.Set (Ext.Trav n t v)
    -> Earley n t v ()
saveActive p ts =
  RWS.modify' $ \h -> h {chart = Chart.saveActive p ts (chart h)}


-- | Check if, for the given active item, the given transitions are already
-- present in the hypergraph.
hasActiveTrav
    :: (Ord n, Ord v)
    => Active v
    -> S.Set (Ext.Trav n t v)
    -> Earley n t v Bool
hasActiveTrav p travSet =
  Chart.hasActiveTrav p travSet . chart <$> RWS.get


--------------------
-- Passive items
--------------------


-- | Check if the passive item is not already processed.
isProcessedP :: (Ord n, Ord v) => NonActive n v -> Earley n t v Bool
isProcessedP p = do
  h <- RWS.get
  return $ Chart.isProcessedP p (automat h) (chart h)


-- | Mark the passive item as processed (`done').
savePassive
    :: (Ord n, Ord v)
    => NonActive n v
    -> S.Set (Ext.Trav n t v)
    -> Earley n t v ()
savePassive p ts =
  -- RWS.state $ \s -> ((), s {donePassive = newDone s})
  RWS.modify' $ \h ->
    h {chart = Chart.savePassive p ts (automat h) (chart h)}


-- | Check if, for the given active item, the given transitions are already
-- present in the hypergraph.
hasPassiveTrav
    :: (Ord n, Ord v)
    => NonActive n v
    -> S.Set (Ext.Trav n t v)
    -> Earley n t v Bool
hasPassiveTrav p travSet = do
  h <- RWS.get
  return $ Chart.hasPassiveTrav p travSet (automat h) (chart h)


-- --------------------
-- -- Top-passive items
-- --------------------
--
--
-- -- | Check if the passive item is not already processed.
-- isProcessedT :: (Ord n) => TopPassive n -> Earley n t a Bool
-- isProcessedT p = do
--   h <- RWS.get
--   return $ Chart.isProcessedT p (chart h)
--
--
-- -- | Mark the passive item as processed (`done').
-- saveTopPassive
--     :: (Ord t, Ord n, Ord a)
--     => TopPassive n
--     -> M.Map (Ext.Trav n t) (S.Set a)
--     -> Earley n t a ()
-- saveTopPassive p ts =
--   RWS.modify' $ \h ->
--     h {chart = Chart.saveTopPassive p ts (chart h)}
--
--
-- -- -- | Check if, for the given active item, the given transitions are already
-- -- -- present in the hypergraph.
-- -- hasTopPassiveTrav
-- --     :: (Ord t, Ord n)
-- --     => Passive
-- --     -> S.Set (Ext.Trav n t)
-- --     -> Earley n t a Bool
-- -- hasTopPassiveTrav p travSet = do
-- --   h <- RWS.get
-- --   return $ Chart.hasPassiveTrav p travSet (automat h) (chart h)

--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | ListT from a maybe.
some :: Monad m => Maybe a -> P.ListT m a
some = each . maybeToList


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each
