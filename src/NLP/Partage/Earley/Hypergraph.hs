module NLP.Partage.Earley.Hypergraph
(
-- * Hypergraph
  Hype (..)
, mkHype
-- ** Stats
, hyperNodesNum
, hyperEdgesNum
) where


import qualified Data.Set as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))

import           NLP.Partage.Earley.Auto (Auto(..))
import           NLP.Partage.Earley.Item -- hiding (printPassive)
import           NLP.Partage.Earley.Trav
import qualified NLP.Partage.Earley.Chart as Chart


--------------------------------------------------
-- Hypergraph
--------------------------------------------------


-- | A hypergraph dynamically constructed during parsing.
data Hype n t v = Hype
    { automat :: Auto n t v
    -- ^ The underlying automaton

    , chart :: Chart.Chart n t v
    -- ^ The underlying chart

    , waiting :: Q.PSQ (Item n v) (ExtPrio n t v)
    -- ^ The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    --
    -- NOTE: The only operation which requires active states to
    -- be put to the queue in the current algorithm is the scan
    -- operation.  So perhaps we could somehow bypass this
    -- problem and perform scan elsewhere.  Nevertheless, it is
    -- not certain that the same will apply to the probabilistic
    -- parser.
    }


-- | Make an initial `Hype` from a set of states.
-- TODO: this can be simplified as in the probabilitic version -- active items
-- can be pushed independently, thus `mkHype` could just take an automaton.
mkHype
    :: (Ord n, Ord v)
    => Auto n t v
    -> S.Set (Active v)
    -> Hype n t v
mkHype auto s = Hype
    { automat = auto
    , chart   = Chart.empty
    , waiting = Q.fromList
        [ ItemA p :-> extPrio (prioA p)
        | p <- S.toList s ] }


--------------------------------------------------
-- Hypergraph stats
--------------------------------------------------


-- -- | Extract hypergraph (hyper)edges.
-- hyperEdges :: Hype n t -> [(Item n t, Trav n t)]
-- hyperEdges earSt =
--     passiveEdges ++ activeEdges
--   where
--     passiveEdges =
--         [ (ItemP p, trav)
--         | (p, travSet) <- listPassive earSt
--         , trav <- S.toList travSet ]
--     activeEdges =
--         [ (ItemA p, trav)
--         | (p, travSet) <- listActive earSt
--         , trav <- S.toList travSet ]
--
--
-- -- | Print the hypergraph edges.
-- printHype :: (Show n, Show t) => Hype n t -> IO ()
-- printHype hype =
--     forM_ edges $ \(p, trav) ->
--         printTrav hype p trav
--   where
--     edges  = sortIt (hyperEdges hype)
--     sortIt = sortBy (comparing $ prio.fst)


-- | List all waiting items together with the corresponding
-- traversals.
listWaiting :: (Ord n, Ord v) => Hype n t v -> [(Item n v, ExtPrio n t v)]
listWaiting =
  let toPair (p :-> w) = (p, w)
   in map toPair . Q.toList . waiting


-- | Number of nodes in the parsing hypergraph.
doneNodesNum :: Hype n t v -> Int
doneNodesNum e = Chart.doneNodesNum (chart e)


-- | Number of waiting nodes in the parsing hypergraph.
waitingNodesNum :: (Ord n, Ord v) => Hype n t v -> Int
waitingNodesNum = length . listWaiting


-- | Number of nodes in the parsing hypergraph.
hyperNodesNum :: (Ord n, Ord v) => Hype n t v -> Int
hyperNodesNum e = doneNodesNum e + waitingNodesNum e


-- | Number of nodes in the parsing hypergraph.
doneEdgesNum :: Hype n t v -> Int
doneEdgesNum e = Chart.doneEdgesNum (chart e)


-- | Number of edges outgoing from waiting nodes in the underlying hypergraph.
waitingEdgesNum :: (Ord n, Ord v) => Hype n t v -> Int
waitingEdgesNum = sumTrav . listWaiting


-- | Number of edges in the parsing hypergraph.
hyperEdgesNum :: (Ord n, Ord v) => Hype n t v -> Int
hyperEdgesNum e = doneEdgesNum e + waitingEdgesNum e


-- | Sum up traversals.
sumTrav :: [(a, ExtPrio n t v)] -> Int
sumTrav xs = sum
    [ S.size (prioTrav ext)
    | (_, ext) <- xs ]
