{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}


module NLP.Partage.Earley.Chart
( Chart (..)
, empty

-- * Stats
, listPassive
, listActive
, doneNodesNum
, doneEdgesNum

-- * Active
, activeTrav
, isProcessedA
, saveActive
, hasActiveTrav

-- * Passive
, passiveTrav
, isProcessedP
, savePassive
, hasPassiveTrav

-- * Extraction
, finalFrom
, expectEnd
, rootSpan
-- , provideBeg'
-- , provideBegIni
-- , provideBegAux
-- , auxModifyGap
) where


import           Control.Monad.Trans.Class   (lift)
import qualified Control.Monad.State.Class   as MS
import           Control.Monad      ((>=>))

import           Data.Maybe                  (maybeToList)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Lens.Light
import qualified Pipes                      as P

import           Data.DAWG.Ord               (ID)

import qualified NLP.Partage.DAG             as DAG
import           NLP.Partage.Earley.Base
import           NLP.Partage.Earley.Auto      (Auto (..))
import           NLP.Partage.Earley.ExtWeight
import           NLP.Partage.Earley.Item


-- | A chart part of the hypergraph.
data Chart n t = Chart
    {

      doneActive  :: M.Map Pos (M.Map ID
        (M.Map Active (S.Set (Trav n t))))
    -- ^ Processed active items partitioned w.r.t ending
    -- positions and state IDs.

    -- TODO: we shoudle distinguish passive top-level and other passive items;
    -- then we should assign potential computation values to the top-level
    -- passive items, i.e., change the set of traversals into a map from
    -- traversals to sets of potential values.
    , donePassive :: M.Map (Pos, n, Pos)
        (M.Map (Passive n t) (S.Set (Trav n t)))
    -- ^ Processed passive items.

    }


-- | Create an empty chart.
empty :: Chart n t
empty = Chart
    { doneActive = M.empty
    , donePassive = M.empty }


--------------------
-- Chart stats
--------------------


-- | List all passive done items together with the corresponding
-- traversals.
listPassive :: Chart n t -> [(Passive n t, S.Set (Trav n t))]
listPassive = (M.elems >=> M.toList) . donePassive


-- | List all active done items together with the corresponding
-- traversals.
listActive :: Chart n t -> [(Active, S.Set (Trav n t))]
listActive = (M.elems >=> M.elems >=> M.toList) . doneActive


-- | Number of nodes in the parsing chart.
doneNodesNum :: Chart n t -> Int
doneNodesNum e
    = length (listPassive e)
    + length (listActive e)


-- | Number of edges in the parsing chart.
doneEdgesNum :: forall n t. Chart n t -> Int
doneEdgesNum earSt
    = sumOver listPassive
    + sumOver listActive
  where
    sumOver :: (Chart n t -> [(a, S.Set (Trav n t))]) -> Int
    sumOver listIt = sum
        [ S.size travSet
        | (_, travSet) <- listIt earSt ]


--------------------
-- Active items
--------------------


-- | Return the corresponding set of traversals for an active item.
activeTrav
    :: (Ord n, Ord t)
    => Active -> Chart n t
    -> Maybe (S.Set (Trav n t))
activeTrav p
    = (   M.lookup (p ^. spanA ^. end)
      >=> M.lookup (p ^. state)
      >=> M.lookup p )
    . doneActive


-- | Check if the active item is not already processed.
isProcessedA :: (Ord n, Ord t) => Active -> Chart n t -> Bool
isProcessedA p =
    check . activeTrav p
  where
    check (Just _) = True
    check _        = False


-- | Mark the active item as processed (`done').
saveActive
    :: (Ord t, Ord n)
    => Active
    -> S.Set (Trav n t)
    -> Chart n t
    -> Chart n t
saveActive p ts chart =
    chart {doneActive = newDone}
  where
    newDone =
        M.insertWith
            ( M.unionWith
                ( M.unionWith S.union ) )
            ( p ^. spanA ^. end )
            ( M.singleton (p ^. state)
                ( M.singleton p ts ) )
            ( doneActive chart )


-- | Check if, for the given active item, the given transitions are already
-- present in the hypergraph.
hasActiveTrav
    :: (Ord t, Ord n)
    => Active
    -> S.Set (Trav n t)
    -> Chart n t
    -> Bool
hasActiveTrav p travSet chart =
  case activeTrav p chart of
    Just travSet' -> travSet `S.isSubsetOf` travSet'
    Nothing -> False


--------------------
-- Passive items
--------------------


-- | Return the corresponding set of traversals for a passive item.
passiveTrav
    :: (Ord n, Ord t)
    => Passive n t
    -> Auto n t
    -> Chart n t
    -> Maybe (S.Set (Trav n t))
passiveTrav p auto chart =
    ( M.lookup
        ( p ^. spanP ^. beg
        , nonTerm (p ^. dagID) auto
        , p ^. spanP ^. end ) >=> M.lookup p )
    ( donePassive chart )


-- | Check if the state is not already processed.
isProcessedP :: (Ord n, Ord t) => Passive n t -> Auto n t -> Chart n t -> Bool
isProcessedP x auto =
    check . passiveTrav x auto
  where
    check (Just _) = True
    check _        = False


-- | Mark the passive item as processed (`done').
savePassive
    :: (Ord t, Ord n)
    => Passive n t
    -> S.Set (Trav n t)
    -> Auto n t
    -> Chart n t
    -> Chart n t
savePassive p ts auto chart =
  chart {donePassive = newDone}
  where
    newDone =
        M.insertWith
            ( M.unionWith S.union )
            ( p ^. spanP ^. beg
            , nonTerm (p ^. dagID) auto
            , p ^. spanP ^. end )
            ( M.singleton p ts )
            ( donePassive chart )


-- | Check if, for the given active item, the given transitions are already
-- present in the hypergraph.
hasPassiveTrav
  :: (Ord t, Ord n)
  => Passive n t
  -> S.Set (Trav n t)
  -> Auto n t
  -> Chart n t
  -> Bool
hasPassiveTrav p travSet auto chart =
  case passiveTrav p auto chart of
    Just travSet' -> travSet `S.isSubsetOf` travSet'
    Nothing -> False


---------------------------------
-- Extraction of Processed Items
---------------------------------


-- | Return the list of final passive chart items.
finalFrom
    :: (Ord n, Eq t)
    => n            -- ^ The start symbol
    -> Int          -- ^ The length of the input sentence
    -> Chart n t    -- ^ Result of the earley computation
    -> [Passive n t]
finalFrom start n Chart{..} =
    case M.lookup (0, start, n) donePassive of
        Nothing -> []
        Just m ->
            [ p
            | p <- M.keys m
            , p ^. dagID == Left start ]


-- -- | Return all active processed items which:
-- -- * expect a given label,
-- -- * end on the given position.
-- expectEnd
--     :: (Ord n, Ord t) => Lab n t -> Pos
--     -> P.ListT (Earley n t) Active
-- expectEnd sym i = do
--     Hype{..} <- lift RWS.get
--     -- determine items which end on the given position
--     doneEnd <- some $ M.lookup i doneActive
--     -- determine automaton states from which the given label
--     -- leaves as a body transition
--     stateSet <- some $ M.lookup sym withBody
--     -- pick one of the states
--     stateID <- each $ S.toList stateSet
--     --
--     -- ALTERNATIVE: state <- each . S.toList $
--     --      stateSet `S.intersection` M.keySet doneEnd
--     --
--     -- determine items which refer to the chosen states
--     doneEndLab <- some $ M.lookup stateID doneEnd
--     -- return them all!
--     each $ M.keys doneEndLab


-- -- | Return all active processed items which:
-- -- * expect a given label,
-- -- * end on the given position.
-- expectEnd
--     :: (HOrd n, HOrd t) => Lab n t -> Pos
--     -> P.ListT (Earley n t) Active
-- expectEnd sym i = do
--     Hype{..} <- lift RWS.get
--     -- determine items which end on the given position
--     doneEnd <- some $ M.lookup i doneActive
--     -- determine automaton states from which the given label
--     -- leaves as a body transition
--     stateSet <- do
--         maybeSet <- lift . lift $
--             H.lookup (withBody automat) sym
--         some maybeSet
--     -- pick one of the states
--     stateID <- each . S.toList $
--          stateSet `S.intersection` M.keysSet doneEnd
--     -- determine items which refer to the chosen states
--     doneEndLab <- some $ M.lookup stateID doneEnd
--     -- return them all!
--     each $ M.keys doneEndLab


-- | Return all active processed items which:
-- * expect a given label,
-- * end on the given position.
expectEnd
    -- :: (HOrd n, HOrd t) => DID -> Pos
    :: (Ord n, Ord t, MS.MonadState s m)
    => (s -> Auto n t)
    -> (s -> Chart n t)
    -> DAG.DID
    -> Pos
    -> P.ListT m Active
expectEnd getAuto getChart did i = do
    compState <- lift MS.get
    let Chart{..} = getChart compState
        automat = getAuto compState
    -- determine items which end on the given position
    doneEnd <- some $ M.lookup i doneActive
    -- determine automaton states from which the given label
    -- leaves as a body transition
    stateSet <- some $ M.lookup did (withBody automat)
    -- pick one of the states
    stateID <- each . S.toList $
         stateSet `S.intersection` M.keysSet doneEnd
    -- determine items which refer to the chosen states
    doneEndLab <- some $ M.lookup stateID doneEnd
    -- return them all!
    each $ M.keys doneEndLab


-- | Check if a passive item exists with:
-- * the given root non-terminal value (but not top-level
--   auxiliary) (UPDATE: is this second part ensured?)
-- * the given span
rootSpan
    :: (Ord n, MS.MonadState s m)
    => (s -> Chart n t)
    -> n -> (Pos, Pos)
    -> P.ListT m (Passive n t)
rootSpan getChart x (i, j) = do
    -- Hype{..} <- lift RWS.get
    Chart{..} <- getChart <$> lift MS.get
    -- listValues (i, x, j) donePassive
    each $ case M.lookup (i, x, j) donePassive of
        Nothing -> []
        Just m -> M.keys m


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | ListT from a maybe.
some :: Monad m => Maybe a -> P.ListT m a
some = each . maybeToList


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each
