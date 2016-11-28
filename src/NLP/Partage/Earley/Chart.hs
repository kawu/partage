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

-- -- * Top-passive
-- , topPassiveTrav
-- , isProcessedT
-- , saveTopPassive
-- -- , hasPassiveTrav

-- * Extraction
, finalFrom
, expectEnd
, rootSpan
) where


import           Control.Monad.Trans.Class   (lift)
import qualified Control.Monad.State.Class   as MS
import           Control.Monad      ((>=>))

import           Data.Maybe                  (isJust, maybeToList)
import           Data.Either                 (lefts)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Lens.Light
import qualified Pipes                      as P

import           Data.DAWG.Ord               (ID)

import qualified NLP.Partage.DAG             as DAG
import           NLP.Partage.Earley.Base
import           NLP.Partage.Earley.Auto      (Auto (..))
import           NLP.Partage.Earley.Trav
import           NLP.Partage.Earley.Item


-- | A chart part of the hypergraph.
data Chart n t v = Chart
    {

      doneActive  :: M.Map Pos (M.Map ID
        (M.Map (Active v) (S.Set (Trav n t v))))
    -- ^ Processed active items partitioned w.r.t ending
    -- positions and state IDs.

    , donePassive :: M.Map (Pos, n, Pos)
        (M.Map (NonActive n v) (S.Set (Trav n t v)))
    -- ^ Processed passive items.

--     , doneTopPassive :: M.Map (Pos, n, Pos)
--         (M.Map (TopPassive n)
--           (M.Map (Trav n t) (S.Set a))
--         )
--     -- ^ Processed top-passive items together with the corresponding values.

    }


-- | Create an empty chart.
empty :: Chart n t v
empty = Chart
    { doneActive = M.empty
    , donePassive = M.empty }
    -- , doneTopPassive = M.empty }


--------------------
-- Chart stats
--------------------


-- | List all passive done items together with the corresponding
-- traversals.
listPassive :: Chart n t v -> [(NonActive n v, S.Set (Trav n t v))]
listPassive = (M.elems >=> M.toList) . donePassive


-- -- | List all passive done items together with the corresponding
-- -- traversals.
-- listTopPassive :: Chart n t a -> [(TopPassive n, S.Set (Trav n t))]
-- listTopPassive = undefined
-- -- listTopPassive = (M.elems >=> M.toList) . donePassive


-- | List all active done items together with the corresponding
-- traversals.
listActive :: Chart n t v -> [(Active v, S.Set (Trav n t v))]
listActive = (M.elems >=> M.elems >=> M.toList) . doneActive


-- | Number of nodes in the parsing chart.
doneNodesNum :: Chart n t v -> Int
doneNodesNum e
    = length (listPassive e)
    -- + length (listTopPassive e)
    + length (listActive e)


-- | Number of edges in the parsing chart.
doneEdgesNum :: forall n t v. Chart n t v -> Int
doneEdgesNum earSt
    = sumOver listPassive
    -- + sumOver listTopPassive
    + sumOver listActive
  where
    sumOver :: (Chart n t v -> [(a, S.Set (Trav n t v))]) -> Int
    sumOver listIt = sum
        [ S.size travSet
        | (_, travSet) <- listIt earSt ]


--------------------
-- Active items
--------------------


-- | Return the set of traversals corresponding to an active item.
activeTrav :: (Ord v) => Active v -> Chart n t v -> Maybe (S.Set (Trav n t v))
activeTrav p
    = (   M.lookup (p ^. spanA ^. end)
      >=> M.lookup (p ^. state)
      >=> M.lookup p )
    . doneActive


-- | Check if the active item is not already processed.
isProcessedA :: (Ord v) => Active v -> Chart n t v -> Bool
isProcessedA p =
    check . activeTrav p
  where
    check (Just _) = True
    check _        = False


-- | Mark the active item as processed (`done').
saveActive
    :: (Ord n, Ord v)
    => Active v
    -> S.Set (Trav n t v)
    -> Chart n t v
    -> Chart n t v
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
    :: (Ord n, Ord v)
    => Active v
    -> S.Set (Trav n t v)
    -> Chart n t v
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
    :: (Ord n, Ord v)
    => NonActive n v
    -> Auto n t v
    -> Chart n t v
    -> Maybe (S.Set (Trav n t v))
passiveTrav p auto chart =
    ( M.lookup
        ( spanN p ^. beg
        , labelN p auto
        , spanN p ^. end ) >=> M.lookup p )
    ( donePassive chart )


-- | Check if the state is not already processed.
isProcessedP
  :: (Ord n, Ord v)
  => NonActive n v
  -> Auto n t v
  -> Chart n t v
  -> Bool
isProcessedP x auto = isJust . passiveTrav x auto


-- | Mark the passive item as processed (`done').
savePassive
    :: (Ord n, Ord v)
    => NonActive n v
    -> S.Set (Trav n t v)
    -> Auto n t v
    -> Chart n t v
    -> Chart n t v
savePassive p ts auto chart =
  chart {donePassive = newDone}
  where
    newDone =
        M.insertWith
            ( M.unionWith S.union )
            ( spanN p ^. beg
            , labelN p auto
            , spanN p ^. end )
            ( M.singleton p ts )
            ( donePassive chart )


-- | Check if, for the given active item, the given transitions are already
-- present in the hypergraph.
hasPassiveTrav
  :: (Ord n, Ord v)
  => NonActive n v
  -> S.Set (Trav n t v)
  -> Auto n t v
  -> Chart n t v
  -> Bool
hasPassiveTrav p travSet auto chart =
  case passiveTrav p auto chart of
    Just travSet' -> travSet `S.isSubsetOf` travSet'
    Nothing -> False


-- --------------------
-- -- Top passive items
-- --------------------
--
--
-- -- | Return the corresponding set of traversals for a passive item.
-- topPassiveTrav
--     :: (Ord n)
--     => TopPassive n
--     -> Chart n t a
--     -> Maybe (M.Map (Trav n t) (S.Set a))
-- topPassiveTrav p chart =
--   ( M.lookup
--     ( p ^. spanT ^. beg
--     , p ^. label
--     , p ^. spanT ^. end )
--     >=>
--     M.lookup p
--   )
--   ( doneTopPassive chart )
--
--
-- -- | Check if the state is not already processed.
-- isProcessedT :: (Ord n) => TopPassive n -> Chart n t a -> Bool
-- isProcessedT x =
--     check . topPassiveTrav x
--   where
--     check (Just _) = True
--     check _        = False
--
--
-- -- | Mark the passive item as processed (`done').
-- saveTopPassive
--     :: (Ord t, Ord n, Ord a)
--     => TopPassive n
--     -> M.Map (Trav n t) (S.Set a)
--     -> Chart n t a
--     -> Chart n t a
-- saveTopPassive p ts chart =
--   chart {doneTopPassive = newDone}
--   where
--     newDone =
--         M.insertWith
--             ( M.unionWith (M.unionWith S.union) )
--             ( p ^. spanT ^. beg
--             , p ^. label
--             , p ^. spanT ^. end )
--             ( M.singleton p ts )
--             ( doneTopPassive chart )
--
--
-- -- -- | Check if, for the given active item, the given transitions are already
-- -- -- present in the hypergraph.
-- -- hasTopPassiveTrav
-- --   :: (Ord t, Ord n)
-- --   => Passive
-- --   -> S.Set (Trav n t)
-- --   -> Auto n t a
-- --   -> Chart n t a
-- --   -> Bool
-- -- hasTopPassiveTrav p travSet auto chart =
-- --   case passiveTrav p auto chart of
-- --     Just travSet' -> travSet `S.isSubsetOf` travSet'
-- --     Nothing -> False


---------------------------------
-- Extraction of Processed Items
---------------------------------


-- | Return the list of final top-passive chart items.
finalFrom
    :: (Ord n)
    => n            -- ^ The start symbol
    -> Int          -- ^ The length of the input sentence
    -> Chart n t v  -- ^ Result of the earley computation
    -> [Top n v]
finalFrom start n Chart{..} =
    case M.lookup (0, start, n) donePassive of
        Nothing -> []
        Just m ->
            [ p
            | Right p <- M.keys m
            , p ^. label == start -- do we need to check this again here?
            , regular (p ^. spanT) ]


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
    :: (MS.MonadState s m)
    => (s -> Auto n t v)
    -> (s -> Chart n t v)
    -> DAG.DID
    -> Pos
    -> P.ListT m (Active v)
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


-- -- | Check if a passive item exists with:
-- -- * the given root non-terminal value (but not top-level auxiliary)
-- --   (BUG/WARNING: the second part is not checked!!!)
-- -- * the given span
-- rootSpan
--     :: (Ord n, MS.MonadState s m)
--     => (s -> Chart n t v)
--     -> n -> (Pos, Pos)
--     -> P.ListT m (NonActive n v)
-- rootSpan getChart x (i, j) = do
--   Chart{..} <- getChart <$> lift MS.get
--   each $ case M.lookup (i, x, j) donePassive of
--     Nothing -> []
--     Just m -> M.keys m


-- | Check if a passive item exists with:
-- * the given root non-terminal value (but not top-level auxiliary)
--   (BUG/WARNING: the second part is not checked!!!)
-- * the given span
rootSpan
    :: (Ord n, MS.MonadState s m)
    => (s -> Chart n t v)
    -> n -> (Pos, Pos)
    -> P.ListT m (Passive v)
rootSpan getChart x (i, j) = do
  Chart{..} <- getChart <$> lift MS.get
  each $ case M.lookup (i, x, j) donePassive of
    Nothing -> []
    Just m -> lefts (M.keys m)


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | ListT from a maybe.
some :: Monad m => Maybe a -> P.ListT m a
some = each . maybeToList


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each
