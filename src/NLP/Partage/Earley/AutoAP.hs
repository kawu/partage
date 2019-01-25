{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}


-- | Earley-style TAG parsing based on automata, with a distinction
-- between active and passive items.


module NLP.Partage.Earley.AutoAP
(
-- * Earley-style parsing
-- ** Input
  Input (..)
, fromList
, fromSets
-- ** From a factorized grammar
, recognize
, recognizeFrom
, parse
, earley
-- ** With automata precompiled
, recognizeAuto
, recognizeFromAuto
, parseAuto
, earleyAuto
-- ** Automaton
, Auto
, mkAuto

-- * Parsing trace (hypergraph)
, Hype (..)
-- ** Extracting parsed trees
, parsedTrees
-- ** Stats
, hyperNodesNum
, hyperEdgesNum
-- -- ** Printing
-- , printHype

-- * Sentence position
, Pos

-- * Provisional
, Item(..)
, finalFrom
) where


import           Prelude hiding             (span, (.))
import           Control.Applicative        ((<$>))
import           Control.Monad      (guard, void) -- , when)
import           Control.Monad.Trans.Class  (lift)
-- import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS
import           Control.Category ((>>>), (.))

-- import           Data.Function              (on)
-- import           Data.Either                (isLeft)
import           Data.Maybe     ( isNothing, mapMaybe
                                , maybeToList )
import qualified Data.Map.Strict            as M
-- import           Data.Ord       ( comparing )
-- import           Data.List      ( sortBy )
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import           Data.Lens.Light
import qualified Data.Vector                as V
-- import           Data.Hashable (Hashable)
-- import qualified Data.HashTable.IO          as H

import qualified Pipes                      as P
-- import qualified Pipes.Prelude              as P

import           Data.DAWG.Ord (ID)
-- import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.Partage.SOrd
import           NLP.Partage.DAG (Gram(..), DID(..))
import qualified NLP.Partage.DAG as DAG
import           NLP.Partage.Earley.Auto (Auto(..), mkAuto)
import qualified NLP.Partage.Auto as A
import qualified NLP.Partage.Auto.Set   as AS
import qualified NLP.Partage.Auto.DAWG  as D
import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.Tree       as T

import           NLP.Partage.Earley.Base hiding (nonTerm)
import qualified NLP.Partage.Earley.Base as Base
import           NLP.Partage.Earley.Item hiding (printPassive)
import           NLP.Partage.Earley.ExtWeight
import qualified NLP.Partage.Earley.Chart as Chart

-- For debugging purposes
#ifdef DebugOn
import qualified NLP.Partage.Earley.Item as Item
import qualified Data.Time              as Time
#endif


--------------------------------------------------
-- Item Type
--------------------------------------------------


-- | Passive or active item.
data Item n t
    = ItemP (Passive n t)
    | ItemA Active
    deriving (Show, Eq, Ord)


#ifdef DebugOn
-- | Print a passive item.
printPassive :: (Show n) => Passive n t -> Hype n t -> IO ()
printPassive p hype = Item.printPassive p (automat hype)


-- | Print an active item.
printItem :: (Show n, Show t) => Item n t -> Hype n t -> IO ()
printItem (ItemP p) h = printPassive p h
printItem (ItemA p) _ = printActive p


-- | Priority of an active item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prio :: Item n t -> Prio
prio (ItemP p) = prioP p
prio (ItemA p) = prioA p
#endif


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | A hypergraph dynamically constructed during parsing.
data Hype n t = Hype
    { automat   :: Auto n t
--     { automat :: A.GramAuto n t
--     -- ^ The underlying automaton
--
--     -- , withBody :: M.Map (Lab n t) (S.Set ID)
--     , withBody :: H.CuckooHashTable (Lab n t) (S.Set ID)
--     -- ^ A data structure which, for each label, determines the
--     -- set of automaton states from which this label goes out
--     -- as a body transition.

    , chart :: Chart.Chart n t
    -- ^ The underlying chart

    , waiting     :: Q.PSQ (Item n t) (ExtPrio n t)
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
mkHype
    -- :: (HOrd n, HOrd t)
    :: (Ord n)
    => Auto n t
    -> S.Set Active
    -> Hype n t
mkHype auto s = Hype
    { automat = auto
    , chart   = Chart.empty
    , waiting = Q.fromList
        [ ItemA p :-> extPrio (prioA p)
        | p <- S.toList s ] }


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


-- -- | Is the rule with the given head top-level?
-- isRoot :: DID -> Earley Bool
-- isRoot x = case x of
--     NonT{..}  -> isNothing labID
--     AuxRoot{} -> True
--     _         -> False


--------------------------------------------------
-- Hypergraph stats
--------------------------------------------------


-- -- | Number of nodes in the parsing hypergraph.
-- hyperNodesNum :: Hype n t -> Int
-- hyperNodesNum e
--     = length (listPassive e)
--     + length (listActive e)
--
--
-- -- | Number of edges in the parsing hypergraph.
-- hyperEdgesNum :: forall n t. Hype n t -> Int
-- hyperEdgesNum earSt
--     = sumOver listPassive
--     + sumOver listActive
--   where
--     sumOver :: (Hype n t -> [(a, S.Set (Trav n t))]) -> Int
--     sumOver listIt = sum
--         [ S.size travSet
--         | (_, travSet) <- listIt earSt ]


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
listWaiting :: (Ord n) => Hype n t -> [(Item n t, ExtPrio n t)]
listWaiting =
  let toPair (p :-> w) = (p, w)
   in map toPair . Q.toList . waiting


-- | Number of nodes in the parsing hypergraph.
doneNodesNum :: Hype n t -> Int
doneNodesNum e = Chart.doneNodesNum (chart e)


-- | Number of waiting nodes in the parsing hypergraph.
waitingNodesNum :: (Ord n) => Hype n t -> Int
waitingNodesNum = length . listWaiting


-- | Number of nodes in the parsing hypergraph.
hyperNodesNum :: (Ord n) => Hype n t -> Int
hyperNodesNum e = doneNodesNum e + waitingNodesNum e


-- | Number of nodes in the parsing hypergraph.
doneEdgesNum :: Hype n t -> Int
doneEdgesNum e = Chart.doneEdgesNum (chart e)


-- | Number of edges outgoing from waiting nodes in the underlying hypergraph.
waitingEdgesNum :: (Ord n) => Hype n t -> Int
waitingEdgesNum = sumTrav . listWaiting


-- | Number of edges in the parsing hypergraph.
hyperEdgesNum :: (Ord n) => Hype n t -> Int
hyperEdgesNum e = doneEdgesNum e + waitingEdgesNum e


-- | Sum up traversals.
sumTrav :: [(a, ExtPrio n t)] -> Int
sumTrav xs = sum
    [ S.size (prioTrav ext)
    | (_, ext) <- xs ]

--------------------
-- Active items
--------------------


-- -- | List all active done items together with the corresponding
-- -- traversals.
-- listActive :: Hype n t -> [(Active, S.Set (Trav n t))]
-- listActive = (M.elems >=> M.elems >=> M.toList) . doneActive
--
--
-- -- | Return the corresponding set of traversals for an active item.
-- activeTrav
--     :: (Ord n, Ord t)
--     => Active -> Hype n t
--     -> Maybe (S.Set (Trav n t))
-- activeTrav p
--     = (   M.lookup (p ^. spanA ^. end)
--       >=> M.lookup (p ^. state)
--       >=> M.lookup p )
--     . doneActive
--
--
-- -- | Check if the active item is not already processed.
-- _isProcessedA :: (Ord n, Ord t) => Active -> Hype n t -> Bool
-- _isProcessedA p =
--     check . activeTrav p
--   where
--     check (Just _) = True
--     check _        = False


-- | Check if the active item is not already processed.
isProcessedA :: Active -> Earley n t Bool
isProcessedA p = Chart.isProcessedA p . chart <$> RWS.get


-- | Mark the active item as processed (`done').
saveActive
    :: (Ord t, Ord n)
    => Active
    -> S.Set (Trav n t)
    -> Earley n t ()
saveActive p ts = do
  RWS.modify' $ \h ->
    let lhsMap = lhsNonTerm (automat h)
    in  h {chart = Chart.saveActive lhsMap p ts (chart h)}


-- -- | Check if, for the given active item, the given transitions are already
-- -- present in the hypergraph.
-- hasActiveTrav
--     :: (Ord t, Ord n)
--     => Active
--     -> S.Set (Trav n t)
--     -> Earley n t Bool
-- hasActiveTrav p travSet =
--   Chart.hasActiveTrav p travSet . chart <$> RWS.get


--------------------
-- Passive items
--------------------


-- -- | List all passive done items together with the corresponding
-- -- traversals.
-- listPassive :: Hype n t -> [(Passive n t, S.Set (Trav n t))]
-- listPassive = (M.elems >=> M.toList) . donePassive
--
--
-- -- | Return the corresponding set of traversals for a passive item.
-- passiveTrav
--     :: (Ord n, Ord t)
--     => Passive n t -> Hype n t
--     -> Maybe (S.Set (Trav n t))
-- passiveTrav p hype =
--     ( M.lookup
--         ( p ^. spanP ^. beg
--         , nonTerm (p ^. dagID) hype
--         , p ^. spanP ^. end ) >=> M.lookup p )
--     ( donePassive hype )
--
--
-- -- | Check if the state is not already processed.
-- _isProcessedP :: (Ord n, Ord t) => Passive n t -> Hype n t -> Bool
-- _isProcessedP x =
--     check . passiveTrav x
--   where
--     check (Just _) = True
--     check _        = False


-- | Check if the passive item is not already processed.
isProcessedP :: (Ord n) => Passive n t -> Earley n t Bool
isProcessedP p = do
  h <- RWS.get
  return $ Chart.isProcessedP p (automat h) (chart h)


-- | Mark the passive item as processed (`done').
savePassive
    :: (Ord t, Ord n)
    => Passive n t
    -> S.Set (Trav n t)
    -> Earley n t ()
savePassive p ts =
  -- RWS.state $ \s -> ((), s {donePassive = newDone s})
  RWS.modify' $ \h -> h {chart = Chart.savePassive p ts (automat h) (chart h)}


-- -- | Check if, for the given active item, the given transitions are already
-- -- present in the hypergraph.
-- hasPassiveTrav
--     :: (Ord t, Ord n)
--     => Passive n t
--     -> S.Set (Trav n t)
--     -> Earley n t Bool
-- hasPassiveTrav p travSet = do
--   h <- RWS.get
--   return $ Chart.hasPassiveTrav p travSet (automat h) (chart h)


--------------------
-- Waiting Queue
--------------------


-- | Add the active item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushActive :: (Ord t, Ord n) => Active -> Trav n t -> Earley n t ()
pushActive p t = isProcessedA p >>= \b -> if b
    then saveActive p $ S.singleton t
    else modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinPrio (ItemA p) newPrio
    newPrio = ExtPrio (prioA p) (S.singleton t)
-- pushActive p = RWS.state $ \s ->
--     let waiting' = if isProcessedA p s
--             then waiting s
--             else Q.insert (ItemA p) (prioA p) (waiting s)
--     in  ((), s {waiting = waiting'})


-- | Add the passive item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushPassive :: (Ord t, Ord n) => Passive n t -> Trav n t -> Earley n t ()
pushPassive p t = isProcessedP p >>= \b -> if b
    then savePassive p $ S.singleton t
    else modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinPrio (ItemP p) newPrio
    newPrio = ExtPrio (prioP p) (S.singleton t)
-- -- | Add the passive item to the waiting queue.  Check first if it
-- -- is not already in the set of processed (`done') states.
-- pushPassive :: (Ord t, Ord n) => Passive n t -> Earley n t ()
-- pushPassive p = RWS.state $ \s ->
--     let waiting' = if isProcessedP p s
--             then waiting s
--             else Q.insert (ItemP p) (prioP p) (waiting s)
--     in  ((), s {waiting = waiting'})


-- | Add to the waiting queue all items induced from
-- the given active item.
pushInduced :: (Ord t, Ord n) => Active -> Trav n t -> Earley n t ()
pushInduced p t = do
    pushActive p t
--     dag <- RWS.gets (gramDAG . automat)
--     hasElems (getL state p) >>= \b -> when b
--         (pushActive p t)
--     P.runListT $ do
--         did <- heads (getL state p)
--         lift . flip pushPassive t $
--             if not (DAG.isRoot did dag)
--             then Passive (Right did) (getL spanA p)
--             else check $ do
--                 x <- mkRoot <$> DAG.label did dag
--                 return $ Passive (Left x) (getL spanA p)
--             where
--               mkRoot node = case node of
--                 O.NonTerm x -> Root {rootLabel=x, isSister=False}
--                 O.Sister x  -> Root {rootLabel=x, isSister=True}
--                 _ -> error "pushInduced: invalid root"
--               check (Just x) = x
--               check Nothing  = error "pushInduced: invalid DID"


-- | Remove a state from the queue.
popItem :: (Ord n) => Earley n t (Maybe (Binding (Item n t) (ExtPrio n t)))
popItem = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (b, s) -> (Just b, st {waiting = s})


---------------------------------
-- Extraction of Processed Items
---------------------------------


-- | See `Chart.expectEnd`.
expectEnd :: DID -> Pos -> P.ListT (Earley n t) Active
expectEnd = Chart.expectEnd automat chart


-- | Return all passive items with:
-- * the given root non-terminal value (but not top-level auxiliary)
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t)
rootSpan = Chart.rootSpan chart


-- | See `Chart.rootEnd`.
rootEnd :: Ord n => n -> Pos -> P.ListT (Earley n t) Active
rootEnd = Chart.rootEnd chart


-- -- -- | Return all active processed items which:
-- -- -- * expect a given label,
-- -- -- * end on the given position.
-- -- expectEnd
-- --     :: (Ord n, Ord t) => Lab n t -> Pos
-- --     -> P.ListT (Earley n t) Active
-- -- expectEnd sym i = do
-- --     Hype{..} <- lift RWS.get
-- --     -- determine items which end on the given position
-- --     doneEnd <- some $ M.lookup i doneActive
-- --     -- determine automaton states from which the given label
-- --     -- leaves as a body transition
-- --     stateSet <- some $ M.lookup sym withBody
-- --     -- pick one of the states
-- --     stateID <- each $ S.toList stateSet
-- --     --
-- --     -- ALTERNATIVE: state <- each . S.toList $
-- --     --      stateSet `S.intersection` M.keySet doneEnd
-- --     --
-- --     -- determine items which refer to the chosen states
-- --     doneEndLab <- some $ M.lookup stateID doneEnd
-- --     -- return them all!
-- --     each $ M.keys doneEndLab
--
--
-- -- -- | Return all active processed items which:
-- -- -- * expect a given label,
-- -- -- * end on the given position.
-- -- expectEnd
-- --     :: (HOrd n, HOrd t) => Lab n t -> Pos
-- --     -> P.ListT (Earley n t) Active
-- -- expectEnd sym i = do
-- --     Hype{..} <- lift RWS.get
-- --     -- determine items which end on the given position
-- --     doneEnd <- some $ M.lookup i doneActive
-- --     -- determine automaton states from which the given label
-- --     -- leaves as a body transition
-- --     stateSet <- do
-- --         maybeSet <- lift . lift $
-- --             H.lookup (withBody automat) sym
-- --         some maybeSet
-- --     -- pick one of the states
-- --     stateID <- each . S.toList $
-- --          stateSet `S.intersection` M.keysSet doneEnd
-- --     -- determine items which refer to the chosen states
-- --     doneEndLab <- some $ M.lookup stateID doneEnd
-- --     -- return them all!
-- --     each $ M.keys doneEndLab
--
--
-- -- | Return all active processed items which:
-- -- * expect a given label,
-- -- * end on the given position.
-- expectEnd
--     -- :: (HOrd n, HOrd t) => DID -> Pos
--     :: (Ord n, Ord t) => DID -> Pos
--     -> P.ListT (Earley n t) Active
-- expectEnd did i = do
--     Hype{..} <- lift RWS.get
--     -- determine items which end on the given position
--     doneEnd <- some $ M.lookup i doneActive
--     -- determine automaton states from which the given label
--     -- leaves as a body transition
--     stateSet <- some $ M.lookup did (withBody automat)
--     -- pick one of the states
--     stateID <- each . S.toList $
--          stateSet `S.intersection` M.keysSet doneEnd
--     -- determine items which refer to the chosen states
--     doneEndLab <- some $ M.lookup stateID doneEnd
--     -- return them all!
--     each $ M.keys doneEndLab
--
--
-- -- | Check if a passive item exists with:
-- -- * the given root non-terminal value (but not top-level
-- --   auxiliary) (UPDATE: is this second part ensured?)
-- -- * the given span
-- rootSpan
--     :: Ord n => n -> (Pos, Pos)
--     -> P.ListT (Earley n t) (Passive n t)
-- rootSpan x (i, j) = do
--     Hype{..} <- lift RWS.get
--     -- listValues (i, x, j) donePassive
--     each $ case M.lookup (i, x, j) donePassive of
--         Nothing -> []
--         Just m -> M.keys m


-- -- | List all processed passive items.
-- listDone :: Done n t -> [Item n t]
-- listDone done = ($ done) $
--     M.elems >=> M.elems >=>
--     M.elems >=> S.toList


--------------------------------------------------
-- New Automaton-Based Primitives
--------------------------------------------------


-- | Follow the given terminal in the underlying automaton.
followTerm :: (Ord t) => ID -> Maybe t -> P.ListT (Earley n t) ID
followTerm i c = do
    -- get the underlying automaton
    auto <- RWS.gets $ automat
    -- get the dag ID corresponding to the given terminal
    did  <- each . S.toList . maybe S.empty id $ M.lookup c (termDID auto)
    -- follow the label
    some $ A.follow (gramAuto auto) i (A.Body did)


-- -- | Follow the given terminal in the underlying automaton.
-- followFoot :: (Ord n, Ord t) => ID -> n -> P.ListT (Earley n t) ID
-- followFoot i c = do
--     -- get the underlying automaton
--     auto <- RWS.gets $ automat
--     -- get the dag ID corresponding to the given terminal
--     did  <- some $ M.lookup c (footDID auto)
--     -- follow the label
--     some $ A.follow (gramAuto auto) i (A.Body did)


-- | Follow the given body transition in the underlying automaton.
-- It represents the transition function of the automaton.
--
-- TODO: merge with `followTerm`.
follow :: ID -> DID -> P.ListT (Earley n t) ID
follow i x = do
    -- get the underlying automaton
    auto <- RWS.gets $ gramAuto . automat
    -- follow the label
    some $ A.follow auto i (A.Body x)


-- | Rule heads outgoing from the given automaton state.
heads :: ID -> P.ListT (Earley n t) DID
heads i = do
    auto <- RWS.gets $ gramAuto . automat
    let mayHead (x, _) = case x of
            A.Body _  -> Nothing
            A.Head y -> Just y
    each $ mapMaybe mayHead $ A.edges auto i


-- -- | Rule body elements outgoing from the given automaton state.
-- elems :: ID -> P.ListT (Earley n t) (Lab n t)
-- elems i = do
--     auto <- RWS.gets automat
--     let mayBody (x, _) = case x of
--             A.Body y  -> Just y
--             A.Head _ -> Nothing
--     each $ mapMaybe mayBody $ A.edges auto i


-- | Check if any body element leaves the given state.
hasElems :: ID -> Earley n t Bool
hasElems i = do
    auto <- RWS.gets $ gramAuto . automat
    let mayBody (x, _) = case x of
            A.Body y  -> Just y
            A.Head _ -> Nothing
    return
        . not . null
        . mapMaybe mayBody
        $ A.edges auto i


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- | Try to perform SCAN on the given active state.
tryScan :: (SOrd t, SOrd n) => Active -> Earley n t ()
tryScan p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- read the word immediately following the ending position of
    -- the state
    c <- readInput $ getL (spanA >>> end) p
    -- follow appropriate terminal transition outgoing from the
    -- given automaton state
    j <- followTerm (getL state p) (Just c)
    -- construct the resultant active item
    -- let q = p {state = j, end = end p + 1}
    let q = setL state j
          . modL' (spanA >>> end) (+1)
          $ p
    -- push the resulting state into the waiting queue
    lift $ pushInduced q $ Scan p c
#ifdef DebugOn
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[S]  " >> printActive p
        putStr "  :  " >> printActive q
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


-- | Try to scan an empty terminal.
tryEmpty :: (SOrd t, SOrd n) => Active -> Earley n t ()
tryEmpty p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- follow appropriate terminal transition outgoing from the
    -- given automaton state
    j <- followTerm (getL state p) Nothing
    -- construct the resultant active item
    -- let q = p {state = j}
    let q = setL state j $ p
    -- push the resulting state into the waiting queue
    lift $ pushInduced q $ Empty p
#ifdef DebugOn
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[E]  " >> printActive p
        putStr "  :  " >> printActive q
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the passive item `p` to complement (=> substitution) other
-- rules. Implementation of regular substitution as well as pseudo-substitution.
trySubst :: (SOrd t, SOrd n) => Passive n t -> Earley n t ()
trySubst p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pDID = getL dagID p
        pSpan = getL spanP p
    -- make sure that `p' represents regular rules
    guard . regular $ pSpan
    -- make sure that `p` does not represent sister tree
    guard $ case pDID of
        Left root -> not (isSister root)
        Right _ -> True
    -- the underlying leaf map
    leafMap <- RWS.gets (leafDID  . automat)
    -- now, we need to choose the DAG node to search for depending on whether
    -- the DAG node provided by `p' is a root or not
    theDID <- case pDID of
        -- real substitution
        Left root ->
            each . S.toList . maybe S.empty id $
                M.lookup (notFootLabel root) leafMap
        -- pseudo-substitution
        Right did -> return did
    -- find active items which end where `p' begins and which
    -- expect the DAG node provided by `p'
    q <- expectEnd theDID (getL beg pSpan)
    -- follow the DAG node
    j <- follow (getL state q) theDID
    -- construct the resultant state
    let q' = setL state j
           . setL (end . spanA) (getL end pSpan)
           $ q
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Subst p q
#ifdef DebugOn
    -- print logging information
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[U]  " >> printPassive p hype
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- FOOT ADJOIN
--------------------------------------------------


-- | `tryAdjoinInit p q':
-- * `p' is a completed state (regular or auxiliary)
-- * `q' not completed and expects a *real* foot
tryAdjoinInit :: (SOrd n, SOrd t) => Passive n t -> Earley n t ()
tryAdjoinInit p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pDID = p ^. dagID
        pSpan = p ^. spanP
    -- the underlying dag grammar
    dag <- RWS.gets (gramDAG . automat)
    footMap <- RWS.gets (footDID  . automat)
    -- make sure that the corresponding rule is either regular or
    -- intermediate auxiliary ((<=) used as implication here)
    -- guard $ auxiliary pSpan <= not (topLevel pLab)
    -- guard $ auxiliary pSpan <= not (DAG.isRoot pDID dag)
    guard $ auxiliary pSpan <= not (isRoot pDID)
    -- what is the symbol in the p's DAG node?
    footNT <- some (nonTerm' pDID dag)
--     footNT <- case pDID of
--         Left rootNT -> return rootNT
--         Right did   -> some (nonTerm' =<< DAG.label did dag)
    -- what is the corresponding foot DAG ID?
    footID <- each . S.toList . maybe S.empty id $ M.lookup footNT footMap
    -- find all active items which expect a foot with the given
    -- symbol and which end where `p` begins
    -- let foot = AuxFoot $ nonTerm pLab
    q <- expectEnd footID (getL beg pSpan)
    -- follow the foot
    j <- follow (getL state q) footID
    -- construct the resultant state
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (Just
                ( pSpan ^. beg
                , pSpan ^. end ))
           $ q
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Foot q p -- -- $ nonTerm foot
#ifdef DebugOn
    -- print logging information
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[A]  " >> printPassive p hype
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- INTERNAL ADJOIN
--------------------------------------------------


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
tryAdjoinCont :: (SOrd n, SOrd t) => Passive n t -> Earley n t ()
tryAdjoinCont p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pDID = p ^. dagID
        pSpan = p ^. spanP
    -- the underlying dag grammar
    -- dag <- RWS.gets (gramDAG . automat)
    -- make sure the label is not top-level (internal spine
    -- non-terminal)
    -- guard . not $ topLevel pLab
    -- guard . not $ DAG.isRoot pDID dag
    -- guard . not $ isRoot pDID
    did <- some $ case pDID of
        Left _rootNT -> Nothing
        Right did -> Just did
    -- make sure that `p' is an auxiliary item
    guard . auxiliary $ pSpan
    -- find all rules which expect a spine non-terminal provided
    -- by `p' and which end where `p' begins
    q <- expectEnd did (pSpan ^. beg)
    -- follow the spine non-terminal
    j <- follow (q ^. state) did
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (pSpan ^. gap)
           $ q
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Subst p q
#ifdef DebugOn
    -- logging info
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[B]  " >> printPassive p hype
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- ROOT ADJOIN
--------------------------------------------------


-- | Adjoin a fully-parsed auxiliary state `p` to a partially parsed
-- tree represented by a fully parsed rule/state `q`.
tryAdjoinTerm :: (SOrd t, SOrd n) => Passive n t -> Earley n t ()
tryAdjoinTerm q = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- let qLab = q ^. label
    let qDID = q ^. dagID
        qSpan = q ^. spanP
    -- the underlying dag grammar
    dag <- RWS.gets (gramDAG . automat)
    -- make sure the label is top-level
    -- guard $ topLevel qLab
    guard $ isRoot qDID
    -- make sure that it is an auxiliary item (by definition only
    -- auxiliary states have gaps)
    (gapBeg, gapEnd) <- some $ qSpan ^. gap
    -- take all passive items with a given span and a given
    -- root non-terminal (IDs irrelevant)
    qNonTerm <- some (nonTerm' qDID dag)
    p <- rootSpan qNonTerm (gapBeg, gapEnd)
#ifdef NoAdjunctionRestriction
    let changeAdjState = id
#else
    -- make sure that node represented by `p` was not yet adjoined to
    guard . not $ getL isAdjoinedTo p
    let changeAdjState = setL isAdjoinedTo True
#endif
    -- construct the resulting item
    let p' = setL (spanP >>> beg) (qSpan ^. beg)
           . setL (spanP >>> end) (qSpan ^. end)
           . changeAdjState
           $ p
    lift $ pushPassive p' $ Adjoin q p
#ifdef DebugOn
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[C]  " >> printPassive q hype
        putStr "  +  " >> printPassive p hype
        putStr "  :  " >> printPassive p' hype
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- SISTER ADJUNCTION
--------------------------------------------------


-- | Try to apply sister-adjunction w.r.t. the given passive item.
trySisterAdjoin :: (SOrd t, SOrd n) => Passive n t -> Earley n t ()
trySisterAdjoin p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pDID = getL dagID p
        pSpan = getL spanP p
    -- make sure that `p' is not gapped
    guard . regular $ pSpan
    -- make sure that `p` represents a sister tree
    Left root <- return pDID
    guard $ isSister root
    -- find active items which end where `p' begins and which have the
    -- corresponding LHS non-terminal
    q <- rootEnd (notFootLabel root) (getL beg pSpan)
    -- construct the resultant item with the same state and extended span
    let q' = setL (end . spanA) (getL end pSpan) $ q
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ SisterAdjoin p q
#ifdef DebugOn
    -- print logging information
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[I]  " >> printPassive p hype
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- DEACTIVATE
--------------------------------------------------


-- | Try to perform DEACTIVATE.
tryDeactivate :: (SOrd t, SOrd n) => Active -> Earley n t ()
tryDeactivate p = void $ P.runListT $ do
#ifdef DebugOn
  begTime <- lift . lift $ Time.getCurrentTime
#endif
  dag <- RWS.gets (gramDAG . automat)
  did <- heads (getL state p)
  let q = if not (DAG.isRoot did dag)
          then Passive
               { _dagID = Right did
               , _spanP = getL spanA p
               , _isAdjoinedTo = False }
          else check $ do
            x <- mkRoot <$> DAG.label did dag
            return $ Passive
              { _dagID = Left x
              , _spanP = getL spanA p
              , _isAdjoinedTo = False }
  lift $ pushPassive q (Deactivate p)
#ifdef DebugOn
  -- print logging information
  hype <- RWS.get
  lift . lift $ do
      endTime <- Time.getCurrentTime
      putStr "[D]  " >> printActive p
      putStr "  :  " >> printPassive q hype
      putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif
  where
    mkRoot node = case node of
      O.NonTerm x -> NotFoot {notFootLabel=x, isSister=False}
      O.Sister x  -> NotFoot {notFootLabel=x, isSister=True}
      _ -> error "pushInduced: invalid root"
    check (Just x) = x
    check Nothing  = error "pushInduced: invalid DID"


--------------------------------------------------
-- Earley step
--------------------------------------------------


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step
    -- :: (SOrd t, SOrd n)
    :: (SOrd t, SOrd n)
    => Binding (Item n t) (ExtPrio n t)
    -> Earley n t ()
step (ItemP p :-> e) = do
    mapM_ ($ p)
      [ trySubst
      , tryAdjoinInit
      , tryAdjoinCont
      , tryAdjoinTerm
      , trySisterAdjoin
      ]
    savePassive p $ prioTrav e
step (ItemA p :-> e) = do
    mapM_ ($ p)
      [ tryScan
      , tryEmpty
      , tryDeactivate
      ]
    saveActive p (prioTrav e)


---------------------------
-- Extracting Parsed Trees
---------------------------


-- | Extract the set of parsed trees obtained on the given input
-- sentence.  Should be run on the result of the earley parser.
parsedTrees
    :: forall n t. (Ord n, Ord t)
    => Hype n t     -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> [T.Tree n (Maybe t)]
parsedTrees hype start n

    = concatMap fromPassive
    $ finalFrom start n hype

  where

    fromPassive :: Passive n t -> [T.Tree n (Maybe t)]
    fromPassive p = concat
        [ fromPassiveTrav p trav
        | travSet <- maybeToList $ passiveTrav p hype
        , trav <- S.toList travSet ]

    fromPassiveTrav _p (Adjoin qa qm) =
        [ replaceFoot ini aux
        | aux <- fromPassive qa
        , ini <- fromPassive qm ]

    fromPassiveTrav p (Deactivate q) =
        [ T.Branch
            (nonTerm (p ^. dagID) hype)
            (reverse ts)
        | ts <- fromActive q
        ]

    fromPassiveTrav _ (SisterAdjoin _ _) =
        error "parsedTrees: impossible SisterAdjoin?"

    fromPassiveTrav _ _ =
        error "parsedTrees: impossible fromPassiveTrav"

    -- | Replace foot (the only non-terminal leaf) by the given
    -- initial tree.
    replaceFoot ini (T.Branch _ []) = ini
    replaceFoot ini (T.Branch x ts) = T.Branch x $ map (replaceFoot ini) ts
    replaceFoot _ t@(T.Leaf _)    = t


    fromActive  :: Active -> [[T.Tree n (Maybe t)]]
    fromActive p = case activeTrav p hype of
        Nothing -> error "fromActive: unknown active item"
        Just travSet -> if S.null travSet
            then [[]]
            else concatMap
                (fromActiveTrav p)
                (S.toList travSet)

    fromActiveTrav _p (Scan q t) =
        [ T.Leaf (Just t) : ts
        | ts <- fromActive q ]

    fromActiveTrav _p (Foot q p) =
        [ T.Branch (nonTerm (p ^. dagID) hype) [] : ts
        | ts <- fromActive q ]

    fromActiveTrav _p (Subst qp qa) =
        [ t : ts
        | ts <- fromActive qa
        , t  <- fromPassive qp ]

    fromActiveTrav _p (SisterAdjoin qp qa) =
        [ ts' ++ ts
        | ts  <- fromActive qa
        , ts' <- T.subTrees <$> fromPassive qp ]

    fromActiveTrav _ _ =
        error "parsedTrees: impossible fromActiveTrav"


--------------------------------------------------
-- EARLEY
--------------------------------------------------


-- | We have some non-determinism at the level of terminals as well as possible
-- empty terminals.
type DAGram n t = DAG.Gram n (S.Set (Maybe t))


-- | Does the given grammar generate the given sentence?
-- Uses the `earley` algorithm under the hood.
recognize
    :: (SOrd t, SOrd n)
    => DAGram n t         -- ^ The grammar (set of rules)
    -> Input t            -- ^ Input sentence
    -> IO Bool
recognize DAG.Gram{..} input = do
    let gram = fromGram (M.keysSet factGram)
        auto = mkAuto dagGram gram
    recognizeAuto auto input


-- | Does the given grammar generate the given sentence from the
-- given non-terminal symbol (i.e. from an initial tree with this
-- symbol in its root)?  Uses the `earley` algorithm under the
-- hood.
recognizeFrom
    :: (SOrd t, SOrd n)
    => DAGram n t           -- ^ The grammar
    -> n                    -- ^ The start symbol
    -> Input t              -- ^ Input sentence
    -> IO Bool
recognizeFrom DAG.Gram{..} start input = do
    let gram = fromGram (M.keysSet factGram)
        auto = mkAuto dagGram gram
    recognizeFromAuto auto start input


-- | Parse the given sentence and return the set of parsed trees.
parse
    :: (SOrd t, SOrd n)
    => DAGram n t           -- ^ The grammar (set of rules)
    -> n                    -- ^ The start symbol
    -> Input t              -- ^ Input sentence
    -> IO [T.Tree n (Maybe t)]
parse DAG.Gram{..} start input = do
    let gram = fromGram (M.keysSet factGram)
        auto = mkAuto dagGram gram
    parseAuto auto start input


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (SOrd t, SOrd n)
    => DAGram n t           -- ^ The grammar (set of rules)
    -> Input t              -- ^ Input sentence
    -> IO (Hype n t)
earley DAG.Gram{..} input = do
    let gram = fromGram (M.keysSet factGram)
        auto = mkAuto dagGram gram
    earleyAuto auto input


-- | Default grammar automaton creation method.
fromGram :: S.Set DAG.Rule -> A.GramAuto
fromGram = AS.fromGram D.fromGram


--------------------------------------------------
-- Parsing with automaton
--------------------------------------------------


-- | See `recognize`.
recognizeAuto
    :: (SOrd t, SOrd n)
    => Auto n t           -- ^ Grammar automaton
    -> Input t            -- ^ Input sentence
    -> IO Bool
recognizeAuto auto xs =
    isRecognized xs <$> earleyAuto auto xs


-- | See `recognizeFrom`.
recognizeFromAuto
    :: (SOrd t, SOrd n)
    => Auto n t       -- ^ Grammar automaton
    -> n                    -- ^ The start symbol
    -> Input t            -- ^ Input sentence
    -> IO Bool
recognizeFromAuto auto start input = do
    hype <- earleyAuto auto input
    let n = V.length (inputSent input)
    return $ (not.null) (finalFrom start n hype)


-- | See `parse`.
parseAuto
    :: (SOrd t, SOrd n)
    => Auto n t           -- ^ Grammar automaton
    -> n                  -- ^ The start symbol
    -> Input t            -- ^ Input sentence
    -> IO [T.Tree n (Maybe t)]
parseAuto auto start input = do
    earSt <- earleyAuto auto input
    let n = V.length (inputSent input)
    return $ parsedTrees earSt start n


-- | See `earley`.
earleyAuto
    :: (SOrd t, SOrd n)
    => Auto n t         -- ^ Grammar automaton
    -> Input t          -- ^ Input sentence
    -> IO (Hype n t)
earleyAuto auto input = do
    fst <$> RWS.execRWST loop input st0
  where
--     init = forM_ (S.toList $ DAG.nodeSet $ gramDAG auto) $ \i -> do
--         lift $ do
--             putStr (show i)
--             putStr " => "
--             print . DAG.label i $ gramDAG auto
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkHype auto $ S.fromList
        [ Active root Span
            { _beg   = i
            , _end   = i
            , _gap   = Nothing }
        | i <- [0 .. n - 1]
        , root <- S.toList . A.roots $ gramAuto auto ]
    -- input length
    n = V.length (inputSent input)
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popItem >>= \mp -> case mp of
        Nothing -> return ()
        Just p  -> step p >> loop


--------------------------------------------------
-- New utilities
--------------------------------------------------


-- -- | Return the list of final passive chart items.
-- finalFrom
--     :: (Ord n, Eq t)
--     => n            -- ^ The start symbol
--     -> Int          -- ^ The length of the input sentence
--     -> Hype n t     -- ^ Result of the earley computation
--     -> [Passive n t]
-- finalFrom start n Hype{..} =
--     case M.lookup (0, start, n) donePassive of
--         Nothing -> []
--         Just m ->
--             [ p
--             | p <- M.keys m
--             , p ^. dagID == Left start ]
--
--
-- -- -- | Return the list of final passive chart items.
-- -- final
-- --     :: (Ord n, Eq t)
-- --     -> Int          -- ^ The length of the input sentence
-- --     -> Hype n t    -- ^ Result of the earley computation
-- --     -> [Passive n t]
-- -- final start n Hype{..} =
-- --     case M.lookup (0, start, n) donePassive of
-- --         Nothing -> []
-- --         Just m ->
-- --             [ p
-- --             | p <- M.keys m
-- --             , p ^. label == NonT start Nothing ]


-- | Check whether the given sentence is recognized
-- based on the resulting state of the earley parser.
isRecognized
    :: (SOrd n)
    => Input t           -- ^ Input sentence
    -> Hype n t          -- ^ Earley parsing result
    -> Bool
isRecognized input Hype{..} =
    (not . null)
    (complete
        (agregate $ Chart.donePassive chart))
  where
    n = V.length (inputSent input)
    complete done =
        [ True | item <- S.toList done
        , item ^. spanP ^. beg == 0
        , item ^. spanP ^. end == n
        , isNothing (item ^. spanP ^. gap)
        -- admit only *fully* recognized trees
        , isRoot (item ^. dagID) ]
        -- , DAG.isRoot (item ^. dagID) (gramDAG automat) ]
        -- , isRoot (item ^. label) ]
    agregate = S.unions . map M.keysSet . M.elems
    -- isRoot (NonT _ Nothing) = True
    -- isRoot _ = False


--------------------------------------------------
-- New Utilities
--------------------------------------------------


-- | Return the corresponding set of traversals for an active item.
activeTrav
  :: Active
  -> Hype n t
  -> Maybe (S.Set (Trav n t))
activeTrav p h = Chart.activeTrav p (chart h)


-- | Return the corresponding set of traversals for a passive item.
passiveTrav
  :: (Ord n)
  => Passive n t
  -> Hype n t
  -> Maybe (S.Set (Trav n t))
passiveTrav p h = Chart.passiveTrav p (automat h) (chart h)


-- | Return the list of final, initial, passive chart items.
finalFrom
    :: (Ord n)
    => n            -- ^ The start symbol
    -> Int          -- ^ The length of the input sentence
    -> Hype n t     -- ^ Result of the earley computation
    -> [Passive n t]
finalFrom start n hype = Chart.finalFrom start n (chart hype)


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | Strict modify (in mtl starting from version 2.2).
modify' :: RWS.MonadState s m => (s -> s) -> m ()
modify' f = do
  x <- RWS.get
  RWS.put $! f x


-- -- | MaybeT transformer.
-- maybeT :: Monad m => Maybe a -> MaybeT m a
-- maybeT = MaybeT . return


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each


-- | ListT from a maybe.
some :: Monad m => Maybe a -> P.ListT m a
some = each . maybeToList


-- -- | Is the rule with the given head top-level?
-- topLevel :: Lab n t -> Bool
-- topLevel x = case x of
--     NonT{..}  -> isNothing labID
--     AuxRoot{} -> True
--     _         -> False


-- -- | Pipe all values from the set corresponding to the given key.
-- listValues
--     :: (Monad m, Ord a)
--     => a -> M.Map a (S.Set b)
--     -> P.ListT m b
-- listValues x m = each $ case M.lookup x m of
--     Nothing -> []
--     Just s -> S.toList s


-- | Take the non-terminal of the underlying DAG node.
nonTerm :: Either (NotFoot n) DID -> Hype n t -> n
nonTerm i = Base.nonTerm i . automat
