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
, Hype
-- ** Extracting parsed trees
, parsedTrees
-- ** Stats
, hyperNodesNum
, hyperEdgesNum
-- ** Printing
, printHype

-- * Sentence position
, Pos
) where


import           Prelude hiding             (span, (.))
import           Control.Applicative        ((<$>))
import           Control.Monad      (guard, void, (>=>), when, forM_)
import           Control.Monad.Trans.Class  (lift)
-- import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS
import           Control.Category ((>>>), (.))

import           Data.Function              (on)
import           Data.Maybe     ( isJust, isNothing, mapMaybe
                                , maybeToList )
import qualified Data.Map.Strict            as M
import           Data.Ord       ( comparing )
import           Data.List      ( sortBy )
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import           Data.Lens.Light
import qualified Data.Vector                as V
import           Data.Hashable (Hashable)
import qualified Data.HashTable.IO          as H

import qualified Pipes                      as P
-- import qualified Pipes.Prelude              as P

import           Data.DAWG.Ord (ID)
-- import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.Partage.SOrd
-- import           NLP.Partage.FactGram (FactGram)
import           NLP.Partage.FactGram.DAG (Gram(..), DID(..), DAG)
import qualified NLP.Partage.FactGram.DAG as DAG
-- import           NLP.Partage.FactGram.Internal
--                                 ( Lab(..), viewLab )
import qualified NLP.Partage.Auto as A
import qualified NLP.Partage.Auto.DAWG  as D
import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.Tree       as T

-- For debugging purposes
#ifdef DebugOn
import qualified Data.Time              as Time
#endif


--------------------------------------------------
-- Input
--------------------------------------------------


-- | Input of the parser.
newtype Input t = Input {
      inputSent :: V.Vector (S.Set t)
    -- ^ The input sentence
    }


-- -- | Input of the parser.
-- data Input t = Input {
--       inputSent :: V.Vector (S.Set t)
--     -- ^ The input sentence
--     , lexGramI  :: t -> S.Set t
--     -- ^ Lexicon grammar interface: each terminal @t@ in the
--     -- `inputSent` can potentially represent several different
--     -- terminals (anchors) at the level of the grammar.
--     -- If equivalent to `id`, no lexicon-grammar interface is used.
--     -- Otherwise, type @t@ represents both anchors and real terminals
--     -- (words from input sentences).
--     }


-- | Construct `Input` from a list of terminals.
fromList :: [t] -> Input t
fromList = fromSets . map S.singleton


-- | Construct `Input` from a list of sets of terminals, each set
-- representing all possible interpretations of a given word.
fromSets :: [S.Set t] -> Input t
-- fromSets xs = Input (V.fromList xs) (\t -> S.singleton t)
fromSets xs = Input (V.fromList xs)


-- -- | Set the lexicon-grammar interface to
-- setLexGramI :: Input t ->


--------------------------------------------------
-- BASE TYPES
--------------------------------------------------


-- | A position in the input sentence.
type Pos = Int


data Span = Span {
    -- | The starting position.
      _beg   :: Pos
    -- | The ending position (or rather the position of the dot).
    , _end   :: Pos
    -- | Coordinates of the gap (if applies)
    , _gap   :: Maybe (Pos, Pos)
    } deriving (Show, Eq, Ord)
$( makeLenses [''Span] )


-- | Active chart item : state reference + span.
data Active = Active {
      _state :: ID
    , _spanA :: Span
    } deriving (Show, Eq, Ord)
$( makeLenses [''Active] )


-- | Passive chart item : label + span.
-- UPDATE: instead of a label, DAG node ID.
data Passive n t = Passive {
      -- _label :: Lab n t
      _dagID :: DID
    , _spanP :: Span
    } deriving (Show, Eq, Ord)
$( makeLenses [''Passive] )


-- | Does it represent regular rules?
regular :: Span -> Bool
regular = isNothing . getL gap


-- | Does it represent auxiliary rules?
auxiliary :: Span -> Bool
auxiliary = isJust . getL gap


-- | Print an active item.
printSpan :: Span -> IO ()
printSpan span = do
    putStr . show $ getL beg span
    putStr ", "
    case getL gap span of
        Nothing -> return ()
        Just (p, q) -> do
            putStr $ show p
            putStr ", "
            putStr $ show q
            putStr ", "
    putStr . show $ getL end span


-- | Print an active item.
printActive :: Active -> IO ()
printActive p = do
    putStr "("
    putStr . show $ getL state p
    putStr ", "
    printSpan $ getL spanA p
    putStrLn ")"


-- | Print a passive item.
printPassive :: (Show n, Show t) => Passive n t -> IO ()
printPassive p = do
    putStr "("
    -- putStr . viewLab $ getL label p
    putStr . show $ getL dagID p
    putStr ", "
    printSpan $ getL spanP p
    putStrLn ")"


--------------------------------------------------
-- Traversal
--------------------------------------------------


-- | Traversal represents an action of inducing a new item on the
-- basis of one or two other chart items.  It can be seen as an
-- application of one of the inference rules specifying the parsing
-- algorithm.
--
-- TODO: Sometimes there is no need to store all the arguments of the
-- inference rules, it seems.  From one of the arguments the other
-- one could be derived.
data Trav n t
    = Scan
        { _scanFrom :: Active
        -- ^ The input active state
        , _scanTerm :: t
        -- ^ The scanned terminal
        }
    | Subst
        { _passArg  :: Passive n t
        -- ^ The passive argument of the action
        , _actArg   :: Active
        -- ^ The active argument of the action
        }
    -- ^ Pseudo substitution
    | Foot
        { _actArg   :: Active
        -- ^ The passive argument of the action
        -- , theFoot  :: n
        , _theFoot  :: Passive n t
        -- ^ The foot non-terminal
        }
    -- ^ Foot adjoin
    | Adjoin
        { _passAdj  :: Passive n t
        -- ^ The adjoined item
        , _passMod  :: Passive n t
        -- ^ The modified item
        }
    -- ^ Adjoin terminate with two passive arguments
    deriving (Show, Eq, Ord)


-- | Print a traversal.
printTrav :: (Show n, Show t) => Item n t -> Trav n t -> IO ()
printTrav q' (Scan p x) = do
    putStr "# " >> printActive p
    putStr "+ " >> print x
    putStr "= " >> printItem q'
printTrav q' (Subst p q) = do
    putStr "# " >> printActive q
    putStr "+ " >> printPassive p
    putStr "= " >> printItem q'
printTrav q' (Foot q p) = do
    putStr "# " >> printActive q
    putStr "+ " >> printPassive p
    putStr "= " >> printItem q'
printTrav q' (Adjoin p s) = do
    putStr "# " >> printPassive p
    putStr "+ " >> printPassive s
    putStr "= " >> printItem q'


--------------------------------------------------
-- Priority
--------------------------------------------------


-- | Priority type.
--
-- NOTE: Priority has to be composed from two elements because
-- otherwise `tryAdjoinTerm` could work incorrectly.  That is,
-- the modified item could be popped from the queue after the
-- modifier (auxiliary) item and, as a result, adjunction would
-- not be considered.
type Prio = (Int, Int)


-- | Priority of an active item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioA :: Active -> Prio
prioA p =
    let i = getL (beg . spanA) p
        j = getL (end . spanA) p
    in  (j, j - i)


-- | Priority of a passive item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioP :: Passive n t -> Prio
prioP p =
    let i = getL (beg . spanP) p
        j = getL (end . spanP) p
    in  (j, j - i)


-- | Extended priority which preservs information about the traversal
-- leading to the underlying chart item.
data ExtPrio n t = ExtPrio
    { prioVal   :: Prio
    -- ^ The actual priority
    , prioTrav  :: S.Set (Trav n t)
    -- ^ Traversal leading to the underlying chart item
    } deriving (Show)

instance (Eq n, Eq t) => Eq (ExtPrio n t) where
    (==) = (==) `on` prioVal
instance (Ord n, Ord t) => Ord (ExtPrio n t) where
    compare = compare `on` prioVal


-- | Construct a new `ExtPrio`.
extPrio :: Prio -> ExtPrio n t
extPrio p = ExtPrio p S.empty


-- | Join two priorities:
-- * The actual priority preserved is the lower of the two,
-- * The traversals are unioned.
--
-- NOTE: at the moment, priority is strictly specified by the
-- underlying chart item itself so we know that both priorities must
-- be equal.  Later when we start using probabilities this statement
-- will no longer hold.
joinPrio :: (Ord n, Ord t) => ExtPrio n t -> ExtPrio n t -> ExtPrio n t
joinPrio x y = ExtPrio
    (min (prioVal x) (prioVal y))
    (S.union (prioTrav x) (prioTrav y))


--------------------------------------------------
-- Item Type
--------------------------------------------------


-- | Passive or active item.
data Item n t
    = ItemP (Passive n t)
    | ItemA Active
    deriving (Show, Eq, Ord)


-- | Print an active item.
printItem :: (Show n, Show t) => Item n t -> IO ()
printItem (ItemP p) = printPassive p
printItem (ItemA p) = printActive p


-- | Priority of an active item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prio :: Item n t -> Prio
prio (ItemP p) = prioP p
prio (ItemA p) = prioA p


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

    -- , doneActive  :: M.Map (ID, Pos) (S.Set (Active n t))
    , doneActive  :: M.Map Pos (M.Map ID
        (M.Map Active (S.Set (Trav n t))))
    -- ^ Processed active items partitioned w.r.t ending
    -- positions and state IDs.

    -- , donePassive :: S.Set (Passive n t)
    , donePassive :: M.Map (Pos, n, Pos)
        (M.Map (Passive n t) (S.Set (Trav n t)))
    -- ^ Processed passive items.

    , waiting     :: Q.PSQ (Item n t) (ExtPrio n t)
    -- ^ The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    --
    -- NOTE2: Don't understand the note below...
    -- NOTE: The only operation which requires active states to
    -- be put to the queue in the current algorithm is the scan
    -- operation.  So perhaps we could somehow bypass this
    -- problem and perform scan elsewhere.  Nevertheless, it is
    -- not certain that the same will apply to the probabilistic
    -- parser.
    }


-- | Make an initial `Hype` from a set of states.
mkHype
    :: (HOrd n, HOrd t)
    => Auto n t
    -> S.Set Active
    -> Hype n t
mkHype auto s = Hype
    { automat  = auto
    -- , withBody = theBody -- mkWithBody dag
    , doneActive  = M.empty
    , donePassive = M.empty
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


--------------------------------------------------
-- Hypergraph stats
--------------------------------------------------


-- | Number of nodes in the parsing hypergraph.
hyperNodesNum :: Hype n t -> Int
hyperNodesNum e
    = length (listPassive e)
    + length (listActive e)


-- | Number of edges in the parsing hypergraph.
hyperEdgesNum :: forall n t. Hype n t -> Int
hyperEdgesNum earSt
    = sumOver listPassive
    + sumOver listActive
  where
    sumOver :: (Hype n t -> [(a, S.Set (Trav n t))]) -> Int
    sumOver listIt = sum
        [ S.size travSet
        | (_, travSet) <- listIt earSt ]


-- | Extract hypergraph (hyper)edges.
hyperEdges :: Hype n t -> [(Item n t, Trav n t)]
hyperEdges earSt =
    passiveEdges ++ activeEdges
  where
    passiveEdges =
        [ (ItemP p, trav)
        | (p, travSet) <- listPassive earSt
        , trav <- S.toList travSet ]
    activeEdges =
        [ (ItemA p, trav)
        | (p, travSet) <- listActive earSt
        , trav <- S.toList travSet ]


-- | Print the hypergraph edges.
printHype :: (Show n, Show t) => Hype n t -> IO ()
printHype earSt =
    forM_ edges $ \(p, trav) ->
        printTrav p trav
  where
    edges  = sortIt (hyperEdges earSt)
    sortIt = sortBy (comparing $ prio.fst)



--------------------
-- Active items
--------------------


-- | List all active done items together with the corresponding
-- traversals.
listActive :: Hype n t -> [(Active, S.Set (Trav n t))]
listActive = (M.elems >=> M.elems >=> M.toList) . doneActive


-- | Return the corresponding set of traversals for an active item.
activeTrav
    :: (Ord n, Ord t)
    => Active -> Hype n t
    -> Maybe (S.Set (Trav n t))
activeTrav p
    = (   M.lookup (p ^. spanA ^. end)
      >=> M.lookup (p ^. state)
      >=> M.lookup p )
    . doneActive


-- | Check if the active item is not already processed.
_isProcessedA :: (Ord n, Ord t) => Active -> Hype n t -> Bool
_isProcessedA p =
    check . activeTrav p
  where
    check (Just _) = True
    check _        = False


-- | Check if the active item is not already processed.
isProcessedA :: (Ord n, Ord t) => Active -> Earley n t Bool
isProcessedA p = _isProcessedA p <$> RWS.get


-- | Mark the active item as processed (`done').
saveActive
    :: (Ord t, Ord n)
    => Active
    -> S.Set (Trav n t)
    -> Earley n t ()
saveActive p ts =
    RWS.state $ \s -> ((), s {doneActive = newDone s})
  where
    newDone st =
        M.insertWith
            ( M.unionWith
                ( M.unionWith S.union ) )
            ( p ^. spanA ^. end )
            ( M.singleton (p ^. state)
                ( M.singleton p ts ) )
            ( doneActive st )


--------------------
-- Passive items
--------------------


-- | List all passive done items together with the corresponding
-- traversals.
listPassive :: Hype n t -> [(Passive n t, S.Set (Trav n t))]
listPassive = (M.elems >=> M.toList) . donePassive


-- | Return the corresponding set of traversals for a passive item.
passiveTrav
    :: (Ord n, Ord t)
    => Passive n t -> Hype n t
    -> Maybe (S.Set (Trav n t))
passiveTrav p
    = ( M.lookup
        ( p ^. spanP ^. beg
        , nonTerm $ p ^. label
        , p ^. spanP ^. end ) >=> M.lookup p )
    . donePassive


-- | Check if the state is not already processed.
_isProcessedP :: (Ord n, Ord t) => Passive n t -> Hype n t -> Bool
_isProcessedP x =
    check . passiveTrav x
  where
    check (Just _) = True
    check _        = False


-- | Check if the passive item is not already processed.
isProcessedP :: (Ord n, Ord t) => Passive n t -> Earley n t Bool
isProcessedP p = _isProcessedP p <$> RWS.get


-- | Mark the passive item as processed (`done').
savePassive
    :: (Ord t, Ord n)
    => Passive n t
    -> S.Set (Trav n t)
    -> Earley n t ()
savePassive p ts =
    RWS.state $ \s -> ((), s {donePassive = newDone s})
  where
    newDone st =
        M.insertWith
            ( M.unionWith S.union )
            ( p ^. spanP ^. beg
            , nonTerm $ p ^. label
            , p ^. spanP ^. end )
            ( M.singleton p ts )
            ( donePassive st )


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


-- | Add to the waiting queue all items induced from the given item.
pushInduced :: (Ord t, Ord n) => Active -> Trav n t -> Earley n t ()
pushInduced p t = do
    hasElems (getL state p) >>= \b -> when b
        (pushActive p t)
    P.runListT $ do
        x <- heads (getL state p)
        lift . flip pushPassive t $
            Passive x (getL spanA p)


-- | Remove a state from the queue.
popItem
    :: (Ord t, Ord n)
    => Earley n t
        (Maybe (Binding (Item n t) (ExtPrio n t)))
popItem = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (b, s) -> (Just b, st {waiting = s})


---------------------------------
-- Extraction of Processed Items
---------------------------------


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
    :: (HOrd n, HOrd t) => DID -> Pos
    -> P.ListT (Earley n t) Active
expectEnd did i = do
    Hype{..} <- lift RWS.get
    -- determine items which end on the given position
    doneEnd <- some $ M.lookup i doneActive
    -- determine automaton states from which the given label
    -- leaves as a body transition
    stateSet <- some $ M.lookup (withBody automat) did
    -- pick one of the states
    stateID <- each . S.toList $
         stateSet `S.intersection` M.keysSet doneEnd
    -- determine items which refer to the chosen states
    doneEndLab <- some $ M.lookup stateID doneEnd
    -- return them all!
    each $ M.keys doneEndLab


-- | Check if a passive item exists with:
-- * the given root non-terminal value (but not top-level
--   auxiliary)
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t)
rootSpan x (i, j) = do
    Hype{..} <- lift RWS.get
    -- listValues (i, x, j) donePassive
    each $ case M.lookup (i, x, j) donePassive of
        Nothing -> []
        Just m -> M.keys m


-- -- | List all processed passive items.
-- listDone :: Done n t -> [Item n t]
-- listDone done = ($ done) $
--     M.elems >=> M.elems >=>
--     M.elems >=> S.toList


--------------------------------------------------
-- New Automaton-Based Primitives
--------------------------------------------------


-- | Follow the given terminal in the underlying automaton.
followTerm :: (Ord n, Ord t) => ID -> t -> P.ListT (Earley n t) ID
followTerm i c = do
    -- get the underlying automaton
    auto <- RWS.gets $ automat
    -- get the dag ID corresponding to the given terminal
    did  <- some $ M.lookup c (termDID auto)
    -- follow the label
    some $ A.follow (gramAuto auto) i (A.Body $ Term did)


-- | Follow the given body transition in the underlying automaton.
-- It represents the transition function of the automaton.
--
-- TODO: merge with `followTerm`.
follow :: (Ord n, Ord t) => ID -> DID -> P.ListT (Earley n t) ID
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


-- | Check if any element leaves the given state.
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
    j <- followTerm (getL state p) c
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


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the passive item `p` to complement
-- (=> substitution) other rules.
trySubst :: (SOrd t, SOrd n) => Passive n t -> Earley n t ()
trySubst p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pDID = getL dagID p
        pSpan = getL spanP p
    -- make sure that `p' represents regular rules
    guard . regular $ pSpan
    -- find active items which end where `p' begins and which
    -- expect the DAG node provided by `p'
    q <- expectEnd pDID (getL beg pSpan)
    -- follow the DAG node
    j <- follow (getL state q) pDID
    -- construct the resultant state
    let q' = setL state j
           . setL (end . spanA) (getL end pSpan)
           $ q
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Subst p q
#ifdef DebugOn
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[U]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- FOOT ADJOIN
--------------------------------------------------


-- TODO: I have finished here!


-- | `tryAdjoinInit p q':
-- * `p' is a completed state (regular or auxiliary)
-- * `q' not completed and expects a *real* foot
tryAdjoinInit :: (SOrd n, SOrd t) => Passive n t -> Earley n t ()
tryAdjoinInit p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- make sure that the corresponding rule is either regular or
    -- intermediate auxiliary ((<=) used as implication here)
    guard $ auxiliary pSpan <= not (topLevel pLab)
    -- find all active items which expect a foot with the given
    -- symbol and which end where `p` begins
    let foot = AuxFoot $ nonTerm pLab
    q <- expectEnd foot (getL beg pSpan)
    -- follow the foot
    j <- follow (getL state q) foot
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
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[A]  " >> printPassive p
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
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- make sure the label is not top-level (internal spine
    -- non-terminal)
    guard . not $ topLevel pLab
    -- make sure that `p' is an auxiliary item
    guard . auxiliary $ pSpan
    -- find all rules which expect a spine non-terminal provided
    -- by `p' and which end where `p' begins
    q <- expectEnd pLab (pSpan ^. beg)
    -- follow the spine non-terminal
    j <- follow (q ^. state) pLab
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
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[B]  " >> printPassive p
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
    let qLab = q ^. label
        qSpan = q ^. spanP
    -- make sure the label is top-level
    guard $ topLevel qLab
    -- make sure that it is an auxiliary item (by definition only
    -- auxiliary states have gaps)
    (gapBeg, gapEnd) <- each $ maybeToList $ qSpan ^. gap
    -- take all passive items with a given span and a given
    -- root non-terminal (IDs irrelevant)
    p <- rootSpan (nonTerm qLab) (gapBeg, gapEnd)
    let p' = setL (spanP >>> beg) (qSpan ^. beg)
           . setL (spanP >>> end) (qSpan ^. end)
           $ p
    lift $ pushPassive p' $ Adjoin q p
#ifdef DebugOn
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[C]  " >> printPassive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printPassive p'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- Earley step
--------------------------------------------------


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step
    :: (SOrd t, SOrd n)
    => Binding (Item n t) (ExtPrio n t)
    -> Earley n t ()
step (ItemP p :-> e) = do
    mapM_ ($ p)
      [ trySubst
      , tryAdjoinInit
      , tryAdjoinCont
      , tryAdjoinTerm ]
    savePassive p $ prioTrav e
step (ItemA p :-> e) = do
    mapM_ ($ p)
      [ tryScan ]
    saveActive p $ prioTrav e


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
    -> [T.Tree n t]
parsedTrees earSt start n

    = concatMap fromPassive
    $ finalFrom start n earSt

  where

    fromPassive :: Passive n t -> [T.Tree n t]
    fromPassive p = concat
        [ fromPassiveTrav p trav
        | travSet <- maybeToList $ passiveTrav p earSt
        , trav <- S.toList travSet ]

    fromPassiveTrav p (Scan q t) =
        [ T.Branch
            (nonTerm $ getL label p)
            (reverse $ T.Leaf t : ts)
        | ts <- fromActive q ]

--     fromPassiveTrav p (Foot q x) =
--         [ T.Branch
--             (nonTerm $ getL label p)
--             (reverse $ T.Branch x [] : ts)
--         | ts <- fromActive q ]

    fromPassiveTrav p (Foot q _p') =
        [ T.Branch
            (nonTerm $ getL label p)
            (reverse $ T.Branch (nonTerm $ p ^. label) [] : ts)
        | ts <- fromActive q ]

    fromPassiveTrav p (Subst qp qa) =
        [ T.Branch
            (nonTerm $ getL label p)
            (reverse $ t : ts)
        | ts <- fromActive qa
        , t  <- fromPassive qp ]

    fromPassiveTrav _p (Adjoin qa qm) =
        [ replaceFoot ini aux
        | aux <- fromPassive qa
        , ini <- fromPassive qm ]

    -- | Replace foot (the only non-terminal leaf) by the given
    -- initial tree.
    replaceFoot ini (T.Branch _ []) = ini
    replaceFoot ini (T.Branch x ts) = T.Branch x $ map (replaceFoot ini) ts
    replaceFoot _ t@(T.Leaf _)    = t


    fromActive  :: Active -> [[T.Tree n t]]
    fromActive p = case activeTrav p earSt of
        Nothing -> error "fromActive: unknown active item"
        Just travSet -> if S.null travSet
            then [[]]
            else concatMap
                (fromActiveTrav p)
                (S.toList travSet)

    fromActiveTrav _p (Scan q t) =
        [ T.Leaf t : ts
        | ts <- fromActive q ]

    fromActiveTrav _p (Foot q p) =
        [ T.Branch (nonTerm $ p ^. label) [] : ts
        | ts <- fromActive q ]

--     fromActiveTrav _p (Foot q x) =
--         [ T.Branch x [] : ts
--         | ts <- fromActive q ]

    fromActiveTrav _p (Subst qp qa) =
        [ t : ts
        | ts <- fromActive qa
        , t  <- fromPassive qp ]

    fromActiveTrav _p (Adjoin _ _) =
        error "parsedTrees: fromActiveTrav called on a passive item"


-- --------------------------------------------------
-- -- EARLEY
-- --------------------------------------------------
-- 
-- 
-- -- | Does the given grammar generate the given sentence?
-- -- Uses the `earley` algorithm under the hood.
-- recognize
-- #ifdef DebugOn
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => FactGram n t         -- ^ The grammar (set of rules)
--     -> Input t            -- ^ Input sentence
--     -> IO Bool
-- recognize gram input = do
--     auto <- mkAuto (D.fromGram gram)
--     recognizeAuto auto input


-- | Does the given grammar generate the given sentence from the
-- given non-terminal symbol (i.e. from an initial tree with this
-- symbol in its root)?  Uses the `earley` algorithm under the
-- hood.
recognizeFrom
#ifdef DebugOn
    :: (SOrd t, SOrd n)
#else
    :: (Hashable t, Ord t, Hashable n, Ord n)
#endif
    => DAG.Gram n t         -- ^ The grammar
    -> n                    -- ^ The start symbol
    -> Input t              -- ^ Input sentence
    -> IO Bool
recognizeFrom DAG.Gram{..} start input = do
    auto <- mkAuto dagGram (D.fromGram factGram)
    recognizeFromAuto auto start input


-- -- | Parse the given sentence and return the set of parsed trees.
-- parse
-- #ifdef DebugOn
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => FactGram n t         -- ^ The grammar (set of rules)
--     -> n                    -- ^ The start symbol
--     -> Input t              -- ^ Input sentence
--     -> IO [T.Tree n t]
-- parse gram start input = do
--     auto <- mkAuto (D.fromGram gram)
--     parseAuto auto start input


-- -- | Perform the earley-style computation given the grammar and
-- -- the input sentence.
-- earley
-- #ifdef DebugOn
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => FactGram n t         -- ^ The grammar (set of rules)
--     -> Input t              -- ^ Input sentence
--     -> IO (Hype n t)
-- earley gram input = do
--     auto <- mkAuto (D.fromGram gram)
--     earleyAuto auto input


--------------------------------------------------
-- Local automaton type
--------------------------------------------------


-- | Local automaton type based on `A.GramAuto`.
data Auto n t = Auto
    { gramDAG   :: DAG (O.Node n t) ()
    -- ^ The underlying grammar DAG
    , gramAuto  :: A.GramAuto
    -- ^ The underlying automaton
    , withBody  :: M.Map DID (S.Set ID)
    -- , withBody :: H.CuckooHashTable (Lab n t) (S.Set ID)
    -- ^ A data structure which, for each label, determines the
    -- set of automaton states from which this label goes out
    -- as a body transition.
    , termDID   :: M.Map t DID
    -- ^ A map which assigns Dag IDs to the corresponding terminals. 
    -- Note that each grammar terminal is represented by exactly
    -- one grammar DAG node.
    }


-- | Construct `Auto` based on the underlying `A.GramAuto`.
mkAuto
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: DAG (O.Node n t) ()
    -> A.GramAuto
    -> Auto n t
    -- -> IO Auto
mkAuto dag auto = Auto
    { gramDAG  = dag
    , gramAuto = auto
    , withBody = mkWithBody auto
    , termDID  = undefined }


-- | Create the `withBody` component based on the automaton.
mkWithBody
    :: (Ord n, Ord t)
    => A.GramAuto n t
    -> M.Map (Lab n t) (S.Set ID)
mkWithBody dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | (i, A.Body x, _j) <- A.allEdges dag ]


--------------------------------------------------
-- Parsing with automaton
--------------------------------------------------


-- -- | See `recognize`.
-- recognizeAuto
-- #ifdef DebugOn
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => Auto n t           -- ^ Grammar automaton
--     -> Input t            -- ^ Input sentence
--     -> IO Bool
-- recognizeAuto auto xs =
--     isRecognized xs <$> earleyAuto auto xs


-- | See `recognizeFrom`.
recognizeFromAuto
#ifdef DebugOn
    :: (SOrd t, SOrd n)
#else
    :: (Hashable t, Ord t, Hashable n, Ord n)
#endif
    => Auto n t       -- ^ Grammar automaton
    -> n                    -- ^ The start symbol
    -> Input t            -- ^ Input sentence
    -> IO Bool
recognizeFromAuto auto start input = do
    hype <- earleyAuto auto input
    let n = V.length (inputSent input)
    return $ (not.null) (finalFrom start n hype)


-- -- | See `parse`.
-- parseAuto
-- #ifdef DebugOn
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => Auto n t           -- ^ Grammar automaton
--     -> n                  -- ^ The start symbol
--     -> Input t            -- ^ Input sentence
--     -> IO [T.Tree n t]
-- parseAuto auto start input = do
--     earSt <- earleyAuto auto input
--     let n = V.length (inputSent input)
--     return $ parsedTrees earSt start n


-- | See `earley`.
earleyAuto
#ifdef DebugOn
    :: (SOrd t, SOrd n)
#else
    :: (Hashable t, Ord t, Hashable n, Ord n)
#endif
    => Auto n t         -- ^ Grammar automaton
    -> Input t          -- ^ Input sentence
    -> IO (Hype n t)
earleyAuto auto input = do
    fst <$> RWS.execRWST loop input st0
  where
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


-- | Return the list of final passive chart items.
finalFrom
    :: (Ord n, Eq t)
    => n            -- ^ The start symbol
    -> Int          -- ^ The length of the input sentence
    -> Hype n t    -- ^ Result of the earley computation
    -> [Passive n t]
finalFrom start n Hype{..} =
    case M.lookup (0, start, n) donePassive of
        Nothing -> []
        Just m ->
            [ p
            | p <- M.keys m
            , p ^. label == NonT start Nothing ]


-- -- | Return the list of final passive chart items.
-- final
--     :: (Ord n, Eq t)
--     -> Int          -- ^ The length of the input sentence
--     -> Hype n t    -- ^ Result of the earley computation
--     -> [Passive n t]
-- final start n Hype{..} =
--     case M.lookup (0, start, n) donePassive of
--         Nothing -> []
--         Just m ->
--             [ p
--             | p <- M.keys m
--             , p ^. label == NonT start Nothing ]


-- | Check whether the given sentence is recognized
-- based on the resulting state of the earley parser.
isRecognized
    :: (SOrd t, SOrd n)
    => Input t           -- ^ Input sentence
    -> Hype n t          -- ^ Earley parsing result
    -> Bool
isRecognized input Hype{..} =
    (not . null)
    (complete
        (agregate donePassive))
  where
    n = V.length (inputSent input)
    complete done =
        [ True | item <- S.toList done
        , item ^. spanP ^. beg == 0
        , item ^. spanP ^. end == n
        , isNothing (item ^. spanP ^. gap)
        -- admit only *fully* recognized trees
        , isRoot (item ^. label) ]
    agregate = S.unions . map M.keysSet . M.elems
    isRoot (NonT _ Nothing) = True
    isRoot _ = False


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


-- | Is the rule with the given head top-level?
topLevel :: Lab n t -> Bool
topLevel x = case x of
    NonT{..}  -> isNothing labID
    AuxRoot{} -> True
    _         -> False


-- -- | Pipe all values from the set corresponding to the given key.
-- listValues
--     :: (Monad m, Ord a)
--     => a -> M.Map a (S.Set b)
--     -> P.ListT m b
-- listValues x m = each $ case M.lookup x m of
--     Nothing -> []
--     Just s -> S.toList s
