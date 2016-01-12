{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}


-- | Earley-style parsing based on a DFSA with an additional
-- distinction on active and passive configurations/items/edges
-- (the third term is used in "Parsing and Hyphergraphs" by Klein
-- and Manning, as well as the idea of probabilistic chart
-- parsing).


module NLP.TAG.Vanilla.Earley.AutoAP where


import           Prelude hiding             (span, (.))
import           Control.Applicative        ((<$>))
import           Control.Monad      (guard, void, (>=>), when, forM_)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
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

import qualified Pipes                      as P
-- import qualified Pipes.Prelude              as P

import           Data.DAWG.Ord (ID)
-- import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.TAG.Vanilla.Core
import           NLP.TAG.Vanilla.Rule
                                ( Lab(..), Rule(..), viewLab )
import qualified NLP.TAG.Vanilla.Auto.Edge  as A
import qualified NLP.TAG.Vanilla.Auto.Mini  as A
import qualified NLP.TAG.Vanilla.Auto.DAWG  as D
import qualified NLP.TAG.Vanilla.Tree       as T


--------------------------------------------------
-- BASE TYPES
--------------------------------------------------


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
data Active n t = Active {
      _state :: ID
    , _spanA :: Span
    } deriving (Show, Eq, Ord)
$( makeLenses [''Active] )


-- | Passive chart item : label + span.
data Passive n t = Passive {
      _label :: Lab n t
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
printActive :: (View n, View t) => Active n t -> IO ()
printActive p = do
    putStr "("
    putStr . show $ getL state p
    putStr ", "
    printSpan $ getL spanA p
    putStrLn ")"


-- | Print a passive item.
printPassive :: (View n, View t) => Passive n t -> IO ()
printPassive p = do
    putStr "("
    putStr . viewLab $ getL label p
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
        { scanFrom :: Active n t
        -- ^ The input active state
        , scanTerm :: t
        -- ^ The scanned terminal
        }
    | Subst
    -- ^ Pseudo substitution
        { passArg  :: Passive n t
        -- ^ The passive argument of the action
        , actArg   :: Active n t
        -- ^ The active argument of the action
        }
    | Foot
    -- ^ Foot adjoin
        { actArg   :: Active n t
        -- ^ The passive argument of the action
        -- , theFoot  :: n
        , theFoot  :: Passive n t
        -- ^ The foot non-terminal
        }
    | Adjoin
    -- ^ Adjoin terminate with two passive arguments
        { passAdj  :: Passive n t
        -- ^ The adjoined item
        , passMod  :: Passive n t
        -- ^ The modified item
        }
    deriving (Show, Eq, Ord)


-- | Print a traversal.
printTrav :: (View n, View t) => Item n t -> Trav n t -> IO ()
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
prioA :: Active n t -> Prio
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
    | ItemA (Active n t)
    deriving (Show, Eq, Ord)


-- | Print an active item.
printItem :: (View n, View t) => Item n t -> IO ()
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


-- | Local automaton type.
type Auto n t = A.Auto (A.Edge (Lab n t))


-- | The reader of the earley monad: vector of sets of terminals.
type EarRd t = V.Vector (S.Set t)


-- | The state of the earley monad.
data EarSt n t = EarSt
    { automat :: Auto n t
    -- ^ The underlying automaton (abstract implementation)

    , withBody :: M.Map (Lab n t) (S.Set ID)
    -- ^ A data structure which, for each label, determines the
    -- set of automaton states from which this label goes out
    -- as a body transition.

    -- , doneActive  :: M.Map (ID, Pos) (S.Set (Active n t))
    , doneActive  :: M.Map Pos (M.Map ID
        (M.Map (Active n t) (S.Set (Trav n t))))
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


-- | Make an initial `EarSt` from a set of states.
mkEarSt
    :: (Ord n, Ord t)
    => Auto n t
    -> S.Set (Active n t)
    -> EarSt n t
mkEarSt dag s = EarSt
    { automat = dag
    , withBody = mkWithBody dag
    , doneActive  = M.empty
    , donePassive = M.empty
    , waiting = Q.fromList
        [ ItemA p :-> extPrio (prioA p)
        | p <- S.toList s ] }


-- | Create the `withBody` component based on the automaton.
mkWithBody
    :: (Ord n, Ord t)
    => Auto n t
    -> M.Map (Lab n t) (S.Set ID)
mkWithBody dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | (i, A.Body x, _j) <- A.allEdges dag ]


-- | Earley parser monad.  Contains the input sentence (reader)
-- and the state of the computation `EarSt'.
type Earley n t = RWS.RWST (EarRd t) () (EarSt n t) IO


-- | Read word from the given position of the input.
readInput :: Pos -> P.ListT (Earley n t) t
readInput i = do
    -- ask for the input
    sent <- RWS.ask
    -- just a safe way to retrieve the i-th element
    -- each $ take 1 $ drop i xs
    xs <- some $ sent V.!? i
    each $ S.toList xs


--------------------------------------------------
-- Hypergraph stats
--------------------------------------------------


-- | Number of nodes in the parsing hypergraph.
hyperNodesNum :: EarSt n t -> Int
hyperNodesNum e
    = length (listPassive e)
    + length (listActive e)


-- | Number of edges in the parsing hypergraph.
hyperEdgesNum :: forall n t. EarSt n t -> Int
hyperEdgesNum earSt
    = sumOver listPassive
    + sumOver listActive
  where
    sumOver :: (EarSt n t -> [(a, S.Set (Trav n t))]) -> Int
    sumOver listIt = sum
        [ S.size travSet
        | (_, travSet) <- listIt earSt ]


-- | Extract hypergraph (hyper)edges.
hyperEdges :: EarSt n t -> [(Item n t, Trav n t)]
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
printHype :: (View n, View t) => EarSt n t -> IO ()
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
listActive :: EarSt n t -> [(Active n t, S.Set (Trav n t))]
listActive = (M.elems >=> M.elems >=> M.toList) . doneActive


-- | Return the corresponding set of traversals for an active item.
activeTrav
    :: (Ord n, Ord t)
    => Active n t -> EarSt n t
    -> Maybe (S.Set (Trav n t))
activeTrav p
    = (   M.lookup (p ^. spanA ^. end)
      >=> M.lookup (p ^. state)
      >=> M.lookup p )
    . doneActive


-- | Check if the active item is not already processed.
_isProcessedA :: (Ord n, Ord t) => Active n t -> EarSt n t -> Bool
_isProcessedA p =
    check . activeTrav p
  where
    check (Just _) = True
    check _        = False


-- | Check if the active item is not already processed.
isProcessedA :: (Ord n, Ord t) => Active n t -> Earley n t Bool
isProcessedA p = _isProcessedA p <$> RWS.get


-- | Mark the active item as processed (`done').
saveActive
    :: (Ord t, Ord n)
    => Active n t
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
listPassive :: EarSt n t -> [(Passive n t, S.Set (Trav n t))]
listPassive = (M.elems >=> M.toList) . donePassive


-- | Return the corresponding set of traversals for a passive item.
passiveTrav
    :: (Ord n, Ord t)
    => Passive n t -> EarSt n t
    -> Maybe (S.Set (Trav n t))
passiveTrav p
    = ( M.lookup
        ( p ^. spanP ^. beg
        , nonTerm $ p ^. label
        , p ^. spanP ^. end ) >=> M.lookup p )
    . donePassive


-- | Check if the state is not already processed.
_isProcessedP :: (Ord n, Ord t) => Passive n t -> EarSt n t -> Bool
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
pushActive :: (Ord t, Ord n) => Active n t -> Trav n t -> Earley n t ()
pushActive p t = isProcessedA p >>= \b -> if b
    then saveActive p $ S.singleton t
    else RWS.modify' $ \s -> s {waiting = newWait (waiting s)}
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
    else RWS.modify' $ \s -> s {waiting = newWait (waiting s)}
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
pushInduced :: (Ord t, Ord n) => Active n t -> Trav n t -> Earley n t ()
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


-- | Return all active processed items which:
-- * expect a given label,
-- * end on the given position.
expectEnd
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Active n t)
expectEnd sym i = do
    EarSt{..} <- lift RWS.get
    -- determine items which end on the given position
    doneEnd <- some $ M.lookup i doneActive
    -- determine automaton states from which the given label
    -- leaves as a body transition
    stateSet <- some $ M.lookup sym withBody
    -- pick one of the states
    stateID <- each $ S.toList stateSet
    --
    -- ALTERNATIVE: state <- each . S.toList $
    --      stateSet `S.intersection` M.keySet doneEnd
    --
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
    EarSt{..} <- lift RWS.get
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
    auto <- RWS.gets automat
    -- follow the label
    some $ A.follow auto i (A.Body $ Term c)


-- | Follow the given body transition in the underlying automaton.
-- It represents the transition function of the automaton.
--
-- TODO: merge with `followTerm`.
follow :: (Ord n, Ord t) => ID -> Lab n t -> P.ListT (Earley n t) ID
follow i x = do
    -- get the underlying automaton
    auto <- RWS.gets automat
    -- follow the label
    some $ A.follow auto i (A.Body x)


-- | Rule heads outgoing from the given automaton state.
heads :: ID -> P.ListT (Earley n t) (Lab n t)
heads i = do
    auto <- RWS.gets automat
    let mayHead (x, _) = case x of
            A.Body _  -> Nothing
            A.Head y -> Just y
    each $ mapMaybe mayHead $ A.edges auto i


-- | Rule body elements outgoing from the given automaton state.
elems :: ID -> P.ListT (Earley n t) (Lab n t)
elems i = do
    auto <- RWS.gets automat
    let mayBody (x, _) = case x of
            A.Body y  -> Just y
            A.Head _ -> Nothing
    each $ mapMaybe mayBody $ A.edges auto i


-- | Check if any element leaves the given state.
hasElems :: ID -> Earley n t Bool
hasElems i = do
    auto <- RWS.gets automat
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
tryScan :: (VOrd t, VOrd n) => Active n t -> Earley n t ()
tryScan p = void $ P.runListT $ do
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
#ifdef Debug
    -- print logging information
    lift . lift $ do
        putStr "[S]  " >> printActive p
        putStr "  :  " >> printActive q
#endif
    -- push the resulting state into the waiting queue
    lift $ pushInduced q $ Scan p c


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the passive item `p` to complement
-- (=> substitution) other rules.
trySubst :: (VOrd t, VOrd n) => Passive n t -> Earley n t ()
trySubst p = void $ P.runListT $ do
    let pLab = getL label p
        pSpan = getL spanP p
    -- make sure that `p' represents regular rules
    guard . regular $ pSpan
    -- find active items which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    q <- expectEnd pLab (getL beg pSpan)
    -- follow the transition symbol
    j <- follow (getL state q) pLab
    -- construct the resultant state
    -- let q' = q {state = j, spanA = spanA p {end = end p}}
    let q' = setL state j
           . setL (end.spanA) (getL end pSpan)
           $ q
#ifdef Debug
    -- print logging information
    lift . lift $ do
        putStr "[U]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
#endif
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Subst p q


--------------------------------------------------
-- FOOT ADJOIN
--------------------------------------------------


-- | `tryAdjoinInit p q':
-- * `p' is a completed state (regular or auxiliary)
-- * `q' not completed and expects a *real* foot
tryAdjoinInit :: (VOrd n, VOrd t) => Passive n t -> Earley n t ()
tryAdjoinInit p = void $ P.runListT $ do
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
#ifdef Debug
    -- print logging information
    lift . lift $ do
        putStr "[A]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
#endif
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Foot q p -- $ nonTerm foot


--------------------------------------------------
-- INTERNAL ADJOIN
--------------------------------------------------


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
tryAdjoinCont :: (VOrd n, VOrd t) => Passive n t -> Earley n t ()
tryAdjoinCont p = void $ P.runListT $ do
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
#ifdef Debug
    -- logging info
    lift . lift $ do
        putStr "[B]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
#endif
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Subst p q


--------------------------------------------------
-- ROOT ADJOIN
--------------------------------------------------


-- | Adjoin a fully-parsed auxiliary state `p` to a partially parsed
-- tree represented by a fully parsed rule/state `q`.
tryAdjoinTerm :: (VOrd t, VOrd n) => Passive n t -> Earley n t ()
tryAdjoinTerm q = void $ P.runListT $ do
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
#ifdef Debug
    lift . lift $ do
        putStr "[C]  " >> printPassive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printPassive p'
#endif
    lift $ pushPassive p' $ Adjoin q p


--------------------------------------------------
-- Earley step
--------------------------------------------------


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step
    :: (VOrd t, VOrd n)
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
-- sentence.  Should be run on the result of the earley algorithm.
parsedTrees
    :: forall n t. (Ord n, Ord t, Show n, Show t)
    => EarSt n t    -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> S.Set (T.Tree n t)
parsedTrees earSt start n

    = S.fromList
    $ concatMap fromPassive
    $ finalFrom start n earSt

  where

    fromPassive :: Passive n t -> [T.Tree n t]
    fromPassive p = concat
        [ fromPassiveTrav p trav
        | travSet <- maybeToList $ passiveTrav p earSt
        , trav <- S.toList travSet ]

    fromPassiveTrav p (Scan q t) =
        [ T.INode
            (nonTerm $ getL label p)
            (reverse $ T.FNode t : ts)
        | ts <- fromActive q ]

--     fromPassiveTrav p (Foot q x) =
--         [ T.INode
--             (nonTerm $ getL label p)
--             (reverse $ T.INode x [] : ts)
--         | ts <- fromActive q ]

    fromPassiveTrav p (Foot q p') =
        [ T.INode
            (nonTerm $ getL label p)
            (reverse $ T.INode (nonTerm $ p ^. label) [] : ts)
        | ts <- fromActive q ]

    fromPassiveTrav p (Subst qp qa) =
        [ T.INode
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
    replaceFoot ini (T.INode _ []) = ini
    replaceFoot ini (T.INode x ts) = T.INode x $ map (replaceFoot ini) ts
    replaceFoot _ t@(T.FNode _)    = t


    fromActive  :: Active n t -> [[T.Tree n t]]
    fromActive p = case activeTrav p earSt of
        Nothing -> error "fromActive: unknown active item"
        Just travSet -> if S.null travSet
            then [[]]
            else concatMap
                (fromActiveTrav p)
                (S.toList travSet)

    fromActiveTrav _p (Scan q t) =
        [ T.FNode t : ts
        | ts <- fromActive q ]

    fromActiveTrav _p (Foot q p) =
        [ T.INode (nonTerm $ p ^. label) [] : ts
        | ts <- fromActive q ]

--     fromActiveTrav _p (Foot q x) =
--         [ T.INode x [] : ts
--         | ts <- fromActive q ]

    fromActiveTrav _p (Subst qp qa) =
        [ t : ts
        | ts <- fromActive qa
        , t  <- fromPassive qp ]

    fromActiveTrav _p (Adjoin _ _) =
        error "parsedTrees: fromActiveTrav called on a passive item"


--------------------------------------------------
-- EARLEY
--------------------------------------------------


-- | Does the given grammar generate the given sentence?
-- Uses the `earley` algorithm under the hood.
recognize
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [S.Set t]            -- ^ Input sentence
    -> IO Bool
recognize gram =
    recognizeAuto (D.shell $ D.buildAuto gram)


-- | Does the given grammar generate the given sentence from the
-- given non-terminal symbol (i.e. from an initial tree with this
-- symbol in its root)?  Uses the `earley` algorithm under the
-- hood.
recognizeFrom
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> n                    -- ^ The start symbol
    -> [S.Set t]            -- ^ Input sentence
    -> IO Bool
recognizeFrom gram =
    recognizeFromAuto (D.shell $ D.buildAuto gram)


-- | Parse the given sentence and return the set of parsed trees.
parse
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> n                    -- ^ The start symbol
    -> [S.Set t]            -- ^ Input sentence
    -> IO (S.Set (T.Tree n t))
parse gram = parseAuto $ D.shell $ D.buildAuto gram


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [S.Set t]            -- ^ Input sentence
    -> IO (EarSt n t)
earley gram = earleyAuto $ D.shell $ D.buildAuto gram


--------------------------------------------------
-- Parsing with automaton
--------------------------------------------------


-- | Alternative to `recognize`.
recognizeAuto
    :: (VOrd t, VOrd n)
    => Auto n t           -- ^ Grammar automaton
    -> [S.Set t]            -- ^ Input sentence
    -> IO Bool
recognizeAuto auto xs =
    isRecognized xs <$> earleyAuto auto xs


-- | Alternative to `recognizeFrom`.
recognizeFromAuto
    :: (VOrd t, VOrd n)
    => Auto n t           -- ^ Grammar automaton
    -> n                    -- ^ The start symbol
    -> [S.Set t]            -- ^ Input sentence
    -> IO Bool
recognizeFromAuto auto start xs = do
    earSt <- earleyAuto auto xs
    return $ (not.null) (finalFrom start (length xs) earSt)


-- | Parse the given sentence and return the set of parsed trees.
parseAuto
    :: (VOrd t, VOrd n)
    => Auto n t           -- ^ Grammar automaton
    -> n                    -- ^ The start symbol
    -> [S.Set t]            -- ^ Input sentence
    -> IO (S.Set (T.Tree n t))
parseAuto auto start xs = do
    earSt <- earleyAuto auto xs
    return $ parsedTrees earSt start (length xs)


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earleyAuto
    :: (VOrd t, VOrd n)
    => Auto n t           -- ^ Grammar automaton
    -> [S.Set t]            -- ^ Input sentence
    -> IO (EarSt n t)
earleyAuto dawg xs =
    fst <$> RWS.execRWST loop (V.fromList xs) st0
  where
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt dawg $ S.fromList
        [ Active root Span
            { _beg   = i
            , _end   = i
            , _gap   = Nothing }
        | i <- [0 .. length xs - 1]
        , root <- S.toList (A.roots dawg) ]
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
    -> EarSt n t    -- ^ Result of the earley computation
    -> [Passive n t]
finalFrom start n EarSt{..} =
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
--     -> EarSt n t    -- ^ Result of the earley computation
--     -> [Passive n t]
-- final start n EarSt{..} =
--     case M.lookup (0, start, n) donePassive of
--         Nothing -> []
--         Just m ->
--             [ p
--             | p <- M.keys m
--             , p ^. label == NonT start Nothing ]


-- | Check whether the given sentence is recognized
-- based on the resulting state of the earley parser.
--
-- TODO: The function returns `True` also when a subtree
-- of an elementary tree is recognized, it seems.
isRecognized
    :: (VOrd t, VOrd n)
    => [S.Set t]            -- ^ Input sentence
    -> EarSt n t            -- ^ Earley parsing result
    -> Bool
isRecognized xs EarSt{..} =
    (not . null)
    (complete
        (agregate donePassive))
  where
    n = length xs
    complete done =
        [ True | item <- S.toList done
        , item ^. spanP ^. beg == 0
        , item ^. spanP ^. end == n
        , isNothing (item ^. spanP ^. gap) ]
    agregate = S.unions . map M.keysSet . M.elems


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | MaybeT transformer.
maybeT :: Monad m => Maybe a -> MaybeT m a
maybeT = MaybeT . return


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
