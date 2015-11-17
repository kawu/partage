{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}


-- | Earley-style parsing based on a DFSA with an additional
-- distinction on active and passive configurations/items/edges
-- (the third term is used in "Parsing and Hyphergraphs" by Klein
-- and Manning, as well as the idea of probabilistic chart
-- parsing).


module NLP.TAG.Vanilla.Earley.AutoAP where


import           Prelude hiding             (span, (.))
import           Control.Applicative        ((<$>), (<*>))
import           Control.Monad              (guard, void, (>=>), when)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS
import           Control.Category ((>>>), (.))

import           Data.Maybe     ( isJust, isNothing, mapMaybe
                                , maybeToList )
import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import           Data.Lens.Light

import qualified Pipes                      as P
-- import qualified Pipes.Prelude              as P

import           Data.DAWG.Gen.Types (ID)
import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.TAG.Vanilla.Core
import           NLP.TAG.Vanilla.Rule
                                ( Lab(..), Rule(..), viewLab )
import qualified NLP.TAG.Vanilla.Automaton  as A


--------------------------------------------------
-- BASE TYPES
--------------------------------------------------


-- | Priority.
type Prio = Int


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


-- testSpan :: Span -> Span
-- testSpan = setL gap $ Nothing
--
--
-- testActive :: Pos -> Active n t -> Active n t
-- testActive end0 = setL (spanA >>> end) end0


-- -- | Active chart item.
-- data Active n t = Active {
--     -- | State of the underlying automaton.
--       state :: ID
--     -- | The starting position.
--     , beg   :: Pos
--     -- | The ending position (or rather the position of the dot).
--     , end   :: Pos
--     -- | Coordinates of the gap (if applies)
--     , gap   :: Maybe (Pos, Pos)
--     } deriving (Show, Eq, Ord)


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


-- | Priority of an active item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioA :: Active n t -> Prio
prioA = getL $ end.spanA


-- | Priority of a passive item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioP :: Passive n t -> Prio
prioP = getL $ end.spanP


--------------------------------------------------
-- Item Type
--------------------------------------------------


-- | Passive or active item.
data Item n t
    = ItemP (Passive n t)
    | ItemA (Active n t)
    deriving (Show, Eq, Ord)


-- -- | Priority of an item.
-- prio :: Item n t -> Prio
-- prio (ItemP x) = prioP x
-- prio (ItemA x) = prioA x


-- --------------------------------------------------
-- -- Set of Passive Processed Items
-- --------------------------------------------------
--
--
-- -- | The set of passive processed items.
-- type DonePassive n =
--
--
-- --------------------------------------------------
-- -- Set of Active Done Items
-- --------------------------------------------------
--
--
-- -- | The set of active processed items.
-- type DoneActive n t =
--
--
-- --------------------------------------------------
-- -- Set of Processed Items (BACKUP)
-- --------------------------------------------------
--
--
-- -- | The set of passive (processed) items is stored as a map
-- -- * from `end` position to a map
-- --  * from `state` ID to a map
-- --   * from `beg` position to a set
-- --    * of the corresponding items
-- type Done n t =
--     M.Map Pos
--         ( M.Map ID
--             ( M.Map Pos
--                 ( S.Set (Item n t) )
--             )
--         )


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt {
    -- | The underlying automaton.
      automat :: A.DAWG n t

    -- | A data structure which, for each label, determines the
    -- set of automaton states from which this label goes out
    -- as a body transition.
    , withBody :: M.Map (Lab n t) (S.Set ID)

    -- | A data structure which, for each source non-terminal,
    -- determines the set of automaton states from which this
    -- non-terminal goes out as a head transition.
    , withHead :: M.Map n (S.Set ID)

    -- | Processed active items partitioned w.r.t ending
    -- positions and state IDs.
    -- , doneActive  :: M.Map (ID, Pos) (S.Set (Active n t))
    , doneActive  :: M.Map Pos (M.Map ID (S.Set (Active n t)))

    -- | Processed passive items.
    , donePassive :: M.Map (Pos, n, Pos) (S.Set (Passive n t))
    -- , donePassive :: S.Set (Passive n t)

    -- | The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    --
    -- NOTE: The only operation which requires active states to
    -- be put to the queue in the current algorithm is the scan
    -- operation.  So perhaps we could somehow bypass this
    -- problem and perform scan elsewhere.  Nevertheless, it is
    -- not certain that the same will apply to the probabilistic
    -- parser.
    , waiting :: Q.PSQ (Item n t) Prio }


-- | Make an initial `EarSt` from a set of states.
mkEarSt
    :: (Ord n, Ord t)
    => A.DAWG n t
    -> S.Set (Active n t)
    -> (EarSt n t)
mkEarSt dag s = EarSt
    { automat = dag
    , withBody = mkWithBody dag
    , withHead = mkWithHead dag
    , doneActive  = M.empty
    , donePassive = M.empty
    , waiting = Q.fromList
        [ ItemA p :-> prioA p
        | p <- S.toList s ] }


-- | Create the `withBody` component based on the automaton.
mkWithBody
    :: (Ord n, Ord t)
    => A.DAWG n t
    -> M.Map (Lab n t) (S.Set ID)
mkWithBody dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | (i, A.Body x, _j) <- A.edges dag ]


-- | Create the `withHead` component based on the automaton.
mkWithHead
    :: (Ord n, Ord t)
    => A.DAWG n t
    -> M.Map n (S.Set ID)
mkWithHead dag = M.fromListWith S.union
    [ (nonTerm x, S.singleton i)
    | (i, A.Head x, _j) <- A.edges dag ]


-- | Earley parser monad.  Contains the input sentence (reader)
-- and the state of the computation `EarSt'.
type Earley n t = RWS.RWST [t] () (EarSt n t) IO


-- | Read word from the given position of the input.
readInput :: Pos -> P.ListT (Earley n t) t
readInput i = do
    -- ask for the input
    xs <- RWS.ask
    -- just a safe way to retrieve the i-th element
    each $ take 1 $ drop i xs
    -- maybeT $ listToMaybe $ drop i xs


-- -- | Check if the state is not already processed (i.e. in one of the
-- -- done-related maps).
-- isProcessed :: (Ord n, Ord t) => Item n t -> EarSt n t -> Bool
-- isProcessed x@Item{..} EarSt{..} = check $
--     (   M.lookup end
--     >=> M.lookup state
--     >=> M.lookup beg
--     >=> return . S.member x ) done
--   where
--     check (Just True) = True
--     check _           = False


-- | Check if the active item is not already processed.
isProcessedA :: (Ord n, Ord t) => Active n t -> EarSt n t -> Bool
isProcessedA p EarSt{..} = check $
    (   M.lookup (p ^. spanA ^. end)
    >=> M.lookup (p ^. state)
    >=> return . S.member p ) doneActive
  where
    check (Just True) = True
    check _           = False


-- | Check if the passive item is not already processed.
isProcessedP :: (Ord n, Ord t) => Passive n t -> EarSt n t -> Bool
isProcessedP p EarSt{..} = check $
    ( M.lookup
        ( p ^. spanP ^. beg
        , nonTerm $ p ^. label
        , p ^. spanP ^. end )
    >=> return . S.member p ) donePassive
  where
    check (Just True) = True
    check _           = False


-- | Add the active item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushActive :: (Ord t, Ord n) => Active n t -> Earley n t ()
pushActive p = RWS.state $ \s ->
    let waiting' = if isProcessedA p s
            then waiting s
            else Q.insert (ItemA p) (prioA p) (waiting s)
    in  ((), s {waiting = waiting'})


-- | Add the passive item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushPassive :: (Ord t, Ord n) => Passive n t -> Earley n t ()
pushPassive p = RWS.state $ \s ->
    let waiting' = if isProcessedP p s
            then waiting s
            else Q.insert (ItemP p) (prioP p) (waiting s)
    in  ((), s {waiting = waiting'})


-- | Add to the waiting queue all items induced from the given
-- item.
pushInduced :: (Ord t, Ord n) => Active n t -> Earley n t ()
pushInduced p = do
    hasElems (getL state p) >>= \b -> when b
        (pushActive p)
    P.runListT $ do
        x <- heads (getL state p)
        lift . pushPassive $ Passive x (getL spanA p)


-- | Remove a state from the queue.
popItem :: (Ord t, Ord n) => Earley n t (Maybe (Item n t))
popItem = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (x :-> _, s) -> (Just x, st {waiting = s})


-- -- | Add the state to the set of processed (`done') states.
-- saveItem :: (Ord t, Ord n) => Item n t -> Earley n t ()
-- saveItem p =
--     RWS.state $ \s -> ((), s {done = newDone s})
--   where
--     newDone st =
--         M.insertWith
--             (M.unionWith (M.unionWith S.union))
--             (end p)
--             ( M.singleton (state p)
--                 ( M.singleton (beg p)
--                     ( S.singleton p )
--                 )
--             )
--             (done st)


-- | Mark the active item as processed (`done').
saveActive :: (Ord t, Ord n) => Active n t -> Earley n t ()
saveActive p =
    RWS.state $ \s -> ((), s {doneActive = newDone s})
  where
    newDone st =
        M.insertWith
            ( M.unionWith S.union )
            ( p ^. spanA ^. end )
            ( M.singleton (p ^. state)
                ( S.singleton p ) )
            ( doneActive st )


-- | Mark the passive item as processed (`done').
savePassive :: (Ord t, Ord n) => Passive n t -> Earley n t ()
savePassive p =
    RWS.state $ \s -> ((), s {donePassive = newDone s})
  where
    newDone st =
        M.insertWith
            S.union
            ( p ^. spanP ^. beg
            , nonTerm $ p ^. label
            , p ^. spanP ^. end )
            ( S.singleton p )
            ( donePassive st )


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
    each $ S.toList doneEndLab


-- | Check if the given passive item exists, i.e. with:
-- * the given root non-terminal value (but not top-level
--   auxiliary)
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t)
rootSpan x (i, j) = do
    EarSt{..} <- lift RWS.get
    listValues (i, x, j) donePassive


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
    some $ D.follow i (A.Body $ Term c) auto


-- | Follow the given body transition in the underlying automaton.
-- It represents the transition function of the automaton.
--
-- TODO: merge with `followTerm`.
follow :: (Ord n, Ord t) => ID -> Lab n t -> P.ListT (Earley n t) ID
follow i x = do
    -- get the underlying automaton
    auto <- RWS.gets automat
    -- follow the label
    some $ D.follow i (A.Body x) auto


-- | Rule heads outgoing from the given automaton state.
heads :: ID -> P.ListT (Earley n t) (Lab n t)
heads i = do
    auto <- RWS.gets automat
    let mayHead (x, _) = case x of
            A.Body _  -> Nothing
            A.Head y -> Just y
    each $ mapMaybe mayHead $ D.edges i auto


-- | Rule body elements outgoing from the given automaton state.
elems :: ID -> P.ListT (Earley n t) (Lab n t)
elems i = do
    auto <- RWS.gets automat
    let mayBody (x, _) = case x of
            A.Body y  -> Just y
            A.Head _ -> Nothing
    each $ mapMaybe mayBody $ D.edges i auto


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
        $ D.edges i auto


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
    -- print logging information
    lift . lift $ do
        putStr "[S]  " >> printActive p
        putStr "  :  " >> printActive q
    -- push the resulting state into the waiting queue
    lift $ pushInduced q


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
    -- print logging information
    lift . lift $ do
        putStr "[U]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift $ pushInduced q'


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
    -- print logging information
    lift . lift $ do
        putStr "[A]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift $ pushInduced q'


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
--     let q' = q { state = j
--                , gap = gap p
--                , end = end p }
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (pSpan ^. gap)
           $ q
    -- logging info
    lift . lift $ do
        putStr "[B]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift $ pushInduced q'


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
    lift . lift $ do
        putStr "[C]  " >> printPassive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printPassive p'
    lift $ pushPassive p'


--------------------------------------------------
-- EARLEY
--------------------------------------------------


-- | Does the given grammar generate the given sentence?
-- Uses the `earley` algorithm under the hood.
recognize
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [t]                  -- ^ Input sentence
    -> IO Bool
recognize gram xs = do
    (done, _) <- earley gram xs
    return $ (not.null) (complete done)
  where
    n = length xs
    complete done =
        [ True | item <- S.toList done
        , item ^. spanP ^. beg == 0
        , item ^. spanP ^. end == n
        , item ^. spanP ^. gap == Nothing ]


-- | Does the given grammar generate the given sentence from the
-- given non-terminal symbol (i.e. from an initial tree with this
-- symbol in its root)?  Uses the `earley` algorithm under the
-- hood.
recognizeFrom
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> n                    -- ^ The start symbol
    -> [t]                  -- ^ Input sentence
    -> IO Bool
recognizeFrom gram start xs = do
    (done, _auto) <- earley gram xs
    return $ (not.null) (complete done)
  where
    n = length xs
    complete done =
        [ True | item <- S.toList done
        , item ^. spanP ^. beg == 0
        , item ^. spanP ^. end == n
        , item ^. label == NonT start Nothing ]


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [t]                  -- ^ Input sentence
    -> IO (S.Set (Passive n t), A.DAWG n t)
earley gram xs
    = ((,) <$> (agregate . donePassive) <*> automat) . fst
    <$> RWS.execRWST loop xs st0
  where
    agregate = S.unions . M.elems
    -- the automaton
    dawg = A.buildAuto gram
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt dawg $ S.fromList
        [ Active (D.root dawg) $ Span
            { _beg  = i
            , _end  = i
            , _gap  = Nothing }
        | Rule{..} <- S.toList gram
        , i <- [0 .. length xs - 1] ]
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popItem >>= \mp -> case mp of
        Nothing -> return ()
        Just p -> do
            step p >> loop


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step :: (VOrd t, VOrd n) => Item n t -> Earley n t ()
step (ItemP p) = do
    sequence_ $ map ($ p)
      [ trySubst
      , tryAdjoinInit
      , tryAdjoinCont
      , tryAdjoinTerm ]
    savePassive p
step (ItemA p) = do
    sequence_ $ map ($ p)
      [ tryScan ]
    saveActive p


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


-- | Pipe all values from the set corresponding to the given key.
listValues
    :: (Monad m, Ord a)
    => a -> M.Map a (S.Set b)
    -> P.ListT m b
listValues x m = each $ case M.lookup x m of
    Nothing -> []
    Just s -> S.toList s
