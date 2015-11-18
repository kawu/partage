{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}


-- | A version in which we don't assume that inference arguments are popped
-- from the queue in any particular order.
--   => towards probabilistic chart parsing


module NLP.TAG.Vanilla.Earley.New where


import           Prelude hiding             (span, (.))
import           Control.Applicative        ((<$>))
import           Control.Monad              (guard, void)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS
import           Control.Category           ((>>>), (.))

import           Data.Function              (on)
import           Data.Maybe                 ( isJust, isNothing
                                            , listToMaybe, maybeToList)
import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import           Data.Lens.Light
import qualified Pipes                      as P

import           NLP.TAG.Vanilla.Core
import           NLP.TAG.Vanilla.Rule       ( Lab(..), viewLab, Rule(..) )


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
data Active n t = Active
    { _root    :: Lab n t
    -- ^ The head of the rule represented by the item.
    -- TODO: Not a terminal nor a foot.
    , _left    :: [Lab n t]
    -- ^ The list of processed elements of the rule, stored in an
    -- inverse order.
    , _right   :: [Lab n t]
    -- ^ The list of elements yet to process.
    , _spanA   :: Span
    -- ^ The span of the item.
    } deriving (Show, Eq, Ord)
$( makeLenses [''Active] )


-- | Passive chart item : label + span.
data Passive n t = Passive
    { _label :: Lab n t
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


-- | Is it a completed (fully-parsed) active item?
completed :: Active n t -> Bool
completed = null . getL right


-- | Print an active item.
printActive :: (View n, View t) => Active n t -> IO ()
printActive p = do
    putStr "("
    -- putStr . show $ getL state p
    putStr . show $ viewLab (p ^. root)
    putStr " -> "
    putStr . unwords $
        map viewLab (reverse (p ^. left)) ++
        ["*"] ++ map viewLab (p ^. right)
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
-- Item Type
--------------------------------------------------


-- | Passive or active item.
data Item n t
    = ItemP (Passive n t)
    | ItemA (Active n t)
    deriving (Show, Eq, Ord)


-- | Deconstruct the right part of the state (i.e. labels yet to
-- process) within the MaybeT monad.
expects
    :: Monad m
    => Active n t
    -> MaybeT m (Lab n t, [Lab n t])
expects = maybeT . expects'


-- | Deconstruct the right part of the active item (i.e. labels yet to
-- process).
expects'
    :: Active n t
    -> Maybe (Lab n t, [Lab n t])
expects' = decoList . getL right


--------------------------------------------------
-- Traversal
--------------------------------------------------


-- | Traversal represents an action of inducing a new item on the basis of one
-- or two other chart items.  It can be seen as an application of one of the
-- inference rules specifying the parsing algorithm.
--
-- TODO: Sometimes there is no need to store all the arguments of the inference
-- rules, it seems.  From one of the arguments the other one could be derived.
data Trav n t
    = Scan
        { scanFrom :: Active n t }
    | Binary
    -- ^ A generic binary inference rule application.  TODO: we will probably
    -- have to split it.
        { passArg  :: Passive n t
        -- ^ The passive argument of the action
        , actArg   :: Active n t
        -- ^ The active argument of the action
        }
    | Adjoin
    -- ^ Adjoin terminate with two passive arguments
        { passAdj  :: Passive n t
        -- ^ The adjoined item
        , passMod  :: Passive n t
        -- ^ The modified item
        }
    deriving (Show, Eq, Ord)


--------------------------------------------------
-- Priority
--------------------------------------------------


-- | Priority type.
type Prio = Int


-- | Priority of an active item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioA :: Active n t -> Prio
-- prioA = negate . getL (end . spanA)
prioA = getL (end . spanA)


-- | Priority of a passive item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioP :: Passive n t -> Prio
-- prioP = negate . getL (end . spanP)
prioP = getL (end . spanP)


-- | Extended priority which preservs information about the traversal leading
-- to the underlying chart item.
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
-- NOTE: at the moment, priority is strictly specified by the underlying chart
-- item itself so we know that both priorities must be equal.  Later when we
-- start using probabilities this statement will no longer hold.
joinPrio :: (Ord n, Ord t) => ExtPrio n t -> ExtPrio n t -> ExtPrio n t
joinPrio x y = ExtPrio
    (min (prioVal x) (prioVal y))
    (S.union (prioTrav x) (prioTrav y))


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt
    { doneActive  :: M.Map (Active n t) (S.Set (Trav n t))
    -- ^ Processed active states.
    , donePassive :: M.Map (Passive n t) (S.Set (Trav n t))
    -- ^ Processed active states.
    , waiting     :: Q.PSQ (Item n t) (ExtPrio n t)
    -- ^ The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    }


-- | Make an initial `EarSt` from a set of states.
mkEarSt :: (Ord n, Ord t) => S.Set (Active n t) -> EarSt n t
mkEarSt s = EarSt
    { doneActive  = M.empty
    , donePassive = M.empty
    , waiting     = Q.fromList
        [ ItemA p :-> extPrio (prioA p)
        | p <- S.toList s ] }


-- | Earley parser monad.  Contains the input sentence (reader)
-- and the state of the computation `EarSt'.
type Earley n t = RWS.RWST [t] () (EarSt n t) IO


-- | Read word from the given position of the input.
readInput :: Pos -> MaybeT (Earley n t) t
readInput i = do
    -- ask for the input
    xs <- RWS.ask
    -- just a safe way to retrieve the i-th element
    maybeT $ listToMaybe $ drop i xs


--------------------
-- Processed Items
--------------------


-- | Check if the active item is not already processed.
isProcessedA :: (Ord n, Ord t) => Active n t -> Earley n t Bool
isProcessedA p = M.member p <$> RWS.gets doneActive


-- | Check if the passive item is not already processed.
isProcessedP :: (Ord n, Ord t) => Passive n t -> Earley n t Bool
isProcessedP p = M.member p <$> RWS.gets donePassive


-- | Add traversal to an active processed item.
saveActive :: (Ord n, Ord t) => Active n t -> S.Set (Trav n t) -> Earley n t ()
saveActive p ts = do
    let newDone = M.insertWith S.union p ts
    RWS.modify' $ \s -> s {doneActive = newDone (doneActive s)}


-- | Add traversal to a passive processed item.
savePassive :: (Ord n, Ord t) => Passive n t -> S.Set (Trav n t) -> Earley n t ()
savePassive p ts = do
    let newDone = M.insertWith S.union p ts
    RWS.modify' $ \s -> s {donePassive = newDone (donePassive s)}


-- -- | Mark the active item as processed (`done').
-- saveActive :: (Ord t, Ord n) => Active n t -> Earley n t ()
-- saveActive p =
--     RWS.state $ \s -> ((), s {doneActive = newDone s})
--   where
--     newDone st = S.insert p (doneActive st)
--
--
-- -- | Mark the passive item as processed (`done').
-- savePassive :: (Ord t, Ord n) => Passive n t -> Earley n t ()
-- savePassive p =
--     RWS.state $ \s -> ((), s {donePassive = newDone s})
--   where
--     newDone st = S.insert p (donePassive st)


--------------------
-- Waiting Queue
--------------------


-- | Add the active item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushActive :: (Ord t, Ord n) => Active n t -> Trav n t -> Earley n t ()
pushActive p t= isProcessedA p >>= \b -> if b
    then saveActive p $ S.singleton t
    else RWS.modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinPrio (ItemA p) newPrio
    newPrio = ExtPrio (prioA p) (S.singleton t)
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
-- pushPassive p = RWS.state $ \s ->
--     let waiting' = if isProcessedP p s
--             then waiting s
--             else Q.insert (ItemP p) (prioP p) (waiting s)
--     in  ((), s {waiting = waiting'})


-- | Add to the waiting queue the item induced from the given item.
-- Use instead of `pushActive` each time you are not sure the item is really
-- active.
pushInduced :: (Ord t, Ord n) => Active n t -> Trav n t -> Earley n t ()
pushInduced p = if completed p
    then pushPassive $ Passive (p ^. root) (p ^. spanA)
    else pushActive p


-- | Remove an item from the queue.
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


-- | Return all processed active items which:
-- * expect a given label,
-- * end on the given position.
expectEnd
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Active n t)
expectEnd x i = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- M.keys doneActive
        , (y, _) <- maybeToList (expects' q)
        , x == y, q ^. spanA ^. end == i ]


-- | Return all passive items with:
-- * the given root non-terminal value
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t)
rootSpan x (i, j) = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- M.keys donePassive
        , q ^. spanP ^. beg == i
        , q ^. spanP ^. end == j
        , nonTerm (q ^. label) == x ]


-- | Return all processed items which:
-- * are fully parsed,
-- * provide a given label,
-- * begin on the given position.
provideBeg
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Passive n t)
provideBeg x i = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- M.keys donePassive
        , q ^. label == x
        , q ^. spanP ^.beg == i ]


-- | Return all processed items which:
-- * are fully parsed,
-- * provide a label with a given non-terminal,
-- * begin on the given position,
provideBeg'
    :: (Ord n, Ord t) => n -> Pos
    -> P.ListT (Earley n t) (Passive n t)
provideBeg' x i = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- M.keys donePassive
        , nonTerm (q ^. label) == x
        , q ^. spanP ^.beg == i ]


-- | Return all fully parsed items:
-- * top-level and representing auxiliary trees,
-- * modifying the given source non-terminal,
-- * with the given gap.
auxModifyGap
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t)
auxModifyGap x gapSpan = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- M.keys donePassive
        , q ^. spanP ^. gap == Just gapSpan
        , topLevel (q ^. label)
        , nonTerm  (q ^. label) == x ]


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- | Try to perform SCAN on the given state.
tryScan :: (VOrd t, VOrd n) => Active n t -> Earley n t ()
tryScan p = void $ runMaybeT $ do
    -- check that the state expects a terminal on the right
    (Term t, _) <- expects p
    -- read the word immediately following the ending position of
    -- the state
    c <- readInput $ getL (spanA >>> end) p
    -- make sure that what the rule expects is consistent with
    -- the input
    guard $ c == t
    -- construct the resultant state
    let q = modL' (spanA >>> end) (+1)
          . modL' left (Term t :)
          . modL' right tail
          $ p
    -- print logging information
    lift . lift $ do
        putStr "[S]  " >> printActive p
        putStr "  :  " >> printActive q
    -- push the resulting state into the waiting queue
    lift $ pushInduced q $ Scan p


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the state (only if fully parsed) to complement
-- (=> substitution) other rules.
trySubst :: (VOrd t, VOrd n) => Passive n t -> Earley n t ()
trySubst p = void $ P.runListT $ do
    let pLab = getL label p
        pSpan = getL spanP p
    -- make sure that `p' represents a regular rule
    guard . regular $ pSpan
    -- find rules which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    q <- expectEnd pLab (pSpan ^. beg)
    -- TODO: what's the point of checking what `q` expects?  After all, we
    -- already know that it expects what `p` provides, i.e. `root p`?
    (r@NonT{}, _) <- some $ expects' q
    -- construct the resultant state
    let q' = setL (end.spanA) (pSpan ^. end)
           . modL' left (r:)
           . modL' right tail
           $ q
    -- print logging information
    lift . lift $ do
        putStr "[U]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Binary p q


-- -- | Reversed `trySubst` version.  Try to completent the item with another
-- -- fully parsed item.
-- trySubst' :: (VOrd t, VOrd n) => Active n t -> Earley n t ()
-- trySubst' q = void $ P.runListT $ do
--     -- Learn what `q` actually expects.
--     (r@NonT{}, _) <- some $ expects' q
--     -- Find processed items which begin where `q` ends and which provide the
--     -- non-terminal expected by `q`.
--     p <- provideBeg r (q ^. spanA ^. end)
--     let pSpan = p ^. spanP
--     -- construct the resultant state
--     let q' = setL (spanA >>> end) (pSpan ^. end)
--            . modL' left (r:)
--            . modL' right tail
--            $ q
--     -- print logging information
--     lift . lift $ do
--         putStr "[U'] " >> printActive q
--         putStr "  +  " >> printPassive p
--         putStr "  :  " >> printActive q'
--     -- push the resulting state into the waiting queue
--     lift $ pushInduced q'


--------------------------------------------------
-- ADJOIN INIT
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
    -- construct the resultant state
    let q' = setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (Just
                ( pSpan ^. beg
                , pSpan ^. end ))
           . modL' left (foot:)
           . modL' right tail
           $ q
    -- print logging information
    lift . lift $ do
        putStr "[A]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Binary p q


-- -- | Reverse of `tryAdjoinInit` where the given state `q`
-- -- expects a real foot.
-- -- * `q' not completed and expects a *real* foot
-- -- * `p' is a completed state (regular or auxiliary)
-- tryAdjoinInit' :: (VOrd n, VOrd t) => Active n t -> Earley n t ()
-- tryAdjoinInit' q = void $ P.runListT $ do
--     -- Retrieve the foot expected by `q`.
--     (r@(AuxFoot u), _) <- some $ expects' q
--     -- Find all fully parsed items which provide the given source
--     -- non-terminal and which begin where `q` ends.
--     p <- provideBeg' u (q ^. spanA ^. end)
--     let pLab = p ^. label
--         pSpan = p ^. spanP
--     -- The retrieved items must not be auxiliary top-level.
--     guard $ auxiliary pSpan <= not (topLevel pLab)
--     -- construct the resultant state
--     let q' = setL (spanA >>> end) (pSpan ^. end)
--            . setL (spanA >>> gap) (Just
--                 ( pSpan ^. beg
--                 , pSpan ^. end ))
--            . modL' left (r:)
--            . modL' right tail
--            $ q
--     -- print logging information
--     lift . lift $ do
--         putStr "[A'] " >> printActive q
--         putStr "  +  " >> printPassive p
--         putStr "  :  " >> printActive q'
--     -- push the resulting state into the waiting queue
--     lift $ pushInduced q'


--------------------------------------------------
-- ADJOIN CONT
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
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (pSpan ^. gap)
           . modL' left (pLab:)
           . modL' right tail
           $ q
    -- logging info
    lift . lift $ do
        putStr "[B]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift $ pushInduced q' $ Binary p q


-- -- | Reversed `tryAdjoinCont`.
-- tryAdjoinCont' :: (VOrd n, VOrd t) => Active n t -> Earley n t ()
-- tryAdjoinCont' q = void $ P.runListT $ do
--     -- Retrieve the auxiliary vertebrea expected by `q`
--     (r@AuxVert{}, _) <- some $ expects' q
--     -- Find all fully parsed items which provide the given label
--     -- and which begin where `q` ends.
--     p <- provideBeg r (q ^. spanA ^. end)
--     let pSpan = p ^. spanP
--     -- construct the resulting state; the span of the gap of the
--     -- inner state `p' is copied to the outer state based on `q'
--     let q' = setL (spanA >>> end) (pSpan ^. end)
--            . setL (spanA >>> gap) (pSpan ^. gap)
--            . modL' left (r:)
--            . modL' right tail
--            $ q
--     -- logging info
--     lift . lift $ do
--         putStr "[B'] " >> printActive q
--         putStr "  +  " >> printPassive p
--         putStr "  :  " >> printActive q'
--     -- push the resulting state into the waiting queue
--     lift $ pushInduced q'


--------------------------------------------------
-- ADJOIN TERM
--------------------------------------------------


-- | Adjoin a fully-parsed auxiliary state `q` to a partially parsed
-- tree represented by a fully parsed rule/state `p`.
tryAdjoinTerm :: (VOrd t, VOrd n) => Passive n t -> Earley n t ()
tryAdjoinTerm q = void $ P.runListT $ do
    let qLab = q ^. label
        qSpan = q ^. spanP
    -- make sure the label is top-level
    guard $ topLevel qLab
    -- make sure that it is an auxiliary item (by definition only
    -- auxiliary states have gaps)
    theGap <- each $ maybeToList $ qSpan ^. gap
    -- take all passive items with a given span and a given
    -- root non-terminal (IDs irrelevant)
    p <- rootSpan (nonTerm qLab) theGap
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- The retrieved item must not be auxiliary top-level.
    guard $ auxiliary pSpan <= not (topLevel pLab)
    -- construct the resultant state
    let p' = setL (spanP >>> beg) (qSpan ^. beg)
           . setL (spanP >>> end) (qSpan ^. end)
           $ p
    lift . lift $ do
        putStr "[C]  " >> printPassive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printPassive p'
    lift $ pushPassive p' $ Adjoin p q


-- -- | Reversed `tryAdjoinTerm`.
-- tryAdjoinTerm' :: (VOrd t, VOrd n) => Passive n t -> Earley n t ()
-- tryAdjoinTerm' p = void $ P.runListT $ do
--     let pLab = p ^. label
--         pSpan = p ^. spanP
--     -- Ensure that `p` is auxiliary but not top-level
--     guard $ auxiliary pSpan <= not (topLevel pLab)
--     -- Retrieve all completed, top-level items representing auxiliary trees
--     -- which have a specific gap and modify a specific source non-terminal.
--     q <- auxModifyGap
--         (nonTerm $ p ^. label)
--         ( p ^. spanP ^. beg
--         , p ^. spanP ^. end )
--     let qSpan = q ^. spanP
--     -- Construct the resulting state:
--     let p' = setL (spanP >>> beg) (qSpan ^. beg)
--            . setL (spanP >>> end) (qSpan ^. end)
--            $ p
--     lift . lift $ do
--         putStr "[C'] " >> printPassive p
--         putStr "  +  " >> printPassive q
--         putStr "  :  " >> printPassive p'
--     lift $ pushPassive p'


-- --------------------------------------------------
-- -- EARLEY
-- --------------------------------------------------
--
--
-- -- | Does the given grammar generate the given sentence?
-- -- Uses the `earley` algorithm under the hood.
-- recognize
--     :: (VOrd t, VOrd n)
--     => S.Set (Rule n t)     -- ^ The grammar (set of rules)
--     -> [t]                  -- ^ Input sentence
--     -> IO Bool
-- recognize gram xs = do
--     done <- earley gram xs
--     return $ (not.null) (complete done)
--   where
--     n = length xs
--     complete sts =
--         [ True | st <- S.toList sts
--         , beg st == 0, end st == n
--         , regular st, completed st ]


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
    done <- earley gram xs
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
    -> IO (S.Set (Passive n t))
earley gram xs =
    M.keysSet . donePassive . fst <$> RWS.execRWST loop xs st0
  where
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt $ S.fromList -- $ Reid.runReid $ mapM reidState
        [ Active
            { _root  = headR
            , _left  = []
            , _right = bodyR
            , _spanA = Span
                { _beg   = i
                , _end   = i
                , _gap   = Nothing } }
        | Rule{..} <- S.toList gram
        , i <- [0 .. length xs - 1] ]
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popItem >>= \mp -> case mp of
        Nothing -> return ()
        Just p -> step p >> loop
            -- lift $ case p of
            --     (StateE q) -> putStr "POPED: " >> printState q
            -- step p >> loop


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
--       , tryAdjoinTerm' ]
    savePassive p $ prioTrav e
step (ItemA p :-> e) = do
    mapM_ ($ p)
      [ tryScan ]
--       , trySubst'
--       , tryAdjoinInit'
--       , tryAdjoinCont' ]
    saveActive p $ prioTrav e


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | Deconstruct list.  Utility function.  Similar to `unCons`.
decoList :: [a] -> Maybe (a, [a])
decoList [] = Nothing
decoList (y:ys) = Just (y, ys)


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
