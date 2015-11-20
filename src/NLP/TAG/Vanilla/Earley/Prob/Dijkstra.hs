{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}


-- | Parsing based on the Dijkstra's shortest-path algorithm.


module NLP.TAG.Vanilla.Earley.Prob.Dijkstra where


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
import qualified NLP.TAG.Vanilla.Tree       as T


--------------------------------------------------
-- BASE TYPES
--------------------------------------------------


-- \ A span in the input sentence.
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
    -- putStr . show $ getL state p
    putStr $ viewLab (p ^. root)
    putStr " -> "
    putStr . unwords $
        map viewLab (p ^. right)
    putStr " ("
    printSpan $ getL spanA p
    putStrLn ")"


-- | Print a passive item.
printPassive :: (View n, View t) => Passive n t -> IO ()
printPassive p = do
    putStr . viewLab $ getL label p
    putStr " ("
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
        -- ^ The active argument of the action
        , theFoot  :: n
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


--------------------------------------------------
-- Priority
--------------------------------------------------


-- | Priority type.  Equivalent to a weight of reaching a given chart
-- configuration from the set of initial configurations in the underlying
-- hypergraph.
--
-- TODO: Change `Prio` -> `Weight` (or `Cost`?)
type Prio = Double


-- -- | Neutral element of the priority.  Corresponds at the moment to
-- -- a logarighm of probability 1.
-- prioDef :: Prio
-- prioDef = 0


-- | Add two weights.
addPrio :: Prio -> Prio -> Prio
addPrio = (+)
{-# INLINE addPrio #-}


-- | Minimum of two weights.
minPrio :: Prio -> Prio -> Prio
minPrio = min
{-# INLINE minPrio #-}


--------------------------------------------------
-- Extended Priority
--
-- NOTE: it forms a semiring?
--------------------------------------------------


-- | Extended priority which preservs information about the traversal leading
-- to the underlying chart item.  The best weight (priority) of reaching the
-- underlying item is preserved as well.  Note that traversals themselves do
-- not introduce any weights.
data ExtPrio n t = ExtPrio
    { prioVal   :: Prio
    -- ^ The actual priority.  In case of initial elements corresponds to
    -- weights (probabilities?) assigned to individual "elementary rules".
    , prioTrav  :: S.Set (Trav n t)
    -- ^ Traversal leading to the underlying chart item
    } deriving (Show)

instance (Eq n, Eq t) => Eq (ExtPrio n t) where
    (==) = (==) `on` prioVal
instance (Ord n, Ord t) => Ord (ExtPrio n t) where
    compare = compare `on` prioVal


-- | Construct an initial `ExtPrio`.  With an empty set of input traversals, it
-- corresponds to a start node in the underlying hyper-graph.
extPrio0 :: Prio -> ExtPrio n t
extPrio0 p = ExtPrio p S.empty


-- | Construct an `ExtPrio` with one incoming traversal
-- (traversal=hyper-edge).
extPrio :: Prio -> Trav n t -> ExtPrio n t
extPrio p = ExtPrio p . S.singleton


-- | Join two extended priorities:
-- * The actual priority (cost) preserved is the lower of the two; we are
-- simply keeping the lowest cost of reaching the underlying chart item.
-- * The traversals are unioned.
joinExtPrio :: (Ord n, Ord t) => ExtPrio n t -> ExtPrio n t -> ExtPrio n t
joinExtPrio x y = ExtPrio
    (minPrio (prioVal x) (prioVal y))
    (S.union (prioTrav x) (prioTrav y))


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt
    { doneActive  :: M.Map (Active n t) (ExtPrio n t)
    -- ^ Processed active states.
    , donePassive :: M.Map (Passive n t) (ExtPrio n t)
    -- ^ Processed active states.
    , waiting     :: Q.PSQ (Item n t) (ExtPrio n t)
    -- ^ The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    } deriving (Show)


-- | Make an initial `EarSt` from a set of initial states.
mkEarSt :: (Ord n, Ord t) => M.Map (Active n t) Prio -> EarSt n t
mkEarSt s = EarSt
    { doneActive  = M.empty
    , donePassive = M.empty
    , waiting     = Q.fromList
        [ ItemA p :-> extPrio0 c
        | (p, c) <- M.toList s ] }


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


---------------------------
-- Extracting Parsed Trees
---------------------------


-- | Extract the set of parsed trees obtained on the given input sentence.
-- Return the corresponding weights of constructing the trees as well.
-- The function should be run on the result of the earley algorithm.
parsedTrees
    :: forall n t. (Ord n, Ord t, Show n, Show t)
    => EarSt n t    -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> M.Map (T.Tree n t) Prio
parsedTrees EarSt{..} start n

    = M.fromList
    $ concatMap fromPassive
    $ final start n donePassive

  where

    fromPassive :: Passive n t -> [(T.Tree n t, Prio)]
    fromPassive p = concat
        [ fromPassiveTrav p trav
        | ExtPrio{..} <- maybeToList $ M.lookup p donePassive
        -- | let travSet = donePassive M.! p
        , trav <- S.toList prioTrav ]

    fromPassiveTrav p (Scan q t) =
        [ ( T.INode
            (nonTerm $ getL label p)
            (reverse $ T.FNode t : ts)
          , c )
        | (ts, c) <- fromActive q ]

    fromPassiveTrav p (Foot q x) =
        [ ( T.INode
            (nonTerm $ getL label p)
            (reverse $ T.INode x [] : ts)
          , c )
        | (ts, c) <- fromActive q ]

    fromPassiveTrav p (Subst qp qa) =
        [ ( T.INode
            (nonTerm $ getL label p)
            (reverse $ t : ts)
          , addPrio c1 c2 )
        | (ts, c1) <- fromActive qa
        , (t,  c2) <- fromPassive qp ]

    fromPassiveTrav _p (Adjoin qa qm) =
        [ (replaceFoot ini aux, addPrio c1 c2)
        | (aux, c1) <- fromPassive qa
        , (ini, c2) <- fromPassive qm ]

    -- | Replace foot (the only non-terminal leaf) by the given initial tree.
    replaceFoot ini (T.INode _ []) = ini
    replaceFoot ini (T.INode x ts) = T.INode x $ map (replaceFoot ini) ts
    replaceFoot _ t@(T.FNode _)    = t


    fromActive  :: Active n t -> [([T.Tree n t], Prio)]
    fromActive p = case M.lookup p doneActive of
        Nothing -> error "fromActive: unknown active item"
        Just ExtPrio{..} -> if S.null prioTrav
            then [([], prioVal)]
            else concatMap
                (fromActiveTrav p)
                (S.toList prioTrav)

    -- \ Here we assume that cost of reading a character is 0.
    fromActiveTrav _p (Scan q t) =
        [ (T.FNode t : ts, c)
        | (ts, c) <- fromActive q ]

    fromActiveTrav _p (Foot q x) =
        [ (T.INode x [] : ts, c)
        | (ts, c) <- fromActive q ]

    fromActiveTrav _p (Subst qp qa) =
        [ (t : ts, addPrio c1 c2)
        | (ts, c1) <- fromActive qa
        , (t,  c2) <- fromPassive qp ]

    fromActiveTrav _p (Adjoin _ _) =
        error "parsedTrees: fromActiveTrav called on a passive item"


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
saveActive :: (Ord n, Ord t) => Active n t -> ExtPrio n t -> Earley n t ()
saveActive p t = do
    let newDone = M.insertWith joinExtPrio p t
    RWS.modify' $ \s -> s {doneActive = newDone (doneActive s)}


-- | Add traversal to a passive processed item.
savePassive :: (Ord n, Ord t) => Passive n t -> ExtPrio n t -> Earley n t ()
savePassive p t = do
    let newDone = M.insertWith joinExtPrio p t
    RWS.modify' $ \s -> s {donePassive = newDone (donePassive s)}


--------------------
-- Waiting Queue
--------------------


-- | Add the active item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushActive :: (Ord t, Ord n) => Active n t -> ExtPrio n t -> Earley n t ()
pushActive p newPrio = isProcessedA p >>= \b -> if b
    then saveActive p newPrio
    else RWS.modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinExtPrio (ItemA p) newPrio


-- | Add the passive item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushPassive :: (Ord t, Ord n) => Passive n t -> ExtPrio n t -> Earley n t ()
pushPassive p newPrio = isProcessedP p >>= \b -> if b
    then savePassive p newPrio
    else RWS.modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinExtPrio (ItemP p) newPrio


-- | Add to the waiting queue the item induced from the given item.
-- Use instead of `pushActive` each time you are not sure the item is really
-- active.
pushInduced :: (Ord t, Ord n) => Active n t -> ExtPrio n t -> Earley n t ()
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
    -> P.ListT (Earley n t) (Active n t, Prio)
expectEnd x i = do
    EarSt{..} <- lift RWS.get
    each
        [ (q, prioVal e) | (q, e) <- M.toList doneActive
        , (y, _) <- maybeToList (expects' q)
        , x == y, q ^. spanA ^. end == i ]


-- | Return all passive items with:
-- * the given root non-terminal value
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t, Prio)
rootSpan x (i, j) = do
    EarSt{..} <- lift RWS.get
    each
        [ (q, prioVal e) | (q, e) <- M.toList donePassive
        , q ^. spanP ^. beg == i
        , q ^. spanP ^. end == j
        , nonTerm (q ^. label) == x ]


-- | Return all processed items which:
-- * are fully parsed (i.e. passive)
-- * provide a given label,
-- * begin on the given position.
provideBeg
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Passive n t, Prio)
provideBeg x i = do
    EarSt{..} <- lift RWS.get
    each
        [ (q, prioVal e) | (q, e) <- M.toList donePassive
        , q ^. spanP ^. beg == i
        , q ^. label == x ]


-- | Return all processed items which:
-- * are fully parsed (i.e. passive)
-- * provide a label with a given non-terminal,
-- * begin on the given position,
--
-- (Note the similarity to `provideBeg`)
provideBeg'
    :: (Ord n, Ord t) => n -> Pos
    -> P.ListT (Earley n t) (Passive n t, Prio)
provideBeg' x i = do
    EarSt{..} <- lift RWS.get
    each
        [ (q, prioVal e) | (q, e) <- M.toList donePassive
        , q ^. spanP ^.beg == i
        , nonTerm (q ^. label) == x ]


-- | Return all fully parsed items:
-- * top-level and representing auxiliary trees,
-- * modifying the given source non-terminal,
-- * with the given gap.
auxModifyGap
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t, Prio)
auxModifyGap x gapSpan = do
    EarSt{..} <- lift RWS.get
    each
        [ (q, prioVal e) | (q, e) <- M.toList donePassive
        , q ^. spanP ^. gap == Just gapSpan
        , topLevel (q ^. label)
        , nonTerm  (q ^. label) == x ]


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- | Try to perform SCAN on the given state.
tryScan
    :: (VOrd t, VOrd n)
    => Active n t   -- ^ The item popped from the queue
    -> Prio         -- ^ The corresponding cost
    -> Earley n t ()
tryScan p cost = void $ runMaybeT $ do
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
          . modL' right tail
          $ p
    -- print logging information
    lift . lift $ do
        putStr "[S]  " >> printActive p
        putStr "  :  " >> printActive q
    -- push the resulting state into the waiting queue
    lift . pushInduced q . extPrio cost $ Scan p t


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the state (only if fully parsed) to complement
-- (=> substitution) other rules.
trySubst
    :: (VOrd t, VOrd n)
    => Passive n t  -- ^ The item popped from the queue
    -> Prio         -- ^ The corresponding cost
    -> Earley n t ()
trySubst p cost = void $ P.runListT $ do
    let pLab = getL label p
        pSpan = getL spanP p
    -- make sure that `p' represents a regular rule
    guard . regular $ pSpan
    -- find items which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    (q, cost') <- expectEnd pLab (pSpan ^. beg)
    -- construct the resultant state
    let q' = setL (end.spanA) (pSpan ^. end)
           . modL' right tail
           $ q
    -- print logging information
    lift . lift $ do
        putStr "[U]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q' . extPrio (addPrio cost cost') $ Subst p q


-- | Reversed `trySubst` version.  Try to completent the item with another
-- fully parsed item.
trySubst' :: (VOrd t, VOrd n) => Active n t -> Prio -> Earley n t ()
trySubst' q cost = void $ P.runListT $ do
    -- Learn what `q` actually expects.
    (r@NonT{}, _) <- some $ expects' q
    -- Find processed items which begin where `q` ends and which provide the
    -- non-terminal expected by `q`.
    (p, cost') <- provideBeg r (q ^. spanA ^. end)
    let pSpan = p ^. spanP
    -- construct the resultant state
    let q' = setL (spanA >>> end) (pSpan ^. end)
           . modL' right tail
           $ q
    -- print logging information
    lift . lift $ do
        putStr "[U'] " >> printActive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q' . extPrio (addPrio cost cost') $ Subst p q


--------------------------------------------------
-- ADJOIN INIT
--------------------------------------------------


-- | `tryAdjoinInit p q':
-- * `p' is a completed state (regular or auxiliary)
-- * `q' not completed and expects a *real* foot
tryAdjoinInit :: (VOrd n, VOrd t) => Passive n t -> Prio -> Earley n t ()
tryAdjoinInit p cost = void $ P.runListT $ do
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- make sure that the corresponding rule is either regular or
    -- intermediate auxiliary ((<=) used as implication here)
    guard $ auxiliary pSpan <= not (topLevel pLab)
    -- find all active items which expect a foot with the given
    -- symbol and which end where `p` begins
    let foot = AuxFoot $ nonTerm pLab
    (q, cost') <- expectEnd foot (getL beg pSpan)
    -- construct the resultant state
    let q' = setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (Just
                ( pSpan ^. beg
                , pSpan ^. end ))
           . modL' right tail
           $ q
    -- print logging information
    lift . lift $ do
        putStr "[A]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q' . extPrio (addPrio cost cost') $ Foot q (nonTerm foot)


-- | Reverse of `tryAdjoinInit` where the given state `q`
-- expects a real foot.
-- * `q' not completed and expects a *real* foot
-- * `p' is a completed state (regular or auxiliary)
tryAdjoinInit' :: (VOrd n, VOrd t) => Active n t -> Prio -> Earley n t ()
tryAdjoinInit' q cost = void $ P.runListT $ do
    -- Retrieve the foot expected by `q`.
    (AuxFoot footNT, _) <- some $ expects' q
    -- Find all fully parsed items which provide the given source
    -- non-terminal and which begin where `q` ends.
    (p, cost') <- provideBeg' footNT (q ^. spanA ^. end)
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- The retrieved items must not be auxiliary top-level.
    guard $ auxiliary pSpan <= not (topLevel pLab)
    -- construct the resultant state
    let q' = setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (Just
                ( pSpan ^. beg
                , pSpan ^. end ))
           . modL' right tail
           $ q
    -- print logging information
    lift . lift $ do
        putStr "[A'] " >> printActive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q' . extPrio (addPrio cost cost') $ Foot q footNT


--------------------------------------------------
-- ADJOIN CONT
--------------------------------------------------


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
tryAdjoinCont :: (VOrd n, VOrd t) => Passive n t -> Prio -> Earley n t ()
tryAdjoinCont p cost = void $ P.runListT $ do
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- make sure the label is not top-level (internal spine
    -- non-terminal)
    guard . not $ topLevel pLab
    -- make sure that `p' is an auxiliary item
    guard . auxiliary $ pSpan
    -- find all rules which expect a spine non-terminal provided
    -- by `p' and which end where `p' begins
    (q, cost') <- expectEnd pLab (pSpan ^. beg)
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (pSpan ^. gap)
           . modL' right tail
           $ q
    -- logging info
    lift . lift $ do
        putStr "[B]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q' . extPrio (addPrio cost cost') $ Subst p q


-- | Reversed `tryAdjoinCont`.
tryAdjoinCont' :: (VOrd n, VOrd t) => Active n t -> Prio -> Earley n t ()
tryAdjoinCont' q cost = void $ P.runListT $ do
    -- Retrieve the auxiliary vertebrea expected by `q`
    (r@AuxVert{}, _) <- some $ expects' q
    -- Find all fully parsed items which provide the given label
    -- and which begin where `q` ends.
    (p, cost') <- provideBeg r (q ^. spanA ^. end)
    let pSpan = p ^. spanP
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (pSpan ^. gap)
           . modL' right tail
           $ q
    -- logging info
    lift . lift $ do
        putStr "[B'] " >> printActive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printActive q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q' . extPrio (addPrio cost cost') $ Subst p q


--------------------------------------------------
-- ADJOIN TERM
--------------------------------------------------


-- | Adjoin a fully-parsed auxiliary state `q` to a partially parsed
-- tree represented by a fully parsed rule/state `p`.
tryAdjoinTerm :: (VOrd t, VOrd n) => Passive n t -> Prio -> Earley n t ()
tryAdjoinTerm q cost = void $ P.runListT $ do
    let qLab = q ^. label
        qSpan = q ^. spanP
    -- make sure the label is top-level
    guard $ topLevel qLab
    -- make sure that it is an auxiliary item (by definition only
    -- auxiliary states have gaps)
    theGap <- each $ maybeToList $ qSpan ^. gap
    -- take all passive items with a given span and a given
    -- root non-terminal (IDs irrelevant)
    (p, cost') <- rootSpan (nonTerm qLab) theGap
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
    lift . pushPassive p' . extPrio (addPrio cost cost') $ Adjoin q p


-- | Reversed `tryAdjoinTerm`.
tryAdjoinTerm' :: (VOrd t, VOrd n) => Passive n t -> Prio -> Earley n t ()
tryAdjoinTerm' p cost = void $ P.runListT $ do
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- Ensure that `p` is auxiliary but not top-level
    guard $ auxiliary pSpan <= not (topLevel pLab)
    -- Retrieve all completed, top-level items representing auxiliary trees
    -- which have a specific gap and modify a specific source non-terminal.
    (q, cost') <- auxModifyGap
        (nonTerm $ p ^. label)
        ( p ^. spanP ^. beg
        , p ^. spanP ^. end )
    let qSpan = q ^. spanP
    -- Construct the resulting state:
    let p' = setL (spanP >>> beg) (qSpan ^. beg)
           . setL (spanP >>> end) (qSpan ^. end)
           $ p
    lift . lift $ do
        putStr "[C'] " >> printPassive p
        putStr "  +  " >> printPassive q
        putStr "  :  " >> printPassive p'
    lift . pushPassive p' . extPrio (addPrio cost cost') $ Adjoin q p


--------------------------------------------------
-- EARLEY
--------------------------------------------------


-- | Does the given grammar generate the given sentence from the
-- given non-terminal symbol (i.e. from an initial tree with this
-- symbol in its root)?  Uses the `earley` algorithm under the
-- hood.
recognize
    :: (VOrd t, VOrd n)
    => M.Map (Rule n t) Prio    -- ^ The grammar
    -> n                        -- ^ The start symbol
    -> [t]                      -- ^ Input sentence
    -> IO Bool
recognize gram start xs = do
    done <- final start (length xs) . donePassive
        <$> _earley gram xs
    return $ (not.null) done


-- | Parse the given sentence and return the set of parsed trees.
parse
    :: (VOrd t, VOrd n)
    => M.Map (Rule n t) Prio    -- ^ The grammar
    -> n                        -- ^ The start symbol
    -> [t]                      -- ^ Input sentence
    -> IO (M.Map (T.Tree n t) Prio)
parse gram start xs = do
    earSt <- _earley gram xs
    return $ parsedTrees earSt start (length xs)


-- | Return the lit of final passive chart items.
final
    :: (Eq n, Eq t)
    => n            -- ^ The start symbol
    -> Int          -- ^ The length of the input sentence
    -> M.Map (Passive n t) (ExtPrio n t)
                    -- ^ Result of the earley computation
    -> [Passive n t]
final start n donePassive =
    [ p
    | p <- S.toList $ M.keysSet donePassive
    , p ^. spanP ^. beg == 0
    , p ^. spanP ^. end == n
    , p ^. label == NonT start Nothing ]


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
_earley
    :: (VOrd t, VOrd n)
    => M.Map (Rule n t) Prio    -- ^ The grammar (set of rules with
                                -- corresponding weights)
    -> [t]                      -- ^ Input sentence
    -> IO (EarSt n t)
_earley gram xs =
    -- M.keysSet . donePassive . fst <$> RWS.execRWST loop xs st0
    fst <$> RWS.execRWST loop xs st0
  where
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt $ M.fromList -- $ Reid.runReid $ mapM reidState
        [ ( Active
            { _root  = headR
            , _right = bodyR
            , _spanA = Span
                { _beg   = i
                , _end   = i
                , _gap   = Nothing } }
          , cost )
        | (Rule{..}, cost) <- M.toList gram
        , i <- [0 .. length xs - 1] ]
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popItem >>= \mp -> case mp of
        Nothing -> return ()
        Just p -> step p >> loop


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step
    :: (VOrd t, VOrd n)
    => Binding (Item n t) (ExtPrio n t)
    -> Earley n t ()
step (ItemP p :-> e) = do
    mapM_ (\f -> f p $ prioVal e)
      [ trySubst
      , tryAdjoinInit
      , tryAdjoinCont
      , tryAdjoinTerm
      , tryAdjoinTerm' ]
    savePassive p e
step (ItemA p :-> e) = do
    mapM_ (\f -> f p $ prioVal e)
      [ tryScan
      , trySubst'
      , tryAdjoinInit'
      , tryAdjoinCont' ]
    saveActive p e


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
