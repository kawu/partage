{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}


-- | A version in which we don't assume that inference arguments are popped
-- from the queue in any particular order.
--   => towards probabilistic chart parsing


module NLP.TAG.Vanilla.Earley.New where


import           Control.Applicative        ((<$>))
import           Control.Monad              (guard, void)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS

import           Data.Maybe     ( isJust, isNothing
                                , listToMaybe, maybeToList)
-- import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import qualified Pipes                      as P

import           NLP.TAG.Vanilla.Core
import           NLP.TAG.Vanilla.Rule
                                ( Lab(..), viewLab, Rule(..) )



--------------------------------------------------
-- CHART STATE ...
--
-- ... and chart extending operations
--------------------------------------------------


-- | Parsing state: processed initial rule elements and the elements
-- yet to process.
data State n t = State {
    -- | The head of the rule represented by the state.
    -- TODO: Not a terminal nor a foot.
      root  :: Lab n t
    -- | The list of processed elements of the rule, stored in an
    -- inverse order.
    , left  :: [Lab n t]
    -- | The list of elements yet to process.
    , right :: [Lab n t]
    -- | The starting position.
    , beg   :: Pos
    -- | The ending position (or rather the position of the dot).
    , end   :: Pos
    -- | Coordinates of the gap (if applies)
    , gap   :: Maybe (Pos, Pos)
    } deriving (Show, Eq, Ord)


-- | Is it a completed (fully-parsed) state?
completed :: State n t -> Bool
completed = null . right


-- | Does it represent a regular rule?
regular :: State n t -> Bool
regular = isNothing . gap


-- | Does it represent an auxiliary rule?
auxiliary :: State n t -> Bool
auxiliary = isJust . gap


-- | Is it top-level?  All top-level states (regular or
-- auxiliary) have an underspecified ID in the root symbol.
topLevel :: State n t -> Bool
-- topLevel = isNothing . ide . root
topLevel = not . subLevel


-- | Is it subsidiary (i.e. not top) level?
subLevel :: State n t -> Bool
-- subLevel = isJust . ide . root
subLevel x = case root x of
    NonT{..}  -> isJust labID
    AuxVert{} -> True
    Term _    -> True
    _         -> False


-- | Deconstruct the right part of the state (i.e. labels yet to
-- process) within the MaybeT monad.
expects
    :: Monad m
    => State n t
    -> MaybeT m (Lab n t, [Lab n t])
expects = maybeT . expects'


-- | Deconstruct the right part of the state (i.e. labels yet to
-- process).
expects'
    :: State n t
    -> Maybe (Lab n t, [Lab n t])
expects' = decoList . right


-- | Print the state.
printState :: (View n, View t) => State n t -> IO ()
printState State{..} = do
    putStr $ viewLab root
    putStr " -> "
    putStr $ unwords $
        map viewLab (reverse left) ++ ["*"] ++ map viewLab right
    putStr " <"
    putStr $ show beg
    putStr ", "
    case gap of
        Nothing -> return ()
        Just (p, q) -> do
            putStr $ show p
            putStr ", "
            putStr $ show q
            putStr ", "
    putStr $ show end
    putStrLn ">"


-- | Priority type.
type Prio = Int


-- | Priority of a state.  Crucial for the algorithm -- states have
-- to be removed from the queue in a specific order.
prio :: State n t -> Prio
-- prio p = negate (end p - beg p)
prio = negate . end


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt {
    -- | The set of done states.  Non-optimal implementation, we want to make
    -- sure that the idea works.
      done  :: S.Set (State n t)
    -- | The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    , waiting    :: Q.PSQ (State n t) Prio }


-- | Make an initial `EarSt` from a set of states.
mkEarSt :: (Ord n, Ord t) => S.Set (State n t) -> EarSt n t
mkEarSt s = EarSt
    { done = S.empty
    , waiting = Q.fromList
        [ p :-> prio p
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


-- | Check if the state is not already processed (i.e. in one of the
-- done-related maps).
isProcessed :: (Ord n, Ord t) => State n t -> EarSt n t -> Bool
isProcessed pE EarSt{..} =
    S.member pE done


-- | Add the state to the waiting queue.  Check first if it is
-- not already in the set of processed (`done') states.
pushState :: (Ord t, Ord n) => State n t -> Earley n t ()
pushState p = RWS.state $ \s ->
    let waiting' = if isProcessed p s
            then waiting s
            else Q.insert p (prio p) (waiting s)
    in  ((), s {waiting = waiting'})


-- | Remove a state from the queue.  In future, the queue
-- will be probably replaced by a priority queue which will allow
-- to order the computations in some smarter way.
popState :: (Ord t, Ord n) => Earley n t (Maybe (State n t))
popState = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (x :-> _, s) -> (Just x, st {waiting = s})


-- | Add the state to the set of processed (`done') states.
saveState :: (Ord t, Ord n) => State n t -> Earley n t ()
saveState p =
    RWS.state $ \s -> ((), doit s)
  where
    doit st = st {done = S.insert p (done st)}
--     doit st@EarSt{..} = st
--       { doneExpEnd = case expects' p of
--           Just (x, _) -> M.insertWith S.union (x, end p)
--                               (S.singleton p) doneExpEnd
--           Nothing -> doneExpEnd
--       , doneProSpan = if completed p
--           then M.insertWith S.union (nonTerm $ root p, beg p, end p)
--                (S.singleton p) doneProSpan
--           else doneProSpan }


-- | Return all processed states which:
-- * expect a given label,
-- * end on the given position.
expectEnd
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (State n t)
expectEnd x i = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- S.toList done
        , (y, _) <- maybeToList (expects' q)
        , x == y, end q == i ]


-- | Return all processed items which:
-- * are fully parsed,
-- * provide a given label,
-- * begin on the given position.
provideBeg
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (State n t)
provideBeg x i = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- S.toList done
        , completed q, root q == x
        , beg q == i ]


-- | Return all processed items which:
-- * are fully parsed,
-- * provide a label with a given non-terminal,
-- * begin on the given position,
provideBeg'
    :: (Ord n, Ord t) => n -> Pos
    -> P.ListT (Earley n t) (State n t)
provideBeg' x i = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- S.toList done
        , completed q
        , nonTerm (root q) == x
        , beg q == i ]


-- | Return all completed states with:
-- * the given root non-terminal value
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (State n t)
rootSpan x (i, j) = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- S.toList done
        , completed q
        , beg q == i, end q == j
        , nonTerm (root q) == x ]


-- | Return all fully parsed items:
-- * top-level and representing auxiliary trees,
-- * modifying the given source non-terminal,
-- * with the given gap.
auxModifyGap
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (State n t)
auxModifyGap x gapSpan = do
    EarSt{..} <- lift RWS.get
    each
        [ q | q <- S.toList done
        , completed q, topLevel q
        , gap q == Just gapSpan
        , nonTerm (root q) == x ]


-- -- | A utility function.
-- listValues
--     :: (Monad m, Ord a)
--     => a -> M.Map a (S.Set b)
--     -> P.ListT m b
-- listValues x m = each $ case M.lookup x m of
--     Nothing -> []
--     Just s -> S.toList s


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- | Try to perform SCAN on the given state.
tryScan :: (VOrd t, VOrd n) => State n t -> Earley n t ()
tryScan p = void $ runMaybeT $ do
    -- check that the state expects a terminal on the right
    (Term t, right') <- expects p
    -- read the word immediately following the ending position of
    -- the state
    c <- readInput $ end p
    -- make sure that what the rule expects is consistent with
    -- the input
    guard $ c == t
    -- construct the resultant state
    let p' = p
            { end = end p + 1
            , left = Term t : left p
            , right = right' }
    -- print logging information
    lift . lift $ do
        putStr "[S]  " >> printState p
        putStr "  :  " >> printState p'
    -- push the resulting state into the waiting queue
    lift $ pushState p'


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the state (only if fully parsed) to complement
-- (=> substitution) other rules.
trySubst :: (VOrd t, VOrd n) => State n t -> Earley n t ()
trySubst p = void $ P.runListT $ do
    -- Make sure that `p' is a fully-parsed regular rule.
    -- Checking that it is regular is not actually necessary here
    -- because, otherwise, `expectEnd` should return nothing.
    -- But still, it should speed up things to check it here.
    guard $ completed p && regular p
    -- find rules which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    q <- expectEnd (root p) (beg p)
    -- TODO: what's the point of checking what `q` expects?  After all, we
    -- already know that it expects what `p` provides, i.e. `root p`?
    (r@NonT{}, _) <- some $ expects' q
    -- construct the resultant state
    let q' = q
            { end = end p
            , left  = r : left q
            , right = tail (right q) }
    -- print logging information
    lift . lift $ do
        putStr "[U]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


-- | Reversed `trySubst` version.  Try to completent the item with another
-- fully parsed item.
trySubst' :: (VOrd t, VOrd n) => State n t -> Earley n t ()
trySubst' q = void $ P.runListT $ do
    -- Make sure that `p' is a fully-parsed regular rule.  Checking that it is
    -- regular is not actually necessary here because, otherwise, `expectEnd`
    -- should return nothing.  But still, it should speed up things to check
    -- it here.

    -- Learn what `q` actually expects.  By doing that we also make sure that
    -- `q` is not a fully parsed item.
    (r@NonT{}, _) <- some $ expects' q
    -- Find processed items which begin where `q` ends and which provide the
    -- non-terminal expected by `q`.
    p <- provideBeg r (end q)
    -- construct the resultant state
    let q' = q
            { end = end p
            , left  = r : left q
            , right = tail (right q) }
    -- print logging information
    lift . lift $ do
        putStr "[U'] " >> printState q
        putStr "  +  " >> printState p
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


--------------------------------------------------
-- ADJOIN INIT
--------------------------------------------------


-- | `tryAdjoinInit p q':
-- * `p' is a completed state (regular or auxiliary)
-- * `q' not completed and expects a *real* foot
tryAdjoinInit :: (VOrd n, VOrd t) => State n t -> Earley n t ()
tryAdjoinInit p = void $ P.runListT $ do
    -- make sure that `p' is fully-matched and that it is either
    -- a regular rule or an intermediate auxiliary rule ((<=)
    -- used as an implication here!); look at `tryAdjoinTerm`
    -- for motivations.
    guard $ completed p && auxiliary p <= subLevel p
    -- find all rules which expect a real foot (with ID == Nothing)
    -- and which end where `p' begins.
    let u = nonTerm (root p)
    q <- expectEnd (AuxFoot u) (beg p)
    (r@AuxFoot{}, _) <- some $ expects' q
    -- construct the resultant state
    let q' = q
            { gap = Just (beg p, end p)
            , end = end p
            , left = r : left q
            , right = tail (right q) }
    -- print logging information
    lift . lift $ do
        putStr "[A]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


-- | Reverse of `tryAdjoinInit` where the given state `q`
-- expects a real foot.
-- * `q' not completed and expects a *real* foot
-- * `p' is a completed state (regular or auxiliary)
tryAdjoinInit' :: (VOrd n, VOrd t) => State n t -> Earley n t ()
tryAdjoinInit' q = void $ P.runListT $ do
    -- Retrieve the foot expected by `q`.
    (r@(AuxFoot u), _) <- some $ expects' q
    -- Find all fully parsed items which provide the given source
    -- non-terminal and which begin where `q` ends.
    p <- provideBeg' u (end q)
    -- Apart from that, retrieved items must not be auxiliary top-level.
    guard $ auxiliary p <= subLevel p
    -- Construct the resultant state.
    let q' = q
            { gap   = Just (beg p, end p)
            , end   = end p
            , left  = r : left q
            , right = tail (right q) }
    -- print logging information
    lift . lift $ do
        putStr "[A'] " >> printState q
        putStr "  +  " >> printState p
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


--------------------------------------------------
-- ADJOIN CONT
--------------------------------------------------


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
tryAdjoinCont :: (VOrd n, VOrd t) => State  n t -> Earley n t ()
tryAdjoinCont p = void $ P.runListT $ do
    -- Make sure that `p' is a completed, sub-level auxiliary rule.
    -- Note that it is also ensured a few lines below that the
    -- rule is sub-level auxiliary.
    guard $ completed p && subLevel p && auxiliary p
    -- find all rules which expect a foot provided by `p'
    -- and which end where `p' begins.
    q <- expectEnd (root p) (beg p)
    (r@AuxVert{}, _) <- some $ expects' q
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = q
            { gap = gap p, end = end p
            , left  = r : left q
            , right = tail $ right q }
    -- logging info
    lift . lift $ do
        putStr "[B]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'



-- | Reversed `tryAdjoinCont`.
tryAdjoinCont' :: (VOrd n, VOrd t) => State  n t -> Earley n t ()
tryAdjoinCont' q = void $ P.runListT $ do
    -- Retrieve the auxiliary vertebrea expected by `q`
    (r@AuxVert{}, _) <- some $ expects' q
    -- Find all fully parsed items which provide the given label
    -- and which begin where `q` ends.
    p <- provideBeg r (end q)
    -- Construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = q
            { gap = gap p, end = end p
            , left  = r : left q
            , right = tail $ right q }
    -- logging info
    lift . lift $ do
        putStr "[B'] " >> printState q
        putStr "  +  " >> printState p
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


--------------------------------------------------
-- ADJOIN TERM
--------------------------------------------------


-- | Adjoin a fully-parsed auxiliary state `p` to a partially parsed
-- tree represented by a fully parsed rule/state `q`.
tryAdjoinTerm :: (VOrd t, VOrd n) => State n t -> Earley n t ()
tryAdjoinTerm p = void $ P.runListT $ do
    -- make sure that `p' is a completed, top-level state ...
    guard $ completed p && topLevel p
    -- ... and that it is an auxiliary state (by definition only
    -- auxiliary states have gaps)
    theGap <- each $ maybeToList $ gap p
    -- take all completed rules with a given span
    -- and a given root non-terminal (IDs irrelevant)
    q <- rootSpan (nonTerm $ root p) theGap
    -- Make sure that `q' is completed as well and that it is either
    -- a regular (perhaps intermediate) rule or an intermediate
    -- auxiliary rule (note that (<=) is used as an implication
    -- here and can be read as `implies`).
    -- (TODO: we don't have to check if `q` is completed, it stems
    -- from the fact that it is pulled using `rootSpan`.)
    guard $ completed q && auxiliary q <= subLevel q
    -- construct the resulting state
    let q' = q { beg = beg p
               , end = end p }
    lift . lift $ do
        putStr "[C]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    lift $ pushState q'


-- | Reversed `tryAdjoinTerm`.  TODO: find a test case which proves that this
-- is needed.
tryAdjoinTerm' :: (VOrd t, VOrd n) => State n t -> Earley n t ()
tryAdjoinTerm' q = void $ P.runListT $ do
    -- Ensure that `q` is fully parsed and not top-level auxiliary
    guard $ completed q && auxiliary q <= subLevel q
    -- Retrieve all completed, top-level items representing auxiliary trees
    -- which have a specific gap and modify a specific source non-terminal.
    p <- auxModifyGap (nonTerm $ root q) (beg q, end q)
    -- Construct the resulting state:
    let q' = q { beg = beg p
               , end = end p }
    lift . lift $ do
        putStr "[C'] " >> printState q
        putStr "  +  " >> printState p
        putStr "  :  " >> printState q'
    lift $ pushState q'


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
    done <- earley gram xs
    return $ (not.null) (complete done)
  where
    n = length xs
    complete sts =
        [ True | st <- S.toList sts
        , beg st == 0, end st == n
        , regular st, completed st ]


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
    complete sts =
        [ True | st <- S.toList sts
        , beg st == 0, end st == n
        , root st == NonT start Nothing
        , regular st, completed st ]


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [t]                  -- ^ Input sentence
    -> IO (S.Set (State n t))
earley gram xs =
    done . fst <$> RWS.execRWST loop xs st0
  where
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt $ S.fromList -- $ Reid.runReid $ mapM reidState
        [ State
            { root  = headR
            , left  = []
            , right = bodyR
            , beg   = i
            , end   = i
            , gap   = Nothing }
        | Rule{..} <- S.toList gram
        , i <- [0 .. length xs - 1] ]
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popState >>= \mp -> case mp of
        Nothing -> return ()
        Just p -> step p >> loop
            -- lift $ case p of
            --     (StateE q) -> putStr "POPED: " >> printState q
            -- step p >> loop


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step :: (VOrd t, VOrd n) => State n t -> Earley n t ()
step p = do
    mapM_ ($p)
      [ tryScan
      , trySubst
      , trySubst'
      , tryAdjoinInit
      , tryAdjoinInit'
      , tryAdjoinCont
      , tryAdjoinCont'
      , tryAdjoinTerm ]
      -- , tryAdjoinTerm' ]
    saveState p


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
