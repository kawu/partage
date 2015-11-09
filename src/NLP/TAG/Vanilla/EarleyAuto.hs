{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}


-- | Earley-style parsing with automaton-based grammar
-- representation.


module NLP.TAG.Vanilla.EarleyAuto where


import           Control.Applicative        ((<$>), (<*>))
import           Control.Monad              (guard, void)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS

-- import           Data.List                  (intercalate)
import           Data.Maybe     ( isJust, isNothing, mapMaybe
                                , listToMaybe, maybeToList)
-- import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import qualified Pipes                      as P

import           Data.DAWG.Gen.Types (ID)
import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.TAG.Vanilla.Core
import           NLP.TAG.Vanilla.Rule
                                ( Lab(..), Rule(..) )
import           NLP.TAG.Vanilla.Automaton



--------------------------------------------------
-- CHART STATE ...
--
-- ... and chart extending operations
--------------------------------------------------


-- | Chart item.
data Item n t = Item {
    -- | State of the underlying automaton.
      state :: ID
    -- | The starting position.
    , beg   :: Pos
    -- | The ending position (or rather the position of the dot).
    , end   :: Pos
    -- | Coordinates of the gap (if applies)
    , gap   :: Maybe (Pos, Pos)
    } deriving (Show, Eq, Ord)


-- | Does it represent regular rules?
regular :: Item n t -> Bool
regular = isNothing . gap


-- | Does it represent auxiliary rules?
auxiliary :: Item n t -> Bool
auxiliary = isJust . gap


-- | Is the rule with the given head top-level?
topLevel :: Lab n t -> Bool
topLevel x = case x of
    NonT{..}  -> isNothing labID
    AuxRoot{} -> True
    _         -> False
    

-- | Print the state.
printItem :: (View n, View t) => Item n t -> IO ()
printItem Item{..} = do
    putStr "("
    putStr $ show state
    putStr ", "
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
    putStrLn ")"


-- | Priority type.
type Prio = Int


-- | Priority of a state.  Crucial for the algorithm -- states have
-- to be removed from the queue in a specific order.
prio :: Item n t -> Prio
prio p = end p


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt {
    -- | The underlying automaton.
      automat :: DAWG n t
--     -- | Items which expect a specific label and which end on a
--     -- specific position.
--       doneExpEnd :: M.Map (Lab n t, Pos) (S.Set (State n t))
--     -- | Rules providing a specific non-terminal in the root
--     -- and spanning over a given range.
--     , doneProSpan :: M.Map (n, Pos, Pos) (S.Set (State n t))
    -- | Processed items.
    , done :: S.Set (Item n t)
    -- | The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    , waiting :: Q.PSQ (Item n t) Prio }


-- | Make an initial `EarSt` from a set of states.
mkEarSt
    :: (Ord n, Ord t)
    => DAWG n t
    -> S.Set (Item n t)
    -> (EarSt n t)
mkEarSt dag s = EarSt
    { automat = dag
    , done = S.empty
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
isProcessed :: (Ord n, Ord t) => Item n t -> EarSt n t -> Bool
isProcessed p EarSt{..} = S.member p done


-- | Add item to the waiting queue.  Check first if it is
-- not already in the set of processed (`done') states.
pushItem :: (Ord t, Ord n) => Item n t -> Earley n t ()
pushItem p = RWS.state $ \s ->
    let waiting' = if isProcessed p s
            then waiting s
            else Q.insert p (prio p) (waiting s)
    in  ((), s {waiting = waiting'})


-- | Remove a state from the queue.  In future, the queue
-- will be probably replaced by a priority queue which will allow
-- to order the computations in some smarter way.
popItem :: (Ord t, Ord n) => Earley n t (Maybe (Item n t))
popItem = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (x :-> _, s) -> (Just x, st {waiting = s})


-- | Add the state to the set of processed (`done') states.
saveItem :: (Ord t, Ord n) => Item n t -> Earley n t ()
saveItem p =
    RWS.state $ \s -> ((), s {done = S.insert p (done s)})
--     RWS.state $ \s -> ((), doit s)
--   where
--     doit st@EarSt{..} = st
--       { doneExpEnd = case expects' p of
--           Just (x, _) -> M.insertWith S.union (x, end p)
--                               (S.singleton p) doneExpEnd
--           Nothing -> doneExpEnd
--       , doneProSpan = if completed p
--           then M.insertWith S.union (nonTerm $ root p, beg p, end p)
--                (S.singleton p) doneProSpan
--           else doneProSpan }



-- | Return all completed states which:
-- * expect a given label,
-- * end on the given position.
expectEnd
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Item n t)
expectEnd x i = do
    EarSt{..} <- lift RWS.get
    p <- each (S.toList done)
    guard $ isJust $ D.follow (state p) (Body x) automat
    guard $ end p == i
    return p


-- | Return all completed items with:
-- * the given root non-terminal value (but not top-level
--   auxiliary)
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Item n t)
rootSpan x (i, j) = do
    EarSt{..} <- lift RWS.get
    p <- each (S.toList done)
    guard $ beg p == i && end p == j
    guard . not $ null
        [ True
        | (Root sym, _)
            <- D.edges (state p) automat
        , check sym ]
    return p
  where
    check (Term _)    = False
    check (AuxRoot _) = False
    check sym         = nonTerm sym == x


--------------------------------------------------
-- New Automaton-Based Primitives
--------------------------------------------------


-- | Follow the given terminal in the underlying automaton.
followTerm :: (Ord n, Ord t) => ID -> t -> MaybeT (Earley n t) ID
followTerm i c = do
    -- get the underlying automaton
    auto <- RWS.gets automat
    -- follow the label
    maybeT $ D.follow i (Body $ Term c) auto


-- | Follow the given body transition in the underlying automaton.
-- It represents the transition function of the automaton.
--
-- TODO: It should be merged with `followTerm` and return simple
-- Maybe within the Earley monad.
follow :: (Ord n, Ord t) => ID -> Lab n t -> P.ListT (Earley n t) ID
follow i x = do
    -- get the underlying automaton
    auto <- RWS.gets automat
    -- follow the label
    some $ D.follow i (Body x) auto


-- | Rule heads outgoing from the given automaton state.
heads :: ID -> P.ListT (Earley n t) (Lab n t)
heads i = do
    auto <- RWS.gets automat
    let mayHead (x, _) = case x of
            Body _  -> Nothing
            Root y -> Just y
    each $ mapMaybe mayHead $ D.edges i auto


-- | Rule body elements outgoing from the given automaton state.
elems :: ID -> P.ListT (Earley n t) (Lab n t)
elems i = do
    auto <- RWS.gets automat
    let mayBody (x, _) = case x of
            Body y  -> Just y
            Root _ -> Nothing
    each $ mapMaybe mayBody $ D.edges i auto


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- | Try to perform SCAN on the given state.
tryScan :: (VOrd t, VOrd n) => Item n t -> Earley n t ()
tryScan p = void $ runMaybeT $ do
    -- read the word immediately following the ending position of
    -- the state
    c <- readInput $ end p
    -- follow appropriate terminal transition outgoin from the
    -- given automaton state
    j <- followTerm (state p) c
    -- construct the resultant state
    let q = p {state = j, end = end p + 1}
    -- print logging information
    lift . lift $ do
        putStr "[S]  " >> printItem p
        putStr "  :  " >> printItem q
    -- push the resulting state into the waiting queue
    lift $ pushItem q


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the state (only if fully parsed) to complement
-- (=> substitution) other rules.
trySubst :: (VOrd t, VOrd n) => Item n t -> Earley n t ()
trySubst p = void $ P.runListT $ do
    -- make sure that `p' represents regular rules
    guard $ regular p
    -- take all the head symbols outgoing from `p`
    x <- heads (state p)
    -- find items which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    q <- expectEnd x (beg p)
    -- follow the transition symbol
    j <- follow (state q) x
    -- construct the resultant state
    let q' = q {state = j, end = end p}
    -- print logging information
    lift . lift $ do
        putStr "[U]  " >> printItem p
        putStr "  +  " >> printItem q
        putStr "  :  " >> printItem q'
    -- push the resulting state into the waiting queue
    lift $ pushItem q'


--------------------------------------------------
-- FOOT ADJOIN
--------------------------------------------------


-- | `tryAdjoinInit p q':
-- * `p' is a completed state (regular or auxiliary)
-- * `q' not completed and expects a *real* foot
tryAdjoinInit :: (VOrd n, VOrd t) => Item n t -> Earley n t ()
tryAdjoinInit p = void $ P.runListT $ do
    -- take all head symbols outgoing from `p`
    x <- heads (state p)
    -- make sure that the corresponding rule is either regular or
    -- intermediate auxiliary ((<=) used as implication here)
    guard $ auxiliary p <= not (topLevel x)
    -- find all rules which expect a foot with the given symbol
    -- and which end where `p` begins
    let foot = AuxFoot $ nonTerm x
    q <- expectEnd foot (beg p)
    -- follow the foot
    j <- follow (state q) foot
    -- construct the resultant state
    let q' = q { state = j
               , gap = Just (beg p, end p)
               , end = end p }
    -- print logging information
    lift . lift $ do
        putStr "[A]  " >> printItem p
        putStr "  +  " >> printItem q
        putStr "  :  " >> printItem q'
    -- push the resulting state into the waiting queue
    lift $ pushItem q'


--------------------------------------------------
-- INTERNAL ADJOIN
--------------------------------------------------


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
tryAdjoinCont :: (VOrd n, VOrd t) => Item  n t -> Earley n t ()
tryAdjoinCont p = void $ P.runListT $ do
    -- make sure that `p' is an auxiliary item
    guard $ auxiliary p
    -- take all head symbols outgoing from `p` and make sure they
    -- are not top-level (internal spine non-terminals)
    x <- heads (state p)
    guard $ not $ topLevel x
    -- find all rules which expect a spine non-terminal provided
    -- by `p' and which end where `p' begins
    q <- expectEnd x (beg p)
    -- follow the spine non-terminal
    j <- follow (state q) x
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = q { state = j
               , gap = gap p
               , end = end p }
    -- logging info
    lift . lift $ do
        putStr "[B]  " >> printItem p
        putStr "  +  " >> printItem q
        putStr "  :  " >> printItem q'
    -- push the resulting state into the waiting queue
    lift $ pushItem q'


--------------------------------------------------
-- ROOT ADJOIN
--------------------------------------------------


-- | Adjoin a fully-parsed auxiliary state `p` to a partially parsed
-- tree represented by a fully parsed rule/state `q`.
tryAdjoinTerm :: (VOrd t, VOrd n) => Item n t -> Earley n t ()
tryAdjoinTerm q = void $ P.runListT $ do
    -- make sure that it is an auxiliary item (by definition only
    -- auxiliary states have gaps)
    (gapBeg, gapEnd) <- each $ maybeToList $ gap q
    -- take all the head symbols outgoing from `q` and make sure
    -- that they are top-level
    x <- heads (state q)
    guard $ topLevel x
    -- take all completed rules with a given span
    -- and a given root non-terminal (IDs irrelevant)
    p <- rootSpan (nonTerm x) (gapBeg, gapEnd)
    -- construct the new state
    let p' = p { beg = beg q
               , end = end q }
    lift . lift $ do
        putStr "[C]  " >> printItem q
        putStr "  +  " >> printItem p
        putStr "  :  " >> printItem p'
    lift $ pushItem p'


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
    complete sts =
        [ True | st <- S.toList sts
        , beg st == 0, end st == n
        , gap st == Nothing ]


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
    (done, auto) <- earley gram xs
    return $ (not.null) (complete done auto)
  where
    n = length xs
    complete items auto =
        [ True | item <- S.toList items
        , beg item == 0, end item == n
        , isJust $ D.follow
            (state item)
            (Root $ NonT start Nothing)
            auto ]


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [t]                  -- ^ Input sentence
    -> IO (S.Set (Item n t), DAWG n t)
earley gram xs =
    ((,) <$> done <*> automat) . fst <$> RWS.execRWST loop xs st0
  where
    -- the automaton
    dawg = buildAuto gram
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt dawg $ S.fromList
        [ Item
            { state = D.root dawg
            , beg   = i
            , end   = i
            , gap   = Nothing }
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
step p = do
    sequence_ $ map ($p)
      [ tryScan, trySubst
      , tryAdjoinInit
      , tryAdjoinCont
      , tryAdjoinTerm ]
    saveItem p


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
