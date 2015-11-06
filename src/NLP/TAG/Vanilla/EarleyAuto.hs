{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}


-- | Earley-style parsing with automaton-based grammar
-- representation.


module NLP.TAG.Vanilla.EarleyAuto where


import           Control.Applicative        ((<$>))
import           Control.Monad              (guard, void)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS

import           Data.List                  (intercalate)
import           Data.Maybe     ( isJust, isNothing, mapMaybe
                                , listToMaybe, maybeToList)
import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import qualified Pipes                      as P

import           Data.DAWG.Gen.Types (ID)
import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.TAG.Vanilla.Core
import           NLP.TAG.Vanilla.Rule
                                ( Lab(..), viewLab, Rule(..) )
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


-- -- | Parsing state: processed initial rule elements and the elements
-- -- yet to process.
-- data State n t = State {
--     -- | The head of the rule represented by the state.
--     -- TODO: Not a terminal nor a foot.
--       root  :: Lab n t
--     -- | The list of processed elements of the rule, stored in an
--     -- inverse order.
--     , left  :: [Lab n t]
--     -- | The list of elements yet to process.
--     , right :: [Lab n t]
--     -- | The starting position.
--     , beg   :: Pos
--     -- | The ending position (or rather the position of the dot).
--     , end   :: Pos
--     -- | Coordinates of the gap (if applies)
--     , gap   :: Maybe (Pos, Pos)
--     } deriving (Show, Eq, Ord)
-- 
-- 
-- -- | Is it a completed (fully matched) item?
-- -- NOTE: It doesn't make sense now, from a auto. state both
-- -- head and body transitions can outgo.
-- completed :: Item n t -> Bool
-- completed = null . right


-- | Does it represent regular rules?
regular :: Item n t -> Bool
regular = isNothing . gap


-- | Does it represent auxiliary rules?
auxiliary :: Item n t -> Bool
auxiliary = isJust . gap


-- -- | Is it top-level?  All top-level states (regular or
-- -- auxiliary) have an underspecified ID in the root symbol.
-- topLevel :: State n t -> Bool
-- -- topLevel = isNothing . ide . root
-- topLevel = not . subLevel


-- | Is the rule with the given head top-level?
topLevel :: Lab n t -> Bool
topLevel x = case x of
    NonT{..}  -> isJust labID
    AuxRoot{} -> True
    _         -> False
    

-- -- | Deconstruct the right part of the state (i.e. labels yet to
-- -- process) within the MaybeT monad.
-- expects
--     :: Monad m
--     => State n t
--     -> MaybeT m (Lab n t, [Lab n t])
-- expects = maybeT . expects'
-- 
-- 
-- -- | Deconstruct the right part of the state (i.e. labels yet to
-- -- process). 
-- expects'
--     :: State n t
--     -> Maybe (Lab n t, [Lab n t])
-- expects' = decoList . right


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


-- | Return all completed states which:
-- * expect a given label,
-- * end on the given position.
expectEnd
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Item n t)
expectEnd x i = do
    EarSt{..} <- lift RWS.get
    p <- each (S.toList done)
    guard $ isJust $ D.follow (state p) (Left x) automat
    guard $ end p == i
    return p
--   listValues (x, i) doneExpEnd



-- -- | Remove a state from the queue.  In future, the queue
-- -- will be probably replaced by a priority queue which will allow
-- -- to order the computations in some smarter way.
-- popState :: (Ord t, Ord n) => Earley n t (Maybe (State n t))
-- popState = RWS.state $ \st -> case Q.minView (waiting st) of
--     Nothing -> (Nothing, st)
--     Just (x :-> _, s) -> (Just x, st {waiting = s})
-- 
-- 
-- -- | Add the state to the set of processed (`done') states.
-- saveState :: (Ord t, Ord n) => State n t -> Earley n t ()
-- saveState p =
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


-- -- | Return all completed states with:
-- -- * the given root non-terminal value
-- -- * the given span
-- rootSpan
--     :: Ord n => n -> (Pos, Pos)
--     -> P.ListT (Earley n t) (State n t)
-- rootSpan x (i, j) = do
--   EarSt{..} <- lift RWS.get
--   listValues (x, i, j) doneProSpan
-- 
-- 
-- -- | A utility function.
-- listValues
--     :: (Monad m, Ord a)
--     => a -> M.Map a (S.Set b)
--     -> P.ListT m b
-- listValues x m = each $ case M.lookup x m of
--     Nothing -> []
--     Just s -> S.toList s


--------------------------------------------------
-- New Automaton-Based Primitives
--------------------------------------------------


-- | Follow the given terminal in the underlying automaton.
followTerm :: (Ord n, Ord t) => ID -> t -> MaybeT (Earley n t) ID
followTerm i c = do
    -- get the underlying automaton
    auto <- RWS.gets automat
    -- follow the label
    maybeT $ D.follow i (Left $ Term c) auto


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
    some $ D.follow i (Left x) auto


-- | Rule heads outgoing from the given automaton state.
heads :: ID -> P.ListT (Earley n t) (Lab n t)
heads i = do
    auto <- RWS.gets automat
    let mayHead (x, _) = case x of
            Left _  -> Nothing
            Right y -> Just y
    each $ mapMaybe mayHead $ D.edges i auto


-- | Rule body elements outgoing from the given automaton state.
elems :: ID -> P.ListT (Earley n t) (Lab n t)
elems i = do
    auto <- RWS.gets automat
    let mayBody (x, _) = case x of
            Left y  -> Just y
            Right _ -> Nothing
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
-- ADJOIN
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


-- -- | `tryAdjoinCont p q':
-- -- * `p' is a completed, auxiliary state
-- -- * `q' not completed and expects a *dummy* foot
-- tryAdjoinCont :: (VOrd n, VOrd t) => State  n t -> Earley n t ()
-- tryAdjoinCont p = void $ P.runListT $ do
--     -- make sure that `p' is a completed, sub-level auxiliary rule
--     guard $ completed p && subLevel p && auxiliary p
--     -- find all rules which expect a foot provided by `p'
--     -- and which end where `p' begins.
--     q <- expectEnd (root p) (beg p)
--     (r@AuxVert{}, _) <- some $ expects' q
--     -- construct the resulting state; the span of the gap of the
--     -- inner state `p' is copied to the outer state based on `q'
--     let q' = q
--             { gap = gap p, end = end p
--             , root  = root q 
--             , left  = r : left q
--             , right = tail $ right q }
--     -- logging info
--     lift . lift $ do
--         putStr "[B]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     -- push the resulting state into the waiting queue
--     lift $ pushState q'
-- 
-- 
-- -- | Adjoin a fully-parsed auxiliary state `p` to a partially parsed
-- -- tree represented by a fully parsed rule/state `q`.
-- tryAdjoinTerm :: (VOrd t, VOrd n) => State n t -> Earley n t ()
-- tryAdjoinTerm p = void $ P.runListT $ do
--     -- make sure that `p' is a completed, top-level state ...
--     guard $ completed p && topLevel p
--     -- ... and that it is an auxiliary state (by definition only
--     -- auxiliary states have gaps)
--     (gapBeg, gapEnd) <- each $ maybeToList $ gap p
--     -- it is top-level, so we can also make sure that the
--     -- root is an AuxRoot.
--     -- pRoot@AuxRoot{} <- some $ Just $ root p
--     -- take all completed rules with a given span
--     -- and a given root non-terminal (IDs irrelevant)
--     q <- rootSpan (nonTerm $ root p) (gapBeg, gapEnd)
--     -- make sure that `q' is completed as well and that it is either
--     -- a regular (perhaps intermediate) rule or an intermediate
--     -- auxiliary rule (note that (<=) is used as an implication
--     -- here and can be read as `implies`).
--     -- NOTE: root auxiliary rules are of no interest to us but they
--     -- are all the same taken into account in an indirect manner.
--     -- We can assume here that such rules are already adjoined thus
--     -- creating either regular or intermediate auxiliary.
--     -- NOTE: similar reasoning can be used to explain why foot
--     -- auxiliary rules are likewise ignored.
--     -- Q: don't get this second remark -- how could a foot node
--     -- be a root of a state/rule `q`?  What `foot auxiliary rules`
--     -- could actually mean?
--     guard $ completed q && auxiliary q <= subLevel q
--     -- TODO: it seems that some of the constraints given above
--     -- follow from the code below:
--     qRoot <- some $ case root q of
--         x@NonT{}    -> Just x
--         x@AuxVert{} -> Just x
--         _           -> Nothing
--     newRoot <- some $ case qRoot of
--         NonT{} -> Just $ NonT
--             { nonTerm = nonTerm qRoot
--             , labID = labID qRoot }
--         AuxVert{} -> Just $ AuxVert
--             { nonTerm = nonTerm qRoot
--             , symID = symID qRoot }
--         _           -> Nothing
--     let q' = q
--             { root = newRoot
--             , left  = left q
--             , right = right q
--             , beg = beg p
--             , end = end p }
--     lift . lift $ do
--         putStr "[C]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     lift $ pushState q'
-- 
-- 
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
--         , beg st == 0, end st == n ]
-- 
-- 
-- -- | Does the given grammar generate the given sentence from the
-- -- given non-terminal symbol (i.e. from an initial tree with this
-- -- symbol in its root)?  Uses the `earley` algorithm under the
-- -- hood.
-- recognizeFrom
--     :: (VOrd t, VOrd n)
--     => S.Set (Rule n t)     -- ^ The grammar (set of rules)
--     -> n                    -- ^ The start symbol
--     -> [t]                  -- ^ Input sentence
--     -> IO Bool
-- recognizeFrom gram start xs = do
--     done <- earley gram xs
--     return $ (not.null) (complete done)
--   where
--     n = length xs
--     complete sts =
--         [ True | st <- S.toList sts
--         , beg st == 0, end st == n
--         , root st == NonT start Nothing ]
-- 
-- 
-- -- | Perform the earley-style computation given the grammar and
-- -- the input sentence.
-- earley
--     :: (VOrd t, VOrd n)
--     => S.Set (Rule n t)     -- ^ The grammar (set of rules)
--     -> [t]                  -- ^ Input sentence
--     -> IO (S.Set (State n t))
-- earley gram xs =
--     agregate . doneProSpan . fst <$> RWS.execRWST loop xs st0
--     -- void $ RWS.execRWST loop xs st0
--   where
--     -- Agregate the results from the `doneProSpan` part of the
--     -- result.
--     agregate = S.unions . M.elems
--     -- we put in the initial state all the states with the dot on
--     -- the left of the body of the rule (-> left = []) on all
--     -- positions of the input sentence.
--     st0 = mkEarSt $ S.fromList -- $ Reid.runReid $ mapM reidState
--         [ State
--             { root  = headR
--             , left  = []
--             , right = bodyR
--             , beg   = i
--             , end   = i
--             , gap   = Nothing }
--         | Rule{..} <- S.toList gram
--         , i <- [0 .. length xs - 1] ]
--     -- the computation is performed as long as the waiting queue
--     -- is non-empty.
--     loop = popState >>= \mp -> case mp of
--         Nothing -> return ()
--         Just p -> do
--             -- lift $ case p of
--             --     (StateE q) -> putStr "POPED: " >> printState q
--             step p >> loop
-- 
-- 
-- -- | Step of the algorithm loop.  `p' is the state popped up from
-- -- the queue.
-- step :: (VOrd t, VOrd n) => State n t -> Earley n t ()
-- step p = do
--     sequence_ $ map ($p)
--       [ tryScan, trySubst
--       , tryAdjoinInit
--       , tryAdjoinCont
--       , tryAdjoinTerm ]
--     saveState p
-- 
-- 
-- --------------------------------------------------
-- -- Utilities
-- --------------------------------------------------
-- 
-- 
-- -- | Deconstruct list.  Utility function.  Similar to `unCons`.
-- decoList :: [a] -> Maybe (a, [a])
-- decoList [] = Nothing
-- decoList (y:ys) = Just (y, ys)


-- | MaybeT transformer.
maybeT :: Monad m => Maybe a -> MaybeT m a
maybeT = MaybeT . return


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each


-- | ListT from a maybe.
some :: Monad m => Maybe a -> P.ListT m a
some = each . maybeToList
