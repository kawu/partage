{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}


-- | Earley-style parsing together with prediction rules.


module NLP.TAG.Vanilla.Earley.Pred where


import           Control.Applicative        ((<$>))
import           Control.Monad              (guard, void, when)
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS

import           Data.List                  (intercalate)
import           Data.Maybe     ( isJust, isNothing
                                , listToMaybe, maybeToList)
import qualified Data.Map.Strict            as M
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
    putStr $ intercalate " " $
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
prio p = end p


--------------------------------------------------
-- Efficient Rule Lookup
--------------------------------------------------


-- | The grammar stored in a form which allows efficient rule
-- lookup based on head non-terminal values.
type Gram n t = M.Map n (M.Map (Lab n t) (S.Set (Rule n t)))


-- | Construct the grammar from the set of rules.
mkGram :: (Ord n, Ord t) => S.Set (Rule n t) -> Gram n t
mkGram rules = M.fromListWith addRule
    [ ( nonTerm (headR r)
      , M.singleton (headR r) (S.singleton r) )
    | r <- S.toList rules ]
  where
    addRule = M.unionWith S.union


--------------------------------------------------
-- Earley monad
--------------------------------------------------



-- | The state of the earley monad.
data EarSt n t = EarSt {
    -- | The underlying grammar (needed for prediction)
      gramMap    :: Gram n t
    -- | Rules which expect a specific label and which end on a
    -- specific position.
    , doneExpEnd :: M.Map (Lab n t, Pos) (S.Set (State n t))
    -- | Rules providing a specific non-terminal in the root
    -- and spanning over a given range.
    , doneProSpan :: M.Map (n, Pos, Pos) (S.Set (State n t))
    -- | The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    , waiting    :: Q.PSQ (State n t) Prio }


-- | Make an initial `EarSt` from a set of states.
mkEarSt
    :: (Ord n, Ord t)
    => S.Set (Rule n t)     -- ^ The set of rules
    -> S.Set n              -- ^ Starting symbols
    -> (EarSt n t)
mkEarSt ruleSet startSet = EarSt
    { gramMap = theGram
    , doneExpEnd = M.empty
    , doneProSpan = M.empty
    , waiting = Q.fromList
        [ p :-> prio p
        | p <- S.toList sts0 ] }
  where
    theGram = mkGram ruleSet
    sts0 = S.fromList
        [ State
            { root  = headR
            , left  = []
            , right = bodyR
            , beg   = 0
            , end   = 0
            , gap   = Nothing }
        -- TODO: we can speed it up by using the
        -- constructed grammar.  
        | Rule{..} <- S.toList ruleSet
        -- make sure it's a regular rule
        , isNonT headR
        -- and that it's a top-level rule
        , isNothing (labID headR)
        -- it must also contain a start symbol
        , nonTerm headR `S.member` startSet ]
    isNonT NonT{} = True
    isNonT _      = False


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
    S.member pE $ chooseSet pE
  where
    chooseSet p = case expects' p of
        Just (x, _) -> M.findWithDefault S.empty
            (x, end p) doneExpEnd
        Nothing -> M.findWithDefault S.empty
            (nonTerm $ root p, beg p, end p) doneProSpan


-- | Add the state to the waiting queue.  Check first if it is
-- not already present in the set of processed (`done') states.
-- Return `False` if it is.
pushState :: (Ord t, Ord n) => State n t -> Earley n t Bool
pushState p = RWS.state $ \s ->
    let (b, waiting') = if isProcessed p s
            then (False, waiting s)
            else (True, Q.insert p (prio p) (waiting s))
    in  (b, s {waiting = waiting'})


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
    doit st@EarSt{..} = st
      { doneExpEnd = case expects' p of
          Just (x, _) -> M.insertWith S.union (x, end p)
                              (S.singleton p) doneExpEnd
          Nothing -> doneExpEnd
      , doneProSpan = if completed p
          then M.insertWith S.union (nonTerm $ root p, beg p, end p)
               (S.singleton p) doneProSpan
          else doneProSpan }


-- | Return all completed states which:
-- * expect a given label,
-- * end on the given position.
expectEnd
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (State n t)
expectEnd x i = do
  EarSt{..} <- lift RWS.get
  listValues (x, i) doneExpEnd


-- | Return all completed states with:
-- * the given root non-terminal value
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (State n t)
rootSpan x (i, j) = do
  EarSt{..} <- lift RWS.get
  listValues (x, i, j) doneProSpan


-- | A utility function.
listValues
    :: (Monad m, Ord a)
    => a -> M.Map a (S.Set b)
    -> P.ListT m b
listValues x m = each $ case M.lookup x m of
    Nothing -> []
    Just s -> S.toList s


-- | Return all rules headed by the given non-terminal.
headedBy
    :: (Ord t, Ord n) => Lab n t
    -> P.ListT (Earley n t) (Rule n t)
headedBy h = do
    EarSt{..} <- lift RWS.get
    let x = nonTerm h
    ruleSet <- some
        (M.lookup x gramMap >>= M.lookup h)
    each $ S.toList ruleSet


-- | Return all rules headed by the given source non-terminal.
headedByN
    :: Ord n => n
    -> P.ListT (Earley n t) (Rule n t)
headedByN x = do
    EarSt{..} <- lift RWS.get
    ruleMap <- some (M.lookup x gramMap)
    each [ r | s <- M.elems ruleMap
             , r <- S.toList s ]


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
    -- make sure that `p' is a fully-parsed regular rule
    guard $ completed p && regular p
    -- find rules which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    q <- expectEnd (root p) (beg p)
    (r@NonT{}, _) <- some $ expects' q
    -- construct the resultant state
    let q' = q
            { end = end p
            , root  = root q
            , left  = r : left q
            , right = tail (right q) }
    -- print logging information
    lift . lift $ do
        putStr "[U]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


-- | Predict pseudo substitution.
predSubst :: (VOrd t, VOrd n) => State n t -> Earley n t ()
predSubst p = void $ P.runListT $ do
    -- make sure that `p' is not fully matched ...
    guard . not $ completed p
    -- ... and that it expects an ordinary (non-auxiliary) non-terminal
    (x, _) <- some $ expects' p
    guard $ ordinary x
    -- identify rules which provide in their heads this very
    -- specific non-terminal
    Rule{..} <- headedBy x
    -- construct the resulting state
    let q = State
            { root  = headR
            , left  = []
            , right = bodyR
            , beg   = end p
            , gap   = Nothing
            , end   = end p }
    b <- lift $ pushState q
    -- print logging information
    when b $ lift . lift $ do
        putStr "[PU] " >> printState p
        putStr "  :  " >> printState q
  where
    ordinary NonT{} = True
    ordinary _      = False
    


--------------------------------------------------
-- ADJOIN
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
    -- before: guard $ completed p
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


-- | Predict foot adjoin.
predAdjoinInit :: (VOrd t, VOrd n) => State n t -> Earley n t ()
predAdjoinInit p = void $ P.runListT $ do
    -- make sure that `p' is regular, not fully matched ...
    -- (in fact it also must be regular, we ask for a foot
    --  a few moments later)
    guard $ (not.completed) p -- && regular p
    -- ... and that it expects a foot
    (x, _) <- some $ expects' p
    guard $ auxFoot x
    -- identify rules which provide non-terminals with the foot
    -- non-terminal and which do not represent roots of auxiliary
    -- trees
    Rule{..} <- headedByN (nonTerm x)
    guard . not $ auxRoot headR
    -- construct the resulting state
    let q = State
            { root  = headR
            , left  = []
            , right = bodyR
            , beg   = end p
            , gap   = Nothing
            , end   = end p }
    b <- lift $ pushState q
    -- print logging information
    when b $ lift . lift $ do
        putStr "[PA] " >> printState p
        putStr "  :  " >> printState q
  where
    -- verify it's a foot non-terminal
    auxFoot AuxFoot{} = True
    auxFoot _         = False
    -- verify that the non-terminal represents a root of an
    -- auxiliary tree
    auxRoot AuxRoot{} = True
    auxRoot _         = False


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
tryAdjoinCont :: (VOrd n, VOrd t) => State  n t -> Earley n t ()
tryAdjoinCont p = void $ P.runListT $ do
    -- make sure that `p' is a completed, sub-level auxiliary rule
    guard $ completed p && subLevel p && auxiliary p
    -- find all rules which expect a foot provided by `p'
    -- and which end where `p' begins.
    q <- expectEnd (root p) (beg p)
    (r@AuxVert{}, _) <- some $ expects' q
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = q
            { gap = gap p, end = end p
            , root  = root q 
            , left  = r : left q
            , right = tail $ right q }
    -- logging info
    lift . lift $ do
        putStr "[B]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


-- | Predict internal adjoin.
predAdjoinCont :: (VOrd t, VOrd n) => State n t -> Earley n t ()
predAdjoinCont p = void $ P.runListT $ do
    -- make sure that `p' is not fully matched ...
    -- (in fact it must be also a spine node, but we check that
    --  one later)
    guard . not $ completed p
    -- ... and that it expects a spine non-terminal
    (x, _) <- some $ expects' p
    guard $ spine x
    -- identify rules which provide in their heads this very
    -- specific non-terminal
    Rule{..} <- headedBy x
    -- construct the resulting state
    let q = State
            { root  = headR
            , left  = []
            , right = bodyR
            , beg   = end p
            , gap   = Nothing
            , end   = end p }
    b <- lift $ pushState q
    -- print logging information
    when b $ lift . lift $ do
        putStr "[PB] " >> printState p
        putStr "  :  " >> printState q
  where
    spine AuxVert{} = True
    spine _         = False


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
    -- make sure that `q' is completed as well and that it is either
    -- a regular (perhaps intermediate) rule or an intermediate
    -- auxiliary rule (note that (<=) is used as an implication
    -- here and can be read as `implies`).
    guard $ completed q && auxiliary q <= subLevel q
    -- construct the resulting state
    let q' = q { beg = beg p
               , end = end p }
    lift . lift $ do
        putStr "[C]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    lift $ pushState q'


-- | Predict root adjoin.
predAdjoinTerm :: (VOrd t, VOrd n) => State n t -> Earley n t ()
predAdjoinTerm p = void $ P.runListT $ do
    -- make sure that `p' is an "infant" state
    guard $ infant p
    -- and that its head it not an auxiliary root
    guard . not $ auxRoot (root p)
    -- identify rules which provide non-terminals with the given
    -- non-terminal and which represent roots of auxiliary trees
    Rule{..} <- headedByN (nonTerm $ root p)
    guard $ auxRoot headR
    -- construct the resulting state
    let q = State
            { root  = headR
            , left  = []
            , right = bodyR
            , beg   = end p
            , gap   = Nothing
            , end   = end p }
    b <- lift $ pushState q
    -- print logging information
    when b $ lift . lift $ do
        putStr "[PC] " >> printState p
        putStr "  :  " >> printState q
  where
    -- a state is infant if none of its elements has been matched
    -- so far
    infant State{..}
        =  gap == Nothing
        && beg == end
        && null left
    -- verify that the non-terminal represents a root of an
    -- auxiliary tree
    auxRoot AuxRoot{} = True
    auxRoot _         = False

--------------------------------------------------
-- EARLEY
--------------------------------------------------


-- | Does the given grammar generate the given sentence?
-- Uses the `earley` algorithm under the hood.
recognize
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> S.Set n              -- ^ Starting symbols
    -> [t]                  -- ^ Input sentence
    -> IO Bool
recognize gram start xs = do
    done <- earley gram start xs
    return $ (not.null) (complete done)
  where
    n = length xs
    complete sts =
        [ True | st <- S.toList sts
        , beg st == 0, end st == n
        , gap st == Nothing ]


-- | A simplified version of `recognize`.
recognize'
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> n                    -- ^ The start symbol
    -> [t]                  -- ^ Input sentence
    -> IO Bool
recognize' gram start xs = do
    done <- earley gram (S.singleton start) xs
    return $ (not.null) (complete done)
  where
    n = length xs
    complete sts =
        [ True | st <- S.toList sts
        , beg st == 0, end st == n
        , root st == NonT start Nothing ]


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> S.Set n              -- ^ Starting symbols
    -> [t]                  -- ^ Input sentence
    -> IO (S.Set (State n t))
earley gram start xs =
    agregate . doneProSpan . fst <$> RWS.execRWST loop xs st0
    -- void $ RWS.execRWST loop xs st0
  where
    -- Agregate the results from the `doneProSpan` part of the
    -- result.
    agregate = S.unions . M.elems
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt gram start
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popState >>= \mp -> case mp of
        Nothing -> return ()
        Just p -> do
            -- lift $ case p of
            --     (StateE q) -> putStr "POPED: " >> printState q
            step p >> loop


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step :: (VOrd t, VOrd n) => State n t -> Earley n t ()
step p = do
    sequence_ $ map ($p)
      [ tryScan
      , trySubst
      , predSubst
      , tryAdjoinInit
      , predAdjoinInit
      , tryAdjoinCont
      , predAdjoinCont
      , tryAdjoinTerm
      , predAdjoinTerm ]
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
