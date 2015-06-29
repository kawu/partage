{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}


{-
 - Early parser for TAGs.  Fourth preliminary version :-).
 -}


module NLP.LTAG.Early4 where


import           Control.Applicative        ((<$>), (*>))
import           Control.Monad              (guard, void)
import qualified Control.Monad.RWS.Strict   as RWS
import qualified Control.Monad.State.Strict as ST
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))

import           Data.List                  (intercalate)
import qualified Data.Map.Strict            as M
import           Data.Maybe                 (isJust, isNothing, listToMaybe,
                                             maybeToList)
import qualified Data.Set                   as S

import qualified Pipes                      as P

import qualified NLP.LTAG.Tree              as G


--------------------------------------------------
-- CUSTOM SHOW
--------------------------------------------------


class Show a => View a where
    view :: a -> String

instance View String where
    view x = x

instance View Int where
    view = show


--------------------------------------------------
-- VIEW + ORD
--------------------------------------------------


class (View a, Ord a) => VOrd a where

instance (View a, Ord a) => VOrd a where


--------------------------------------------------
-- CORE TYPES
--------------------------------------------------


-- | Position in the sentence.
type Pos = Int


----------------------
-- Initial Trees
----------------------


-- Each initial tree is factorized into a collection of flat CF
-- rules.  In order to make sure that this collection of rules
-- can be only used to recognize this particular tree, each
-- non-terminal is paired with an additional identifier.
--
-- Within the context of substitution, both the non-terminal and
-- the identifier have to agree.  In case of adjunction, only the
-- non-terminals have to be equal.


-- | Additional identifier.
type ID = Int


-- | Symbol: a (non-terminal, maybe identifier) pair.
type Sym n = (n, Maybe ID)


-- | Show the symbol.
viewSym :: View n => Sym n -> String
viewSym (x, Just i) = "(" ++ view x ++ ", " ++ show i ++ ")"
viewSym (x, Nothing) = "(" ++ view x ++ ", _)"


-- | Label: a symbol, a terminal or a generalized foot node.
-- Generalized in the sense that it can represent not only a foot
-- note of an auxiliary tree, but also a non-terminal on the path
-- from the root to the real foot note of an auxiliary tree.
data Lab n t
    = NonT (Sym n)
    | Term t
    | Foot (Sym n)
    deriving (Show, Eq, Ord)


-- | Show the label.
viewLab :: (View n, View t) => Lab n t -> String
viewLab (NonT s) = "N" ++ viewSym s
viewLab (Term t) = "T(" ++ view t ++ ")"
viewLab (Foot s) = "F" ++ viewSym s


-- | A rule for initial tree.
data Rule n t = Rule {
    -- | The head of the rule
      headI :: Sym n
    -- | The body of the rule
    , body  :: [Lab n t]
    } deriving (Show, Eq, Ord)


--------------------------
-- Rule generation monad
--------------------------


-- | Identifier generation monad.
type RM n t a = RWS.RWS () [Rule n t] Int a


-- | Pull the next identifier.
nextID :: RM n t ID
nextID = RWS.state $ \i -> (i, i + 1)


-- | Save the rule in the writer component of the monad.
keepRule :: Rule n t -> RM n t ()
keepRule = RWS.tell . (:[])


-- | Evaluate the RM monad.
runRM :: RM n t a -> (a, [Rule n t])
runRM rm = RWS.evalRWS rm () 0


-----------------------------------------
-- Tree Factorization
-----------------------------------------


-- | Take an initial tree and factorize it into a list of rules.
treeRules
    :: Bool         -- ^ Is it a top level tree?  `True' for
                    -- an entire initial tree, `False' otherwise.
    -> G.Tree n t   -- ^ The tree itself
    -> RM n t (Lab n t)
treeRules isTop G.INode{..} = case subTrees of
    [] -> do
        let x = (labelI, Nothing)
        -- keepRule $ Rule x []
        return $ NonT x
    _  -> do
        x <- if isTop
            then return (labelI, Nothing)
            else (labelI,) . Just <$> nextID
        xs <- mapM (treeRules False) subTrees
        keepRule $ Rule x xs
        return $ NonT x
treeRules _ G.FNode{..} = return $ Term labelF


-----------------------------------------
-- Auxiliary Tree Factorization
-----------------------------------------


-- | Convert an auxiliary tree to a lower-level auxiliary
-- representation and a list of corresponding rules which
-- represent the "substitution" trees on the left and on the
-- right of the spine.
auxRules :: Bool -> G.AuxTree n t -> RM n t (Lab n t)
-- auxRules :: Bool -> G.AuxTree n t -> RM n t (Maybe (Sym n))
auxRules b G.AuxTree{..} =
    doit b auxTree auxFoot
  where
    -- doit _ G.INode{..} [] = return Nothing
    doit _ G.INode{..} [] = return $ Foot (labelI, Nothing)
    doit isTop G.INode{..} (k:ks) = do
        let (ls, bt, rs) = split k subTrees
        x <- if isTop
            then return (labelI, Nothing)
            else (labelI,) . Just <$> nextID
        ls' <- mapM (treeRules False) ls
        bt' <- doit False bt ks
        rs' <- mapM (treeRules False) rs
--         keepAux $ Aux x ls' bt' rs'
--         return $ Just x
        keepRule $ Rule x $ ls' ++ (bt' : rs')
        return $ Foot x
    doit _ _ _ = error "auxRules: incorrect path"
    split =
        doit []
      where
        doit acc 0 (x:xs) = (reverse acc, x, xs)
        doit acc k (x:xs) = doit (x:acc) (k-1) xs
        doit acc _ [] = error "auxRules.split: index to high"


--------------------------------------------------
-- CHART STATE ...
--
-- ... and chart extending operations
--------------------------------------------------


-- | Parsing state: processed initial rule elements and the elements
-- yet to process.
data State n t = State {
    -- | The head of the rule represented by the state.
      root  :: Sym n
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


-- | Does it represent a regular rule?
auxiliary :: State n t -> Bool
auxiliary = isJust . gap


-- | Is it top-level?  All top-level states (regular or
-- auxiliary) have an underspecified ID in the root symbol.
topLevel :: State n t -> Bool
topLevel = isNothing . snd . root


-- | Is it subsidiary (i.e. not top) level?
subLevel :: State n t -> Bool
subLevel = isJust . snd . root


-- | Deconstruct the right part of the state (i.e. labels yet to
-- process) within the MaybeT monad.
expects :: Monad m => State n t -> MaybeT m (Lab n t, [Lab n t])
expects = maybeT . expects'


-- | Deconstruct the right part of the state (i.e. labels yet to
-- process) within the MaybeT monad.
expects' :: State n t -> Maybe (Lab n t, [Lab n t])
expects' = decoList . right


-- | Print the state.
printState :: (View n, View t) => State n t -> IO ()
printState State{..} = do
    putStr $ viewSym root
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


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt {
    -- | Rules which expect a specific symbol and which end on a
    -- specific position.
      doneExpEnd :: M.Map (Sym n, Pos) (S.Set (State n t))
    -- | Processed, fully-parsed rules which provide a specific
    -- non-terminal and which begin on a specific position.
    , doneProBeg :: M.Map (Sym n, Pos) (S.Set (State n t))
    -- | The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    , waiting    :: S.Set (State n t) }
    deriving (Show, Eq, Ord)


-- | Make an initial `EarSt` from a set of states.
mkEarSt :: S.Set (State n t) -> (EarSt n t)
mkEarSt s = EarSt
    { doneExpEnd = M.empty
    , doneProBeg = M.empty
    , waiting = s }


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


-- | Retrieve the set of "done" states.
--  :: Earley n t (S.Set (State n t))
--  = done <$> RWS.get


-- | Add the state to the waiting queue.  Check first if it is
-- not already in the set of processed (`done') states.
pushState :: (Ord t, Ord n) => State n t -> Earley n t ()
pushState p = RWS.state $ \s ->
    -- let waiting' = if S.member p (done s)
    let waiting' = if isProcessed p s
            then waiting s
            else S.insert p (waiting s)
    in  ((), s {waiting = waiting'})


-- | Remove a state from the queue.  In future, the queue
-- will be probably replaced by a priority queue which will allow
-- to order the computations in some smarter way.
popState :: (Ord t, Ord n) => Earley n t (Maybe (State n t))
popState = RWS.state $ \st -> case S.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (x, s) -> (Just x, st {waiting = s})


-- | Add the state to the set of processed (`done') states.
saveState :: (Ord t, Ord n) => State n t -> Earley n t ()
saveState p = RWS.state $ \s -> ((), doit s)
  where
    doit st@EarSt{..} = st
      { doneExpEnd = case expects' p of
          Just (NonT x, _) -> M.insertWith S.union (x, end p)
                              (S.singleton p) doneExpEnd
          Nothing -> doneExpEnd
      , doneProBeg = if completed p
          then M.insertWith S.union (root p, beg p)
               (S.singleton p) doneProBeg
          else doneProBeg }


-- | Check if the state is not already processed (i.e. in one of the
-- done-related maps).
isProcessed :: State n t -> EarSt n t -> Bool
isProcessed = undefined


-- | Return all the states which (for `trySubst`)
-- * expect a given non-terminal,
-- * end on the given position.
expect_Sym_End :: Ord n => Sym n -> Pos -> P.ListT (Earley n t) (State n t)
expect_Sym_End x i = do
  EarSt{..} <- lift RWS.get
  listValues (x, i) doneExpEnd


-- | Return all states which (for `trySubst'`)
-- * provide a specific symbol,
-- * begin on the given position.
-- * TODO: Should be regular!!! (see `trySubst`); se also below (`tryAdjoinCont`)
provide_Sym_Beg :: Ord n => Sym n -> Pos -> P.ListT (Earley n t) (State n t)
provide_Sym_Beg x i = do
  EarSt{..} <- lift RWS.get
  listValues (x, i) doneProBeg


-- | Return all states which (for `tryAdjoinCont'`)
-- * Provide a specific symbol,
-- * Begin on a given position.
-- * Are auxiliary (Q: do we have to enforce this explicitely?
--     perhaps it will be guaranteed by the symbol which is already
--     related to auxiliary rules?)


-- | Return all states which (for `tryAdjoinCont`)
-- * Expect a specific symbol,
-- * End on a given position.
--   <== This function already exists!
-- expect_Sym_End :: Ord n => Sym n -> Pos -> P.ListT (Earley n t) (State n t)


-- | Return all states which (for `tryAdjoinInit`)
-- * Provide a specific non-terminal (with any ID value)
-- * Begins on a given position.
provide_NT_Beg :: Ord n => n -> Pos -> P.ListT (Earley n t) (State n t)
provide_NT_Beg = undefined


-- | Return all states which (for `tryAdjoinInit'`)
-- * Expect a real foot (i.e. Foot (u, Nothing)) with a specific `u` value.
-- * Ends on a given position,
expect_RF_End :: Ord n => n -> Pos -> P.ListT (Earley n t) (State n t)
expect_RF_End = undefined


-- | Return all states which (for `tryAdjoinTerm`)
-- * are completed (i.e. provide sth.),
-- * are either regular or intermediate auxiliary,
-- * begin and end on specific positions,
-- * have a specific non-terminal (ID irrelevant)


-- | Return all states which (for `tryAdjoinTerm'`)
-- * are completed (i.e. provide sth.) and top-level
--   (i.e. with underspecified ID),
-- * have a specific gap (=> are auxiliary),
-- * begin and end on specific positions,
-- * have a specific non-terminal (ID irrelevant)


-- | A utility function.
listValues :: (Monad m, Ord a) => a -> M.Map a (S.Set b) -> P.ListT m b
listValues x m = each $ case M.lookup x m of
    Nothing -> []
    Just s -> S.toList s


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t) -- ^ The grammar (set of rules)
    -> [t]              -- ^ Input sentence
    -- -> IO (S.Set (State n t))
    -> IO ()
earley gram xs =
    -- done . fst <$> RWS.execRWST loop xs st0
    void $ RWS.execRWST loop xs st0
  where
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt $ S.fromList
        [ State
            { root = headI
            , left = []
            , right = body
            , beg = i, end = i
            , gap = Nothing }
        | Rule{..} <- S.toList gram
        , i <- [0 .. length xs - 1] ]
    -- the computetion is performed as long as the waiting queue
    -- is non-empty.
    loop = popState >>= \mp -> case mp of
        Nothing -> return ()
        Just p -> step p >> loop


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step :: (VOrd t, VOrd n) => State n t -> Earley n t ()
step p = do
    -- lift $ putStr "PP:  " >> print p
    -- try to scan the state
    tryScan p
    -- if the state is parsed, find all the states which could be
    -- potentially completed by it (i.e. substitution)
    trySubst p *> trySubst' p
--     P.runListT $ do
--         -- for each state in the set of the processed states
--         q <- each . S.toList =<< lift getDone
--         lift $ do
--             tryCompose p q
--             tryCompose q p
--     -- processing of the state is done, store it in `done'
    saveState p


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


-- | Try to use the state (only if fully parsed) to complement
-- (=> substitution) other rules.
trySubst
    :: (VOrd t, VOrd n)
    => State n t
    -> Earley n t ()
trySubst p = void $ P.runListT $ do
    -- make sure that `p' is a fully-parsed regular rule
    guard $ completed p && regular p
--     -- make sure `q' is not yet completed and expects
--     -- a non-terminal
--     (NonT x, right') <- expects q
--     -- make sure that `p' begins where `q' ends
--     guard $ beg p == end q
--     -- make sure that the root of `p' matches with the next
--     -- non-terminal of `q'; IDs of the symbols have to be
--     -- the same as well
--     guard $ root p == x
    -- find rules which end where `p' begins and which
    -- expect a specific non-terminal
    q <- expect_Sym_End (root p) (beg p)
    -- construct the resultant state
    let q' = q
            { end = end p
            -- , left = NonT x : left q
            , left = NonT (root p) : left q
            -- , right = right' }
            , right = tail (right q) }
    -- print logging information
    lift . lift $ do
        putStr "[U]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


-- | Inverse to `trySubst`.
trySubst'
    :: (VOrd t, VOrd n)
    => State n t
    -> Earley n t ()
trySubst' q = void $ P.runListT $ do
--     -- make sure that `p' is a fully-parsed regular rule
--     guard $ completed p && regular p
    -- make sure `q' is not yet completed and expects
    -- a non-terminal
    (NonT x, right') <- each $ maybeToList $ expects' q
--     -- make sure that `p' begins where `q' ends
--     guard $ beg p == end q
--     -- make sure that the root of `p' matches with the next
--     -- non-terminal of `q'; IDs of the symbols have to be
--     -- the same as well
--     guard $ root p == x
--     -- find rules which end where `p' begins and which
--     -- expect a specific non-terminal
--     q <- expect_Sym_End (root p) (beg p)

    -- find rules which begin where `q` ends and which
    -- provide a specific non-terminal
    p <- provide_Sym_Beg x (end q)
    -- construct the resultant state
    let q' = q
            { end = end p
            , left = NonT x : left q
            , right = right' }
    -- print logging information
    lift . lift $ do
        putStr "[W]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


-- -- | `tryAdjoinInit p q':
-- -- * `p' is a completed state (regular or auxiliary)
-- -- * `q' not completed and expects a *real* foot
-- tryAdjoinInit
--     :: (VOrd n, VOrd t)
--     => State n t
--     -> Earley n t ()
-- tryAdjoinInit p = void $ P.runListT $ do
--     -- make sure that `p' is fully-parsed
--     guard $ completed p
--     -- find not-yet-completed rules which expect a specific, real
--     -- (with ID == Nothing) foot and which end where `p` begins
-- 
-- 
-- 
--     -- make sure `q' is not yet completed and expects
--     -- a real (with ID == Nothing) foot
--     (Foot (u, Nothing), right') <- expects q
--     -- make sure that `p' begins where `q' ends, so that the foot
--     -- node of `q' cab be eventually completed with `p', which
--     -- represents (a part of) an adjunction operation
--     guard $ beg p == end q
--     -- make sure that the root of `p' matches with the non-terminal
--     -- of the foot of `q'; IDs of the symbols *no not* have to be
--     -- the same
--     guard $ fst (root p) == u
--     -- construct the resultant state
--     let q' = q
--             { gap = Just (beg p, end p)
--             , end = end p
--             , left = Foot (u, Nothing) : left q
--             , right = right' }
--     -- print logging information
--     lift . lift $ do
--         putStr "[A]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     -- push the resulting state into the waiting queue
--     lift $ pushState q'


-- -- | Try compose the two states using one of the possible
-- -- binary composition operations.
-- tryCompose
--     :: (VOrd t, VOrd n)
--     => State n t
--     -> State n t
--     -> Earley n t ()
-- tryCompose p q = do
--     trySubst p q
--     tryAdjoinInit p q
--     tryAdjoinCont p q
--     tryAdjoinTerm p q
--
--
-- -- | Try to substitute the non-terminal expected by the second
-- -- state/rule with the first state (if corresponding symbols
-- -- match).  While the first state has to represent a regular
-- -- (non-auxiliary) rule, the second state not necessarily.
-- trySubst
--     :: (VOrd t, VOrd n)
--     => State n t
--     -> State n t
--     -> Earley n t ()
-- trySubst p q = void $ runMaybeT $ do
--     -- make sure that `p' is a fully-parsed regular rule
--     guard $ completed p && regular p
--     -- make sure `q' is not yet completed and expects
--     -- a non-terminal
--     (NonT x, right') <- expects q
--     -- make sure that `p' begins where `q' ends
--     guard $ beg p == end q
--     -- make sure that the root of `p' matches with the next
--     -- non-terminal of `q'; IDs of the symbols have to be
--     -- the same as well
--     guard $ root p == x
--     -- construct the resultant state
--     let q' = q
--             { end = end p
--             , left = NonT x : left q
--             , right = right' }
--     -- print logging information
--     lift . lift $ do
--         putStr "[U]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     -- push the resulting state into the waiting queue
--     lift $ pushState q'


-- -- | `tryAdjoinInit p q':
-- -- * `p' is a completed state (regular or auxiliary)
-- -- * `q' not completed and expects a *real* foot
-- tryAdjoinInit
--     :: (VOrd n, VOrd t)
--     => State n t
--     -> State n t
--     -> Earley n t ()
-- tryAdjoinInit p q = void $ runMaybeT $ do
--     -- make sure that `p' is fully-parsed
--     guard $ completed p
--     -- make sure `q' is not yet completed and expects
--     -- a real (with ID == Nothing) foot
--     (Foot (u, Nothing), right') <- expects q
--     -- make sure that `p' begins where `q' ends, so that the foot
--     -- node of `q' cab be eventually completed with `p', which
--     -- represents (a part of) an adjunction operation
--     guard $ beg p == end q
--     -- make sure that the root of `p' matches with the non-terminal
--     -- of the foot of `q'; IDs of the symbols *no not* have to be
--     -- the same
--     guard $ fst (root p) == u
--     -- construct the resultant state
--     let q' = q
--             { gap = Just (beg p, end p)
--             , end = end p
--             , left = Foot (u, Nothing) : left q
--             , right = right' }
--     -- print logging information
--     lift . lift $ do
--         putStr "[A]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     -- push the resulting state into the waiting queue
--     lift $ pushState q'


-- -- | `tryAdjoinCont p q':
-- -- * `p' is a completed, auxiliary state
-- -- * `q' not completed and expects a *dummy* foot
-- tryAdjoinCont
--     :: (VOrd n, VOrd t)
--     => State n t
--     -> State n t
--     -> Earley n t ()
-- tryAdjoinCont p q = void $ runMaybeT $ do
--     -- make sure that `p' is a completed, auxiliary rule
--     guard $ completed p && auxiliary p
--     -- make sure `q' is not yet completed and expects
--     -- a dummy foot
--     (Foot x@(_, Just _), right') <- expects q
--     -- make sure that `p' begins where `q' ends, so that the foot
--     -- node of `q' cab be completed with `p'
--     guard $ beg p == end q
--     -- make sure that the root of `p' matches the non-terminal of
--     -- the foot of `q'; IDs of the symbols *must* match as well
--     guard $ root p == x
--     -- construct the resulting state; the span of the gap of the
--     -- inner state `p' is copied to the outer state based on `q'
--     let q' = q
--             { gap = gap p
--             , end = end p
--             , left = Foot x : left q
--             , right = right' }
--     -- logging info
--     lift . lift $ do
--         putStr "[B]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     -- push the resulting state into the waiting queue
--     lift $ pushState q'


-- | Adjoin a fully-parsed auxiliary state to a partially parsed
-- tree represented by a fully parsed rule/state.
tryAdjoinTerm
    :: (VOrd t, VOrd n)
    => State n t
    -> State n t
    -> Earley n t ()
tryAdjoinTerm p q = void $ runMaybeT $ do
    -- make sure that `p' is a completed, top-level state ...
    guard $ completed p && topLevel p
    -- ... and that it is an auxiliary state
    (gapBeg, gapEnd) <- maybeT $ gap p
    -- make sure that `q' is completed as well and that it is
    -- either a regular rule or an intermediate auxiliary rule
    -- ((<=) used as an implication here!)
    guard $ completed q && auxiliary q <= subLevel q
    -- finally, check that the spans match
    guard $ gapBeg == beg q && gapEnd == end q
    -- and that non-terminals match (not IDs)
    guard $ fst (root p) == fst (root q)
    let q' = q
            { beg = beg p
            , end = end p }
    lift . lift $ do
        putStr "[C]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    lift $ pushState q'


--------------------------------------------------
-- UTILS
--------------------------------------------------


-- | Deconstruct list.  Utility function.
decoList :: [a] -> Maybe (a, [a])
decoList [] = Nothing
decoList (y:ys) = Just (y, ys)


-- | MaybeT transformer.
maybeT :: Monad m => Maybe a -> MaybeT m a
maybeT = MaybeT . return


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each
