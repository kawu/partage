{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}


module NLP.TAG.Vanilla.Earley where


import           Control.Applicative        ((<$>))
import           Control.Arrow              (second)
import           Control.Monad              (guard, void, forever)
import qualified Control.Monad.State.Strict as E
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS
import           Control.Monad.Identity     (Identity(..))

import           Data.Function              (on)
import           Data.Monoid                (mappend, mconcat)
import           Data.List                  (intercalate)
-- import           Data.Foldable (Foldable)
-- import           Data.Traversable (Traversable)
import           Data.Maybe     ( isJust, isNothing
                                , listToMaybe, maybeToList)
import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import qualified Data.Partition             as Part
import qualified Pipes                      as P
-- import qualified Pipes.Prelude              as P

import           NLP.TAG.Vanilla.Core
-- import qualified NLP.TAG.Vanilla.Rule as R
import           NLP.TAG.Vanilla.Rule
    ( Lab(..), viewLab, Rule(..) )


--------------------------------------------------
-- Eq/Ord Instances
--------------------------------------------------


-- | Label equality.
--
-- TODO: Reimplement based on `labEq'`
labEq
    :: (Eq n, Eq t)
    => Lab n t -> Lab n t -> Bool
labEq p q =
    eq p q
  where
    eq x@NonT{} y@NonT{}
        =  eqOn nonTerm x y
        && eqOn labID x y
    eq (Term x) (Term y)
        =  x == y
    eq x@AuxRoot{} y@AuxRoot{}
        =  eqOn nonTerm x y
    eq (AuxFoot x) (AuxFoot y)
        =  x == y
    eq x@AuxVert{} y@AuxVert{}
        =  eqOn nonTerm x y
        && eqOn symID x y
    eq _ _ = False
    eqOn f x y = f x == f y


-- | Label equality.  Concerning the `SymID` values, it is only
-- checkes if either both are `Nothing` or both are `Just`.
labEq' :: (Eq n, Eq t) => Lab n t -> Lab n t -> Bool
labEq' p q =
    eq p q
  where
    eq x@NonT{} y@NonT{}
        =  eqOn nonTerm x y
        && eqOn (isJust . labID) x y
    eq (Term x) (Term y)
        =  x == y 
    eq x@AuxRoot{} y@AuxRoot{}
        =  eqOn nonTerm x y
    eq (AuxFoot x) (AuxFoot y)
        =  x == y
    eq x@AuxVert{} y@AuxVert{}
        =  eqOn nonTerm x y
    eq _ _ = False
    eqOn f x y = f x == f y


-- | Label comparison.
labCmp :: (Ord n, Ord t) => Lab n t -> Lab n t -> Ordering
labCmp p q =
    cmp p q
  where
    cmp x@NonT{} y@NonT{} =
        cmpOn nonTerm x y       `mappend`
        cmpOn labID x y
    cmp (Term x) (Term y) =
        compare x y
    cmp x@AuxRoot{} y@AuxRoot{} =
        cmpOn nonTerm x y
    cmp (AuxFoot x) (AuxFoot y) =
        compare x y
    cmp x@AuxVert{} y@AuxVert{} =
        cmpOn nonTerm x y       `mappend`
        cmpOn symID x y
    cmp x y = cmpOn conID x y
    cmpOn f x y = compare (f x) (f y)
    -- data constructur identifier
    conID x = case x of
        NonT{}      -> 1 :: Int
        Term _      -> 2
        AuxRoot{}   -> 3
        AuxFoot{}   -> 4
        AuxVert{}   -> 5


-- | Label comparison.  Concerning the `SymID` values, it is only
-- checked if either both are `Nothing` or both are `Just`.
labCmp' :: (Ord n, Ord t) => Lab n t -> Lab n t -> Ordering
labCmp' p q =
    cmp p q
  where
    cmp x@NonT{} y@NonT{} =
        cmpOn nonTerm x y       `mappend`
        cmpOn (isJust . labID) x y
    cmp (Term x) (Term y) =
        compare x y
    cmp x@AuxRoot{} y@AuxRoot{} =
        cmpOn nonTerm x y
    cmp (AuxFoot x) (AuxFoot y) =
        compare x y
    cmp x@AuxVert{} y@AuxVert{} =
        cmpOn nonTerm x y
    cmp x y = cmpOn conID x y
    cmpOn f x y = compare (f x) (f y)
    conID x = case x of
        NonT{}      -> 1 :: Int
        Term _      -> 2
        AuxRoot{}   -> 3
        AuxFoot{}   -> 4
        AuxVert{}   -> 5

--------------------------------------------------
-- Trash?
--------------------------------------------------


-- -- -- | A simplified label which does not contain any information
-- -- -- about FSs.  In contrast to `Lab n t`, it provides Eq and Ord
-- -- -- instances.  TODO: note that we lose the distinction between
-- -- -- `AuxRoot` and `AuxFoot` here.
-- -- data SLab n t
-- --     = SNonT (n, Maybe SymID)
-- --     | STerm t
-- --     | SAux (n, Maybe SymID)
-- --     deriving (Show, Eq, Ord)
-- -- 
-- -- 
-- -- -- | Simplify label.
-- -- simpLab :: Lab n t i -> SLab n t
-- -- simpLab NonT{..} = SNonT (nonTerm, labID)
-- -- simpLab (Term t) = STerm t
-- -- simpLab AuxRoot{..} = SAux (nonTerm, Nothing)
-- -- simpLab AuxFoot{..} = SAux (nonTerm, Nothing)
-- -- simpLab AuxVert{..} = SAux (nonTerm, Just symID)
-- -- 
-- -- 
-- -- -- | Show the label.
-- -- viewLab :: (View n, View t) => Lab n t i -> String
-- -- viewLab NonT{..} = "N" ++ viewSym (nonTerm, labID)
-- -- viewLab (Term t) = "T(" ++ view t ++ ")"
-- -- viewLab AuxRoot{..} = "A" ++ viewSym (nonTerm, Nothing)
-- -- viewLab AuxVert{..} = "V" ++ viewSym (nonTerm, Just symID)
-- -- viewLab AuxFoot{..} = "F" ++ viewSym (nonTerm, Nothing)
-- -- 
-- -- 
-- -- -- | View part of the label.  Utility function.
-- -- viewSym :: View n => (n, Maybe SymID) -> String
-- -- viewSym (x, Just i) = "(" ++ view x ++ ", " ++ show i ++ ")"
-- -- viewSym (x, Nothing) = "(" ++ view x ++ ", _)"


--------------------------------------------------
-- Substructure Sharing
--------------------------------------------------


-- | Duplication-removal state serves to share common
-- substructures.
--
-- The idea is to remove redundant rules equivalent to other
-- rules already present in the set of processed rules
-- `rulDepo`(sit).
--
-- Note that rules have to be processed in an appropriate order
-- so that lower-level rules are processed before the
-- higher-level rules from which they are referenced.
data DupS n t = DupS {
    -- | A disjoint set for `SymID`s
      symDisj   :: Part.Partition SymID
    -- | Rules already saved
    , rulDepo   :: S.Set (Rule n t)
    } 


-- Let us take a rule and let us assume that all identifiers it
-- contains point to rules which have already been processed (for
-- this assumption to be valid we just need to order the set of
-- rules properly).  So we have a rule `r`, a set of processed
-- rules `rs` and a clustering (disjoint-set) over `SymID`s
-- present in `rs`.
--
-- Now we want to process `r` and, in particular, check if it is
-- not already in `rs` and update its `SymID`s.
--
-- First we translate the body w.r.t. the existing clustering of
-- `SymID`s (thanks to our assumption, these `SymID`s are already
-- known and processed).  The `SymID` in the root of the rule (if
-- present) is the new one and it should not yet have been mentioned
-- in `rs`.  Even when `SymID` is not present in the root, we can
-- still try to check if `r` is not present in `rs` -- after all, there
-- may be some duplicates in the input grammar.
--
-- Case 1: we have a rule with a `SymID` in the root.  We want to
-- check if there is already a rule in `rs` which:
-- * Has identical body (remember that we have already
--   transformed `SymID`s of the body of the rule in question)
-- * Has the same non-terminal in the root and some `SymID`
--
-- Case 2: the same as case 1 with the difference that we look
-- for the rules which have an empty `SymID` in the root.
--
-- For this to work we just need a specific comparison function
-- which works as specified in the two cases desribed above
-- (i.e. either there are some `SymID`s in the roots, or there
-- are no `SymID`s in both roots.) 
--
-- Once we have this comparison, we simply process the set of
-- rules incrementally.


-- | Duplication-removal transformer.
type DupT n t m = E.StateT (DupS n t) m


-- | Duplication-removal monad.
type DupM n t = DupT n t Identity


-- | Run the transformer.
runDupT
    :: (Functor m, Monad m)
    => DupT n t m b
    -> m (b, S.Set (Rule n t))
runDupT = fmap (second rulDepo) . flip E.runStateT
    (DupS Part.empty S.empty)


-- | Update the body of the rule by replacing old `SymID`s with
-- their representatives.
updateBody
    :: Rule n t
    -> DupM n t (Rule n t)
updateBody r = do
    d <- E.gets symDisj
    let body' = map (updLab d) (bodyR r)
    return $ r { bodyR = body' }
  where
    updLab d x@NonT{..}     = x { labID = updSym d <$> labID }
    updLab d x@AuxVert{..}  = x { symID = updSym d symID }
    updLab _ x              = x
    updSym                  = Part.rep


-- | Find a rule if already present.
findRule 
    :: (Ord n, Ord t)
    => Rule n t
    -> DupM n t (Maybe (Rule n t))
findRule x = do
    s <- E.gets rulDepo
    return $ lookupSet x s


-- | Join two `SymID`s.
joinSym :: SymID -> SymID -> DupM n t ()
joinSym x y = E.modify $ \s@DupS{..} -> s
    { symDisj = Part.joinElems x y symDisj }
    


-- | Save the rule in the underlying deposit. 
keepRule
    :: (Ord n, Ord t)
    => Rule n t
    -> DupM n t ()
keepRule r = E.modify $ \s@DupS{..} -> s
    { rulDepo = S.insert r rulDepo }


-- | Retrieve the symbol of the head of the rule.
headSym :: Rule n t -> Maybe SymID
headSym r = case headR r of
    NonT{..}    -> labID
    AuxVert{..} -> Just symID
    _           -> Nothing


-- | Removing duplicates updating `SymID`s at the same time.
-- WARNING: The pipe assumes that `SymID`s to which the present
-- rule refers have already been processed -- in other words,
-- that rule on which the present rule depends have been
-- processed earlier.
rmDups
    :: (Ord n, Ord t)
    => P.Pipe
        (Rule n t)    -- Input
        (Rule n t)    -- Output 
        (DupM n t)    -- Underlying state
        ()            -- No result
rmDups = forever $ do
    r <- P.await >>= lift . updateBody
    lift (findRule r) >>= \mr -> case mr of
        Nothing -> do
            lift $ keepRule r
            P.yield r
        Just r' -> case (headSym r, headSym r') of
            (Just x, Just y)    -> lift $ joinSym x y
            _                   -> return ()
--         Just r' -> void $ runMaybeT $ joinSym
--             <$> headSymT r
--             <*> headSymT r'
    -- where headSymT = maybeT . headSym


instance (Eq n, Eq t) => Eq (Rule n t) where
    r == s = (hdEq `on` headR) r s
        && ((==) `on` length.bodyR) r s
        && and [eq x y | (x, y) <- zip (bodyR r) (bodyR s)]
      where
        eq x y   = labEq  x y
        hdEq x y = labEq' x y


instance (Ord n, Ord t) => Ord (Rule n t) where
    r `compare` s = (hdCmp `on` headR) r s    `mappend`
        (compare `on` length.bodyR) r s       `mappend`
        mconcat [cmp x y | (x, y) <- zip (bodyR r) (bodyR s)]
      where
        cmp x y   = labCmp  x y
        hdCmp x y = labCmp' x y


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


-- -- | Equality of states.
-- statEq :: (Eq n, Eq t) => State n t -> State n t -> Bool
-- statEq r s
--      = eqOn beg r s
--     && eqOn end r s
--     && eqOn gap r s
--     && leq (root r) (root s)
--     && eqOn (length.left) r s
--     && eqOn (length.right) r s
--     && and [leq x y | (x, y) <- zip (left r) (left s)]
--     && and [leq x y | (x, y) <- zip (right r) (right s)]
--   where
--     leq x y = labEq x y
--     eqOn f x y = f x == f y
-- 
-- 
-- instance (Eq n, Eq t) => Eq (State n t) where
--     (==) = statEq
-- 
-- 
-- -- | Equality of states.
-- statCmp
--     :: (Ord n, Ord t)
--     => State n t
--     -> State n t
--     -> Ordering
-- statCmp r s = cmpOn beg r s
--     `mappend` cmpOn end r s
--     `mappend` cmpOn gap r s
--     `mappend` lcmp (root r) (root s)
--     `mappend` cmpOn (length.left) r s
--     `mappend` cmpOn (length.right) r s
--     `mappend` mconcat [lcmp x y | (x, y) <- zip (left r) (left s)]
--     `mappend` mconcat [lcmp x y | (x, y) <- zip (right r) (right s)]
--   where
--     lcmp x y = labCmp x y
--     cmpOn f x y = compare (f x) (f y)
-- 
-- 
-- instance (Ord n, Ord t) => Ord (State n t) where
--     compare = statCmp


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
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt {
    -- | Rules which expect a specific label and which end on a
    -- specific position.
      doneExpEnd :: M.Map (Lab n t, Pos) (S.Set (State n t))
    -- | Rules providing a specific non-terminal in the root
    -- and spanning over a given range.
    , doneProSpan :: M.Map (n, Pos, Pos) (S.Set (State n t))
    -- | The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    , waiting    :: Q.PSQ (State n t) Prio }


-- | Make an initial `EarSt` from a set of states.
mkEarSt :: (Ord n, Ord t) => S.Set (State n t) -> (EarSt n t)
mkEarSt s = EarSt
    { doneExpEnd = M.empty
    , doneProSpan = M.empty
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
    S.member pE $ chooseSet pE
  where
    chooseSet p = case expects' p of
        Just (x, _) -> M.findWithDefault S.empty
            (x, end p) doneExpEnd
        Nothing -> M.findWithDefault S.empty
            (nonTerm $ root p, beg p, end p) doneProSpan


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
    -- Q: Why are we using `Right` here?
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


-- | Adjoin a fully-parsed auxiliary state `p` to a partially parsed
-- tree represented by a fully parsed rule/state `q`.
tryAdjoinTerm :: (VOrd t, VOrd n) => State n t -> Earley n t ()
tryAdjoinTerm p = void $ P.runListT $ do
    -- make sure that `p' is a completed, top-level state ...
    guard $ completed p && topLevel p
    -- ... and that it is an auxiliary state (by definition only
    -- auxiliary states have gaps)
    (gapBeg, gapEnd) <- each $ maybeToList $ gap p
    -- it is top-level, so we can also make sure that the
    -- root is an AuxRoot.
    -- pRoot@AuxRoot{} <- some $ Just $ root p
    -- take all completed rules with a given span
    -- and a given root non-terminal (IDs irrelevant)
    q <- rootSpan (nonTerm $ root p) (gapBeg, gapEnd)
    -- make sure that `q' is completed as well and that it is either
    -- a regular (perhaps intermediate) rule or an intermediate
    -- auxiliary rule (note that (<=) is used as an implication
    -- here and can be read as `implies`).
    -- NOTE: root auxiliary rules are of no interest to us but they
    -- are all the same taken into account in an indirect manner.
    -- We can assume here that such rules are already adjoined thus
    -- creating either regular or intermediate auxiliary.
    -- NOTE: similar reasoning can be used to explain why foot
    -- auxiliary rules are likewise ignored.
    -- Q: don't get this second remark -- how could a foot node
    -- be a root of a state/rule `q`?  What `foot auxiliary rules`
    -- could actually mean?
    guard $ completed q && auxiliary q <= subLevel q
    -- TODO: it seems that some of the constraints given above
    -- follow from the code below:
    qRoot <- some $ case root q of
        x@NonT{}    -> Just x
        x@AuxVert{} -> Just x
        _           -> Nothing
    newRoot <- some $ case qRoot of
        NonT{} -> Just $ NonT
            { nonTerm = nonTerm qRoot
            , labID = labID qRoot }
        AuxVert{} -> Just $ AuxVert
            { nonTerm = nonTerm qRoot
            , symID = symID qRoot }
        _           -> Nothing
    let q' = q
            { root = newRoot
            , left  = left q
            , right = right q
            , beg = beg p
            , end = end p }
    lift . lift $ do
        putStr "[C]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    lift $ pushState q'


--------------------------------------------------
-- EARLEY
--------------------------------------------------


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [t]                  -- ^ Input sentence
    -> IO (S.Set (State n t))
    -- -> IO ()
earley gram xs =
    agregate . doneProSpan . fst <$> RWS.execRWST loop xs st0
    -- void $ RWS.execRWST loop xs st0
  where
    -- Agregate the results from the `doneProSpan` part of the
    -- result.
    agregate = S.unions . M.elems
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
        Just p -> do
            -- lift $ case p of
            --     (StateE q) -> putStr "POPED: " >> printState q
            step p >> loop


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step :: (VOrd t, VOrd n) => State n t -> Earley n t ()
step p = do
    sequence_ $ map ($p)
      [ tryScan, trySubst
      , tryAdjoinInit
      , tryAdjoinCont
      , tryAdjoinTerm ]
    saveState p


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- -- | Retrieve the Just value.  Error otherwise.
-- unJust :: Maybe a -> a
-- unJust (Just x) = x
-- unJust Nothing = error "unJust: got Nothing!" 


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


-- | Lookup an element in a set.
lookupSet :: Ord a => a -> S.Set a -> Maybe a
lookupSet x s = do    
    y <- S.lookupLE x s
    guard $ x == y
    return y
