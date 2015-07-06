{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}


{-
 - Early parser for TAGs.  Fourth preliminary version :-).
 -}


module NLP.LTAG.Early5 where


import           Control.Monad              (guard, void)
import qualified Control.Monad.State.Strict as ST
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS

import           Data.Function              (on)
import           Data.Monoid                (mappend, mconcat)
import           Data.List                  (intercalate)
import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)
import           Data.Maybe     ( isJust, isNothing
                                , listToMaybe, maybeToList)
import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import qualified Pipes                      as P

import qualified NLP.FeatureStructure.Tree as FT
import qualified NLP.FeatureStructure.Graph as FG
import qualified NLP.FeatureStructure.Join as J

import           NLP.LTAG.Core
import qualified NLP.LTAG.Rule as R


--------------------------
-- Internal rule
--------------------------


-- | A feature graph identifier, i.e. an identifier used to refer
-- to individual nodes in a FS.
type FID = Int


-- -- | Symbol: a (non-terminal, maybe identifier) pair addorned with
-- -- a feature structure. 
-- data Sym n = Sym
--     { nonTerm :: n
--     , ide     :: Maybe SymID
--     , fgID    :: FID }
--     deriving (Show, Eq, Ord)
-- 
-- 
-- -- | A simplified symbol without FID.
-- type SSym n = (n, Maybe SymID)
-- 
-- 
-- -- | Simplify symbol.
-- simpSym :: Sym n -> SSym n
-- simpSym Sym{..} = (nonTerm, ide)
-- 
-- 
-- -- | Show the symbol.
-- viewSym :: View n => Sym n -> String
-- viewSym (Sym x (Just i) _) = "(" ++ view x ++ ", " ++ show i ++ ")"
-- viewSym (Sym x Nothing _) = "(" ++ view x ++ ", _)"


-- -- | Label: a symbol, a terminal or a generalized foot node.
-- -- Generalized in the sense that it can represent not only a foot
-- -- note of an auxiliary tree, but also a non-terminal on the path
-- -- from the root to the real foot note of an auxiliary tree.
-- data Lab n t
--     = NonT (Sym n)
--     | Term t
--     | Foot (Sym n)
--     deriving (Show, Eq, Ord)


-- | Label represent one of the following:
-- * A non-terminal
-- * A terminal
-- * A root of an auxiliary tree
-- * A foot node of an auxiliary tree
-- * A vertebra of the spine of the auxiliary tree
--
-- It has neither Eq nor Ord instances, because the comparison of
-- feature graph identifiers without context doesn't make much
-- sense.
data Lab n t
    = NonT
        { nonTerm   :: n
        , labID     :: Maybe SymID
        , topID     :: FID
        , botID     :: FID }
    | Term t
    | AuxRoot
        { nonTerm   :: n
        , topID     :: FID
        , botID     :: FID
        , footTopID :: FID
        , footBotID :: FID }
    | AuxFoot
        { nonTerm   :: n }
    | AuxVert
        { nonTerm   :: n
        , symID     :: SymID
        , topID     :: FID
        , botID     :: FID }
    deriving (Show)


-- | Label equality within the context of corresponding
-- feature graphs.
labEq
    :: (Eq n, Eq t, Eq f, Eq a)
    => Lab n t      -- ^ First label `x`
    -> FG.Graph f a -- ^ Graph corresponding to `x`
    -> Lab n t      -- ^ Second label `y`
    -> FG.Graph f a -- ^ Graph corresponding to `y`
    -> Bool
labEq p g q h =
    eq p q
  where
    eq x@NonT{} y@NonT{}
        =  eqOn nonTerm x y
        && eqOn labID x y
        && nodeEqOn topID x y
        && nodeEqOn botID x y
    eq (Term x) (Term y)
        =  x == y 
    eq x@AuxRoot{} y@AuxRoot{}
        =  eqOn nonTerm x y
        && nodeEqOn topID x y
        && nodeEqOn botID x y
        && nodeEqOn footTopID x y
        && nodeEqOn footBotID x y
    eq (AuxFoot x) (AuxFoot y)
        =  x == y
    eq x@AuxVert{} y@AuxVert{}
        =  eqOn nonTerm x y
        && eqOn symID x y
        && nodeEqOn topID x y
        && nodeEqOn botID x y
    eq _ _ = False
    eqOn f = (==) `on` f
    nodeEqOn f = nodeEq `on` f
    -- assumption: the first index belongs to the first
    -- graph, the second to the second graph.
    nodeEq i j = FG.equal g i h j


-- | Label comparison within the context of corresponding
-- feature graphs.
labCmp
    :: (Ord n, Ord t, Ord f, Ord a)
    => Lab n t      -- ^ First label `x`
    -> FG.Graph f a -- ^ Graph corresponding to `x`
    -> Lab n t      -- ^ Second label `y`
    -> FG.Graph f a -- ^ Graph corresponding to `y`
    -> Ordering
labCmp p g q h =
    cmp p q
  where
    cmp x@NonT{} y@NonT{} =
        cmpOn nonTerm x y       `mappend`
        cmpOn labID x y         `mappend`
        nodeCmpOn topID x y `mappend`
        nodeCmpOn botID x y
    cmp (Term x) (Term y) =
        compare x y
    cmp x@AuxRoot{} y@AuxRoot{} =
        cmpOn nonTerm x y       `mappend`
        nodeCmpOn topID x y `mappend`
        nodeCmpOn botID x y `mappend`
        nodeCmpOn footTopID x y `mappend`
        nodeCmpOn footBotID x y
    cmp (AuxFoot x) (AuxFoot y) =
        compare x y
    cmp x@AuxVert{} y@AuxVert{} =
        cmpOn nonTerm x y       `mappend`
        cmpOn symID x y         `mappend`
        nodeCmpOn topID x y `mappend`
        nodeCmpOn botID x y
    cmp x y = cmpOn conID x y
    cmpOn f = compare `on` f
    nodeCmpOn f = nodeCmp `on` f
    -- assumption: the first index belongs to the first
    -- graph, the second to the second graph.
    nodeCmp i j = FG.compare' g i h j
    -- data constructur identifier
    conID x = case x of
        NonT{}      -> 1
        Term _      -> 2
        AuxRoot{}   -> 3
        AuxFoot{}   -> 4
        AuxVert{}   -> 5


-- | A simplified label.  In contrast to `Lab n t`, it provides
-- Eq and Ord instances.  TODO: note that we lose the distinction
-- between `AuxRoot` and `AuxFoot` here.
data SLab n t
    = SNonT (n, Maybe SymID)
    | STerm t
    | SAux (n, Maybe SymID)
    deriving (Show, Eq, Ord)


-- | Simplify label.
simpLab :: Lab n t -> SLab n t
simpLab NonT{..} = SNonT (nonTerm, labID)
simpLab (Term t) = STerm t
simpLab AuxRoot{..} = SAux (nonTerm, Nothing)
simpLab AuxFoot{..} = SAux (nonTerm, Nothing)
simpLab AuxVert{..} = SAux (nonTerm, Just symID)


-- | Show the label.
viewLab :: (View n, View t) => Lab n t -> String
viewLab NonT{..} = "N" ++ viewSym (nonTerm, labID)
viewLab (Term t) = "T(" ++ view t ++ ")"
viewLab AuxRoot{..} = "A" ++ viewSym (nonTerm, Nothing)
viewLab AuxVert{..} = "V" ++ viewSym (nonTerm, Just symID)
viewLab AuxFoot{..} = "F" ++ viewSym (nonTerm, Nothing)


-- | View part of the label.  Utility function.
viewSym :: View n => (n, Maybe SymID) -> String
viewSym (x, Just i) = "(" ++ view x ++ ", " ++ show i ++ ")"
viewSym (x, Nothing) = "(" ++ view x ++ ", _)"


-- | A rule for an elementary tree.
data Rule n t f a = Rule {
    -- | The head of the rule.  TODO: Should never be a foot or a
    -- terminal <- can we enforce this constraint?
      headR :: Lab n t
    -- | The body of the rule
    , bodyR :: [Lab n t]
    -- | The underlying feature graph.
    , graphR :: FG.Graph f a
    } deriving (Show)


instance (Eq n, Eq t, Eq f, Eq a) => Eq (Rule n t f a) where
    r == s = (eq `on` headR) r s
        && ((==) `on` length.bodyR) r s
        && and [eq x y | (x, y) <- zip (bodyR r) (bodyR s)]
        where eq x y = labEq x (graphR r) y (graphR s)


instance (Ord n, Ord t, Ord f, Ord a) => Ord (Rule n t f a) where
    r `compare` s = (cmp `on` headR) r s    `mappend`
        (compare `on` length.bodyR) r s     `mappend`
        mconcat [cmp x y | (x, y) <- zip (bodyR r) (bodyR s)]
        where cmp x y = labCmp x (graphR r) y (graphR s)


-- | Compile a regular rule to an internal rule.
compile :: (Ord i, Ord f, Eq a) => R.Rule n t i f a -> Rule n t f a
compile R.Rule{..} = unJust $ do
    (is, g) <- FT.compiles $ fromList $ (headR : bodyR)
    (rh, rb) <- unCons is
    return $ Rule
        { headR = mkLab headR rh
        , bodyR = mergeBody bodyR rb
        , graphR = g }
  where
    fromList [] = FNil
    fromList (x:xs) = ($ fromList xs) $ case x of
        x@R.AuxRoot{}   -> FNode2
            (R.rootTopFS x) (R.rootBotFS x)
            (R.footTopFS x) (R.footBotFS x)
        x@R.NonT{}      -> FNode1
            (R.rootTopFS x) (R.rootBotFS x)
        x@R.AuxVert{}   -> FNode1
            (R.rootTopFS x) (R.rootBotFS x)
        R.AuxFoot{}     -> FGap
        R.Term _        -> FGap
    mergeBody (R.Term t : xs) (FGap is) =
        Term t : mergeBody xs is
    mergeBody (R.AuxFoot n : xs) (FGap is) =
        AuxFoot n : mergeBody xs is
    mergeBody (x : xs) (FNode1 it ib is) =
        mkLab x (Left (it, ib)) : mergeBody xs is
    mergeBody (x : xs) (FNode2 it ib jt jb is) =
        mkLab x (Right ((it, ib), (jt, jb))) : mergeBody xs is
    mergeBody _ _ = error "compile.mergeBody: unexpected case"
    mkLab R.NonT{..} (Left (it, ib)) = NonT
        { nonTerm = nonTerm
        , labID = labID
        , topID = it
        , botID = ib }
    mkLab R.AuxVert{..} (Left (it, ib)) = AuxVert
        { nonTerm = nonTerm
        , symID = symID
        , topID = it
        , botID = ib }
    mkLab R.AuxRoot{..} (Right ((it, ib), (jt, jb))) = AuxRoot
        { nonTerm = nonTerm
        , topID = it
        , botID = ib
        , footTopID = jt
        , footBotID = jb }
    mkLab _ _ = error "compile.mkLab: unexpected case"


--------------------------------------------------
-- CHART STATE ...
--
-- ... and chart extending operations
--------------------------------------------------


-- | Parsing state: processed initial rule elements and the elements
-- yet to process.
data State n t f a = State {
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
    -- | The underlying feature graph.
    , graph :: FG.Graph f a
    } deriving (Show)


instance (Eq n, Eq t, Eq f, Eq a) => Eq (State n t f a) where
    r == s
         = eqOn beg r s
        && eqOn end r s
        && eqOn gap r s
        && (leq `on` root) r s
        && eqOn (length.left) r s
        && eqOn (length.right) r s
        && and [leq x y | (x, y) <- zip (left r) (left s)]
        && and [leq x y | (x, y) <- zip (right r) (right s)]
      where
        leq x y = labEq x (graph r) y (graph s)
        eqOn f = (==) `on` f


instance (Ord n, Ord t, Ord f, Ord a) => Ord (State n t f a) where
    compare r s = cmpOn beg r s
        `mappend` cmpOn end r s
        `mappend` cmpOn gap r s
        `mappend` (lcmp `on` root) r s
        `mappend` cmpOn (length.left) r s
        `mappend` cmpOn (length.right) r s
        `mappend` mconcat [lcmp x y | (x, y) <- zip (left r) (left s)]
        `mappend` mconcat [lcmp x y | (x, y) <- zip (right r) (right s)]
      where
        lcmp x y = labCmp x (graph r) y (graph s)
        cmpOn f = compare `on` f


-- | Is it a completed (fully-parsed) state?
completed :: State n t f a -> Bool
completed = null . right


-- | Does it represent a regular rule?
regular :: State n t f a -> Bool
regular = isNothing . gap


-- | Does it represent an auxiliary rule?
auxiliary :: State n t f a -> Bool
auxiliary = isJust . gap


-- | Is it top-level?  All top-level states (regular or
-- auxiliary) have an underspecified ID in the root symbol.
topLevel :: State n t f a -> Bool
-- topLevel = isNothing . ide . root
topLevel = not . subLevel


-- | Is it subsidiary (i.e. not top) level?
subLevel :: State n t f a -> Bool
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
    => State n t f a
    -> MaybeT m (Lab n t, [Lab n t])
expects = maybeT . expects'


-- | Print the state.
printState :: (View n, View t) => State n t f a -> IO ()
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


-- | Deconstruct the right part of the state (i.e. labels yet to
-- process) within the MaybeT monad.
expects'
    :: State n t f a
    -> Maybe (Lab n t, [Lab n t])
expects' = decoList . right


-- | Priority type.
type Prio = Int


-- | Priority of a state.  Crucial for the algorithm -- states have
-- to be removed from the queue in a specific order.
prio :: State n t f a -> Prio
prio p = end p


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t f a = EarSt {
    -- | Rules which expect a specific label and which end on a
    -- specific position.
      doneExpEnd :: M.Map (SLab n t, Pos) (S.Set (State n t f a))
    -- | Rules providing a specific non-terminal in the root
    -- and spanning over a given range.
    , doneProSpan :: M.Map (n, Pos, Pos) (S.Set (State n t f a))
    -- | The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    , waiting    :: Q.PSQ (State n t f a) Prio }
    deriving (Show)


-- | Make an initial `EarSt` from a set of states.
mkEarSt
    :: (Ord n, Ord t, Ord a, Ord f)
    => S.Set (State n t f a)
    -> (EarSt n t f a)
mkEarSt s = EarSt
    { doneExpEnd = M.empty
    , doneProSpan = M.empty
    , waiting = Q.fromList
        [ p :-> prio p
        | p <- S.toList s ] }


-- | Earley parser monad.  Contains the input sentence (reader)
-- and the state of the computation `EarSt'.
type Earley n t f a = RWS.RWST [t] () (EarSt n t f a) IO


-- | Read word from the given position of the input.
readInput :: Pos -> MaybeT (Earley n t f a) t
readInput i = do
    -- ask for the input
    xs <- RWS.ask
    -- just a safe way to retrieve the i-th element
    maybeT $ listToMaybe $ drop i xs


-- | Check if the state is not already processed (i.e. in one of the
-- done-related maps).
isProcessed
    :: (Ord n, Ord t, Ord a, Ord f)
    => State n t f a
    -> EarSt n t f a
    -> Bool
isProcessed p EarSt{..} = S.member p $ case expects' p of
    Just (x, _) -> M.findWithDefault S.empty
        (simpLab x, end p) doneExpEnd
    Nothing -> M.findWithDefault S.empty
        (nonTerm $ root p, beg p, end p) doneProSpan


-- | Add the state to the waiting queue.  Check first if it is
-- not already in the set of processed (`done') states.
pushState
    :: (Ord t, Ord n, Ord a, Ord f)
    => State n t f a
    -> Earley n t f a ()
pushState p = RWS.state $ \s ->
    let waiting' = if isProcessed p s
            then waiting s
            else Q.insert p (prio p) (waiting s)
    in  ((), s {waiting = waiting'})


-- | Remove a state from the queue.  In future, the queue
-- will be probably replaced by a priority queue which will allow
-- to order the computations in some smarter way.
popState
    :: (Ord t, Ord n, Ord a, Ord f)
    => Earley n t f a (Maybe (State n t f a))
popState = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (x :-> _, s) -> (Just x, st {waiting = s})


-- | Add the state to the set of processed (`done') states.
saveState
    :: (Ord t, Ord n, Ord a, Ord f)
    => State n t f a
    -> Earley n t f a ()
saveState p = RWS.state $ \s -> ((), doit s)
  where
    doit st@EarSt{..} = st
      { doneExpEnd = case expects' p of
          Just (x, _) -> M.insertWith S.union (simpLab x, end p)
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
    :: (Ord n, Ord t) => SLab n t -> Pos
    -> P.ListT (Earley n t f a) (State n t f a)
expectEnd x i = do
  EarSt{..} <- lift RWS.get
  listValues (x, i) doneExpEnd


-- | Return all completed states with:
-- * the given root non-terminal value
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t f a) (State n t f a)
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
tryScan
    :: (VOrd t, VOrd n, Ord a, Ord f)
    => State n t f a
    -> Earley n t f a ()
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
trySubst
    :: (VOrd t, VOrd n, Ord a, Ord f)
    => State n t f a
    -> Earley n t f a ()
trySubst p = void $ P.runListT $ do
    -- make sure that `p' is a fully-parsed regular rule
    guard $ completed p && regular p
    -- find rules which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    q <- expectEnd (simpLab $ root p) (beg p)
    (r@NonT{}, _) <- some $ expects' q
    -- unify the corresponding feature structures
    -- TODO: We assume here that graph IDs are disjoint.
    g' <- some $ flip J.execJoin
        (FG.fromTwo (graph p) (graph q)) $ do
            J.join (topID $ root p) (topID r)
            -- in practice, `botID r` should be empty, but
            -- it seems that we don't lose anything by taking
            -- the other possibility into account.
            J.join (botID $ root p) (botID r)
    -- construct the resultant state
    let q' = q
            { end = end p
            , left = root p : left q
            , right = tail (right q)
            , graph = g' }
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
--
-- No FS unification is taking place here, it is performed at the
-- level of `tryAdjoinTerm(inate)`.
--
tryAdjoinInit
    :: (VOrd n, VOrd t, Ord a, Ord f)
    => State n t f a
    -> Earley n t f a ()
tryAdjoinInit p = void $ P.runListT $ do
    -- make sure that `p' is fully-parsed
    guard $ completed p
    -- find all rules which expect a real foot (with ID == Nothing)
    -- and which end where `p' begins.
    let u = nonTerm (root p)
    q <- expectEnd (SAux (u, Nothing)) (beg p)  
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
tryAdjoinCont
    :: (VOrd n, VOrd t, Ord f, Ord a)
    => State n t f a
    -> Earley n t f a ()
tryAdjoinCont p = void $ P.runListT $ do
    -- make sure that `p' is a completed, sub-level auxiliary rule
    guard $ completed p && subLevel p && auxiliary p
    -- find all rules which expect a foot provided by `p'
    -- and which end where `p' begins.
    q <- expectEnd (simpLab $ root p) (beg p)
    (r@AuxVert{}, _) <- some $ expects' q
    -- unify the feature structures corresponding to the 'p's
    -- root and 'q's foot.  TODO: We assume here that graph IDs
    -- are disjoint.
    g' <- some $ flip J.execJoin
        (FG.fromTwo (graph p) (graph q)) $ do
            J.join (topID $ root p) (topID r)
            J.join (botID $ root p) (botID r)
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = q
            { gap = gap p, end = end p
            , left = r : left q
            , right = tail (right q)
            , graph = g' }
    -- logging info
    lift . lift $ do
        putStr "[B]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    -- push the resulting state into the waiting queue
    lift $ pushState q'


-- | Adjoin a fully-parsed auxiliary state to a partially parsed
-- tree represented by a fully parsed rule/state.
tryAdjoinTerm
    :: (VOrd t, VOrd n, Ord a, Ord f)
    => State n t f a
    -> Earley n t f a ()
tryAdjoinTerm p = void $ P.runListT $ do
    -- make sure that `p' is a completed, top-level state ...
    guard $ completed p && topLevel p
    -- ... and that it is an auxiliary state
    (gapBeg, gapEnd) <- each $ maybeToList $ gap p
    -- it is top-level, so we can also make sure that the
    -- root is an AuxRoot.
    pRoot@AuxRoot{} <- some $ Just $ root p
    -- take all completed rules with a given span
    -- and a given root non-terminal (IDs irrelevant)
    q <- rootSpan (nonTerm $ root p) (gapBeg, gapEnd)
    -- make sure that `q' is completed as well and that it is
    -- either a regular rule or an intermediate auxiliary rule
    -- ((<=) used as an implication here!)
    guard $ completed q && auxiliary q <= subLevel q
    -- TODO: it seems that some of the constraints given above
    -- follow from the code below:
    qRoot <- some $ case root q of
        x@NonT{}    -> Just x
        x@AuxVert{} -> Just x
        _           -> Nothing
    -- TODO: We assume here that graph IDs are disjoint.
    g' <- some $ flip J.execJoin
        (FG.fromTwo (graph p) (graph q)) $ do
            J.join (topID pRoot)     (topID qRoot)
            J.join (footBotID pRoot) (botID qRoot)
    let q' = q
            { beg = beg p
            , end = end p
            , graph = g' }
    lift . lift $ do
        putStr "[C]  " >> printState p
        putStr "  +  " >> printState q
        putStr "  :  " >> printState q'
    lift $ pushState q'


--------------------------------------------------
-- Utility
--------------------------------------------------


-- | Retrieve the Just value.  Error otherwise.
unJust :: Maybe a -> a
unJust (Just x) = x
unJust Nothing = error "unJust: got Nothing!" 


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


-- | A list with potential gaps.
data FList a
    = FNil
    | FGap (FList a)
    | FNode1 a a (FList a)
    | FNode2 a a a a (FList a)
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


-- | Uncons the FList.  Ignore the leading gaps.
unCons :: FList a -> Maybe (Either (a, a) ((a, a), (a, a)), FList a)
unCons FNil = Nothing
unCons (FGap xs) = unCons xs
unCons (FNode1 x x' xs) = Just (Left (x, x'), xs)
unCons (FNode2 x x' y y' xs) = Just (Right ((x, x'), (y, y')), xs)
