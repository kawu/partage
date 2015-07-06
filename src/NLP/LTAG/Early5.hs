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
        , featID    :: FID }
    | Term t
    | AuxRoot
        { nonTerm   :: n
        , featID    :: FID
        , footID    :: FID }
    | AuxFoot
        { nonTerm   :: n }
    | AuxVert
        { nonTerm   :: n
        , symID     :: SymID
        , featID    :: FID }
    deriving (Show)


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
    r == s = (labEq `on` headR) r s
          && eqOn (length.bodyR) r s
          && and [labEq x y | (x, y) <- zip (bodyR r) (bodyR s)]
      where
        labEq x@NonT{} y@NonT{}
            =  eqOn nonTerm x y
            && eqOn labID x y
            && nodeEqOn featID x y
        labEq (Term x) (Term y)
            =  x == y 
        labEq x@AuxRoot{} y@AuxRoot{}
            =  eqOn nonTerm x y
            && nodeEqOn featID x y
            && nodeEqOn footID x y
        labEq (AuxFoot x) (AuxFoot y)
            =  x == y
        labEq x@AuxVert{} y@AuxVert{}
            =  eqOn nonTerm x y
            && eqOn symID x y
            && nodeEqOn featID x y
        labEq _ _ = False
        eqOn f = (==) `on` f
        -- assumption: the first index belongs to the first
        -- graph, the second to the second graph.
        nodeEqOn f = nodeEq `on` f
        nodeEq i j = FG.equal
            (graphR r) i
            (graphR s) j 


-- -- | Compile a regular rule to an internal rule.
-- compile :: (Ord i, Ord f, Eq a) => R.Rule n t i f a -> Rule n t f a
-- compile R.Rule{..} = unJust $ do
--     (is, g) <- FT.compiles $ fromList $ (headR : bodyR)
--     (rh, rb) <- unCons is
--     return $ Rule
--         { headR = mkLab headR rh
--         , bodyR = mergeBody bodyR rb
--         , graphR = g }
--   where
--     fromList [] = FNil
--     fromList (x:xs) = ($ fromList xs) $ case x of
--         x@R.AuxRoot{}   -> FNode2 (R.featStr x) (R.footStr x)
--         x@R.NonT{}      -> FNode1 $ R.featStr x
--         x@R.AuxVert{}   -> FNode1 $ R.featStr x
--         R.AuxFoot{}     -> FGap
--         R.Term _        -> FGap
--     mergeBody (R.Term t : xs) (FGap is) =
--         Term t : mergeBody xs is
--     mergeBody (R.AuxFoot n : xs) (FGap is) =
--         AuxFoot n : mergeBody xs is
--     mergeBody (x : xs) (FNode1 i is) =
--         mkLab x (Left i) : mergeBody xs is
--     mergeBody (x : xs) (FNode2 i j is) =
--         mkLab x (Right (i, j)) : mergeBody xs is
--     mergeBody _ _ = error "compile.mergeBody: unexpected case"
--     mkLab R.NonT{..} (Left i) = NonT
--         { nonTerm = nonTerm
--         , labID = labID
--         , featID = i }
--     mkLab R.AuxVert{..} (Left i) = AuxVert
--         { nonTerm = nonTerm
--         , symID = symID
--         , featID = i }
--     mkLab R.AuxRoot{..} (Right (i, j)) = AuxRoot
--         { nonTerm = nonTerm
--         , featID = i
--         , footID = j }
--     mkLab _ _ = error "compile.mkLab: unexpected case"
-- 
-- 
-- --------------------------------------------------
-- -- CHART STATE ...
-- --
-- -- ... and chart extending operations
-- --------------------------------------------------
-- 
-- 
-- -- | Parsing state: processed initial rule elements and the elements
-- -- yet to process.
-- data State n t f a = State {
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
--     -- | The underlying feature graph.
--     , graph :: FG.Graph f a
--     } deriving (Show, Eq, Ord)
-- 
-- 
-- -- | Is it a completed (fully-parsed) state?
-- completed :: State n t f a -> Bool
-- completed = null . right
-- 
-- 
-- -- | Does it represent a regular rule?
-- regular :: State n t f a -> Bool
-- regular = isNothing . gap
-- 
-- 
-- -- | Does it represent an auxiliary rule?
-- auxiliary :: State n t f a -> Bool
-- auxiliary = isJust . gap
-- 
-- 
-- -- | Is it top-level?  All top-level states (regular or
-- -- auxiliary) have an underspecified ID in the root symbol.
-- topLevel :: State n t f a -> Bool
-- -- topLevel = isNothing . ide . root
-- topLevel = not . subLevel
-- 
-- 
-- -- | Is it subsidiary (i.e. not top) level?
-- subLevel :: State n t f a -> Bool
-- -- subLevel = isJust . ide . root
-- subLevel x = case root x of
--     NonT{..}  -> isJust labID
--     AuxVert{} -> True
--     Term _    -> True
--     _         -> False
--     
-- 
-- -- | Deconstruct the right part of the state (i.e. labels yet to
-- -- process) within the MaybeT monad.
-- expects
--     :: Monad m
--     => State n t f a
--     -> MaybeT m (Lab n t, [Lab n t])
-- expects = maybeT . expects'
-- 
-- 
-- -- | Print the state.
-- printState :: (View n, View t) => State n t f a -> IO ()
-- printState State{..} = do
--     putStr $ viewLab root
--     putStr " -> "
--     putStr $ intercalate " " $
--         map viewLab (reverse left) ++ ["*"] ++ map viewLab right
--     putStr " <"
--     putStr $ show beg
--     putStr ", "
--     case gap of
--         Nothing -> return ()
--         Just (p, q) -> do
--             putStr $ show p
--             putStr ", "
--             putStr $ show q
--             putStr ", "
--     putStr $ show end
--     putStrLn ">"
-- 
-- 
-- -- | Deconstruct the right part of the state (i.e. labels yet to
-- -- process) within the MaybeT monad.
-- expects'
--     :: State n t f a
--     -> Maybe (Lab n t, [Lab n t])
-- expects' = decoList . right
-- 
-- 
-- -- | Priority type.
-- type Prio = Int
-- 
-- 
-- -- | Priority of a state.  Crucial for the algorithm -- states have
-- -- to be removed from the queue in a specific order.
-- prio :: State n t f a -> Prio
-- prio p = end p
-- 
-- 
-- --------------------------------------------------
-- -- Earley monad
-- --------------------------------------------------
-- 
-- 
-- -- | The state of the earley monad.
-- data EarSt n t f a = EarSt {
--     -- | Rules which expect a specific label and which end on a
--     -- specific position.
--       doneExpEnd :: M.Map (SLab n t, Pos) (S.Set (State n t f a))
--     -- | Rules providing a specific non-terminal in the root
--     -- and spanning over a given range.
--     , doneProSpan :: M.Map (n, Pos, Pos) (S.Set (State n t f a))
--     -- | The set of states waiting on the queue to be processed.
--     -- Invariant: the intersection of `done' and `waiting' states
--     -- is empty.
--     , waiting    :: Q.PSQ (State n t f a) Prio }
--     deriving (Show)
-- 
-- 
-- -- | Make an initial `EarSt` from a set of states.
-- mkEarSt
--     :: (Ord n, Ord t, Ord a, Ord f)
--     => S.Set (State n t f a)
--     -> (EarSt n t f a)
-- mkEarSt s = EarSt
--     { doneExpEnd = M.empty
--     , doneProSpan = M.empty
--     , waiting = Q.fromList
--         [ p :-> prio p
--         | p <- S.toList s ] }
-- 
-- 
-- -- | Earley parser monad.  Contains the input sentence (reader)
-- -- and the state of the computation `EarSt'.
-- type Earley n t f a = RWS.RWST [t] () (EarSt n t f a) IO
-- 
-- 
-- -- | Read word from the given position of the input.
-- readInput :: Pos -> MaybeT (Earley n t f a) t
-- readInput i = do
--     -- ask for the input
--     xs <- RWS.ask
--     -- just a safe way to retrieve the i-th element
--     maybeT $ listToMaybe $ drop i xs
-- 
-- 
-- -- | Check if the state is not already processed (i.e. in one of the
-- -- done-related maps).
-- isProcessed
--     :: (Ord n, Ord t, Ord a, Ord f)
--     => State n t f a
--     -> EarSt n t f a
--     -> Bool
-- isProcessed p EarSt{..} = S.member p $ case expects' p of
--     Just (x, _) -> M.findWithDefault S.empty
--         (simpLab x, end p) doneExpEnd
--     Nothing -> M.findWithDefault S.empty
--         (nonTerm $ root p, beg p, end p) doneProSpan
-- 
-- 
-- -- | Add the state to the waiting queue.  Check first if it is
-- -- not already in the set of processed (`done') states.
-- pushState
--     :: (Ord t, Ord n, Ord a, Ord f)
--     => State n t f a
--     -> Earley n t f a ()
-- pushState p = RWS.state $ \s ->
--     let waiting' = if isProcessed p s
--             then waiting s
--             else Q.insert p (prio p) (waiting s)
--     in  ((), s {waiting = waiting'})
-- 
-- 
-- -- | Remove a state from the queue.  In future, the queue
-- -- will be probably replaced by a priority queue which will allow
-- -- to order the computations in some smarter way.
-- popState
--     :: (Ord t, Ord n, Ord a, Ord f)
--     => Earley n t f a (Maybe (State n t f a))
-- popState = RWS.state $ \st -> case Q.minView (waiting st) of
--     Nothing -> (Nothing, st)
--     Just (x :-> _, s) -> (Just x, st {waiting = s})
-- 
-- 
-- -- | Add the state to the set of processed (`done') states.
-- saveState
--     :: (Ord t, Ord n, Ord a, Ord f)
--     => State n t f a
--     -> Earley n t f a ()
-- saveState p = RWS.state $ \s -> ((), doit s)
--   where
--     doit st@EarSt{..} = st
--       { doneExpEnd = case expects' p of
--           Just (x, _) -> M.insertWith S.union (simpLab x, end p)
--                               (S.singleton p) doneExpEnd
--           Nothing -> doneExpEnd
--       , doneProSpan = if completed p
--           then M.insertWith S.union (nonTerm $ root p, beg p, end p)
--                (S.singleton p) doneProSpan
--           else doneProSpan }
-- 
-- 
-- -- | Return all completed states which:
-- -- * expect a given label,
-- -- * end on the given position.
-- expectEnd
--     :: (Ord n, Ord t) => SLab n t -> Pos
--     -> P.ListT (Earley n t f a) (State n t f a)
-- expectEnd x i = do
--   EarSt{..} <- lift RWS.get
--   listValues (x, i) doneExpEnd
-- 
-- 
-- -- | Return all completed states with:
-- -- * the given root non-terminal value
-- -- * the given span
-- rootSpan
--     :: Ord n => n -> (Pos, Pos)
--     -> P.ListT (Earley n t f a) (State n t f a)
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
-- 
-- 
-- --------------------------------------------------
-- -- SCAN
-- --------------------------------------------------
-- 
-- 
-- -- | Try to perform SCAN on the given state.
-- tryScan
--     :: (VOrd t, VOrd n, Ord a, Ord f)
--     => State n t f a
--     -> Earley n t f a ()
-- tryScan p = void $ runMaybeT $ do
--     -- check that the state expects a terminal on the right
--     (Term t, right') <- expects p
--     -- read the word immediately following the ending position of
--     -- the state
--     c <- readInput $ end p
--     -- make sure that what the rule expects is consistent with
--     -- the input
--     guard $ c == t
--     -- construct the resultant state
--     let p' = p
--             { end = end p + 1
--             , left = Term t : left p
--             , right = right' }
--     -- print logging information
--     lift . lift $ do
--         putStr "[S]  " >> printState p
--         putStr "  :  " >> printState p'
--     -- push the resulting state into the waiting queue
--     lift $ pushState p'
-- 
-- 
-- --------------------------------------------------
-- -- SUBST
-- --------------------------------------------------
-- 
-- 
-- -- | Try to use the state (only if fully parsed) to complement
-- -- (=> substitution) other rules.
-- trySubst
--     :: (VOrd t, VOrd n, Ord a, Ord f)
--     => State n t f a
--     -> Earley n t f a ()
-- trySubst p = void $ P.runListT $ do
--     -- make sure that `p' is a fully-parsed regular rule
--     guard $ completed p && regular p
--     -- find rules which end where `p' begins and which
--     -- expect the non-terminal provided by `p' (ID included)
--     q <- expectEnd (simpLab $ root p) (beg p)
--     (r@NonT{}, _) <- some $ expects' q
--     -- unify the corresponding feature structures
--     -- TODO: We assume here that graph IDs are disjoint.
--     g' <- some $ J.execJoin
--         (J.join (featID $ root p) (featID r))
--         (FG.fromTwo (graph p) (graph q))
--     -- construct the resultant state
--     let q' = q
--             { end = end p
--             , left = root p : left q
--             , right = tail (right q)
--             , graph = g' }
--     -- print logging information
--     lift . lift $ do
--         putStr "[U]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     -- push the resulting state into the waiting queue
--     lift $ pushState q'
-- 
-- 
-- --------------------------------------------------
-- -- ADJOIN
-- --------------------------------------------------
-- 
-- 
-- -- | `tryAdjoinInit p q':
-- -- * `p' is a completed state (regular or auxiliary)
-- -- * `q' not completed and expects a *real* foot
-- --
-- -- No FS unification is taking place here, it is performed at the
-- -- level of `tryAdjoinTerm(inate)`.
-- --
-- tryAdjoinInit
--     :: (VOrd n, VOrd t, Ord a, Ord f)
--     => State n t f a
--     -> Earley n t f a ()
-- tryAdjoinInit p = void $ P.runListT $ do
--     -- make sure that `p' is fully-parsed
--     guard $ completed p
--     -- find all rules which expect a real foot (with ID == Nothing)
--     -- and which end where `p' begins.
--     let u = nonTerm (root p)
--     q <- expectEnd (SAux (u, Nothing)) (beg p)  
--     (r@AuxFoot{}, _) <- some $ expects' q
--     -- construct the resultant state
--     let q' = q
--             { gap = Just (beg p, end p)
--             , end = end p
--             , left = r : left q
--             , right = tail (right q) }
--     -- print logging information
--     lift . lift $ do
--         putStr "[A]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     -- push the resulting state into the waiting queue
--     lift $ pushState q'
-- 
-- 
-- -- | `tryAdjoinCont p q':
-- -- * `p' is a completed, auxiliary state
-- -- * `q' not completed and expects a *dummy* foot
-- tryAdjoinCont
--     :: (VOrd n, VOrd t, Ord f, Ord a)
--     => State n t f a
--     -> Earley n t f a ()
-- tryAdjoinCont p = void $ P.runListT $ do
--     -- make sure that `p' is a completed, sub-level auxiliary rule
--     guard $ completed p && subLevel p && auxiliary p
--     -- find all rules which expect a foot provided by `p'
--     -- and which end where `p' begins.
--     q <- expectEnd (simpLab $ root p) (beg p)
--     (r@AuxVert{}, _) <- some $ expects' q
--     -- unify the feature structures corresponding to the 'p's
--     -- root and 'q's foot.  TODO: We assume here that graph IDs
--     -- are disjoint.
--     g' <- some $ J.execJoin
--         (J.join (featID $ root p) (featID r))
--         (FG.fromTwo (graph p) (graph q))
--     -- construct the resulting state; the span of the gap of the
--     -- inner state `p' is copied to the outer state based on `q'
--     let q' = q
--             { gap = gap p, end = end p
--             , left = r : left q
--             , right = tail (right q)
--             , graph = g' }
--     -- logging info
--     lift . lift $ do
--         putStr "[B]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     -- push the resulting state into the waiting queue
--     lift $ pushState q'
-- 
-- 
-- -- | Adjoin a fully-parsed auxiliary state to a partially parsed
-- -- tree represented by a fully parsed rule/state.
-- tryAdjoinTerm
--     :: (VOrd t, VOrd n, Ord a, Ord f)
--     => State n t f a
--     -> Earley n t f a ()
-- tryAdjoinTerm p = void $ P.runListT $ do
--     -- make sure that `p' is a completed, top-level state ...
--     guard $ completed p && topLevel p
--     -- ... and that it is an auxiliary state
--     (gapBeg, gapEnd) <- each $ maybeToList $ gap p
--     -- it is top-level, so we can also make sure that the
--     -- root is an AuxRoot.
--     pRoot@AuxRoot{} <- some $ Just $ root p
--     -- take all completed rules with a given span
--     -- and a given root non-terminal (IDs irrelevant)
--     q <- rootSpan (nonTerm $ root p) (gapBeg, gapEnd)
--     -- make sure that `q' is completed as well and that it is
--     -- either a regular rule or an intermediate auxiliary rule
--     -- ((<=) used as an implication here!)
--     guard $ completed q && auxiliary q <= subLevel q
--     -- TODO: it seems that some of the constraints follow
--     -- from the code below:
--     qRoot <- some $ case root q of
--         x@NonT{}    -> Just x
--         x@AuxVert{} -> Just x
--         _           -> Nothing
--     -- unify the feature structures corresponding to the 'p's
--     -- foot *and* root (!?) with 'q's root.
--     -- TODO: We assume here that graph IDs are disjoint.
--     g' <- some $ flip J.execJoin
--         (FG.fromTwo (graph p) (graph q)) $ do
--             J.join (featID $ pRoot) (featID qRoot)
--             J.join (footID $ pRoot) (featID qRoot)
--     let q' = q
--             { beg = beg p
--             , end = end p
--             , graph = g' }
--     lift . lift $ do
--         putStr "[C]  " >> printState p
--         putStr "  +  " >> printState q
--         putStr "  :  " >> printState q'
--     lift $ pushState q'


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
    | FNode1 a (FList a)
    | FNode2 a a (FList a)
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


-- | Uncons the FList.  Ignore the leading gaps.
unCons :: FList a -> Maybe (Either a (a, a), FList a)
unCons FNil = Nothing
unCons (FGap xs) = unCons xs
unCons (FNode1 x xs) = Just (Left x, xs)
unCons (FNode2 x y xs) = Just (Right (x, y), xs)
