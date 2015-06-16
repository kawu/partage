{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}


{- 
 - Early parser for TAGs.  Third preliminary version :-).
 -}


module NLP.LTAG.Early3 where


import           Control.Applicative ((<$>))
import           Control.Monad (guard, void)
import qualified Control.Monad.RWS.Strict as RWS
import           Control.Monad.Trans.Maybe (MaybeT(..))
import           Control.Monad.Trans.Class (lift)

import qualified Data.Set as S
import           Data.Maybe (isNothing, isJust, listToMaybe)

import qualified Pipes as P

import qualified NLP.LTAG.Tree as G


class (Show a, Ord a) => SOrd a where

instance (Show a, Ord a) => SOrd a where


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


-- | Label: a symbol, a terminal or a generalized foot node.
-- Generalized in the sense that it can represent not only a foot
-- note of an auxiliary tree, but also a non-terminal on the path
-- from the root to the real foot note of an auxiliary tree.
data Lab n t
    = NonT (Sym n)
    | Term t
    | Foot (Sym n)
    deriving (Show, Eq, Ord)


-- | A rule for initial tree.
data Rule n t = Rule {
    -- | The head of the rule
      headI :: Sym n
    -- | The body of the rule
    , body  :: [Lab n t]
    } deriving (Show, Eq, Ord)


-- -- | A rule in general.
-- type Rule n t = Either (Init n t) (Aux n t)


--------------------------
-- Rule generation monad
--------------------------


-- | Identifier generation monad.
type RM n t a = RWS.RWS () [Rule n t] Int a


-- | Pull the next identifier.
nextID :: RM n t ID
nextID = RWS.state $ \i -> (i, i + 1)


-- -- | Save the rule in the writer component of the monad.
-- keepInit :: Init n t -> RM n t ()
-- keepInit = keepRule . Left
-- 
-- 
-- -- | Save the rule in the writer component of the monad.
-- keepAux :: Aux n t -> RM n t ()
-- keepAux = keepRule . Right


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


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt
    { done :: S.Set (State n t)
    , waiting :: S.Set (State n t) }
    deriving (Show, Eq, Ord)


-- | Dummy Earley computation monad for now.
type Earley n t = RWS.RWST [t] () (EarSt n t) IO


-- | Read input on the given position.
readInput :: Pos -> MaybeT (Earley n t) t
readInput i = do
    xs <- RWS.ask
    maybeT $ listToMaybe $ drop i xs


-- | Retrieve the set of "done" states. 
getDone :: Earley n t (S.Set (State n t))
getDone = done <$> RWS.get


-- | Add the state to the queue.  Check first if it is not already in
-- the set of processed ("done") states.
pushState :: (Ord t, Ord n) => State n t -> Earley n t ()
pushState p = RWS.state $ \s ->
    let waiting' = if S.member p (done s)
            then waiting s
            else S.insert p (waiting s)
    in  ((), s {waiting = waiting'})


-- | Pop a state from the queue.
popState :: (Ord t, Ord n) => Earley n t (Maybe (State n t))
popState = RWS.state $ \st -> case S.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (x, s) -> (Just x, st {waiting = s})


-- | Add the state to the queue.
saveState :: (Ord t, Ord n) => State n t -> Earley n t ()
saveState p = RWS.state $ \s -> ((),
    s {done = S.insert p (done s)})


-- | Earley.
earley
    :: (SOrd t, SOrd n)
    => S.Set (Rule n t) -- ^ The grammar (set of rules)
    -> [t]              -- ^ Input sentence
    -> IO (S.Set (State n t))
earley gram xs =
    done . fst <$> RWS.execRWST loop xs st0
  where
    st0 = EarSt S.empty $ S.fromList
        [ State
            { root = headI
            , left = []
            , right = body
            , beg = i, end = i
            , gap = Nothing }
        | Rule{..} <- S.toList gram
        , i <- [0 .. length xs - 1] ]
    loop = popState >>= \mp -> case mp of
        Nothing -> return ()
        Just p -> step p >> loop

-- | Step of the algorithm loop.  `p' is the state poped off from the
-- queue.
step :: (SOrd t, SOrd n) => State n t -> Earley n t ()
step p = do
    -- lift $ putStr "PP:  " >> print p
    -- Try to scan it
    tryScan p
    P.runListT $ do
        -- For each state in the set of already processed states
        let each = P.Select . P.each
        q <- each . S.toList =<< lift getDone
        lift $ do
            tryCompose p q
            tryCompose q p
    -- | Processing of the state is done.
    saveState p


-- | Try to perform the SCAN operation w.r.t. to the given state.
tryScan :: (SOrd t, SOrd n) => State n t -> Earley n t ()
tryScan p = void $ runMaybeT $ do
    c <- readInput $ end p
    (Term t, right') <- maybeT $ decoList $ right p
    guard $ c == t
    let p' = p
            { end = end p + 1
            , left = Term t : left p
            , right = right' }
    lift . lift $ do
        putStr "[S]  " >> print p
        putStr "  :  " >> print p'
    lift $ pushState p'


-- | Try compose two states.
tryCompose
    :: (SOrd t, SOrd n)
    => State n t
    -> State n t
    -> Earley n t ()
tryCompose p q = do
    trySubst p q
    tryAdjoin p q
    tryAdjoin' p q
    tryComplete p q
    -- tryComplete' p q


-- | Try substitute the first state with the second state.
trySubst
    :: (SOrd t, SOrd n)
    => State n t
    -> State n t
    -> Earley n t ()
trySubst p q = void $ runMaybeT $ do
    -- make sure that `p' is completed...
    guard $ null $ right p
    -- ... and that it is a regular rule
    guard $ isNothing $ gap p
    -- make sure `q' is not yet completed and expects
    -- a non-terminal
    (NonT x, right') <- maybeT $ decoList $ right q
    -- make sure that `p' begins where `q' ends
    guard $ beg p == end q
    -- make sure that the root of `p' matches with the next
    -- non-terminal of `q'; IDs of the symbols have to be
    -- the same as well
    guard $ root p == x
    let q' = q
            { end = end p
            , left = NonT x : left q
            , right = right' }
    lift . lift $ do
        putStr "[U]  " >> print p
        putStr "  +  " >> print q
        putStr "  :  " >> print q'
    lift $ pushState q'


-- | Try adjoining...
tryAdjoin
    :: (SOrd n, SOrd t)
    => State n t
    -> State n t
    -> Earley n t ()
tryAdjoin p q = void $ runMaybeT $ do
    -- make sure that `p' is completed...
    guard $ null $ right p
--     -- ... and that it is a regular rule
--     guard $ isNothing $ gap p  <- NOPE, not necessarily!
    -- make sure `q' is not yet completed and expects
    -- a real foot
    (Foot x@(u, Nothing), right') <- maybeT $ decoList $ right q
    -- make sure that `p' begins where `q' ends
    guard $ beg p == end q
    -- make sure that the root of `p' matches with the non-terminal
    -- of the foot of `q'; IDs of the symbols *no not* have to be
    -- the same
    guard $ fst (root p) == u
    let q' = q
            { gap = Just (beg p, end p)
            , end = end p
            , left = Foot x : left q
            , right = right' }
    lift . lift $ do
        putStr "[A]  " >> print p
        putStr "  +  " >> print q
        putStr "  :  " >> print q'
    lift $ pushState q'


-- | Try adjoining, second option...
tryAdjoin'
    :: (SOrd n, SOrd t)
    => State n t
    -> State n t
    -> Earley n t ()
tryAdjoin' p q = void $ runMaybeT $ do
    -- make sure that `p' is completed...
    guard $ null $ right p
    -- ... and that it is an auxiliary rule
    guard $ isJust $ gap p
    -- make sure `q' is not yet completed and expects
    -- a dummy foot
    (Foot x@(_, Just _), right') <- maybeT $ decoList $ right q
    -- make sure that `p' begins where `q' ends
    guard $ beg p == end q
    -- make sure that the root of `p' matches with the non-terminal
    -- of the foot of `q'; IDs of the symbols have to be the same
    guard $ root p == x
    let q' = q
            { gap = gap p
            , end = end p
            , left = Foot x : left q
            , right = right' }
    lift . lift $ do
        putStr "[B]  " >> print p
        putStr "  +  " >> print q
        putStr "  :  " >> print q'
    lift $ pushState q'


-- | Adjoin a fully parsed auxiliary rule to a partially parsed
-- initial tree represented by a regular, fully parsed rule.
tryComplete
    :: (SOrd t, SOrd n)
    => State n t
    -> State n t
    -> Earley n t ()
tryComplete p q = void $ runMaybeT $ do
    -- make sure that `p' is completed ...
    guard $ null $ right p
    -- ... and that it is an auxiliary rule ...
    (gapBeg, gapEnd) <- maybeT $ gap p
    -- ... and also that it's a top-level auxiliary rule
    guard $ isNothing $ snd $ root p
    -- make sure that `q' is completed as well ...
    guard $ null $ right q
    -- ... and that it is either a regular rule or an intermediate
    -- auxiliary rule; (<=) used as an implication here!
    guard $ (isJust $ gap q) <= (isJust $ snd $ root q)
    -- finally, check that the spans match
    guard $ gapBeg == beg q
    guard $ gapEnd == end q
    -- and that non-terminals match (not IDs)
    guard $ fst (root p) == fst (root q)
    let q' = q
            { beg = beg p
            , end = end p }
    lift . lift $ do
        putStr "[C]  " >> print p
        putStr "  +  " >> print q
        putStr "  :  " >> print q'
    lift $ pushState q'


-- -- | Adjoin a fully parsed auxiliary rule to a partially parsed
-- -- tree represented by an auxiliary, fully parsed rule.
-- tryComplete'
--     :: (SOrd t, SOrd n)
--     => State n t
--     -> State n t
--     -> Earley n t ()
-- tryComplete' p q = void $ runMaybeT $ do
--     -- make sure that `p' is completed ...
--     guard $ null $ right p
--     -- ... and that it is an auxiliary rule ...
--     (gapBeg, gapEnd) <- maybeT $ gap p
--     -- ... and also that it's a top-level auxiliary rule
--     guard $ isNothing $ snd $ root p
--     -- make sure that `q' is completed as well ...
--     guard $ null $ right q
--     -- ... and that it is an intermediate auxiliary rule
--     guard $ isJust $ gap q
--     guard $ isJust $ snd $ root q
--     -- finally, check that the spans match
--     guard $ gapBeg == beg q
--     guard $ gapEnd == end q
--     -- and that non-terminals match (not IDs)
--     guard $ fst (root p) == fst (root q)
--     let q' = q
--             { beg = beg p
--             , end = end p }
--     lift . lift $ do
--         putStr "[D]  " >> print p
--         putStr "  +  " >> print q
--         putStr "  :  " >> print q'
--     lift $ pushState q'


--------------------------------------------------
-- UTILS
--------------------------------------------------


-- | Deconstruct list.  Utility function.
decoList :: [a] -> Maybe (a, [a])
decoList [] = Nothing
decoList (y:ys) = Just (y, ys)


-- | A non-terminal expected by the rule.
expected :: [a] -> Maybe a
expected xs = fst <$> decoList xs


-- | MaybeT transformer.
maybeT :: Monad m => Maybe a -> MaybeT m a
maybeT = MaybeT . return
