{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}


{- 
 - Early parser for TAGs.  Third preliminary version :-).
 -}


module NLP.LTAG.Early3 where


import           Control.Applicative ((<$>))
import           Control.Monad (guard, void)
import qualified Control.Monad.RWS.Strict as RWS
import           Control.Monad.Trans.Maybe (MaybeT(..))
import           Control.Monad.Trans.Class (lift)

import qualified Pipes as P
import qualified Data.Set as S
import           Data.Maybe (isNothing, isJust)

import qualified NLP.LTAG.Tree as G


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
        keepRule $ Rule x []
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
        return $ NonT x
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
type Earley n t a = RWS.RWS [t] () (EarSt n t) a


-- | Read input on the given position.
readInput :: Pos -> Earley n t t 
readInput i = RWS.reader (!! i)


-- | Retrieve the set of "done" states. 
getDone :: Earley n t (S.Set (State n t))
getDone = done <$> RWS.get


-- | Add the state to the queue.
pushState :: (Ord t, Ord n) => State n t -> Earley n t ()
pushState p = RWS.state $ \s -> ((),
    s {waiting = S.insert p (waiting s)})


-- | Add the state to the queue.
saveState :: (Ord t, Ord n) => State n t -> Earley n t ()
saveState p = RWS.state $ \s -> ((),
    s {done = S.insert p (done s)})


-- | Step of the algorithm loop.  `p' is the state poped off from the
-- queue.
step :: (Ord t, Ord n) => State n t -> Earley n t ()
step p = do
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
tryScan :: (Ord t, Ord n) => State n t -> Earley n t ()
tryScan p = do 
    c <- readInput $ end p
    void $ runMaybeT $ do
        (Term t, right') <- maybeT $ decoList $ right p
        guard $ c == t
        lift $ pushState $ p
            { end = end p + 1
            , left = Term t : left p
            , right = right' }


-- | Try compose two states.
tryCompose
    :: (Ord t, Ord n)
    => State n t
    -> State n t
    -> Earley n t ()
tryCompose p q = do
    trySubst p q
    tryAdjoin p q
    -- tryAdjoin' p q


-- | Try substitute the first state with the second state.
trySubst
    :: (Ord t, Ord n)
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
    -- make sure that the root of `p' matches with the next
    -- non-terminal of `q'; IDs of the symbols have to be
    -- the same as well
    guard $ root p == x
    lift $ pushState $ q
        { end = end p
        , left = NonT x : left q
        , right = right' }


-- | Try adjoining...
tryAdjoin
    :: (Ord n, Ord t)
    => State n t
    -> State n t
    -> Earley n t ()
tryAdjoin p q = void $ runMaybeT $ do
    -- make sure that `p' is completed...
    guard $ null $ right p
    -- ... and that it is a regular rule
    guard $ isNothing $ gap p
    -- make sure `q' is not yet completed and expects
    -- a real foot
    (Foot x@(u, Nothing), right') <- maybeT $ decoList $ right q
    -- make sure that the root of `p' matches with the non-terminal
    -- of the foot of `q'; IDs of the symbols *no not* have to be
    -- the same
    guard $ fst (root p) == u
    lift $ pushState $ q
        { gap = Just (beg p, end p)
        , end = end p
        , left = Foot x : left q
        , right = right' }


-- | Try adjoining, second option...
tryAdjoin'
    :: (Ord n, Ord t)
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
    -- make sure that the root of `p' matches with the non-terminal
    -- of the foot of `q'; IDs of the symbols have to be the same
    guard $ root p == x
    lift $ pushState $ q
        { gap = gap p
        , end = end p
        , left = Foot x : left q
        , right = right' }


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
