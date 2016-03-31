{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


-- | A simple, experimental tree generation module, with the aim
-- to generate /all/, or /randomly/, language trees satisfying
-- certain simple constraints.
--
-- One of the possible usecases where such a functionality can be
-- useful is to automatically generate test sets over which
-- efficiency of a parser can be measured.


module NLP.Partage.Gen
( Gram

-- * Generation
, generateAll
-- ** Randomized generation
, generateRand
, GenConf (..)
) where



import           Control.Applicative ((<$>), (<*>))
import qualified Control.Monad.State.Strict   as E
import           Control.Monad.Trans.Maybe (MaybeT (..))

import           Pipes
import qualified Pipes.Prelude as Pipes
import           System.Random (randomRIO)

import qualified Data.Foldable as F
import           Data.Maybe (maybeToList)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.PSQueue as Q
import           Data.PSQueue (Binding(..))
import qualified Data.Tree as R

import           NLP.Partage.Tree.Other
import           NLP.Partage.DAG () -- for Ord (R.Tree a)


--------------------------
-- Basic types
--------------------------


-- deriving instance (Ord n, Ord t) => (Ord (Tree n t))


-- | A TAG grammar: a set of (elementary) initial and auxiliary
-- trees.
type Gram n t = S.Set (Tree n t)


--------------------------
-- Tree size
--------------------------


-- | Size of a tree, i.e. number of nodes.
treeSize :: Tree n t -> Int
treeSize = length . R.flatten


--------------------------
-- Generation state
--------------------------


-- | Map of visited trees.
type DoneMap n t = M.Map Int (S.Set (Tree n t))


-- | Underlying state of the generation pipe.
data GenST n t = GenST {
      waiting :: Q.PSQ (Tree n t) Int
    -- ^ Queue of the derived trees yet to be visited.
    , doneFinal :: DoneMap n t
    -- ^ Set of visited, final trees divided by size
    , doneActive :: DoneMap n t
    -- ^ Set of visited, active (not final) trees divided by size
    }


-- | Construct new generation state with all trees in the priority queue.
newGenST :: (Ord n, Ord t) => Gram n t -> GenST n t
newGenST gramSet = GenST {
      waiting = Q.fromList
        [ t :-> treeSize t
        | t <- S.toList gramSet ]
    , doneFinal  = M.empty
    , doneActive = M.empty }


-- | Pop the tree with the lowest score from the queue.
pop
    :: (E.MonadState (GenST n t) m, Ord n, Ord t)
    -- => m (Maybe (Tree n t))
    => ListT m (Tree n t)
pop = do
    mayTree <- E.state $ \s@GenST{..} -> case Q.minView waiting of
        Nothing -> (Nothing, s)
        Just (t :-> _, q) -> (Just t, s {waiting=q})
    -- return mayTree
    some $ maybeToList mayTree


-- | Push tree into the waiting queue.
push :: (E.MonadState (GenST n t) m, Ord n, Ord t) => Tree n t -> m ()
push t = E.modify $ \s -> s
    {waiting = Q.insert t (treeSize t) (waiting s)}


-- | Save tree as visited.
save :: (E.MonadState (GenST n t) m, Ord n, Ord t) => Tree n t -> m ()
save t = if isFinal t
    then E.modify $ \s -> s
            { doneFinal = M.insertWith S.union
                 (treeSize t) (S.singleton t) (doneFinal s) }
    else E.modify $ \s -> s
            { doneActive = M.insertWith S.union
                 (treeSize t) (S.singleton t) (doneActive s) }


-- | Check if tree already visited.
visited
    :: (E.MonadState (GenST n t) m, Ord n, Ord t)
    => Tree n t -> m Bool
visited t = if isFinal t
    then isVisited doneFinal
    else isVisited doneActive
  where
    isVisited doneMap = do
        done <- E.gets doneMap
        return $ case M.lookup (treeSize t) done of
             Just ts -> S.member t ts
             Nothing -> False


-- | Retrieve all trees from the given map with the size satsifying
-- the given condition.
visitedWith
    :: (E.MonadState (GenST n t) m, Ord n, Ord t)
    => (GenST n t -> DoneMap n t)
    -> (Int -> Bool)
    -> ListT m (Tree n t)
visitedWith doneMap cond = do
    done <- E.gets doneMap
    some [ t
      | (k, treeSet) <- M.toList done
      , cond k, t <- S.toList treeSet ]


-- -- | Retrieve all visited final trees with a size satsifying the
-- -- given condition.
-- finalWith
--     :: (E.MonadState (GenST n t) m, Ord n, Ord t)
--     => (Int -> Bool) -> ListT m (Tree n t)
-- finalWith = visitedWith doneFinal
--
--
-- -- | Retrieve all visited trees with a size satsifying
-- -- the given condition.
-- activeWith
--     :: (E.MonadState (GenST n t) m, Ord n, Ord t)
--     => (Int -> Bool) -> ListT m (Tree n t)
-- activeWith cond = visitedWith doneActive


--------------------------
-- Higher-level generation
--------------------------


-- | Randomized generation configuration.
-- First all derivable trees up to the size `genAllSize` are
-- generated, and on this basis other derived trees (with adjunction
-- probability controlled by `adjProb`) are constructed.
data GenConf = GenConf {
      genAllSize    :: Int
    -- ^ Generate all derivable trees up to the given size
    , adjProb       :: Double
    -- ^ Adjunction probability
    } deriving (Show, Eq, Ord)


-- | Randomly generate derived trees from the grammar, according to
-- the given configuration.
generateRand
    :: (MonadIO m, Ord n, Ord t)
    => Gram n t
    -> GenConf
    -> Producer (Tree n t) m ()
generateRand gramSet cfg = E.forever $ do
    finalSet <- collect basePipe
    mayTree  <- drawTree gramSet finalSet cfg
    F.forM_ mayTree yield
--     case mayTree of
--         Nothing -> return ()
--         Just t  -> yield t
  where
    -- first compute the base set of final trees
    basePipe = generateAll gramSet (genAllSize cfg)
           >-> Pipes.filter isFinal


-- | Try to construct randomly a tree based on the TAG grammar and
-- on the pre-built set of derived final trees.
drawTree
    :: (MonadIO m, Ord n, Ord t)
    => Gram n t     -- ^ The grammar
    -> Gram n t     -- ^ Final trees
    -> GenConf      -- ^ Global config
    -> m (Maybe (Tree n t))
drawTree gramSet finalSet GenConf{..} = runMaybeT $ do
    -- randomly draw an elementary tree
    t0 <- drawFrom $ limitTo isInitial gramSet
    -- recursivey modify the tree
    modify t0
  where
    modify t@(R.Node (Term _) []) =
        return t
    modify (R.Node (NonTerm x) []) =
        let cond = (&&) <$> hasRoot x <*> isInitial
        in  drawFrom (limitTo cond finalSet)
    modify (R.Node (NonTerm x) xs0) = do
        -- modify subtrees
        xs <- mapM modify xs0
        -- construct the new tree
        let t = R.Node (NonTerm x) xs
        -- adjoin some tree if lucky
        lottery adjProb (return t) $ do
            let cond = (&&) <$> hasRoot x <*> isAuxiliary
            auxTree <- drawFrom $ limitTo cond finalSet
            return $ replaceFoot t auxTree
    modify _ = error "drawTree.modify: unhandled node type"
    drawFrom s = do
        E.guard $ S.size s > 0
        i <- liftIO $ randomRIO (0, S.size s - 1)
        -- return $ S.elemAt i s <- works starting from containers 0.5.2
        return $ S.toList s !! i
    limitTo f = S.fromList . filter f . S.toList



--------------------------
-- Generation
--------------------------


-- | Type of the generator.
type Gen m n t = E.StateT (GenST n t) (Producer (Tree n t) m) ()


-- | Generate all trees derivable from the given grammar up to the
-- given size.
generateAll
    :: (MonadIO m, Ord n, Ord t)
    => Gram n t -> Int -> Producer (Tree n t) m ()
generateAll gram0 sizeMax =
    -- gram <- subGram gram0
    E.evalStateT
        (genPipe sizeMax)
        (newGenST gram0)


-- -- | Select sub-grammar rules.
-- subGram
--     :: (MonadIO m, Ord n, Ord t) => Double -> Gram n t -> m (Gram n t)
-- subGram probMax gram = do
--     stdGen <- liftIO getStdGen
--     let ps = randomRs (0, 1) stdGen
--     return $ S.fromList
--         [t | (t, p) <- zip (S.toList gram) ps, p <= probMax]


-- | A function which generates trees derived from the grammar.  The
-- second argument allows to specify a probability of ignoring a tree
-- popped up from the waiting queue.  When set to `1`, all derived
-- trees up to the given size should be generated.
genPipe :: (MonadIO m, Ord n, Ord t) => Int -> Gen m n t
genPipe sizeMax = runListT $ do
    -- pop best-score tree from the queue
    t <- pop
    lift $ do
        genStep sizeMax t
        genPipe sizeMax


-- | Generation step.
genStep
    :: (MonadIO m, Ord n, Ord t)
    => Int              -- ^ Tree size limit
    -> Tree n t         -- ^ Tree from the queue
    -> Gen m n t
genStep sizeMax t = runListT $ do
    -- check if it's not in the set of visited trees yet
    -- TODO: is it even necessary?
    E.guard . not =<< visited t

    -- save tree `t` and yield it
    save t
    lift . lift $ yield t

    -- choices based on whether 't' is final
    let doneMap = if isFinal t
            then doneActive
            else doneFinal

    -- find all possible combinations of 't' and some visited 'u',
    -- and add them to the waiting queue;
    -- note that `t` is now in the set of visited trees --
    -- this allows the process to generate `combinations t t`;
    u <- visitedWith doneMap $
        let n = treeSize t
        in \k -> k + n <= sizeMax + 1

    -- NOTE: at this point we know that `v` cannot yet be visited;
    -- it must be larger than any tree in the set of visited trees.
    let  combine x y = some $
            inject x y ++
            inject y x
    v <- combine t u

    -- we only put to the queue trees which do not exceed
    -- the specified size
    E.guard $ treeSize v <= sizeMax
    push v


---------------------------------------------------------------------
-- Composition
---------------------------------------------------------------------


-- | Identify all possible ways to inject (i.e. substitute
-- or adjoin) the first tree to the second one.
inject :: (Eq n, Eq t) => Tree n t -> Tree n t -> [Tree n t]
inject s t = if isAuxiliary s
    then adjoin s t
    else subst s t


-- | Compute all possible ways of adjoining the first tree into the
-- second one.
adjoin :: (Eq n, Eq t) => Tree n t -> Tree n t -> [Tree n t]
adjoin _ (R.Node (NonTerm _) []) = []
adjoin s (R.Node n ts) =
    here ++ below
  where
    -- perform adjunction here
    here = [replaceFoot (R.Node n ts) s | R.rootLabel s == n]
    -- consider to perform adjunction lower in the tree
    below = map (R.Node n) (doit ts)
    doit [] = []
    doit (x:xs) =
        [u : xs | u <- adjoin s x] ++
        [x : us | us <- doit xs]


-- | Replace foot of the second tree with the first tree.
-- If there is no foot in the second tree, it will be returned
-- unchanged.
replaceFoot :: Tree n t -> Tree n t -> Tree n t
replaceFoot t (R.Node (Foot _) []) = t
replaceFoot t (R.Node x xs) = R.Node x $ map (replaceFoot t) xs


-- | Compute all possible ways of substituting the first tree into
-- the second one.
subst :: (Eq n, Eq t) => Tree n t -> Tree n t -> [Tree n t]
subst s = take 1 . _subst s


-- | Compute all possible ways of substituting the first tree into
-- the second one.
_subst :: (Eq n, Eq t) => Tree n t -> Tree n t -> [Tree n t]
_subst s (R.Node n []) =
    [s | R.rootLabel s == n]
_subst s (R.Node n ts) =
    map (R.Node n) (doit ts)
  where
    doit [] = []
    doit (x:xs) =
        [u : xs | u <- subst s x] ++
        [x : us | us <- doit xs]


--------------------------
-- Utils
--------------------------


-- -- | MaybeT constructor.
-- maybeT :: Monad m => Maybe a -> MaybeT m a
-- maybeT = MaybeT . return


-- | ListT from a list.
some :: Monad m => [a] -> ListT m a
some = Select . each


-- -- | Draw a number between 0 and 1, and check if it is <= the given
-- -- maximal probability.
-- lottery :: (MonadPlus m, MonadIO m) => Double -> m ()
-- lottery probMax = do
--     p <- liftIO $ randomRIO (0, 1)
--     E.guard $ p <= probMax


-- | Collect elements from the pipe into a set.
collect :: (Monad m, Ord a) => Producer a m () -> m (S.Set a)
collect inputPipe =
    flip E.execStateT S.empty
        $ runEffect
            $ hoist lift inputPipe >-> collectPipe
  where
    collectPipe = E.forever $ do
        x <- await
        lift . E.modify $ S.insert x


-- | Run `my` if lucky, `mx` otherwise.
lottery :: (MonadIO m, MonadPlus m) => Double -> m a -> m a -> m a
lottery probMax mx my = do
    p <- liftIO $ randomRIO (0, 1)
    if p > probMax
        then mx
        else my
