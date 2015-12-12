{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


-- | An simple, experimental tree generation module.


module NLP.TAG.Vanilla.Gen
( generate
) where



-- import           Control.Applicative ((<$>))
-- import           Control.Monad (void, when, forM_)
-- import           Control.Monad (when)
import qualified Control.Monad.State.Strict   as E
-- import           Control.Monad.Trans.Maybe (MaybeT (..))
-- import           Control.Monad.Trans.Class (lift)
-- import           Control.Monad.IO.Class (liftIO)

import           Pipes
import           System.Random (randomRIO, randomRs, getStdGen)

import           Data.Maybe (maybeToList)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.PSQueue as Q
import           Data.PSQueue (Binding(..))
import qualified Data.Tree as R

import           NLP.TAG.Vanilla.Tree.Other hiding (SomeTree)


--------------------------
-- Basic types
--------------------------


-- | Some TAG tree.
-- type SomeTree n t = Either (Tree n t) (AuxTree n t)
type SomeTree n t = Tree n t


deriving instance (Ord n, Ord t) => (Ord (SomeTree n t))


-- | A TAG grammar.
type Gram n t = S.Set (SomeTree n t)


--------------------------
-- Tree size
--------------------------


-- | Size of a tree, i.e. number of nodes.
treeSize :: SomeTree n t -> Int
treeSize = length . R.flatten


--------------------------
-- Generation state
--------------------------


-- | Map of visited trees.
type DoneMap n t = M.Map Int (S.Set (SomeTree n t))


-- | Underlying state of the generation pipe.
data GenST n t = GenST {
      waiting :: Q.PSQ (SomeTree n t) Int
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
    -- => m (Maybe (SomeTree n t))
    => ListT m (SomeTree n t)
pop = do
    mayTree <- E.state $ \s@GenST{..} -> case Q.minView waiting of
        Nothing -> (Nothing, s)
        Just (t :-> _, q) -> (Just t, s {waiting=q})
    -- return mayTree
    some $ maybeToList mayTree


-- | Push tree into the waiting queue.
push :: (E.MonadState (GenST n t) m, Ord n, Ord t) => SomeTree n t -> m ()
push t = do
    E.modify $ \s -> s
        {waiting = Q.insert t (treeSize t) (waiting s)}


-- | Save tree as visited.
save :: (E.MonadState (GenST n t) m, Ord n, Ord t) => SomeTree n t -> m ()
save t = if final t
    then E.modify $ \s -> s
            { doneFinal = M.insertWith S.union
                 (treeSize t) (S.singleton t) (doneFinal s) }
    else E.modify $ \s -> s
            { doneActive = M.insertWith S.union
                 (treeSize t) (S.singleton t) (doneActive s) }


-- | Check if tree already visited.
visited
    :: (E.MonadState (GenST n t) m, Ord n, Ord t)
    => SomeTree n t -> m Bool
visited t = if final t
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
    -> ListT m (SomeTree n t)
visitedWith doneMap cond = do
    done <- E.gets doneMap
    some [ t
      | (k, treeSet) <- M.toList done
      , cond k, t <- S.toList treeSet ]


-- -- | Retrieve all visited final trees with a size satsifying the
-- -- given condition.
-- finalWith
--     :: (E.MonadState (GenST n t) m, Ord n, Ord t)
--     => (Int -> Bool) -> ListT m (SomeTree n t)
-- finalWith = visitedWith doneFinal
-- 
-- 
-- -- | Retrieve all visited trees with a size satsifying
-- -- the given condition.
-- activeWith
--     :: (E.MonadState (GenST n t) m, Ord n, Ord t)
--     => (Int -> Bool) -> ListT m (SomeTree n t)
-- activeWith cond = visitedWith doneActive


--------------------------
-- Generation producer
--------------------------


-- | Type of the generator.
-- type Gen m n t = Producer (Tree n t) (E.StateT (GenST n t) m) ()
type Gen m n t = E.StateT (GenST n t) (Producer (Tree n t) m) ()


-- | Run generation on the given grammar.
-- Generate trees up to a given size.
generate
    :: (MonadIO m, Ord n, Ord t)
    => Gram n t -> Int -> Double -> Producer (Tree n t) m ()
generate gram0 sizeMax probMax = do
    -- gram <- subGram probMax gram0
    E.evalStateT
        (genPipe sizeMax probMax)
        (newGenST gram0)


-- -- | Select sub-grammar rules.
-- subGram
--     :: (MonadIO m, Ord n, Ord t) => Double -> Gram n t -> m (Gram n t)
-- subGram probMax gram = do
--     stdGen <- liftIO getStdGen
--     let ps = randomRs (0, 1) stdGen
--     return $ S.fromList
--         [t | (t, p) <- zip (S.toList gram) ps, p <= probMax]


--------------------------
-- Generation proper
--------------------------


-- | A function which generates trees derived from the grammar.  The
-- second argument allows to specify a probability of ignoring a tree
-- popped up from the waiting queue.  When set to `1`, all derived
-- trees up to the given size should be generated.
genPipe :: (MonadIO m, Ord n, Ord t) => Int -> Double -> Gen m n t
genPipe sizeMax probMax = runListT $ do
    -- pop best-score tree from the queue
    t <- pop
    lift $ genStep sizeMax probMax t
--         -- we select only a specified percentage of 't's
--         p <- liftIO $ randomRIO (0, 1)
--         E.when (p <= probMax)
--             (genStep sizeMax probMax t)
    lift $ genPipe sizeMax probMax


-- | Generation step.
genStep
    :: (MonadIO m, Ord n, Ord t)
    => Int              -- ^ Tree size limit
    -> Double           -- ^ Probability threshold
    -> SomeTree n t     -- ^ Tree from the queue
    -> Gen m n t
genStep sizeMax probMax t = runListT $ do
    -- check if it's not in the set of visited trees yet
    -- TODO: is it even necessary?
    E.guard . not =<< visited t

    -- save tree `t` and yield it
    save t
    lift . lift $ yield t

    -- choices based on whether 't' is final
    let doneMap = if final t
            then doneActive
            else doneFinal

    -- find all possible combinations of 't' and some visited 'u',
    -- and add them to the waiting queue;
    -- note that `t` is now in the set of visited trees --
    -- this allows the process to generate `combinations t t`;
    u <- visitedWith doneMap $
        let n = treeSize t
        in \k -> k + n <= sizeMax + 1

    -- we select only a specified percentage of 'u's
    p <- liftIO $ randomRIO (0, 1)
    E.guard $ p <= probMax

    -- NOTE: at this point we know that `v` cannot yet be visited;
    -- it must be larger than any tree in the set of visited trees.
    let  combine x y = some $
            inject x y ++
            inject y x
    v <- combine t u

    -- we only put to the queue trees which do not exceed
    -- the specified size
    E.guard $ treeSize v <= sizeMax
    -- lottery probMax >>
    push v


----------------------------------
-- Finding tree combinations
----------------------------------


-- -- | Return all possible combinations of the two trees.
-- combinations
--     :: (Monad m, Eq n, Eq t)
--     => SomeTree n t
--     -> SomeTree n t
--     -> ListT m (SomeTree n t)
-- combinations s t = some $ inject s t ++ inject t s


---------------------------------------------------------------------
-- Composition
---------------------------------------------------------------------


-- | Identify all possible ways to inject (i.e. substitute
-- or adjoin) the first tree to the second one.
inject :: (Eq n, Eq t) => Tree n t -> Tree n t -> [Tree n t]
inject s t = if isAux s
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
    here = if R.rootLabel s == n
        then [replaceFoot (R.Node n ts) s]
        else []
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
    if R.rootLabel s == n
        then [s]
        else []
_subst s (R.Node n ts) =
    map (R.Node n) (doit ts)
  where
    doit [] = []
    doit (x:xs) =
        [u : xs | u <- subst s x] ++
        [x : us | us <- doit xs]


-- | Check if the tree is auxiliary.
isAux :: Tree n t -> Bool
isAux (R.Node (Foot _) _) = True
isAux (R.Node _ xs) = or (map isAux xs)


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
