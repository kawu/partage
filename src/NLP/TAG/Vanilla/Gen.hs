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
import           System.Random (randomRIO)

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
-- Tree score
--------------------------


-- | Size of a tree, i.e. number of nodes.
treeSize :: SomeTree n t -> Int
treeSize = length . R.flatten
--     case st of
--         Left t -> realSize t
--         Right (AuxTree t _) -> realSize t
--   where
--     realSize INode{..} = 1 + sum (map realSize subTrees)
--     realSize FNode{..} = 1


-- -- | Is it a final tree (i.e. does it contain only terminals
-- in its leaves?)
-- final :: SomeTree n t -> Bool
-- final st =
--     case st of
--         Left t  -> doit t
--         Right _ -> False
--   where
--     doit INode{..} = (not.null) subTrees
--                   && and (map doit subTrees)
--     doit FNode{..} = True


-- -- | Extract the underlying tree.
-- theTree :: SomeTree n t -> Tree n t
-- theTree (Left t) = t
-- theTree (Right (AuxTree t _)) = t


--------------------------
-- Generation state
--------------------------


-- | Underlying state of the generation pipe.
data GenST n t = GenST {
      waiting :: Q.PSQ (SomeTree n t) Int
    -- ^ Queue of the derived trees yet to be visited.
    , doneMap :: M.Map Int (S.Set (SomeTree n t))
    -- ^ Set of visited trees divided by size
    }


-- | Construct new generation state with all trees in the priority queue.
newGenST :: (Ord n, Ord t) => Gram n t -> GenST n t
newGenST gramSet = GenST {
      waiting = Q.fromList
        [ t :-> treeSize t
        | t <- S.toList gramSet ]
    , doneMap = M.empty }


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
save t = do
    E.modify $ \s -> s
        { doneMap = M.insertWith S.union
             (treeSize t) (S.singleton t) (doneMap s) }


-- | Check if tree already visited.
visited
    :: (E.MonadState (GenST n t) m, Ord n, Ord t)
    => SomeTree n t -> m Bool
visited t = do
    done <- E.gets doneMap
    return $ case M.lookup (treeSize t) done of
         Just ts -> S.member t ts
         Nothing -> False


-- | Retrieve all visited trees with a size satsifying
-- the given condition.
visitedWith
    :: (E.MonadState (GenST n t) m, Ord n, Ord t)
    => (Int -> Bool) -> ListT m (SomeTree n t)
visitedWith cond = do
    done <- E.gets doneMap
    some [ t
      | (k, treeSet) <- M.toList done
      , cond k, t <- S.toList treeSet ]


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
generate gram sizeMax probMax =
    E.evalStateT
        (genPipe sizeMax probMax)
        (newGenST gram)


--------------------------
-- Generation proper
--------------------------


-- | A function which generates trees derived from the grammar.  The second
-- argument allows to specify a probability of ignoring a tree popped up from
-- the waiting queue.  When set to `1`, all derived trees up to the given size
-- should be generated.
genPipe :: (MonadIO m, Ord n, Ord t) => Int -> Double -> Gen m n t
genPipe sizeMax probMax = runListT $ do
    -- pop best-score tree from the queue
    t <- pop
    lift $ do
        genStep sizeMax probMax t
        genPipe sizeMax probMax


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

    -- find all possible combinations of 't' and some visited 'u',
    -- and add them to the waiting queue;
    -- note that `t` is now in the set of visited trees --
    -- this allows the process to generate `combinations t t`;
    u <- visitedWith $
        let n = treeSize t
        in \k -> k + n <= sizeMax + 1

    -- we select only a specified percentage of 'u's
    p <- liftIO $ randomRIO (0, 1)
    E.guard $ p <= probMax

    -- NOTE: at this point we know that `v` cannot yet be visited;
    -- it must be larger than any tree in the set of visited trees.
    v <- combinations t u

    -- we only put to the queue trees which do not exceed
    -- the specified size
    E.guard $ treeSize v <= sizeMax
    push v


----------------------------------
-- Finding tree combinations
----------------------------------


-- | Return all possible combinations of the two trees.
combinations
    :: (Monad m, Eq n, Eq t)
    => SomeTree n t
    -> SomeTree n t
    -> ListT m (SomeTree n t)
combinations s t = some $ inject s t ++ inject t s


--------------------------
-- Utils
--------------------------


-- -- | MaybeT constructor.
-- maybeT :: Monad m => Maybe a -> MaybeT m a
-- maybeT = MaybeT . return


-- | ListT from a list.
some :: Monad m => [a] -> ListT m a
some = Select . each
