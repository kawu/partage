{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | An simple, experimental tree generation module.


module NLP.TAG.Vanilla.Gen
( Gen
, generate
, newGenST
) where



-- import           Control.Applicative ((<$>))
-- import           Control.Monad (void, when, forM_)
import           Control.Monad (when)
import qualified Control.Monad.State.Strict   as E
-- import           Control.Monad.Trans.Maybe (MaybeT (..))
-- import           Control.Monad.Trans.Class (lift)

import           Pipes

import           Data.Maybe (maybeToList)
import qualified Data.Set as S
import qualified Data.PSQueue as Q
import           Data.PSQueue (Binding(..))

import           NLP.TAG.Vanilla.Tree


--------------------------
-- Basic types
--------------------------


-- | Some TAG tree.
type SomeTree n t = Either (Tree n t) (AuxTree n t)


-- | A TAG grammar.
type Gram n t = S.Set (SomeTree n t)


--------------------------
-- Tree score
--------------------------


-- | Size of a tree, i.e. number of nodes.
treeSize :: SomeTree n t -> Int
treeSize st =
    case st of
        Left t -> realSize t
        Right (AuxTree t _) -> realSize t
  where
    realSize INode{..} = 1 + sum (map realSize subTrees)
    realSize FNode{..} = 1


-- | Is it a final tree (i.e. does it contain only terminals in its leaves?)
final :: SomeTree n t -> Bool
final st =
    case st of
        Left t  -> doit t
        Right _ -> False
  where
    doit INode{..} = (not.null) subTrees
                  && and (map doit subTrees)
    doit FNode{..} = True


-- | Extract the underlying tree.
theTree :: SomeTree n t -> Tree n t
theTree (Left t) = t
theTree (Right (AuxTree t _)) = t


--------------------------
-- Generation state
--------------------------


-- | Underlying state of the generation pipe.
data GenST n t = GenST {
      waiting :: Q.PSQ Int (SomeTree n t)
    -- ^ Queue of the derived trees yet to be visited.
    , doneSet :: S.Set (SomeTree n t)
    }


-- | Construct new generation state with all trees in the priority queue.
newGenST :: (Ord n, Ord t) => Gram n t -> GenST n t
newGenST gramSet = GenST {
      waiting = Q.fromList
        [ treeSize t :-> t
        | t <- S.toList gramSet ]
    , doneSet = S.empty }


-- | Pop the tree with the lowest score from the queue.
pop
    :: (E.MonadState (GenST n t) m, Ord n, Ord t)
    => ListT m (SomeTree n t)
pop = do
    mayTree <- E.state $ \s@GenST{..} -> case Q.minView waiting of
        Nothing -> (Nothing, s)
        Just (_ :-> t, q) -> (Just t, s {waiting=q})
    some $ maybeToList mayTree


-- | Push tree into the waiting queue.
push :: (E.MonadState (GenST n t) m, Ord n, Ord t) => SomeTree n t -> m ()
push t = do
    E.modify $ \s -> s
        {waiting = Q.insert (treeSize t) t (waiting s)}


-- | Check if tree already visited.
visited
    :: (E.MonadState (GenST n t) m, Ord n, Ord t)
    => SomeTree n t -> m Bool
visited t = do
    done <- E.gets doneSet
    return $ S.member t done 


--------------------------
-- Generation producer
--------------------------


-- | Type of the generator.
type Gen m n t = Producer (Tree n t) (E.StateT (GenST n t) m) ()


--------------------------
-- Generation proper
--------------------------


-- | A function which generates non-auxiliary trees derived from the grammar.
generate :: (Monad m, Ord n, Ord t) => Gen m n t
generate = runListT $ do
    -- pop best-score tree from the queue
    t <- pop

    -- check if it's not in the set of visited trees yet
    E.guard . not =<< visited t

    -- if final, yield it
    when (final t) $
        lift . yield $ theTree t

    -- take some visited tree 'u'
    treeSet <- E.gets doneSet
    u <- some $ S.toList treeSet

    -- find all possible combinations of 't' and 'u' and add them
    -- to the waiting queue.
    v <- combinations t u
    push v


----------------------------------
-- Finding tree combinations
----------------------------------


-- | Return all possible combinations of the two trees.
combinations
    :: Monad m
    => SomeTree n t
    -> SomeTree n t
    -> ListT m (SomeTree n t)
combinations = undefined


--------------------------
-- Utils
--------------------------


-- -- | MaybeT constructor.
-- maybeT :: Monad m => Maybe a -> MaybeT m a
-- maybeT = MaybeT . return


-- | ListT from a list.
some :: Monad m => [a] -> ListT m a
some = Select . each
