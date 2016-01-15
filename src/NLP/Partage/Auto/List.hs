{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | List-based grammar representation: each rule is represented as a
-- separate, trivial automaton.


module NLP.Partage.Auto.List
(
-- -- * ListSet
--   ListSet
-- , buildList
--
-- -- * Interface
-- , shell
  fromGram
) where


import qualified Control.Arrow as Arr
import qualified Control.Monad.State.Strict as E

import           Data.Maybe (maybeToList)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           Data.DAWG.Ord (ID)

import qualified NLP.Partage.Auto as A
import           NLP.Partage.FactGram (FactGram, Lab(..), Rule(..))


-- | A single list.
type List a = Maybe (a, ID)


-- | List-based grammar representation: each rule is represented as a
-- separate, trivial automaton.
data ListSet a = ListSet
    { rootSet   :: S.Set ID
    , listMap   :: M.Map ID (List a)
    }


-- | Convert list to a `ListSet`.
convert :: Ord a => [[a]] -> ListSet a
convert xs0 = ListSet
    { rootSet = S.fromList rootList
    , listMap = listMap0 }
  where
    (rootList, (_, listMap0)) = E.runState
        (mapM mkList xs0)
        (0 :: Int, M.empty)
    mkList [] = do
        i <- newID
        yield i Nothing
        return i
    mkList (x:xs) = do
        i <- newID
        j <- mkList xs
        yield i $ Just (x, j)
        return i
    newID = E.state $ \(n, m) -> (n, (n + 1, m))
    yield i node = E.modify $ Arr.second (M.insert i node)


-- | Follow symbol from the given node.
follow :: Ord a => ListSet a -> ID -> a -> Maybe ID
follow ListSet{..} i x = do
    (y, j) <- E.join $ M.lookup i listMap
    E.guard (x == y)
    return j


-- | All edges outgoing from the given node ID.
edges :: ListSet a -> ID -> [(a, ID)]
edges ListSet{..} i
    = maybeToList . E.join
    $ M.lookup i listMap


--------------------------------------------------
-- List from grammar
--------------------------------------------------


-- | Build trie from the given grammar.
buildList :: (Ord n, Ord t) => FactGram n t -> [[A.Edge (Lab n t)]]
buildList gram =
    [ map A.Body bodyR ++ [A.Head headR]
    | Rule{..} <- S.toList gram ]


--------------------------------------------------
-- Interface
--------------------------------------------------


-- | Abstract over the concrete implementation.
shell :: (Ord n, Ord t) => [[A.Edge (Lab n t)]] -> A.GramAuto n t
shell d0 = A.Auto
    { roots  = rootSet d
    , follow = follow d
    , edges  = edges d }
    where d = convert d0


-- | Build the list-based representation of the given grammar.
fromGram :: (Ord n, Ord t) => FactGram n t -> A.GramAuto n t
fromGram = shell . buildList
