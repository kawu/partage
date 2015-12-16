{-# LANGUAGE RecordWildCards #-}


-- | (Prefix) trie grammar representation.


module NLP.TAG.Vanilla.Auto.Trie
(
-- * Trie
  Trie
, empty
, insert
, fromLang

-- * From grammar
, buildTrie

-- * Interface
, shell
) where


import qualified Control.Arrow as Arr
import           Control.Applicative ((<$>), (<*>), pure)
import qualified Control.Monad.State.Strict as E

import           Data.Maybe (fromMaybe)
import           Data.List (foldl')
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           Data.DAWG.Gen.Types (ID)

import qualified NLP.TAG.Vanilla.Auto.Mini as Mini
import           NLP.TAG.Vanilla.Auto.Edge (Edge(..))
import           NLP.TAG.Vanilla.Rule (Lab(..), Rule(..))


--------------------------------------------------
-- Trie
--------------------------------------------------


-- | Simple trie implementation.
newtype Trie a = Trie { _unTrie :: M.Map a (Trie a) }


-- | Empty trie.
empty :: Trie a
empty = Trie M.empty


-- | Insert new element into the trie.
insert :: Ord a => [a] -> Trie a -> Trie a
insert (x:xs) (Trie t) =
    let s = fromMaybe empty (M.lookup x t)
    in  Trie $ M.insert x (insert xs s) t
insert [] t = t


-- | Build trie from language.
fromLang :: Ord a => [[a]] -> Trie a
fromLang = foldl' (flip insert) empty


--------------------------------------------------
-- Trie from grammar
--------------------------------------------------


-- | Build trie from the given grammar.
buildTrie :: (Ord n, Ord t) => S.Set (Rule n t) -> Trie (Edge (Lab n t))
buildTrie gram = fromLang
    [ map Body bodyR ++ [Head headR]
    | Rule{..} <- S.toList gram ]


--------------------------------------------------
-- Interface
--------------------------------------------------


-- | Abstract over the concrete implementation.
shell
    :: (Ord n, Ord t)
    => Trie (Edge (Lab n t))
    -> Mini.Auto (Edge (Lab n t))
shell d0 = Mini.Auto
    { roots  = S.singleton (rootID d)
    , follow = follow d
    , edges  = edges d }
    where d = convert d0


-- | Node type.
type Node a = M.Map a ID


-- | Alternative trie represetation with explicit node identifiers.
data ITrie a = ITrie
    { rootID    :: ID
    -- ^ Root of the trie
    , nodeMap   :: M.Map ID (Node a)
    }


-- | Follow symbol from the given node.
follow :: Ord a => ITrie a -> ID -> a -> Maybe ID
follow ITrie{..} i x = do
    node <- M.lookup i nodeMap
    M.lookup x node


-- | All edges outgoing from the given node ID.
edges :: ITrie a -> ID -> [(a, ID)]
edges ITrie{..} i = case M.lookup i nodeMap of
    Nothing -> []
    Just m  -> M.toList m


-- | Convert `Trie` to `ITrie`.
convert :: Ord a => Trie a -> ITrie a
convert t0 = ITrie
    { rootID  = root
    , nodeMap = nodeMap' }
  where
    (root, (_, nodeMap')) = E.runState (doit t0) (0 :: Int, M.empty)
    doit (Trie t) = do
        i <- newID
        node <- M.fromList <$> sequence
            [ (,) <$> pure x <*> doit s
            | (x, s) <- M.toList t ]
        yield i node
        return i
    newID = E.state $ \(n, m) -> (n, (n + 1, m))
    yield i node = E.modify $ Arr.second (M.insert i node)
