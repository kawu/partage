{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | Prefix tree grammar representation: the set of rules is stored
-- in a form of a prefix tree.


module NLP.Partage.Auto.Trie
(
-- * Trie
  Trie (..)
, empty
, insert
, fromLang

-- * From grammar
, buildTrie

-- * Interface
, fromGram
) where


import qualified Control.Arrow as Arr
import           Control.Applicative ((<$>), (<*>), pure)
import qualified Control.Monad.State.Strict as E

import           Data.Maybe (fromMaybe)
import           Data.List (foldl')
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           Data.DAWG.Ord (ID)

import qualified NLP.Partage.Auto as A
import           NLP.Partage.DAG (DID(..), Rule(..))


--------------------------------------------------
-- Trie
--------------------------------------------------


-- | Simple trie implementation.  Note that we don't store info if the
-- particular trie represents a final node or not because, given that
-- head elements are distinguished from body elements, the final node
-- is always represented by an empty trie.
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
buildTrie :: S.Set Rule -> Trie (A.Edge DID)
buildTrie gram = fromLang [A.ruleSeq r | r <- S.toList gram]


--------------------------------------------------
-- Interface
--------------------------------------------------


-- | Abstract over the concrete implementation.
shell :: Trie (A.Edge DID) -> A.GramAuto
shell d0 = A.Auto
    { roots  = S.singleton (rootID d)
    , follow = follow d
    , edges  = edges d }
    where d = convert d0


-- | Build the trie-based representation of the given grammar.
fromGram :: S.Set Rule -> A.GramAuto
fromGram = shell . buildTrie


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
