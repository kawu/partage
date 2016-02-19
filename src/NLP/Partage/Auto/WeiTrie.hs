{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | Prefix tree grammar representation: the set of rules is stored
-- in a form of a prefix tree.


module NLP.Partage.Auto.WeiTrie
( fromGram
) where


import qualified Control.Arrow as Arr
import           Control.Applicative ((<$>), (<*>), pure)
import qualified Control.Monad.State.Strict as E
import           Control.Exception (assert)

import           Data.Ord (comparing)
import           Data.List (sortBy, foldl')
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           Data.DAWG.Ord (ID)

import qualified NLP.Partage.Auto as A
import           NLP.Partage.FactGram (Lab(..))
import           NLP.Partage.FactGram.Weighted (Weight, WeiFactGram)


--------------------------------------------------
-- Trie
--------------------------------------------------


-- | Simple trie implementation.
newtype WeiTrie a w = WeiTrie { _unWeiTrie :: M.Map a (w, WeiTrie a w) }


-- | Empty weighted trie.
empty :: WeiTrie a w
empty = WeiTrie M.empty


-- -- | Insert the (word, weight) pair into the trie.  The weight will
-- -- be stored in the last, `A.Head` component.  The function works
-- -- correctly provided that the trie has its weights in head
-- -- components only.
-- insert :: (Ord a, Num w)
--     => ([A.Edge a], w)
--     -> WeiTrie (A.Edge a) w
--     -> WeiTrie (A.Edge a) w
-- insert (x@(A.Body _) : xs, w) (WeiTrie t) =
--     let s = fromMaybe empty (snd <$> M.lookup x t)
--     in  WeiTrie $ M.insert x (0, insert (xs, w) s) t
-- insert (x@(A.Head _) : [], w) (WeiTrie t) =
--     WeiTrie $ M.insert x (w, empty) t
-- insert _ _ = error "insert: the unthinkable happened!"


-- -- | Build trie from the weighted language.
-- fromLang :: (Ord a, Num w) => [([A.Edge a], w)] -> WeiTrie (A.Edge a) w
-- fromLang = foldl' (flip insert) empty


-- | Insert the (word, weight) pair into the trie.
-- The function can lead to negative weights on some edges.
insert :: (Ord a, Num w)
    => [A.Edge a] -> w
    -> WeiTrie (A.Edge a) w
    -> WeiTrie (A.Edge a) w
insert (x@(A.Body _) : xs) totalWei (WeiTrie t) =
    WeiTrie $ case M.lookup x t of
        Nothing -> 
            -- we put the rest of the weight at this trie node
            M.insert x (totalWei, insert xs 0 empty) t
        Just (w, s) ->
            -- we cannot change the weight at this trie node;
            -- it would change weights of the some already
            -- inserted rules
            M.insert x (w, insert xs (totalWei - w) s) t
insert (x@(A.Head _) : []) w (WeiTrie t) =
    WeiTrie $ M.insert x (w, empty) t
insert _ _ _ = error "insert: the unthinkable happened!"


-- | Build trie from the weighted language.  The rules are added to
-- the trie w.r.t. the increasing order of their weights.
fromLang :: (Ord a, Ord w, Num w) => [([A.Edge a], w)] -> WeiTrie (A.Edge a) w
fromLang = assertPositive .
    let ins t (xs, w) = insert xs w t
    in  foldl' ins empty . sortBy (comparing snd)
  where
    assertPositive t = flip assert t $ check (\_ w -> w >= 0) t


--------------------------------------------------
-- Checking
--------------------------------------------------


-- | Check that the given predicate holds for all edges of the trie.
check :: (a -> w -> Bool) -> WeiTrie a w -> Bool
check p (WeiTrie t) = and
    [ p x w && check p s
    | (x, (w, s)) <- M.toList t ]


--------------------------------------------------
-- Trie from grammar
--------------------------------------------------


-- | Build trie from the given grammar.
buildTrie :: (Ord n, Ord t) => WeiFactGram n t -> WeiTrie (A.Edge (Lab n t)) Weight
buildTrie gram = fromLang [(A.ruleSeq r, w) | (r, w) <- M.toList gram]


--------------------------------------------------
-- Interface
--------------------------------------------------


-- | Abstract over the concrete implementation.
shell :: (Ord n, Ord t) => WeiTrie (A.Edge (Lab n t)) Weight -> A.WeiGramAuto n t
shell d0 = A.WeiAuto
    { rootsWei  = S.singleton (rootID d)
    , followWei = follow d
    , edgesWei  = edges d }
    where d = convert d0


-- | Build the trie-based representation of the given grammar.
fromGram :: (Ord n, Ord t) => WeiFactGram n t -> A.WeiGramAuto n t
fromGram = shell . buildTrie


-- | Node type.
type Node a w = M.Map a (w, ID)


-- | Alternative trie represetation with explicit node identifiers.
data ITrie a w = ITrie
    { rootID    :: ID
    -- ^ Root of the trie
    , nodeMap   :: M.Map ID (Node a w)
    }


-- | Follow symbol from the given node.
follow :: Ord a => ITrie a w -> ID -> a -> Maybe (w, ID)
follow ITrie{..} i x = do
    node <- M.lookup i nodeMap
    M.lookup x node


-- | All edges outgoing from the given node ID.
edges :: ITrie a w -> ID -> [(a, w, ID)]
edges ITrie{..} i = case M.lookup i nodeMap of
    Nothing -> []
    Just m  ->
        let mkFlat (x, (w, j)) = (x, w, j)
        in  map mkFlat (M.toList m)


-- | Convert `WeiTrie` to `ITrie`.
convert :: (Ord a) => WeiTrie a w -> ITrie a w
convert t0 = ITrie
    { rootID  = root
    , nodeMap = nodeMap' }
  where
    (root, (_, nodeMap')) = E.runState (doit t0) (0 :: Int, M.empty)
    doit (WeiTrie t) = do
        i <- newID
        node <- M.fromList <$> sequence
            [ mkEdge x w <$> doit s
            | (x, (w, s)) <- M.toList t ]
        yield i node
        return i
    mkEdge x w i = (x, (w, i))
    newID = E.state $ \(n, m) -> (n, (n + 1, m))
    yield i node = E.modify $ Arr.second (M.insert i node)
