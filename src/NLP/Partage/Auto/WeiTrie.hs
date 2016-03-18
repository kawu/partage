{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards  #-}


-- | Prefix tree grammar representation: the set of rules is stored
-- in a form of a prefix tree.


module NLP.Partage.Auto.WeiTrie
( fromGram
) where


import           Control.Applicative           (pure, (<$>), (<*>))
import qualified Control.Arrow                 as Arr
import           Control.Exception             (assert)
import qualified Control.Monad.State.Strict    as E

import           Data.List                     (foldl', sortBy)
import qualified Data.Map.Strict               as M
import           Data.Ord                      (comparing)
import qualified Data.Set                      as S

import           Data.DAWG.Ord                 (ID)

import qualified NLP.Partage.Auto              as A
import           NLP.Partage.DAG      (DID, Rule, Weight)


--------------------------------------------------
-- Trie
--------------------------------------------------


-- | Simple trie implementation.
newtype WeiTrie a w = WeiTrie { _unWeiTrie :: M.Map a (w, WeiTrie a w) }


-- | Empty weighted trie.
empty :: WeiTrie a w
empty = WeiTrie M.empty


-- -- | Insert the (word, weight) pair into the trie.
-- -- The function can lead to negative weights on some edges.
-- insert :: (Ord a, Num w)
--     => [A.Edge a] -> w
--     -> WeiTrie (A.Edge a) w
--     -> WeiTrie (A.Edge a) w
-- insert (x@(A.Body _) : xs) totalWei (WeiTrie t) =
--     WeiTrie $ case M.lookup x t of
--         Nothing ->
--             -- we put the rest of the weight at this trie node
--             M.insert x (totalWei, insert xs 0 empty) t
--         Just (w, s) ->
--             -- we cannot change the weight at this trie node;
--             -- it would change weights of the some already
--             -- inserted rules
--             M.insert x (w, insert xs (totalWei - w) s) t
-- insert (x@(A.Head _) : []) w (WeiTrie t) =
--     WeiTrie $ M.insert x (w, empty) t
-- insert _ _ _ = error "insert: the unthinkable happened!"
--
--
-- -- | Build trie from the weighted language.  The rules are added to
-- -- the trie w.r.t. the increasing order of their weights.
-- fromLang :: (Ord a, Ord w, Num w) => [([A.Edge a], w)] -> WeiTrie (A.Edge a) w
-- fromLang = assertPositive .
--     let ins t (xs, w) = insert xs w t
--     in  foldl' ins empty . sortBy (comparing snd)
--   where
--     assertPositive t = flip assert t $ check (\_ w -> w >= 0) t


-- | Insert the (word, weight) pair into the trie.
-- The function can lead to negative weights on some edges.
insert :: (Ord a, Num w)
    => [A.Edge a] -> w
    -> WeiTrie (A.Edge a) w
    -> WeiTrie (A.Edge a) w
insert (x@(A.Body _) : xs) totalWei (WeiTrie t) =
    WeiTrie $ case M.lookup x t of
        Nothing ->
            M.insert x (0, insert xs totalWei empty) t
        Just (w, s) ->
            -- we cannot change the weight at this trie node;
            -- it would change weights of the some already
            -- inserted rules; but actually, the way it works
            -- now, `w` should be equal to 0 here.
            M.insert x (w, insert xs (totalWei - w) s) t
insert (x@(A.Head _) : []) w (WeiTrie t) =
    WeiTrie $ M.insert x (w, empty) t
insert _ _ _ = error "insert: the unthinkable happened!"


-- | Build a trie from a weighted language.  Weights will be placed
-- in the final, head edges.
fromLang :: (Ord a, Ord w, Num w) => [([A.Edge a], w)] -> WeiTrie (A.Edge a) w
fromLang = assertPositive .
    let ins t (xs, w) = insert xs w t
    in  foldl' ins empty
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
buildTrie
    :: M.Map Rule Weight
    -> WeiTrie (A.Edge DID) Weight
buildTrie gram = fromLang [(A.ruleSeq r, w) | (r, w) <- M.toList gram]


--------------------------------------------------
-- Interface
--------------------------------------------------


-- | Abstract over the concrete implementation.
shell
    :: WeiTrie (A.Edge DID) Weight
    -> A.WeiGramAuto n t
shell d0 = A.WeiAuto
    { rootsWei  = S.singleton (rootID d)
    , followWei = follow d
    , edgesWei  = edges d }
    where d = convert d0


-- | Build the trie-based representation of the given grammar.
fromGram
    :: M.Map Rule Weight
    -> A.WeiGramAuto n t
fromGram = shell . buildTrie


-- | Node type.
type Node a w = M.Map a (w, ID)


-- | Alternative trie represetation with explicit node identifiers.
data ITrie a w = ITrie
    { rootID  :: ID
    -- ^ Root of the trie
    , nodeMap :: M.Map ID (Node a w)
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
