{-# LANGUAGE RecordWildCards #-}


-- | This module provides datatypes representing TAG trees.
-- `Tree` is an initial tree, while `AuxTree` represents an auxiliary
-- tree.


module NLP.Partage.Tree
(
-- * Initial tree
  Tree (..)
-- , showTree
-- , showTree'
, project

-- * Auxiliary tree
, AuxTree (..)
-- ** Path
, Path
, follow

-- -- * Combining operations
-- -- ** Substitution
-- , subst
-- -- ** Adjoining
-- , adjoin

-- -- * Derivation
-- , Deriv
-- , Trans
-- , derive
-- -- * Traversal
-- , walk
) where


-- import           Control.Applicative ((<$>))
-- import           Control.Arrow (first)
import           Control.Monad (foldM)


-- | A tree with values of type @a@ (/non-termianls/) kept in
-- branching nodes, and values of type @b@ (/terminals/) kept in leaf
-- nodes
data Tree a b
    -- | Branching node with a non-terminal symbol
    = Branch
        { labelI    :: a
        -- ^ The non-terminal kept in the branching node
        , subTrees  :: [Tree a b]
        -- ^ The list of subtrees
        }
    -- | Leaf node with a terminal symbol
    | Leaf
        { labelF    :: b
        -- ^ The terminal symbol
        }
    deriving (Show, Eq, Ord)


-- | List of frontier values.
toWord :: Tree a b -> [b]
toWord t = case t of
    Branch{..} -> concatMap toWord subTrees
    Leaf{..}   -> [labelF]


-- | Projection of a tree: the list of terminal symbols in its
-- leaves
project :: Tree a b -> [b]
project = toWord


-- -- | Replace the tree on the given position.
-- replaceChild :: Tree a b -> Int -> Tree a b -> Tree a b
-- replaceChild t@INode{..} k t' = t { subTrees = replace subTrees k t' }
-- replaceChild _ _ _ = error "replaceChild: frontier node"


-- -- | Show a tree given the showing functions for label values.
-- showTree :: (a -> String) -> (b -> String) -> Tree a b -> String
-- showTree f g = unlines . go
--   where
--     go t = case t of
--         INode{..}   -> ("INode " ++ f labelI)
--             : map ("  " ++) (concatMap go subTrees)
--         FNode{..}   -> ["FNode " ++ g labelF]
--
--
-- -- | Like `showTree`, but using the default `Show` instances
-- -- to present label values.
-- showTree' :: (Show a, Show b) => Tree a b -> String
-- showTree' = showTree show show


---------------------------------------------------------------------
-- Path
---------------------------------------------------------------------


-- | A path indicates a particular node in a tree and can be used to
-- extract a particular subtree of the tree (see `follow`).
-- For instance, @[]@ designates the entire tree, @[0]@ the first
-- child, and @[1,3]@ the fourth child of the second child of the
-- underlying tree.
type Path = [Int]


-- | Follow the path to a particular subtree.
follow :: Path -> Tree a b -> Maybe (Tree a b)
follow = flip $ foldM step


-- | Follow one step of the `Path`.
step :: Tree a b -> Int -> Maybe (Tree a b)
step (Leaf _) _      = Nothing
step (Branch _ xs) k = xs !? k


---------------------------------------------------------------------
-- Substitution
---------------------------------------------------------------------


-- -- | Perform substitution on a tree.  It is neither whether
-- -- the path indicates a leaf, nor if its symbol is identical to the
-- -- symbol of the root of the substituted tree.
-- subst
--     :: Path             -- ^ Place of the substitution
--     -> Tree a b         -- ^ Tree to be substituted
--     -> Tree a b         -- ^ Original tree
--     -> Maybe (Tree a b) -- ^ Resulting tree (or `Nothing`
--                         --   if substitution not possible)
-- subst (k:ks) st t = do
--     replaceChild t k <$> (step t k >>= subst ks st)
-- subst [] st _ = Just st


---------------------------------------------------------------------
-- Adjoining
---------------------------------------------------------------------


-- | An auxiliary tree
data AuxTree a b = AuxTree
    { auxTree   :: Tree a b
    -- ^ The underlying initial tree
    , auxFoot   :: Path
    -- ^ The path to the foot node.  Beware that currently it is
    -- possible to use the `AuxTree` constructor to build an invalid
    -- auxiliary tree, i.e. with an incorrect `auxFoot` value.
    } deriving (Show, Eq, Ord)


-- -- | Perform adjoining operation on a tree.
-- adjoin
--     :: Path             -- ^ Where to adjoin
--     -> AuxTree a b      -- ^ Tree to be adjoined
--     -> Tree a b         -- ^ Tree with the node to be modified
--     -> Maybe (Tree a b) -- ^ Resulting tree
-- adjoin (k:ks) aux t = do
--     replaceChild t k <$> (step t k >>= adjoin ks aux)
-- adjoin [] AuxTree{..} t = do
--     subst auxFoot t auxTree


-- ---------------------------------------------------------------------
-- -- Derivation
-- ---------------------------------------------------------------------
--
--
-- -- | A derived tree is constructed by applying a sequence of
-- -- transforming (substitution or adjoining) rules on particular
-- -- positions of a tree.  The `Deriv` sequence represents a
-- -- derivation process.  One could also construct a derivation
-- -- tree, which to some extent abstracts over the particular order
-- -- of derivations (when it doesn't matter).
-- type Deriv a b = [(Path, Trans a b)]
--
--
-- -- | Transformation of a tree.
-- type Trans a b = Either (Tree a b) (AuxTree a b)
--
--
-- -- | Derive a tree.
-- derive :: Deriv a b -> Tree a b -> Maybe (Tree a b)
-- derive =
--     flip $ foldM m
--   where
--     m t (pos, op) = case op of
--         Left x  -> subst  pos x t
--         Right x -> adjoin pos x t


---------------------------------------------------------------------
-- Traversal
---------------------------------------------------------------------


-- -- | Return all tree paths with corresponding subtrees.
-- walk :: Tree a b -> [(Path, Tree a b)]
-- walk =
--     map (first reverse) . go []
--   where
--     go acc n@INode{..} = (acc, n) : concat
--         [ go (k:acc) t
--         | (k, t) <- zip [0..] subTrees ]
--     go acc n@FNode{..} = [(acc, n)]


---------------------------------------------------------------------
-- Misc
---------------------------------------------------------------------


-- | Maybe a k-th element of a list.
(!?) :: [a] -> Int -> Maybe a
(x:xs) !? k
    | k > 0     = xs !? (k-1)
    | otherwise = Just x
[] !? _ = Nothing


-- -- | Replace the k-th element of a list.  If the given position is
-- -- outside of the list domain, the returned list will be unchanged.
-- -- It the given index is negative, the first element will be
-- -- replaced.
-- replace :: [a] -> Int -> a -> [a]
-- replace (x:xs) k y
--     | k > 0     = x : replace xs (k - 1) y
--     | otherwise = y : xs
-- replace [] _ _  = []
