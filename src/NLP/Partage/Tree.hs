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


---------------------------------------------------------------------
-- Misc
---------------------------------------------------------------------


-- | Maybe a k-th element of a list.
(!?) :: [a] -> Int -> Maybe a
(x:xs) !? k
    | k > 0     = xs !? (k-1)
    | otherwise = Just x
[] !? _ = Nothing
