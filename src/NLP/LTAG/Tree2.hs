{-# LANGUAGE RecordWildCards #-}


module NLP.LTAG.Tree2 where


import           Control.Applicative ((<$>))
import           Control.Arrow (first)
import           Control.Monad (foldM)

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import qualified NLP.FeatureStructure.Tree as FS


-- | A tree with values of type 'n' kept in the interior nodes,
-- values of type 'l' kept in the leaf nodes, FS features
-- (attributes) of type 'f', FS atomic values of type 'a'
-- and FS identifiers (variables) of type 'i'.
data Tree n l i f a
    = INode -- ^ Interior node
        { labelI    :: n
        , topFS     :: FS.FN i f a
        , botFS     :: FS.FN i f a
        , subTrees  :: [Tree n l i f a] }
    | LNode -- ^ Leaf node
        { labelL    :: l }
    deriving (Show, Eq, Ord)


-- -- | List of frontier values. 
-- toWord :: Tree n l a v r -> [l]
-- toWord t = case t of
--     INode{..}   -> concatMap toWord subTrees
--     LNode{..}   -> [labelL]
--     -- FNode{..}   -> []


-- | Transform a tree into an equivalent tree with dummy attributes
-- so that the relations between variables in the resultant tree are
-- of a height-distance at most 1.
dummify
    :: (Ord i, Ord f)
    => Tree n l i f a
    -> Tree n l i (Either f i) a
dummify = undefined


-- -- | Transform a tree into an equivalent tree with dummy attributes
-- -- so that the relations between variables in the resultant tree are
-- -- of a height-distance at most 1.
-- dummify :: (Ord i, Ord f) => Tree n l i f a -> Tree n l i (Either f i) a
-- dummify =
--     addIds S.empty
--   where
--     addIds ids n@INode{..} = n
--         { fsTree = addIdFeats ids fsTree
--         , subTrees = map doit subTrees }
--     addIds _ (LNode x) = LNode x
--     doit n@INode{..} =
--         addIds (ids' S.\\ ids) n
--       where
--         ids  = idsIn fsTree
--         ids' = S.unions $ map idsInTree subTrees
--     doit (LNode x) = LNode x


---------------------------------------------------------------------
-- Path
---------------------------------------------------------------------


-- | A path can be used to extract a particular tree node.
type Path = [Int]


-- -- | Follow the path to a particular tree node. 
-- follow :: Path -> Tree a b -> Maybe (Tree a b)
-- follow = flip $ foldM step
-- 
-- 
-- -- | Follow one step of the `Path`.
-- step :: Tree a b -> Int -> Maybe (Tree a b)
-- step (FNode _) _    = Nothing
-- step (INode _ xs) k = xs !? k


---------------------------------------------------------------------
-- Adjoining
---------------------------------------------------------------------


-- | An auxiliary tree.
data AuxTree n l i f a = AuxTree
    { auxTree   :: Tree n l i f a
    , auxFoot   :: Path }
    deriving (Show, Eq, Ord)
