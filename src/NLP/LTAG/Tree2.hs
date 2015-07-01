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
        , fsTree    :: FS.FN i f a
        , subTrees  :: [Tree n l i f a] }
--     | FNode -- ^ Foot node
--         { labelI    :: n
--         , fsTree    :: FS.FN i f a
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
dummify :: (Ord i, Ord f) => Tree n l i f a -> Tree n l i (Either f i) a
dummify =
    addIds S.empty
  where
    addIds ids n@INode{..} = n
        { fsTree = addIdFeats ids fsTree
        , subTrees = map doit subTrees }
    addIds _ (LNode x) = LNode x
    doit n@INode{..} =
        addIds (ids' S.\\ ids) n
      where
        ids  = idsIn fsTree
        ids' = S.unions $ map idsInTree subTrees
    doit (LNode x) = LNode x


-- | Retrieve identifiers from an FS.
idsIn :: Ord i => FS.FN i f a -> S.Set i
idsIn FS.FN{..} =
    here `S.union` below
  where
    here = case ide of
        Just x -> S.singleton x
        Nothing -> S.empty
    below = case val of
        FS.Subs av -> avIds av
        FS.Atom x  -> S.empty
    avIds av = S.unions $ map idsIn $ M.elems av


-- | Retrieve identifiers from an elementary tree.
idsInTree :: Ord i => Tree n l i f a  -> S.Set i
idsInTree INode{..} = S.unions $
    idsIn fsTree :
    map idsInTree subTrees
idsInTree LNode{} = S.empty


-- | Add specifc ID features to an FS.
addIdFeats
    :: (Ord i, Ord f)
    => S.Set i
    -> FS.FN i f a
    -> FS.FN i (Either f i) a
addIdFeats is =
    doFN
  where
    doFN fn@FS.FN{} = fn {FS.val = doFT (FS.val fn)}
    doFT (FS.Subs av) = FS.Subs $ M.fromList $
        [ (Right i, var i)
        | i <- S.toList is ]
            ++
        [ (Left f, doFN fn)
        | (f, fn) <- M.toList av ]
    doFT (FS.Atom x) = FS.Atom x
    var i = FS.FN (Just i) (FS.Subs M.empty)


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
