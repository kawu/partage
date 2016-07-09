{-# LANGUAGE RecordWildCards #-}


-- | A tree data type base on standard `Data.Tree` which
-- allows to assign labels to tree edges.


module NLP.Partage.EdgeTree
( Tree
, Node (..)
, modifyNode
, modifyEdge
) where


import qualified Data.Tree               as R


-- | Node of an edge tree.
data Node a b = Node
  -- NOTE: as it is defined now, this type is fully isomorphic to the type
  -- defined in the skladnica-parser package (even if uses a slightly different
  -- naming convention).  I prefer to use rose tree over a custom data type
  -- because this allows to use all the standard functions already defined
  -- for standard rose trees.  Otherwise, there is a sligh inconvenience --
  -- we have to somehow deal with top-level dummy edge.
  { nodeLabel :: a
    -- ^ Label assigned to the node itself
  , edgeLabel :: b
    -- ^ Label assigned to the ingoing edge
  } deriving (Show, Eq, Ord)


-- | Modify edge label value.
modifyNode :: (a -> c) -> Node a b -> Node c b
modifyNode f e@Node{..} =
  e {nodeLabel = f nodeLabel}


-- | Modify node label value.
modifyEdge :: (b -> c) -> Node a b -> Node a c
modifyEdge f e@Node{..} =
  e {edgeLabel = f edgeLabel}


-- | An edge tree with edges of the type `a` and nodes of type `b`.
type Tree a b = R.Tree (Node a b)
