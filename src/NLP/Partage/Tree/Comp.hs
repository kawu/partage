{-# LANGUAGE RecordWildCards #-}


-- | Additional computation accompanying elementary trees (ETs).


module NLP.Partage.Tree.Comp
(
-- * Types
  Path
, Comp
, NodeVMap
, LeafVMap
) where


import qualified Data.Map.Strict as M


---------------------------------------------------------------------
-- Types
---------------------------------------------------------------------


-- | A path unambiguously identyfying a node in the corresponding ET. The `[]`
-- value stands for the root of the tree, while `x : xs` stands for the
-- `xs`-addressed node in the `x`th subtree of the tree.
type Path = [Int]


-- | Computation from the values assigned to individual nodes of an ET to a
-- value of this ET.  If the function returns `Nothing` then computation
-- fails and the corresponding ET cannot be inferred.
type Comp a = NodeVMap a -> LeafVMap a -> Maybe a


-- | A map assigning (pairs of) values to individual internal nodes of the tree.
-- Values need not be assigned to all internal nodes (adjunction is optional by
-- default). First element of the pair represents the computed top value for the
-- corresponding auxiliary tree, while the second element -- the bottom value.
type NodeVMap a = M.Map Path (a, a)


-- | A map assigning values to individual leaf nodes in the tree. To each leaf
-- some value has to be assigned (substitution is always obligatory).
type LeafVMap a = M.Map Path a
