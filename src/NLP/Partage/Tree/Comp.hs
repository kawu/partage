{-# LANGUAGE RecordWildCards #-}


-- | Additional computation accompanying elementary trees (ETs).


module NLP.Partage.Tree.Comp
( Env
, Comp (..)
, BottomUp
, TopDown
, dummyTopDown
, leaf
, foot
) where


-- import qualified Data.Map.Strict as M
import qualified Data.Tree as T


---------------------------------------------------------------------
-- Types
---------------------------------------------------------------------


-- -- | A path unambiguously identyfying a node in the corresponding ET. The `[]`
-- -- value stands for the root of the tree, while `x : xs` stands for the
-- -- `xs`-addressed node in the `x`th subtree of the tree.
-- type Path = [Int]
--
--
-- -- | A map assigning values to individual nodes of the tree.
-- -- Values are required to be assigned to leaf nodes but not internal nodes
-- -- (adjunction is optional).
-- type VMap a = M.Map Path a
--
--
-- -- | Computation from the values assigned to individual nodes of an ET to a
-- -- value of this ET.  If the function returns `Nothing`, then the computation
-- -- fails and the corresponding ET cannot be "inferred".
-- type Comp a = VMap a -> Maybe a


-- | A map assigning values to individual nodes of the tree. Values are required
-- to be assigned to leaf nodes but not internal nodes (adjunction is optional).
type Env a = T.Tree (Maybe a)


-- | Create a leaf environment.
leaf :: a -> Env a
leaf x = T.Node (Just x) []


-- | Create a foot environment.
foot :: Env a
foot = T.Node Nothing []


-- -- | Create an internal node environment.
-- node :: Maybe a -> [Env a] -> Env a
-- node x xs = T.Node (Just x) []


-- -- | Computation from the values assigned to individual nodes of an ET to a
-- -- value of this ET.  If the function returns `Nothing`, then the computation
-- -- fails and the corresponding ET cannot be "inferred".
-- -- Note that no node corresponding to the foot is present in the tree.
-- type Comp a = Env a -> Maybe a


-- | Bottom-up computation.
type BottomUp a = Env a -> Maybe a


-- | Top-down computation.
type TopDown a = Env a -> Env a
-- type TopDown a = a -> Env a -> Env a


-- | A computation related to an elementary tree.
data Comp a = Comp
  { bottomUp :: BottomUp a
    -- ^ Computation from the values assigned to individual nodes of an ET to a
    -- value of this ET (and, more precisely, to its root). If the function
    -- returns `Nothing`, then the computation fails and the corresponding ET
    -- cannot be "inferred". Note that no node corresponding to the foot is
    -- present in the tree.
  , topDown  :: TopDown a
    -- ^ Used to determine the value of the entire ET and propagate the values
    -- down the derivation tree; used when extracting derivations.  Note that
    -- `topDown` is a generalization of `bottomUp` and thus results of the
    -- both functions must be consistent.
  }


-- | A dummy top-down computation which does not propagate any values down the
-- derivation tree.
dummyTopDown :: TopDown a
dummyTopDown = id


-- -- | Computation from the values assigned to individual nodes of an ET to a
-- -- value of this ET.  If the function returns `Nothing` then computation
-- -- fails and the corresponding ET cannot be inferred.
-- type Comp a = NodeVMap a -> LeafVMap a -> Maybe a
--
--
-- -- | A map assigning (pairs of) values to individual internal nodes of the tree.
-- -- Values need not be assigned to all internal nodes (adjunction is optional by
-- -- default). First element of the pair represents the computed top value for the
-- -- corresponding auxiliary tree, while the second element -- the bottom value.
-- type NodeVMap a = M.Map Path (a, a)
--
--
-- -- | A map assigning values to individual leaf nodes in the tree. To each leaf
-- -- some value has to be assigned (substitution is always obligatory).
-- type LeafVMap a = M.Map Path a
