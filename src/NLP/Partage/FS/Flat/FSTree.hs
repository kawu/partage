{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


-- | Defining elementary trees with FS unification.


module NLP.Partage.FS.Flat.FSTree
(
-- * Types
  OFSTree
, CFSTree
-- -- * Smart constructors
-- , node
-- , leaf
-- , term
-- , foot
-- * Compilation
, bottomUp
, topDown
-- , unifyRoot
, compile
, extract
-- * Utils
, zipTree
) where


import           Data.Maybe (maybeToList)
-- import qualified Data.Foldable as F
import qualified Data.Functor.Compose as F
import qualified Data.Tree as R
import qualified Data.Map.Strict as M

import qualified NLP.Partage.FS as FS
import qualified NLP.Partage.Env as Env
import qualified NLP.Partage.Earley.Comp as C
import qualified NLP.Partage.Tree.Other as O
-- import qualified NLP.Partage.Earley.Base as B


--------------------------------------------------
-- Types
--------------------------------------------------


-- -- | An elementary tree.
-- type Tree n t = R.Tree (O.Node n t)


-- -- | An elementary tree with the accompanying feature structures.
-- type FSTree n t f = R.Tree (FSNode n t f)
--
--
-- -- | A feature structure node.
-- data FSNode n t f = FSNode
--   { treeNode :: O.Node n t
--     -- ^ The underlying (non-terminal, terminal, foot) node.
--   , featStr :: f
--     -- ^ The corresponding feature structure, with variables (in case of OFS)
--     -- having the scope of the corresponding FSTree.
--   , nullAdj :: Bool
--     -- ^ Set to true if the node is marked with the null adjunction constraint.
--   } deriving (Show, Eq, Ord)


-- | An open FSTree together with the corresponding environment.
type OFSTree k v = Env.EnvM v (R.Tree (FS.OFS k))
-- type OFSTree n t k = FSTree n t (FS.OFS k)


-- | A closed FSTree.
type CFSTree k v = R.Tree (FS.CFS k v)
-- type CFSTree n t k v = FSTree n t (FS.CFS k v)


-- --------------------------------------------------
-- -- Smart constructors
-- --------------------------------------------------
--
--
-- -- | Create an internal node.
-- node :: n -> FS.OFS k -> [OFSTree n t k] -> OFSTree n t k
-- -- node x fs = R.Node (O.NonTerm x, fs)
-- node x fs = R.Node $
--   let nod = simple (O.NonTerm x)
--   in  nod {featStr = fs}
--
--
-- -- | Create a leaf node.
-- leaf :: n -> FS.OFS k -> OFSTree n t k
-- -- leaf x fs = R.Node (O.NonTerm x, fs) []
-- leaf x fs = node x fs []
--
--
-- term :: t -> FS.OFS k -> OFSTree n t k
-- -- term x fs = R.Node (O.Term x, fs) []
-- term x fs =
--   let nod = (simple (O.Term x)) {featStr = fs}
--   in  R.Node nod []
--
--
-- foot :: n -> OFSTree n t k
-- -- foot x = R.Node (O.Foot x, M.empty) []
-- foot x =
--   let nod = simple (O.Foot x)
--   in  R.Node nod []
--
--
-- -- | Construct fs-node with default values: empty FS and no null-adjunction
-- -- constraint.
-- simple :: O.Node n t -> FSNode n t (FS.OFS k)
-- simple nod = FSNode
--   { treeNode = nod
--   , featStr = M.empty
--   , nullAdj = False
--   }


--------------------------------------------------
-- Compilation
--------------------------------------------------


-- | Compile the given OFSTree to a computation over closed FSs which requires
-- unification between the corresponding nodes.
bottomUp
  :: (Ord k, Ord v, Show k, Show v)
  => OFSTree k v
  -> C.BottomUp (FS.CFS k v)
bottomUp ofsTreeM cfsTree = maybeToList . fst . Env.runEnvM $ do
  fsTree' <- common ofsTreeM cfsTree
  FS.close $ R.rootLabel fsTree'


-- | Like `bottomUp` but propagates values downward the derivation tree.
topDown
  :: (Ord k, Ord v, Show k, Show v)
  => OFSTree k v
  -> C.TopDown (FS.CFS k v)
topDown ofsTreeM topVal cfsTree =
  -- (:[]) . fmap Just . check . fst . Env.runEnvM $ do
  map (fmap Just) . maybeToList . fst . Env.runEnvM $ do
    -- unify the corresponding FS-like values
    fsTree' <- common ofsTreeM cfsTree
    -- unify the top-FS with the FS percolating from above
    topVal' <- FS.unifyFS (R.rootLabel fsTree') =<< FS.reopen topVal
    -- put back the resulting FS into the tree's root
    fsTree'' <- putRootFS topVal' fsTree'
    -- explicate the resulting tree so that values and IDs assigned
    -- to the individual nodes are explicit
    fmap F.getCompose . FS.explicate . F.Compose $ fsTree''
  where
    putRootFS fs t = do
      fs' <- FS.unifyFS fs (R.rootLabel t)
      return $ t {R.rootLabel = fs'}
--     check may = case may of
--       Nothing -> error "topDown: computation failed"
--       Just x -> x


-- -- | Like `bottomUp` but propagates values downwards the derivation tree.
-- topDown'
--   :: (Ord k, Ord v, Show k, Show v)
--   => Env.EnvM v (OFSTree n t k)
--   -> C.TopDown (FS.CFS k v)
-- topDown' ofsTreeM topVal cfsTree = fmap Just . check . fst . Env.runEnvM $ do
--   fsTree' <- common ofsTreeM cfsTree
--   _ <- FS.unifyFS (R.rootLabel fsTree') =<< FS.reopen topVal
--   mapM FS.close fsTree'
--   where
--     check may = case may of
--       Nothing -> error "topDown: computation failed"
--       Just x -> x


-- | Common part of the bottom-up and the top-down computations.
common
  :: (Ord v, Ord k, Show k, Show v)
  => OFSTree k v
  -> R.Tree (Maybe (FS.CFS k v))
  -> OFSTree k v
common ofsTreeM cfsTree = do
  ofsTree <- ofsTreeM
  let fsTree = zipTree ofsTree cfsTree
  mapM (uncurry doit) fsTree
  where
    doit ofs Nothing = return ofs
    doit ofs (Just cfs) = do
      ofs' <- FS.reopen cfs
      FS.unifyFS ofs ofs'


-- -- | Unify the given FS with the root FS of the given tree.
-- unifyRoot :: (B.Unify v) => v -> C.Env v -> Maybe (C.Env v)
-- unifyRoot cfsMod cfsTree = do
--   let cfsMay = R.rootLabel cfsTree
--   newCfs <- case cfsMay of
--     Nothing -> Just cfsMod
--     Just cfsRoot -> B.unify cfsMod cfsRoot
--   return $ cfsTree {R.rootLabel = Just newCfs}


-- | Compile the given OFSTree to a computation over closed FSs which requires
-- unification between the corresponding nodes.
compile
  :: (Ord k, Ord v, Show k, Show v)
  => OFSTree k v
  -> C.Comp (FS.CFS k v)
compile ofsTreeM = C.Comp
  { C.up   = bottomUp ofsTreeM
  , C.down = topDown ofsTreeM }


-- | Extract elementary tree represented by the given computation (due to
-- unification constraints the function can fail and return `Nothing`).
extract
  :: OFSTree k v
  -- -> Maybe (R.Tree (O.Node n t, FS.CFS k v))
  -> Maybe (CFSTree k v)
extract ofsTreeM = fst . Env.runEnvM $ do
  ofsTree <- ofsTreeM
  fmap F.getCompose . FS.explicate . F.Compose $ ofsTree


-- | Zip two trees.
zipTree :: R.Tree a -> R.Tree b -> R.Tree (a, b)
zipTree (R.Node x xs) (R.Node y ys) = R.Node
  (x, y)
  (map (uncurry zipTree) (zip xs ys))
