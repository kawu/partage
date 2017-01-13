{-# LANGUAGE OverloadedStrings #-}


-- | Defining elementary trees with FS unification.


module NLP.Partage.FSTree
(
-- * Types
  Tree
, FSTree
-- * Smart constructors
, node
, leaf
, term
, foot
-- * Compilation
, bottomUp
, topDown
-- , unifyRoot
, compile
, extract
-- * Utils
, zipTree
) where


import qualified Data.Foldable as F
import qualified Data.Functor.Compose as F
import qualified Data.Tree as R
import qualified Data.Map.Strict as M

import qualified NLP.Partage.FS as FS
import qualified NLP.Partage.Env as Env
import qualified NLP.Partage.Tree.Comp as C
import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.Earley.Base as B


--------------------------------------------------
-- Types
--------------------------------------------------


-- | An elementary tree.
type Tree n t = R.Tree (O.Node n t)


-- | An elementary tree with the accompanying feature structures.
type FSTree n t k = R.Tree (O.Node n t, FS.OFS k)


--------------------------------------------------
-- Smart constructors
--------------------------------------------------


-- | Create an internal node.
node :: n -> FS.OFS k -> [FSTree n t k] -> FSTree n t k
node x fs = R.Node (O.NonTerm x, fs)


-- | Create a leaf node.
leaf :: n -> FS.OFS k -> FSTree n t k
leaf x fs = R.Node (O.NonTerm x, fs) []


term :: t -> FS.OFS k -> FSTree n t k
term x fs = R.Node (O.Term x, fs) []


foot :: n -> FSTree n t k
foot x = R.Node (O.Foot x, M.empty) []


--------------------------------------------------
-- Compilation
--------------------------------------------------


-- | Compile the given FSTree to a computation over closed FSs which requires
-- unification between the corresponding nodes.
bottomUp
  :: (Ord k, Ord v, Show k, Show v)
  => Env.EnvM v (FSTree n t k)
  -> C.BottomUp (FS.CFS k v)
bottomUp ofsTreeM cfsTree = fst . Env.runEnvM $ do
  fsTree' <- common ofsTreeM cfsTree
  FS.close $ R.rootLabel fsTree'


-- | Like `bottomUp` but propagates values downwards the derivation tree.
topDown
  :: (Ord k, Ord v, Show k, Show v)
  => Env.EnvM v (FSTree n t k)
  -> C.TopDown (FS.CFS k v)
topDown ofsTreeM topVal cfsTree = fmap Just . check . fst . Env.runEnvM $ do
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
    check may = case may of
      Nothing -> error "topDown: computation failed"
      Just x -> x
    putRootFS fs t = do
      fs' <- FS.unifyFS fs (R.rootLabel t)
      return $ t {R.rootLabel = fs'}


-- -- | Like `bottomUp` but propagates values downwards the derivation tree.
-- topDown'
--   :: (Ord k, Ord v, Show k, Show v)
--   => Env.EnvM v (FSTree n t k)
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
  => Env.EnvM v (FSTree n t k)
  -> R.Tree (Maybe (FS.CFS k v))
  -> Env.EnvM v (R.Tree (FS.OFS k))
common ofsTreeM cfsTree = do
  ofsTree <- fmap snd <$> ofsTreeM
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


-- | Compile the given FSTree to a computation over closed FSs which requires
-- unification between the corresponding nodes.
compile
  :: (Ord k, Ord v, Show k, Show v)
  => Env.EnvM v (FSTree n t k)
  -> C.Comp (FS.CFS k v)
compile ofsTreeM = C.Comp
  { C.bottomUp = bottomUp ofsTreeM
  , C.topDown = topDown ofsTreeM }


-- | Extract tree elementary represented by the given computation (due to
-- unification constraints the function can fail and return `Nothing`).
extract :: Env.EnvM v (FSTree n t k) -> Maybe (FSTree n t k)
extract ofsTreeM = fst . Env.runEnvM $ do
  ofsTreeM


-- | Zip two trees.
zipTree :: R.Tree a -> R.Tree b -> R.Tree (a, b)
zipTree (R.Node x xs) (R.Node y ys) = R.Node
  (x, y)
  (map (uncurry zipTree) (zip xs ys))
