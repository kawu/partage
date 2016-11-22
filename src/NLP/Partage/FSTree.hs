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
, compile
, extract
) where


import qualified Data.Tree as R
import qualified Data.Map.Strict as M

import qualified NLP.Partage.FS as FS
import qualified NLP.Partage.Env as Env
import qualified NLP.Partage.Tree.Comp as C
import qualified NLP.Partage.Tree.Other as O


--------------------------------------------------
-- Types
--------------------------------------------------


-- | An elementary tree.
type Tree n t = R.Tree (O.Node n t)


-- | An elementary tree with the accompanying feature structures.
type FSTree n t k v = R.Tree (O.Node n t, FS.FS k v)


--------------------------------------------------
-- Smart constructors
--------------------------------------------------


-- | Create an internal node.
node :: n -> FS.FS k v -> [FSTree n t k v] -> FSTree n t k v
node x fs = R.Node (O.NonTerm x, fs)


-- | Create a leaf node.
leaf :: n -> FS.FS k v -> FSTree n t k v
leaf x fs = R.Node (O.NonTerm x, fs) []


term :: t -> FS.FS k v -> FSTree n t k v
term x fs = R.Node (O.Term x, fs) []


foot :: n -> FSTree n t k v
foot x = R.Node (O.Foot x, M.empty) []


--------------------------------------------------
-- Compilation
--------------------------------------------------


-- | Compile the fiven FSTree to a computation over closed FSs which requires
-- unification between the corresponding nodes.
compile :: (Ord k, Ord v) => Env.EnvM v (FSTree n t k v) -> C.Comp (FS.ClosedFS k v)
compile ofsTreeM cfsTree = fst . Env.runEnvM $ do
  ofsTree <- fmap snd <$> ofsTreeM
  let fsTree = zipTree ofsTree cfsTree
  fsTree' <- mapM (uncurry doit) fsTree
  FS.close $ R.rootLabel fsTree'
  where
    doit ofs Nothing = return ofs
    doit ofs (Just cfs) = do
      ofs' <- FS.reopen cfs
      FS.unifyFS ofs ofs'


-- | Extract tree elementary represented by the given computation (due to
-- unification constraints the function can fail and return `Nothing`).
extract :: Env.EnvM v (FSTree n t k v) -> Maybe (Tree n t)
extract ofsTreeM = fst . Env.runEnvM $ do
  fmap fst <$> ofsTreeM


-- | Zip two trees.
zipTree :: R.Tree a -> R.Tree b -> R.Tree (a, b)
zipTree (R.Node x xs) (R.Node y ys) = R.Node
  (x, y)
  (map (uncurry zipTree) (zip xs ys))
