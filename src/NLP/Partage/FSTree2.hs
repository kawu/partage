{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}


-- | Elementary trees with FS unification. Top and bottom feature structures are
-- distinguished.


module NLP.Partage.FSTree2
(
-- * Types
  FST.Tree
, FSTree
, Loc (..)
-- -- * Smart constructors
-- , node
-- , leaf
-- , term
-- , foot
-- * Compilation
, bottomUp
, topDown
, compile
-- , unifyRoot
, FST.extract
-- -- * Utils
-- , zipTree
) where

-- import Debug.Trace (trace)

import qualified Data.Foldable as F
import qualified Data.Tree as R
import qualified Data.Map.Strict as M

import qualified NLP.Partage.FS as FS
import qualified NLP.Partage.FSTree as FST
import qualified NLP.Partage.Env as Env
import qualified NLP.Partage.Tree.Comp as C
import qualified NLP.Partage.Tree.Other as O
-- import qualified NLP.Partage.Earley.Base as B


--------------------------------------------------
-- Types
--------------------------------------------------


-- | Top or bottom FS.
data Loc k = Top k | Bot k
  deriving (Show, Eq, Ord)


isTop :: Loc k -> Bool
isTop x = case x of
  Top _ -> True
  _ -> False


isBot :: Loc k -> Bool
isBot x = case x of
  Bot _ -> True
  _ -> False


-- | An elementary tree with the accompanying feature structures.
type FSTree n t k v = FST.FSTree n t (Loc k) v


--------------------------------------------------
-- Smart constructors
--------------------------------------------------


-- -- | Create an internal node.
-- node :: n -> FS.FS k v -> [FSTree n t k v] -> FSTree n t k v
-- node x fs = R.Node (O.NonTerm x, fs)
--
--
-- -- | Create a leaf node.
-- leaf :: n -> FS.FS k v -> FSTree n t k v
-- leaf x fs = R.Node (O.NonTerm x, fs) []
--
--
-- term :: t -> FS.FS k v -> FSTree n t k v
-- term x fs = R.Node (O.Term x, fs) []
--
--
-- foot :: n -> FSTree n t k v
-- foot x = R.Node (O.Foot x, M.empty) []


--------------------------------------------------
-- Compilation
--------------------------------------------------


-- | Compile the given FSTree to a computation over closed FSs which performs
-- unification between the corresponding nodes.
bottomUp
  :: (Ord k, Ord v, Show k, Show v)
  => Env.EnvM v (FSTree n t k v)
  -> C.BottomUp (FS.ClosedFS (Loc k) v)
bottomUp ofsTreeM cfsTree = fst . Env.runEnvM $ do
  fsTree' <- common ofsTreeM cfsTree
  let fsTop = FS.select isTop (snd $ R.rootLabel fsTree')
      fsBot = case findFootFS fsTree' of
        Nothing -> M.empty
        Just fs -> FS.select isBot fs
  -- not really a unification: the sets of keys are disjoint below!
  result <- FS.unifyFS fsTop fsBot
  FS.close result


-- | Like `bottomUp` but propagates values downwards the derivation tree.
topDown
  :: (Ord k, Ord v, Show k, Show v)
  => Env.EnvM v (FSTree n t k v)
  -> C.TopDown (FS.ClosedFS (Loc k) v)
-- topDown ofsTreeM = id
topDown ofsTreeM topVal cfsTree = fmap Just . check . fst . Env.runEnvM $ do
  -- fsTree' <- trace ("A: " ++ show cfsTree) $ fmap snd <$> common ofsTreeM cfsTree
  -- trace ("B: " ++ show fsTree') $ mapM FS.close fsTree'
  fsTree' <- common ofsTreeM cfsTree
  let fsTop = FS.select isTop (snd $ R.rootLabel fsTree')
      fsBot = case findFootFS fsTree' of
        Nothing -> M.empty
        Just fs -> FS.select isBot fs
  topValO <- FS.reopen topVal
  _ <- FS.unifyFS fsTop topValO
  _ <- FS.unifyFS fsBot topValO
  mapM FS.close $ fmap snd fsTree'
  where
    check may = case may of
      Nothing -> error "topDown: computation failed"
      Just x -> x


-- | The common part of the bottom-up and top-down computations.
common
  :: (Ord k, Ord v, Show k, Show v)
  => Env.EnvM v (FSTree n t k v)
  -> R.Tree (Maybe (FS.ClosedFS (Loc k) v))
  -> Env.EnvM v (FSTree n t k v)
common ofsTreeM cfsTree = do
  ofsTree <- ofsTreeM
  let fsTree = FST.zipTree ofsTree cfsTree
  mapM (uncurry doit) fsTree
  where
    doit (node, ofs) Nothing = (node,) <$> unifyTopBot ofs
    doit (node, ofs) (Just cfs) = do
      ofs' <- FS.reopen cfs
      (node,) <$> FS.unifyFS ofs ofs'


-- | Unify the top with the bottom part of the given FS.
unifyTopBot
  :: (Ord k, Ord v, Show k, Show v)
  => FS.FS (Loc k) v
  -> Env.EnvM v (FS.FS (Loc k) v)
unifyTopBot fs = do
  FS.unifyFS fs $ M.fromList
    [ (inv k, v)
    | (k, v) <- M.toList fs ]
  where
    inv (Top x) = (Bot x)
    inv (Bot x) = (Top x)


-- | Retrieve the FS assigned to the foot node (if exists, `Nothing` otherwise).
findFootFS :: FSTree n t k v -> Maybe (FS.FS (Loc k) v)
findFootFS = fmap snd . F.find (O.isFoot . fst)


-- -- | Like `bottomUp` but propagates values downwards the derivation tree.
-- topDown :: (Ord k, Ord v) => Env.EnvM v (FSTree n t k v) -> C.TopDown (FS.ClosedFS k v)
-- topDown ofsTreeM cfsTree = fmap Just . check . fst . Env.runEnvM $ do
--   ofsTree <- fmap snd <$> ofsTreeM
--   let fsTree = zipTree ofsTree cfsTree
--   fsTree' <- mapM (uncurry doit) fsTree
--   mapM FS.close fsTree'
--   where
--     check may = case may of
--       Nothing -> error "topDown: computation failed"
--       Just x -> x
--     doit ofs Nothing = return ofs
--     doit ofs (Just cfs) = do
--       ofs' <- FS.reopen cfs
--       FS.unifyFS ofs ofs'
--
--
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
  => Env.EnvM v (FSTree n t k v)
  -> C.Comp (FS.ClosedFS (Loc k) v)
compile ofsTreeM = C.Comp
  { C.bottomUp = bottomUp ofsTreeM
  , C.topDown = topDown ofsTreeM }


-- -- | Extract tree elementary represented by the given computation (due to
-- -- unification constraints the function can fail and return `Nothing`).
-- extract :: Env.EnvM v (FSTree n t k v) -> Maybe (Tree n t)
-- extract ofsTreeM = fst . Env.runEnvM $ do
--   fmap fst <$> ofsTreeM
--
--
-- -- | Zip two trees.
-- zipTree :: R.Tree a -> R.Tree b -> R.Tree (a, b)
-- zipTree (R.Node x xs) (R.Node y ys) = R.Node
--   (x, y)
--   (map (uncurry zipTree) (zip xs ys))
