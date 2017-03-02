{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}


-- | Elementary trees with FS unification. Top and bottom feature structures are
-- distinguished.


module NLP.Partage.FSTree2
(
-- * Types
  OFSTree
, OFSTreeM
, CFSTree
, Node (..)
, OFS
, CFS
, Loc (..)
-- * Compilation
, bottomUp
, topDown
, compile
, extract
-- * Utils
, unifyTopBot
-- , zipTree
) where

-- import Debug.Trace (trace)

import           Control.Monad (guard)

import           Data.Maybe (maybeToList)
import qualified Data.Foldable as F
import qualified Data.Functor.Compose as F
import qualified Data.Tree as R
import qualified Data.Map.Strict as M


import qualified NLP.Partage.FS as FS
-- import qualified NLP.Partage.FSTree as FST
import qualified NLP.Partage.Env as Env
import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.Earley.Comp as C
-- import qualified NLP.Partage.Earley.Base as B


--------------------------------------------------
-- Types
--------------------------------------------------


-- | Top or bottom FS.
data Loc k = Top k | Bot k
-- data Loc k = Sim k | Top k | Bot k
  deriving (Show, Eq, Ord)


-- isSim :: Loc k -> Bool
-- isSim x = case x of
--   Sim _ -> True
--   _ -> False


isTop :: Loc k -> Bool
isTop x = case x of
  Top _ -> True
  _ -> False


isBot :: Loc k -> Bool
isBot x = case x of
  Bot _ -> True
  _ -> False


-- unLoc :: Loc k -> k
-- unLoc loc = case loc of
--   -- Sim x -> x
--   Top x -> x
--   Bot x -> x


-- | A node of an FTAG elementary tree.
data Node n t f = Node
  { treeNode :: O.Node n t
    -- ^ The TAG tree node itself
  -- , featStr  :: FS.OFS (Loc k)
  , featStr  :: f
    -- ^ The feature structure attached to this node
  , nullAdj  :: Bool
    -- ^ Is the null adjunction constraint attached to this node?
  } deriving (Show, Eq, Ord)



-- | An open FS.
type OFS k = FS.OFS (Loc k)


-- | An open FSTree.
type OFSTree n t k = R.Tree (Node n t (OFS k))
-- type OFSTree n t k = R.Tree (Node n t k)
-- type OFSTree n t k = R.Tree (O.Node n t, FS.OFS (Loc k))


-- | An open FSTree together with the corresponding environment.
type OFSTreeM n t k v = Env.EnvM v (OFSTree n t k)
-- type OFSTreeM n t k v = Env.EnvM v (R.Tree (O.Node n t, FS.OFS (Loc k)))


-- | A closed FS.
type CFS k v = FS.CFS (Loc k) v


-- | A closed FSTree.
type CFSTree n t k v = R.Tree (Node n t (CFS k v))


--------------------------------------------------
-- Compilation
--------------------------------------------------


-- | Compile the given FSTree to a computation over closed FSs which performs
-- unification between the corresponding nodes.
bottomUp
  :: (Ord k, Ord v, Show k, Show v)
  => OFSTreeM n t k v
  -> C.BottomUp (CFS k v)
bottomUp ofsTreeM cfsTree = maybeToList . fst . Env.runEnvM $ do
  fsTree' <- common ofsTreeM cfsTree
  let fsTop = FS.select isTop (featStr $ R.rootLabel fsTree')
      fsBot = case findFootFS fsTree' of
        Nothing -> M.empty
        Just fs -> FS.select isBot fs
  -- below, not really a unification: the sets of keys are disjoint!
  -- we just merge the two parts into a single FS.
  result <- FS.unifyFS fsTop fsBot
  FS.close result


-- | Like `bottomUp` but propagates values downwards the derivation tree.
topDown
  :: (Ord k, Ord v, Show k, Show v)
  => C.TreeID
     -- ^ ID of the corresponding elementary tree
  -> OFSTreeM n t k v
  -> C.TopDown (CFS k v)
topDown treeID ofsTreeM topVal cfsTree =
  -- fmap Just . check . fst . Env.runEnvM $ do
  map finalize . maybeToList . fst . Env.runEnvM $ do
    -- fsTree' <- trace ("A: " ++ show cfsTree) $
    --   fmap snd <$> common ofsTreeM cfsTree
    -- trace ("B: " ++ show fsTree') $ mapM FS.close fsTree'
    fsTree' <- common ofsTreeM cfsTree
    topValO <- FS.reopen topVal
    let fsTop = FS.select isTop (featStr $ R.rootLabel fsTree')
        fsBot = case findFootFS fsTree' of
          Nothing -> M.empty
          Just fs -> FS.select isBot fs
    fsTop' <- FS.unifyFS fsTop $ FS.select isTop topValO
    fsBot' <- FS.unifyFS fsBot $ FS.select isBot topValO
    fsTree'' <- putFootFS fsBot' =<< putRootFS fsTop' fsTree'
    fmap F.getCompose . FS.explicate . F.Compose $ fmap featStr fsTree''
    -- mapM FS.close $ fmap snd fsTree'
  where
    -- finalize the computation and add info about elementary tree ID
    finalize cfs = (fmap Just cfs, treeID)
--   where
--     check may = case may of
--       Nothing -> error "topDown: computation failed"
--       Just x -> x


-- | The common part of the bottom-up and top-down computations.
common
  :: (Ord k, Ord v, Show k, Show v)
  => OFSTreeM n t k v
  -> R.Tree (Maybe (CFS k v))
  -> OFSTreeM n t k v
common ofsTreeM cfsTree = do
  ofsTree <- ofsTreeM
  let fsTree = zipTree ofsTree cfsTree
  mapM (uncurry doit) fsTree
  where
--     doit (node, ofs) Nothing = (node,) <$> unifyTopBot ofs
--     doit (node, ofs) (Just cfs) = do
--       ofs' <- FS.reopen cfs
--       (node,) <$> FS.unifyFS ofs ofs'
    doit node Nothing = do
      ofs <- unifyTopBot (featStr node)
      return $ node {featStr = ofs}
    doit node (Just cfs) = do
      -- first we check that adjunction constraint is not set up
      guard . not $ nullAdj node
      ofs <- FS.reopen cfs
      ofs' <- FS.unifyFS (featStr node) ofs
      return $ node {featStr = ofs'}


-- | Unify the top with the bottom part of the given FS.
unifyTopBot
  :: (Ord k, Ord v, Show k, Show v)
  => FS.OFS (Loc k)
  -> Env.EnvM v (FS.OFS (Loc k))
-- unifyTopBot = return
unifyTopBot fs = do
  FS.unifyFS fs $ M.fromList
    [ (inv k, v)
    | (k, v) <- M.toList fs ]
  where
    inv (Top x) = (Bot x)
    inv (Bot x) = (Top x)
-- below, an alternative solution, which does not seem to work 100% correctly --
-- if a key is present only in one of the parts of a complex FS, it's not going
-- to be unified with its counter-part.
-- unifyTopBot = FS.groupBy unLoc


-- | Retrieve the FS assigned to the foot node (if exists, `Nothing` otherwise).
findFootFS
  -- :: R.Tree (O.Node n t, FS.OFS (Loc k))
  :: OFSTree n t k
  -> Maybe (FS.OFS (Loc k))
findFootFS = fmap featStr . F.find (O.isFoot . treeNode)


-- | Unify the given FS with the root FS.
putRootFS
  :: (Ord k, Ord v, Show k, Show v)
  => FS.OFS (Loc k)
  -> OFSTree n t k
  -> OFSTreeM n t k v
putRootFS fs R.Node{..} = do
  fs' <- FS.unifyFS fs (featStr rootLabel)
  return R.Node
    -- { R.rootLabel = (fst rootLabel, fs')
    { R.rootLabel = rootLabel {featStr = fs'}
    , R.subForest = subForest }


-- | Unify the given FS with the foot FS.
putFootFS
  :: (Ord k, Ord v, Show k, Show v)
  => FS.OFS (Loc k)
  -> OFSTree n t k
  -> OFSTreeM n t k v
putFootFS fs R.Node{..}
  | O.isFoot (treeNode rootLabel) = do
      fs' <- FS.unifyFS fs (featStr rootLabel)
      return R.Node
        { R.rootLabel = rootLabel {featStr = fs'}
        , R.subForest = subForest }
  | otherwise = R.Node rootLabel <$> mapM (putFootFS fs) subForest


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
  => C.TreeID
  -> OFSTreeM n t k v
  -> C.Comp (CFS k v)
compile treeID ofsTreeM = C.Comp
  { C.up = bottomUp ofsTreeM
  , C.down = topDown treeID ofsTreeM }


-- | Extract elementary tree represented by the given computation (due to
-- unification constraints the function can fail and return `Nothing`).
extract
  :: OFSTreeM n t k v
  -> Maybe (CFSTree n t k v)
extract ofsTreeM = fst . Env.runEnvM $ do
  ofsTree <- ofsTreeM
  fsTree' <- fmap F.getCompose . FS.explicate . F.Compose $ fmap featStr ofsTree
  return . fmap merge $ zipTree ofsTree fsTree'
  where
    merge (node, ofs) = node {featStr = ofs}


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


---------------------------------------------
-- Utils
---------------------------------------------


-- | Zip two trees.
zipTree :: R.Tree a -> R.Tree b -> R.Tree (a, b)
zipTree (R.Node x xs) (R.Node y ys) = R.Node
  (x, y)
  (map (uncurry zipTree) (zip xs ys))
