{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE RecordWildCards #-}


-- | Module for working with dependency trees.


module NLP.Partage.AStar.DepTree
( Tree (..)
, Dep (..)
, toRose
, fromDeriv
) where


import qualified Data.Map.Strict              as M
import qualified Data.Set                     as S
import qualified Data.Tree                    as R

import qualified NLP.Partage.AStar.Deriv.Gorn as D
import qualified NLP.Partage.Tree.Other       as O
-- import qualified NLP.Partage.EdgeTree         as Edge


---------------------------------------------------
-- Dependency Tree
---------------------------------------------------


-- | A dependency tree with node (token) labels of type `a` and
-- arc labels of type `b`.  We use a `Data.Map` to represent
-- depenedency subtrees because (i) their ordering doesn't
-- matter, (ii) we assume they cannot repeat.
data Tree a b = Tree
  -- { root     :: S.Set (Tok t)
  -- { root     :: S.Set a
  { root     :: a
    -- ^ Label assigned to the root of a dependency tree
  , children :: M.Map (Tree a b) b
    -- ^ Children dependency trees and the corresponding dependency labels
  } deriving (Show, Eq, Ord)
-- type Tree n t = Edge.Tree (S.Set t) (Dep n)


-- | Transform the dependency tree to a rose tree.
toRose :: Tree a b -> R.Tree (a, Maybe b)
toRose =
  go Nothing
  where
    go rootArc Tree{..} =
      R.Node
      { R.rootLabel = (root, rootArc)
      , R.subForest =
        [ go (Just arc) child
        | (child, arc) <- M.toList children ] }


-- -- | Transform a rose tree to a dependency tree.
-- -- Top-level arc dependency label is ignored.
-- fromRose :: R.Tree (a, b) -> Tree a b
-- fromRose = undefined


-- | Dependency label.
data Dep
  = Arg
    -- ^ Argument dependency (related to substitution)
  | Mod
    -- ^ Modifier dependency (related to adjunction)
--   | Top
--     -- ^ Dummy dependency to be used with top-level (root) nodes
  deriving (Show, Eq, Ord)


---------------------------------------------------
-- Derivation -> Dependency Tree Conversion
---------------------------------------------------


-- | Create a dependency tree from a derivation tree.
-- Terminals become nodes of the dependency tree, enriched
-- with information about the position in the input sentence.
-- Non-terminals assigned to roots of the individual ETs
-- become arcs.
fromDeriv :: (Ord t) => D.Deriv n t -> Tree (S.Set t) Dep
fromDeriv D.Deriv{..} = Tree
  { root = S.fromList (O.project rootET)
  , children = M.fromList
    -- [ (fromDeriv deriv, Arg $ rootNT deriv)
    [ (fromDeriv deriv, modTyp gorn rootET)
    | (gorn, derivs) <- M.toList modifs
    , deriv <- derivs ] }
  where
    modTyp gorn tree = case O.follow gorn tree of
      Nothing -> error "fromDeriv.modTyp: incorrenct Gorn address"
      Just subTree -> case R.subForest subTree of
        [] -> Arg -- meaning that substitution was used
        _  -> Mod -- meaning that adjunction was used

-- fromDeriv rootDeriv =
--   go rootDeriv (Top $ rootNT rootDeriv)
--   where
--     go D.Deriv{..} edgeLabel =
--       R.Node
--       { R.rootLabel = Edge.Node
--         { Edge.nodeLabel = S.fromList (O.project rootET)
--         , Edge.edgeLabel = edgeLabel }
--       , R.subForest =
--         [ go deriv (Top $ rootNT deriv)
--           -- TODO: above we take `Top` for granted
--         | (_gorn, derivs) <- M.toList modifs
--         , deriv <- derivs ]
--       }


-- | Obtain the non-terminal in the root of the given derivation.
_rootNT :: D.Deriv n t -> n
_rootNT D.Deriv{..} =
  case R.rootLabel rootET of
    O.NonTerm x -> x
    _ -> error "rootNT: ET's root not a non-terminal"
