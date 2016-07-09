{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE RecordWildCards #-}


-- | Module for working with dependency trees.


module NLP.Partage.AStar.DepTree
( Tok (..)
, Dep (..)
, fromDeriv
) where


import qualified Data.Map.Strict              as M
import qualified Data.Set                     as S
import qualified Data.Tree                    as R

import qualified NLP.Partage.AStar.Deriv.Gorn as D
import qualified NLP.Partage.Tree.Other       as O
import qualified NLP.Partage.EdgeTree         as Edge


---------------------------------------------------
-- Dependency Tree
---------------------------------------------------


-- | A dependency tree.
type Tree n t = Edge.Tree (S.Set (Tok t)) (Dep n)
-- data Tree n t = Tree
--   { root     :: S.Set (Tok t)
--     -- ^ A set of tokens assigned to the root of a dependency tree
--   , children :: M.Map (Tree n t) (Dep n)
--     -- ^ Children derivation trees, together with the corresponding
--     -- dependency labels
--   } deriving (Show, Eq, Ord)


-- | A token is a terminal enriched with information about the position
-- in the input sentence.
data Tok t = Tok
  { position :: Int
    -- ^ Position of the node in the dependency tree
  , terminal :: t
    -- ^ Terminal on the corresponding position
  } deriving (Show, Eq, Ord)


-- | Dependency label.
data Dep a
  = Arg a
    -- ^ Argument dependency (related to substitution)
  | Mod a
    -- ^ Modifier dependency (related to adjunction)
  | Top a
    -- ^ Dummy dependency to be used with top-level (root) nodes
  deriving (Show, Eq, Ord, Functor)


---------------------------------------------------
-- Derivation -> Dependency Tree Conversion
---------------------------------------------------


-- | Create a dependency tree from a derivation tree.
-- Terminals become nodes of the dependency tree, enriched
-- with information about the position in the input sentence.
-- Non-terminals assigned to roots of the individual ETs
-- become arcs.
fromDeriv :: (Ord n, Ord t) => D.Deriv n (Tok t) -> Tree n t
fromDeriv rootDeriv =
  go rootDeriv (Top $ rootNT rootDeriv)
  where
    go D.Deriv{..} edgeLabel =
      R.Node
      { R.rootLabel = Edge.Node
        { Edge.nodeLabel = S.fromList (O.project rootET)
        , Edge.edgeLabel = edgeLabel }
      , R.subForest =
        [ go deriv (Top $ rootNT deriv)
          -- TODO: above we take `Top` for granted
        | (_gorn, derivs) <- M.toList modifs
        , deriv <- derivs ]
      }
-- fromDeriv D.Deriv{..} = Tree
--   { root = S.fromList (O.project rootET)
--   , children = M.fromList
--     [ (fromDeriv deriv, Top $ rootNT deriv)
--       -- TODO: above we take `Top` for granted
--     | (_gorn, derivs) <- M.toList modifs
--     , deriv <- derivs ] }


-- | Obtain the non-terminal in the root of the given derivation.
rootNT :: D.Deriv n t -> n
rootNT D.Deriv{..} =
  case R.rootLabel rootET of
    O.NonTerm x -> x
    _ -> error "rootNT: ET's root not a non-terminal"
