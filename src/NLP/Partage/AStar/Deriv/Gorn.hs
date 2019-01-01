{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}


-- | Alternative (and, in fact, more standard) representation
-- of a derivation trees, i.e., a tree of elementary trees.


module NLP.Partage.AStar.Deriv.Gorn
( Deriv (..)
, size
, deriv4show
, fromDeriv
) where


import qualified Control.Arrow           as Arr

import qualified Data.Map.Strict         as M
import qualified Data.Tree               as R

import qualified NLP.Partage.AStar.Deriv as D
-- import qualified NLP.Partage.EdgeTree    as Edge
import           NLP.Partage.Tree        (Path)
import qualified NLP.Partage.Tree.Other  as O


---------------------------------------------------
-- Derivation Tree
---------------------------------------------------


-- | A derivation tree contains ETs in its nodes and Gorn addresses in its
-- edges. A Gorn address indicates to which node of the parent ET the given ET
-- attaches. Note that the address determines the type of the operation:
-- substitution or adjunction.
data Deriv n t = Deriv
  { rootET :: O.Tree n t
    -- ^ Root (elementary tree, ET) of the derivation tree
    -- (reminder: using the `rootET` name because it doesn't stem from
    --  the type the the root is an ET)
  , modifs :: M.Map Path [Deriv n t]
    -- ^ Derivations attached to the individual nodes (specified by the
    -- corresponding Gorn addresses) of the root ET; note that, in case of
    -- adjunction, many derivations can attach at one and the same Gorn address
    -- and in this case the attachement (adjunction) order matters.
  }
-- type Deriv n t = Edge.Tree (O.Tree n t) Gorn


-- | Size of a derivation tree (i.e., number of nodes).
size :: Deriv n t -> Int
size Deriv{..} = 1 + sum
  [ size deriv
  | (_path, derivs) <- M.toList modifs
  , deriv <- derivs ]


-- | Transform the derivation tree into a tree which is easy
-- to draw using the standard `R.draw` function.
deriv4show :: Deriv n t -> R.Tree (Either Path (O.Node n t))
deriv4show =
  go
  where
    go Deriv{..} = addChildren
      (fmap Right rootET)
      [ (path, go deriv)
      | (path, derivs) <- M.toList modifs
      , deriv <- derivs ]
    addChildren R.Node{..} ts = R.Node
      { R.rootLabel = rootLabel
      , R.subForest = subForest ++
        [ R.Node (Left path) [deriv]
        | (path, deriv) <- ts ]
      }


---------------------------------------------------
-- Conversion
---------------------------------------------------


-- | Conversion from the base derivation data type.
fromDeriv :: D.Deriv n t -> Deriv n t
fromDeriv =
  go . D.normalize
  where
    go t = Deriv
      { rootET = getRootET t
      , modifs = M.fromList
        [ (gorn, map go ts)
        | (gorn, ts) <- getModifs t ] }


-- | Extract the root ET from the given derivation.
getRootET :: D.Deriv n t -> O.Tree n t
getRootET = fmap D.node


-- | Get the derivations (and their corresponding Gorn addresses)
-- modifying the rootET.
getModifs :: D.Deriv n t -> [(Path, [D.Deriv n t])]
getModifs =
  map (Arr.first reverse) . go []
  where
    go gorn R.Node{..}
      = (gorn, D.modif rootLabel)
      : concat
        [ go (i:gorn) child
        | (i, child) <- zip [0..] subForest ]
