{-# LANGUAGE RecordWildCards #-}


-- | Alternative representation of TAG trees.


module NLP.TAG.Vanilla.Tree.Other
(
-- * Tree
  Tree
, SomeTree
, Node (..)

-- * Conversion
, encode
, decode

-- * Utils
, isTerm
, final
, proj
) where


-- import           Control.Applicative ((<$>))
import           Control.Monad (msum)
import qualified Data.Foldable as F

import qualified Data.Tree as R

import qualified NLP.TAG.Vanilla.Tree as T


---------------------------------------------------------------------
-- Types
---------------------------------------------------------------------


-- | Node type.
data Node n t
    = NonTerm n     -- ^ Standard non-terminal
    | Foot n        -- ^ Foot non-terminal
    | Term t        -- ^ Terminal
    deriving (Show, Eq, Ord)


-- | Is it a teminal?
isTerm :: Node n t -> Bool
isTerm (Term _) = True
isTerm _        = False


-- | TAG initial or auxiliary tree.
type Tree n t = R.Tree (Node n t)


-- | Original tree representation.
type SomeTree n t = Either (T.Tree n t) (T.AuxTree n t)


---------------------------------------------------------------------
-- Encoding
---------------------------------------------------------------------


-- | Encode the tree using the alternative representation.
encode :: SomeTree n t -> Tree n t
encode (Left t) = unTree t
encode (Right T.AuxTree{..}) = markFoot auxFoot (unTree auxTree)


-- | Encode the initial tree using the alternative representation.
unTree :: T.Tree n t -> Tree n t
unTree (T.INode x xs) = R.Node (NonTerm x) (map unTree xs)
unTree (T.FNode x)    = R.Node (Term x) []


-- | Mark non-terminal under the path as a foot.
markFoot :: T.Path -> Tree n t -> Tree n t
markFoot [] (R.Node (NonTerm x) []) = R.Node (Foot x) []
markFoot (i:is) (R.Node y ys) =
    R.Node y $ doit i ys
  where
    doit 0 (x:xs) = markFoot is x : xs
    doit k (x:xs) = x : doit (k-1) xs
    doit _      _      = error "markFoot.doit: unhandled case"
markFoot _ _ = error "markFoot: unhandled case"


---------------------------------------------------------------------
-- Decoding
---------------------------------------------------------------------


-- | Decode a tree represented using the alternative representation.
decode :: Tree n t -> SomeTree n t
decode t = case findFoot t of
    Just is -> Right $ T.AuxTree (mkTree t) is
    Nothing -> Left $ mkTree t


-- | Convert the parsed tree into an LTAG tree.
mkTree :: Tree n t -> T.Tree n t
mkTree (R.Node n xs) = case n of
    Term x  -> T.FNode x
    Foot x  -> T.INode
        { T.labelI = x
        , T.subTrees = [] }
    NonTerm x   -> T.INode
        { T.labelI = x
        , T.subTrees = map mkTree xs }


-- | Find the path of the foot (if present) in the tree.
findFoot :: Tree n t -> Maybe T.Path
findFoot (R.Node n xs) = case n of
    Foot _  -> Just []
    _       -> msum
        $ map (uncurry addID)
        $ zip [0..]
        $ map findFoot xs
  where
    addID i (Just is) = Just (i:is)
    addID _ Nothing   = Nothing


---------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------


-- | Is it a final tree (i.e. does it contain only terminals
-- in its leaves?)
final :: Tree n t -> Bool
final (R.Node n []) = isTerm n
final (R.Node _ xs) = and (map final xs)


-- | Projection of a tree, i.e. a list of terminals.
proj :: Tree n t -> [t]
proj =
    F.foldMap term
  where
    term (Term x) = [x]
    term _        = []
