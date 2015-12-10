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

-- * Composition
, inject
) where


-- import           Control.Applicative ((<$>))
import           Control.Monad (msum)

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


-- -- | Partial function returning the non-terminal symbol
-- -- for `NonTerm` and `Foot`.
-- nonTerm :: Node n t -> n


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
-- Composition
---------------------------------------------------------------------


-- | Identify all possible ways to inject (i.e. substitute
-- or adjoin) the first tree to the second one.
inject :: (Eq n, Eq t) => Tree n t -> Tree n t -> [Tree n t]
inject s t = if isAux s
    then adjoin s t
    else subst s t


-- | Compute all possible ways of adjoining the first tree into the
-- second one.
adjoin :: (Eq n, Eq t) => Tree n t -> Tree n t -> [Tree n t]
adjoin _ (R.Node (NonTerm _) []) = []
-- adjoin _ (R.Node (Foot _) _) = []
-- adjoin _ (R.Node (Term _) _) = []
adjoin s (R.Node n ts) =
    here ++ below
  where
    -- perform adjunction here
    here = if R.rootLabel s == n
        then [replaceFoot (R.Node n ts) s]
        else []
    -- consider to perform adjunction lower in the tree
    below = map (R.Node n) (doit ts)
    doit [] = []
    doit (x:xs) =
        [u : xs | u <- adjoin s x] ++
        [x : us | us <- doit xs]


-- | Replace foot of the second tree with the first tree.
-- If there is no foot in the second tree, it will be returned
-- unchanged.
replaceFoot :: Tree n t -> Tree n t -> Tree n t
replaceFoot t (R.Node (Foot _) []) = t
replaceFoot t (R.Node x xs) = R.Node x $ map (replaceFoot t) xs


-- | Compute all possible ways of substituting the first tree into
-- the second one.
subst :: (Eq n, Eq t) => Tree n t -> Tree n t -> [Tree n t]
subst s (R.Node n []) =
    if R.rootLabel s == n
        then [s]
        else []
subst s (R.Node n ts) =
    map (R.Node n) (doit ts)
  where
    doit [] = []
    doit (x:xs) = 
        [u : xs | u <- subst s x] ++
        [x : us | us <- doit xs]


-- | Check if the tree is auxiliary.
isAux :: Tree n t -> Bool
isAux (R.Node (Foot _) _) = True
isAux (R.Node _ xs) = or (map isAux xs)
