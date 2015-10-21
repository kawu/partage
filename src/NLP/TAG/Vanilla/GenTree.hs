{-# LANGUAGE RecordWildCards #-}


{- 
 - An alternative representation of elementary trees where
 - foot nodes are simply marked with a star.
 -}


module NLP.LTAG.GenTree where


import           Control.Applicative ((<$>))
import           Control.Arrow (first)
import           Control.Monad (foldM)

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import qualified NLP.FeatureStructure.Tree as FS
import qualified NLP.LTAG.Tree2 as T


-- | A tree with values of type 'n' kept in the interior nodes,
-- values of type 'l' kept in the leaf nodes, FS features
-- (attributes) of type 'f', FS atomic values of type 'a'
-- and FS identifiers (variables) of type 'i'.
data GenTree n l i f a
    = Node -- ^ Regular (interior, foot or substitution) node
        { labelN    :: n
        , topFS     :: FS.FN i f a
        , botFS     :: FS.FN i f a
        -- | Nothing if a *foot* node
        , subTrees  :: Maybe [GenTree n l i f a] }
    | Leaf -- ^ Leaf node
        { labelL    :: l }
    deriving (Show, Eq, Ord)


-- | Translate to a primary tree representation.
toTree
    :: GenTree n l i f a
    -> Either
        (T.Tree n l i f a)
        (T.AuxTree n l i f a)
toTree n@Node{..} = case subTrees of
    -- A foot node:
    Nothing -> Right $ T.AuxTree (mkNode []) []
    -- Not a foot node:
    Just xs -> case findRight (map toTree xs) of
        Left ys -> Left $ mkNode ys
        Right (ls, x, rs) -> Right $ T.AuxTree
            { T.auxTree = mkNode $ ls ++ (T.auxTree x : rs)
            , T.auxFoot = length ls : T.auxFoot x }
  where
    mkNode ys = T.INode
      { T.labelI = labelN
      , T.topFS  = topFS
      , T.botFS  = botFS
      , T.subTrees = ys }
toTree (Leaf x) = Left $ T.LNode x


-- | Find the first (and only!) instance of `Right` in the input
-- list.  If it exists, return a Right triple.  Left, plain list
-- otherwise.
findRight
    :: [Either a b]
    -> Either [a] ([a], b, [a])
findRight (x:xs) = case x of
    Left  y -> add y $ findRight xs
    Right y -> Right ([], y, takeLefts xs)
  where
    add y (Left ys)           = Left $ y : ys
    add y (Right (ls, z, rs)) = Right (y : ls, z, rs)
findRight [] = Left []


-- | Retrieve Left values from the list and raise error if there is
-- some Right value inside.
takeLefts (Left x : xs) = x : takeLefts xs
takeLefts (Right _ : _) = error "takeLefts: right value"
takeLefts [] = []
