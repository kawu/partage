{-# LANGUAGE RecordWildCards #-}


-- | A first, simple version of LTAGs.
-- Additional constraints over the adjoining operation are not
-- taken into account.


module NLP.LTAG.V1
( LTAG (..)
, whereSubst
, whereAdjoin
, generate
, treeLang
, unique
, module NLP.LTAG.Tree
) where


import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.List as L
import           Data.Maybe (mapMaybe, catMaybes)
import           NLP.LTAG.Tree


-- | We define LTAG with respect to the description above.  The sets of
-- terminal and non-terminal symbols are implicit.
data LTAG a b = LTAG
    { startSym  :: a
    , iniTrees  :: Set (E Tree a b)
    , auxTrees  :: Set (E AuxTree a b) }
    deriving (Show, Eq, Ord)


-- | A grammar structure (e.g. tree). 
-- TODO: Find appropriate name.
type E t a b = t a (Either a b)


-- In a lexicalized LTAG grammar, at least one terminal symbol (the anchor) 
-- must appear at the frontier of all (initial or auxiliary) trees.
-- It would be hard to ensure this property on the level of the type system.


-- | Determine positions, on which the given elementary tree can be
-- substituted.
whereSubst :: (Eq a, Eq b) => E Tree a b -> E Tree a b -> [Path]
whereSubst s t
    = map fst
    . filter (pr . snd)
    $ walk t
  where
    q = rootLabelE s
    pr x = rootLabelE x == q && isLeaf x


-- | Determine positions, on which the given elementary tree can be
-- adjoined.
whereAdjoin :: (Eq a, Eq b) => E AuxTree a b -> E Tree a b -> [Path]
whereAdjoin s t
    = map fst
    . filter (pr . snd)
    $ walk t
  where
    q = rootLabelE $ auxTree s
    pr x = rootLabelE x == q && (not.isLeaf) x


---------------------------------------------------------------------
-- Tree language
---------------------------------------------------------------------


-- | Generate the tree language represented by the LTAG grammar.
-- Trees with non-termial frontier nodes are not filtered out.
--
-- The function is based on a notion of a generation.
-- Iteratively, starting with the set of initial starting trees,
-- we produce all trees which can be derived from the current
-- generation of trees.  This way we obtain the next generation
-- of trees, which is simultaneously returned as a result of
-- the `generate` function and subjected to the next iteration
-- of the process.
generate :: (Ord a, Ord b) => LTAG a b -> [E Tree a b]
generate LTAG{..} =
    go treeSet0
  where
    -- `ts` is the current generation
    go ts =
        -- `ts'` is the next generation
        let ts' = S.toList . S.fromList
                $ concat [step t | t <- ts]
        in  ts ++ go ts'
    -- Initial set of trees
    treeSet0
        = filter ((== Left startSym) . rootLabelE)
        $ S.toList iniTrees
    -- Next generation
    step t = stepSubst t ++ stepAdjoin t
    stepSubst t = catMaybes
        [ subst x s t
        | s <- S.toList iniTrees
        , x <- whereSubst s t ]
    stepAdjoin t = catMaybes
        [ adjoin x s t
        | s <- S.toList auxTrees
        , x <- whereAdjoin s t ]


-- | Like `generate`, but non-termial frontier nodes are removed.
treeLang :: (Ord a, Ord b) => LTAG a b -> [Tree a b]
treeLang = mapMaybe finalTree . generate


---------------------------------------------------------------------
-- Misc
---------------------------------------------------------------------


-- | Return only unique elements in the list.
unique :: Ord a => [a] -> [a]
unique =
    catMaybes . snd . L.mapAccumL step S.empty
  where
    step acc x = case S.member x acc of
        True    -> (acc, Nothing)
        False   -> (S.insert x acc, Just x)


-- | Check if the tree is final. 
finalTree :: E Tree a b -> Maybe (Tree a b)
finalTree n@INode{..} = do
    subTrees' <- mapM finalTree subTrees
    return $ n { subTrees = subTrees' }
finalTree FNode{..} = case labelF of
    Right x -> Just $ FNode x
    _       -> Nothing


-- | Alternate list elements.
alternate :: [[a]] -> [a]
alternate [] = []
alternate xs =
    mapMaybe hd xs ++ alternate (mapMaybe tl xs)
  where
    hd (x:_)  = Just x
    hd _      = Nothing
    tl (_:ys) = Just ys
    tl _      = Nothing


-- | Get root non-terminal.
rootLabelE :: E Tree a b -> Either a b
rootLabelE INode{..} = Left labelI
rootLabelE FNode{..} = labelF


-- | Is it a leaf tree?
isLeaf :: E Tree a b -> Bool
isLeaf FNode{} = True
isLeaf _       = False


-- | Generate the tree-language represented by the grammar.



-- IMPORTANT: note the difference between the two:
-- * Perform lexical insertion -> substitute terminal symbols with lexical items,
-- * Lexicalized grammar -> each tree has at least on terminal frontier node.
--
-- BTW: I \union A is called the set of *elementary* trees.
--
-- Other properties of an LTAG grammar:
-- * In elementary trees, we can check a set of properties between terminal nodes.
--   For example, we can enforce (case, number, gender?) agreement between different
--   terminal nodes (in fact this applies to the inserted lexical items).
--   !! Q: does it apply (in some way) to non-terminal nodes? !!
-- * We can also state within an elementary tree a constraint over a particular
--   non-terminal node, for example it is possible to say that the particular node
--   can be substituted only by a transivite (or intransivite) verb, but not by
--   any verb.
