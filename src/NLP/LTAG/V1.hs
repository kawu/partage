{-# LANGUAGE RecordWildCards #-}


-- | A first, simple version of LTAGs.
-- Additional constraints over the adjoining operation are not
-- taken into account.


module NLP.LTAG.V1
( LTAG (..)
, module NLP.LTAG.Tree
) where


import           Data.Set (Set)
import qualified Data.Set as S
import           NLP.LTAG.Tree


-- An LTAG grammar consists of:
-- * A finite set of terminal symbols T,
-- * A finite set of non-terminal symbols N, N and T are disjoint,
-- * One of the non-terminal symbols is a starting symbol S \in N,
-- * A set of initial trees I,
--   - Interior nodes have non-terminal symbols,
--   - Frontier nodes have terminal or non-terminal symbols;
--     Non-terminal frontier nodes are marked for substitution.
-- * A set of auxiliary trees A,
--   - Interior nodes have non-terminal symbols,
--   - Frontier nodes have terminal or non-terminal symbols;
--     Non-terminal frontier nodes are marked for substitution, apart
--     from one special adjoining node called the foot node.  The foot
--     node has the same label as the root node.
--
-- Q: Can we use the adjoining operation on non-terminal frontier nodes?
--    Or, to rephrase the question: can we perform the substitution
--    operation with an auxiliary tree?  


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


-- -- | A derivated tree is constructed by applying a sequence of transforming
-- -- (substitution or adjoining) rules on particular positions of a tree.
-- type Deriv a b = [(Path, Trans a b)]
-- 
-- 
-- -- | A transformation of a tree.
-- type Trans a b = Either (E Tree a b) (E AuxTree a b)
-- 
-- 
-- -- | Derive a tree.
-- derive :: Deriv a b -> E Tree a b -> Maybe (E Tree a b)


-- -- | Perform the given transformation.
-- perform :: Trans a b -> IniTree a b -> Maybe (IniTree a b)
-- perform Subst{..} t = do
--     
-- 
-- 
-- -- | Enumerate trees which can be generated from the tree by using the
-- -- substitution rules.
-- subst :: LTAG a b -> 


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
