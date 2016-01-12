{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}


-- | This module contains the core types used across the entire
-- library.


module NLP.TAG.Vanilla.Core
(
-- * Classes
  View (..)
, VOrd

-- * Types
, Pos
, SymID
-- , Cost
) where


--------------------------------------------------
-- CUSTOM SHOW
--------------------------------------------------


-- | A custom, 'Show'-like typeclass.
class Show a => View a where
    view :: a -> String

instance View String where
    view x = x

instance View Int where
    view = show

instance (View a, View b) => View (Either a b) where
    view (Left x) = "L " ++ view x
    view (Right x) = "R " ++ view x


--------------------------------------------------
-- VIEW + ORD
--------------------------------------------------


-- | 'View' + 'Ord'
class (View a, Ord a) => VOrd a where

instance (View a, Ord a) => VOrd a where


--------------------------------------------------
-- CORE TYPES
--------------------------------------------------


-- | A position in the input sentence.
type Pos = Int


-- | 'SymID' is used to mark internal (non-leaf, non-root)
-- non-terminals with unique (up to subtree sharing) identifiers so
-- that incompatible rule combinations are not possible.
type SymID = Int


-- -- | Cost (weight, probability) of employing an elementary
-- -- unit (tree, rule) in a parse tree.
-- type Cost = Double
