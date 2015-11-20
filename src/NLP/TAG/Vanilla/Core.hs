{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}


module NLP.TAG.Vanilla.Core where


--------------------------------------------------
-- CUSTOM SHOW
--------------------------------------------------


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


class (View a, Ord a) => VOrd a where

instance (View a, Ord a) => VOrd a where


--------------------------------------------------
-- CORE TYPES
--------------------------------------------------


-- | Position in the sentence.
type Pos = Int


-- | Additional symbol identifier.
type SymID = Int


-- | Cost (weight, probability) of employing the given elementary unit (tree,
-- rule)
type Cost = Double
