{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}


-- | Additional computation accompanying elementary trees (ETs).


module NLP.Partage.Earley.Comp
(
-- * Environment
  Env
, leaf
, foot

-- * Computations
, BottomUp
, TopDown
, Comp (..)
-- ** Complex
, fail
, or
, any

-- * Utilities
, dummyTopDown
) where


import           Prelude hiding (or, any, fail)
-- import qualified Control.Monad as M
-- import           Data.Maybe (mapMaybe)
import qualified Data.Tree as R

-- import qualified NLP.Partage.Earley.Base as B


---------------------------------------------------------------------
-- Types
---------------------------------------------------------------------


-- | A map assigning values to individual nodes of the tree. Values are required
-- to be assigned to leaf nodes but not internal nodes (adjunction is optional).
-- TODO: If we assume that there is some empty value which unifies with
-- everything, we could ignore the difference between `Nothing` and an empty
-- value! At the moment, it seems that there are good reasons to do that.
type Env a = R.Tree (Maybe a)


-- | Create a leaf environment.
leaf :: a -> Env a
leaf x = R.Node (Just x) []


-- | Create a foot environment.
foot :: Env a
foot = R.Node Nothing []


-- | Bottom-up computation. An empty-list result stands for unification failure.
--
-- Computation from the values assigned to individual nodes of an ET to a value
-- of this ET (and, more precisely, to its root). If the function fails (i.e.
-- returns []), then the corresponding ET cannot be "inferred".
--
-- Normally, the function should either fail or return one result (singleton
-- list), but we generalize it so that computations can be composed from smaller
-- computations.
type BottomUp a = Env a -> [a]


-- | Top-down computation. The first argument is the value that comes from
-- upwards, the second argument is equal to the first argument of the
-- corresponding bottom-up computation, and the result is a tree of values. Or
-- rather, a list thereof, because we want to be able to generalize the top-down
-- computations in a similar way as the bottom-up computations.
--
-- The top-down computation is used to determine the value of the entire ET and
-- propagate the values down the derivation tree; used when extracting
-- derivations. Note that `topDown` is a generalization of `bottomUp` and thus
-- results of the both functions must be consistent.
type TopDown a = a -> Env a -> [Env a]


-- | An elementary computation.
data Comp a = Comp
  { up :: BottomUp a
  , down :: TopDown a
  }


-- | A computation which always fails.
fail :: Comp a
fail = Comp
  { up = \_ -> []
  , down = \_ _ -> [] }


---------------------------------------------------------------------
-- Complex computations
---------------------------------------------------------------------


-- | A disjunctive computation.
or :: Comp a -> Comp a -> Comp a
or x y = Comp
  { up = \env -> up x env ++ up y env
  , down = \top env -> down x top env ++ down y top env }


-- | A disjunction of a list of compuations.
any :: [Comp a] -> Comp a
any (x : xs) = or x (any xs)
any [] = fail


-- -- | A disjunctive computation.
-- data Or a b = Or a b
--
-- instance (Comp a v, Comp b v) => Comp (Or a b) v where
--   bottomUp (Or x y) = \env -> bottomUp x env ++ bottomUp y env
--   topDown  (Or x y) = \top env -> topDown x top env ++ topDown y top env

-- -- | A type-level list.
-- data List f
--   = Cons (f (List f))
--   | Nil
--
-- instance (Comp (f a a) v) => Comp (List (f a)) v where
--   bottomUp (Cons )
--
--
-- -- | A disjunction of a list of computations.
-- any :: [a] -> List (Or a)
-- any (x : xs) = Cons $ Or x (any xs)
-- any [] = Nil


-- -- | A disjunctive computation.
-- newtype Or a = Or [a]
--
-- instance Comp a b => Comp (Or a) b where
--   bottomUp (Or xs) = \env -> concat [bottomUp x env | x <- xs]
--   topDown  (Or xs) = \top env -> concat [topDown x top env | x <- xs]


-- -- | A conjunctive computation.
-- data And a b = And a b
--
-- instance (Comp a v, Comp b v, B.Unify v) => Comp (And a b) v where
--   bottomUp (And x y) =
--     \env ->
--       mapMaybe (uncurry B.unify) $
--       cart (bottomUp x env)
--            (bottomUp y env)
--   -- topDown  (Or xs) = \top env -> concat [topDown x top env | x <- xs]


-- -- | A productive computation.
-- data Prod a b = Prod a b
--
-- instance (Comp a v, Comp b w) => Comp (Prod a b) (v, w) where
--   bottomUp (Prod x y) =
--     \env ->
--       cart (bottomUp x $ fmap (fmap fst) env)
--            (bottomUp y $ fmap (fmap snd) env)
--   topDown (Prod x y) =
--     \top env ->
--       map (fmap pairM . uncurry zipTree) $
--       cart (topDown x (fst top) $ fmap (fmap fst) env)
--            (topDown y (snd top) $ fmap (fmap snd) env)


---------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------


-- | A dummy top-down computation which does not propagate any values down the
-- derivation tree.  It just assignes the value from top to the root of the
-- given tree, which is not necessarily the correct behavior in every case.
dummyTopDown :: TopDown a
dummyTopDown x t = [t {R.rootLabel = Just x}]



-- -- | Cartesian product.
-- cart :: [a] -> [b] -> [(a, b)]
-- cart xs ys = [(x, y) | x <- xs, y <- ys]
--
--
-- -- | Join two monadic values.
-- pairM :: Monad m => (m a, m b) -> m (a, b)
-- pairM (m, n) = do
--   x <- m
--   y <- n
--   return (x, y)
--
--
-- -- | Zip two trees, assuming that they have identical topology.
-- zipTree :: R.Tree a -> R.Tree b -> R.Tree (a, b)
-- zipTree = error "Comp.zipTree: not implemented!"
