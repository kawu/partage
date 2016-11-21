-- {-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}


-- | Feature structure-related facilities.


module NLP.Partage.FS
( FS
, unifyFS
, Val (..)
, unify

-- * Provisional
, fsTest
) where


import           Control.Monad.Trans.Class (lift)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Pipes as P
import qualified Pipes.Prelude as P

import           NLP.Partage.Env (EnvT)
import qualified NLP.Partage.Env as Env


--------------------------------------------------
-- Open FS
--------------------------------------------------


-- | An open feature structure.
type FS k v = M.Map k (Val v)


-- | A value associated to a key.
data Val v
  = Val (Env.Alt v)
  | Var Env.Var
  deriving (Show, Eq, Ord)


-- -- | Alternative value.
-- alt :: (Ord v) => [v] -> Val v
-- alt = Val . S.fromList
--
--
-- -- | Singleton value.
-- single :: (Ord v) => v -> Val v
-- single x = alt [x]


-- | Unify two open feature structures.
unifyFS :: (Monad m, Ord k, Ord v) => FS k v -> FS k v -> EnvT v m (FS k v)
unifyFS fs1 fs2 = fmap M.fromList . runListT $ do
  let keys = S.union (M.keysSet fs1) (M.keysSet fs2)
  key <- each $ S.toList keys
  val <- case (M.lookup key fs1, M.lookup key fs2) of
    (Just v1, Just v2) -> lift $ unify v1 v2
    (Just v1, Nothing) -> return v1
    (Nothing, Just v2) -> return v2
    _ -> error "unifyFS: impossible happened"
  return (key, val)
  where
    runListT = P.toListM . P.enumerate


-- | Unify two values.
unify :: (Monad m, Ord v) => Val v -> Val v -> EnvT v m (Val v)
unify val1 val2 = case (val1, val2) of
  (Var var1, Var var2) -> Var var1 <$ Env.equal var1 var2
  (Var var , Val alt)  -> Var var  <$ Env.set var alt
  (Val alt , Var var)  -> Var var  <$ Env.set var alt
  (Val alt1, Val alt2) -> return $ Val (S.intersection alt1 alt2)


--------------------------------------------------
-- Closed FS
--------------------------------------------------


-- | A closed feature structure.
-- type ClosedFS k v = M.Map k (Env.Alt v)


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each


--------------------------------------------------
-- Tests
--------------------------------------------------


fsTest :: IO ()
fsTest = print $ Env.runEnvM $ do
  let alt = Val . S.fromList
      fs1 = M.fromList
        [ ("key1", alt ["a"])
        , ("key2", Var 1) ]
      fs2 = M.fromList
        [ ("key1", Var 2)
        , ("key2", Var 2) ]
  Env.set 2 $ S.fromList ["a", "b"]
  unifyFS fs1 fs2
