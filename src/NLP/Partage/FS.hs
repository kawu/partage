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
import           Control.Monad (forM)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as List
import           Data.Function (on)
import           Data.Either (lefts, rights)
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
    (Just v1, Nothing) -> pure v1
    (Nothing, Just v2) -> pure v2
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
  (Val alt1, Val alt2) -> pure $ Val (S.intersection alt1 alt2)


--------------------------------------------------
-- Closed FS
--------------------------------------------------


-- | A closed feature structure.
type ClosedFS k v = [(S.Set k, Maybe (Env.Alt v))]


-- | Close a feature structure.
close :: (Monad m, Ord k) => FS k v -> EnvT v m (ClosedFS k v)
close openFS = do
  xs <- toList openFS
  let regular = lefts xs
  special <- getSpecial (rights xs)
  return $ regular ++ special

  where

    runListT = P.toListM . P.enumerate
    toList fs = runListT $ do
      (key, val) <- each $ M.toList fs
      case val of
        Val alt -> return $ Left (S.singleton key, Just alt)
        Var var -> do
          rep <- lift $ Env.rep var
          return $ Right (rep, S.singleton key)

    getSpecial xs = do
      let specials = List.groupBy ((==) `on` fst) xs
      forM specials $ \special -> do
        let rep = fst $ head special
            keySet = S.unions $ map snd special
        alt <- Env.get rep
        return (keySet, alt)



-- -- | Unify two open feature structures.
-- unifyFS' :: (Monad m, Ord k, Ord v) => FS k v -> ClosedFS k v -> EnvT v m (FS k v)
-- unifyFS' fs1 fs2 = fmap M.fromList . runListT $ do
--   where
--     runListT = P.toListM . P.enumerate


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
fsTest = print . fst $ Env.runEnvM $ do
  x <- Env.var
  y <- Env.var
  z <- Env.var
  let alt = Val . S.fromList
      fs1 = M.fromList
        [ ("key1", alt ["a"])
        , ("key2", Var x) ]
      fs2 = M.fromList
        [ ("key1", Var y)
        , ("key2", Var y)
        , ("key3", Var z) ]
  Env.set y $ S.fromList ["a", "b"]
  Env.set z $ S.fromList ["a", "b"]
  Env.equal y z
  fs <- unifyFS fs1 fs2
  close fs
