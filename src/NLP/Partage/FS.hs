{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


-- | Feature structure-related facilities.


module NLP.Partage.FS
( FS
, unifyFS
, Val (..)
, unify
, select

-- * Closed
, ClosedFS
, close
, reopen
-- , unifyFS'

-- * Provisional
, fsTest
) where

-- import Debug.Trace (trace)

import qualified Control.Monad.State.Strict as E
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
import qualified NLP.Partage.Earley.Base as B


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
unifyFS :: (Monad m, Ord k, Ord v, Show k, Show v) => FS k v -> FS k v -> EnvT v m (FS k v)
unifyFS fs1 fs2 = do
  env <- E.get
  -- trace ("unifyFS: " ++ show (fs1, fs2)) $ return ()
  -- trace ("<<" ++ show env ++ ">>") $ return ()
  result <- _unifyFS fs1 fs2
  -- trace (" => " ++ show result) $ return ()
  return result

-- | Unify two open feature structures.
_unifyFS :: (Monad m, Ord k, Ord v, Show k, Show v) => FS k v -> FS k v -> EnvT v m (FS k v)
_unifyFS fs1 fs2 = fmap M.fromList . runListT $ do
  let keys = S.union (M.keysSet fs1) (M.keysSet fs2)
  key <- each $ S.toList keys
  val <- case (M.lookup key fs1, M.lookup key fs2) of
    (Just v1, Just v2) -> lift $ unify v1 v2
    (Just v1, Nothing) -> pure v1
    (Nothing, Just v2) -> pure v2
    _ -> error "unifyFS: impossible happened"
  return (key, val)


-- | Unify two values.
unify :: (Monad m, Ord v) => Val v -> Val v -> EnvT v m (Val v)
unify val1 val2 = case (val1, val2) of
  (Var var1, Var var2) -> Var var1 <$ Env.equal var1 var2
  (Var var , Val alt)  -> Var var  <$ Env.set var alt
  (Val alt , Var var)  -> Var var  <$ Env.set var alt
  (Val alt1, Val alt2) -> pure $ Val (S.intersection alt1 alt2)


-- | Select those keys which satisfy the given predicate.
select :: (Ord k) => (k -> Bool) -> FS k v -> FS k v
select p = M.fromList . filter (p . fst) . M.toList


--------------------------------------------------
-- Closed FS
--------------------------------------------------


-- | A closed feature structure.
type ClosedFS k v = [(S.Set k, Maybe (Env.Alt v))]

instance (Ord k, Ord v, Show k, Show v) => B.Unify (ClosedFS k v) where
  unify x0 y0 = fst . Env.runEnvM $ do
    x <- reopen x0
    y <- reopen y0
    z <- unifyFS x y
    close z


-- | Close a feature structure.
close :: (Monad m, Ord k) => FS k v -> EnvT v m (ClosedFS k v)
close openFS = do
  xs <- toList openFS
  let regular = lefts xs
  special <- getSpecial (rights xs)
  return $ regular ++ special

  where

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


-- | Reopen a closed FS within the current environment.
reopen :: (Monad m, Ord k, Ord v) => ClosedFS k v -> EnvT v m (FS k v)
reopen closedFS = fmap M.fromList . runListT $ do
  (keySet, val) <- each closedFS
  var <- lift Env.var
  case val of
    Nothing -> return ()
    Just v  -> lift $ Env.set var v
  key <- each (S.toList keySet)
  return (key, Var var)


-- -- | Unify an open feature structure with a closed one.
-- unifyFS' :: (Monad m, Ord k, Ord v) => FS k v -> ClosedFS k v -> EnvT v m (FS k v)
-- unifyFS' fs1 fs2 = do
--   fs2' <- reopen fs2
--   unifyFS fs1 fs2'


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each


-- | Run a ListT computation (unidiomatic Haskell?).
runListT :: (Monad m) => P.ListT m a -> m [a]
runListT = P.toListM . P.enumerate


--------------------------------------------------
-- Tests
--------------------------------------------------


fsTest :: IO ()
fsTest = print $ Env.runEnvM $ do
  x <- Env.var
  y <- Env.var
  z <- Env.var
  q <- Env.var
  let alt = Val . S.fromList
      fs1 = M.fromList
        [ ("key1", alt ["a"])
        , ("key2", Var x)
        , ("key4", Var q) ]
      fs2 = M.fromList
        [ ("key1", Var y)
        , ("key2", Var y)
        , ("key3", Var z)
        , ("key5", Var q) ]
  Env.set y $ S.fromList ["a", "b"]
  Env.set z $ S.fromList ["a", "b"]
  Env.equal y z
  fs <- unifyFS fs1 fs2
  close fs
