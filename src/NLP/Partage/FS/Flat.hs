{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


-- | Feature structure-related facilities.


module NLP.Partage.FS.Flat
( OFS
, unifyFS
-- , Val (..)
, unify
, select
-- , groupBy

-- * Closed
, CFS
, Val (..)
, ID
, close
, explicate
, reopen
-- , unifyFS'

-- * Provisional
, fsTest
) where

-- import Debug.Trace (trace)

import qualified Control.Monad.State.Strict as E
import           Control.Monad.Trans.Class (lift)
import           Control.Monad (forM, unless, void)

import qualified Data.Traversable as T
import           Data.Traversable (Traversable)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as List
import           Data.Function (on)
import           Data.Either (lefts, rights)
import qualified Pipes as P
import qualified Pipes.Prelude as P

import           NLP.Partage.FS.Flat.Env (EnvT)
import qualified NLP.Partage.FS.Flat.Env as Env
import           NLP.Partage.FS.Flat.Env (Var, Alt)
import qualified NLP.Partage.Earley.Base as B


--------------------------------------------------
-- Open FS
--------------------------------------------------


-- | An open feature structure.
type OFS k = M.Map k Var


-- -- | A value associated to a key.
-- data Val v
--   = Val (Env.Alt v)
--   | Var Env.Var
--   deriving (Show, Eq, Ord)


-- -- | Alternative value.
-- alt :: (Ord v) => [v] -> Val v
-- alt = Val . S.fromList
--
--
-- -- | Singleton value.
-- single :: (Ord v) => v -> Val v
-- single x = alt [x]


-- | Unify two open feature structures.
unifyFS
  :: (Monad m, Ord k, Ord v, Show k, Show v)
  => OFS k -> OFS k -> EnvT v m (OFS k)
unifyFS fs1 fs2 = do
  env <- E.get
  -- trace ("unifyFS: " ++ show (fs1, fs2)) $ return ()
  -- trace ("<<" ++ show env ++ ">>") $ return ()
  result <- _unifyFS fs1 fs2
  -- trace (" => " ++ show result) $ return ()
  return result

-- | Unify two open feature structures.
_unifyFS
  :: (Monad m, Ord k, Ord v)
  => OFS k -> OFS k -> EnvT v m (OFS k)
_unifyFS fs1 fs2 = fmap M.fromList . runListT $ do
  let keys = S.union (M.keysSet fs1) (M.keysSet fs2)
  key <- each $ S.toList keys
  val <- case (M.lookup key fs1, M.lookup key fs2) of
    (Just v1, Just v2) -> lift $ unify v1 v2
    (Just v1, Nothing) -> pure v1
    (Nothing, Just v2) -> pure v2
    _ -> error "unifyFS: impossible happened"
  return (key, val)


-- -- | Unify two values.
-- unify :: (Monad m, Ord v) => Val v -> Val v -> EnvT v m (Val v)
-- unify val1 val2 = case (val1, val2) of
--   (Var var1, Var var2) -> Var var1 <$ Env.equal var1 var2
--   (Var var , Val alt)  -> Var var  <$ Env.set var alt
--   (Val alt , Var var)  -> Var var  <$ Env.set var alt
--   (Val alt1, Val alt2) -> pure $ Val (S.intersection alt1 alt2)


-- | Unify two values.
unify :: (Monad m, Ord v) => Var -> Var -> EnvT v m Var
unify var1 var2 = var1 <$ Env.equal var1 var2


-- | Select those keys which satisfy the given predicate.
select :: (Ord k) => (k -> Bool) -> M.Map k v -> M.Map k v
select p = M.fromList . filter (p . fst) . M.toList


-- groupBy :: (Monad m, Ord k, Ord k', Ord v) => (k -> k') -> FS k v -> EnvT v m (FS k v)
-- groupBy f fs = fmap M.fromList . runListT $ do
--   (_grpKey, m) <- each (M.toList groups)
--   let mList = M.toList m
--       (key0, val0) = head mList
--   (key, val) <- each mList
--   val' <- if key == key0
--     then return val
--     else lift $ unify val val0
--   return (key, val')
--   where
--     groups = M.fromListWith M.union
--       [ (f key, M.singleton key val)
--       | (key, val) <- M.toList fs ]


--------------------------------------------------
-- Closed FS
--------------------------------------------------


-- -- | A data structure with variables in a closed environment.
-- data Closed v a = Closed
--   { value :: a
--     -- ^ The value
--   , varMap :: M.Map Var (Alt v)
--     -- ^ The underlying environment
--   } deriving (Show, Eq, Ord)


-- | An identifier used to mark a common re-entrancy point.
type ID = Int


-- | Variable explicated == value
data Val v = Val
  { valID :: ID
    -- ^ Identifier of the value
  , valAlt :: Maybe (Alt v)
    -- ^ The set of the corresponding values
  } deriving (Show, Eq, Ord)


-- | A closed feature structure.
type CFS k v = M.Map k (Val v)


-- -- | A closed feature structure.
-- type ClosedFS k v = [(S.Set k, Maybe (Env.Alt v))]


-- | Close (== explicate) a feature structure.
close
  :: (Monad m)
  => OFS k
  -> EnvT v m (CFS k v)
close = explicate


-- | Make the values assigned to the individual variables explicit and replace
-- the variables by identifiers.
explicate
  :: (Monad m, Traversable t)
  => t Var
  -> EnvT v m (t (Val v))
explicate = flip E.evalStateT M.empty . T.mapM valFor


-- | A map of the variable <-> ID correspondence.
type VarMap = M.Map Var ID


-- | Retrieve the value corresponding to the given variable.
valFor :: (Monad m) => Var -> E.StateT VarMap (EnvT v m) (Val v)
valFor var0 = do
  var <- lift $ Env.rep var0
  mayI <- getID var
  case mayI of
    Just i -> return $ Val i Nothing
    Nothing -> do
      i <- newID var
      v <- lift $ Env.get var
      return $ Val i v


-- | Retrieve the ID for the given variable.
getID :: (Monad m) => Var -> E.StateT VarMap m (Maybe ID)
getID = E.gets . M.lookup


-- | Create a new ID and assign if to the given variable.
newID :: (Monad m) => Var -> E.StateT VarMap m ID
newID var = do
  i <- E.gets M.size
  E.modify' $ M.insert var i
  return i


--------------------------------------------------
-- Re-opening
--------------------------------------------------


-- | Reopen a closed FS within the current environment.
reopen
  :: (Monad m, Ord k, Ord v)
  => CFS k v
  -> EnvT v m (OFS k)
reopen = flip E.evalStateT M.empty . T.mapM varFor


-- | A map of the variable <-> ID correspondence.
type IDMap = M.Map ID Var


-- | Retrieve the variable corresponding to the given value. Update the value
-- corresponding to this variable too, if needed.
varFor
  :: (Monad m, Ord v)
  => Val v
  -> E.StateT IDMap (EnvT v m) Var
varFor val = do
  mayVar <- getVar val
  case mayVar of
    Just v -> return v
    Nothing -> newVar val


-- | Retrieve the ID for the given variable.
getVar
  :: (Monad m)
  => Val v
  -> E.StateT IDMap m (Maybe Var)
getVar = E.gets . M.lookup . valID


-- | Create a new variable and assign it to the given ID.
newVar
  :: (Monad m, Ord v)
  => Val v
  -> E.StateT IDMap (EnvT v m) Var
newVar Val{..} = do
  var <- lift Env.var
  E.modify' $ M.insert valID var
  case valAlt of
    Just alt -> lift $ Env.set var alt
    Nothing -> return ()
  return var


instance (Ord k, Ord v, Show k, Show v) => B.Unify (CFS k v) where
  unify x0 y0 = fst . Env.runEnvM $ do
    x <- reopen x0
    y <- reopen y0
    z <- unifyFS x y
    close z


-- -- | Close a feature structure.
-- close :: (Monad m, Ord k) => FS k v -> EnvT v m (ClosedFS k v)
-- close openFS = do
--   xs <- toList openFS
--   let regular = lefts xs
--   special <- getSpecial (rights xs)
--   return $ regular ++ special
--
--   where
--
--     toList fs = runListT $ do
--       (key, val) <- each $ M.toList fs
--       case val of
--         Val alt -> return $ Left (S.singleton key, Just alt)
--         Var var -> do
--           rep <- lift $ Env.rep var
--           return $ Right (rep, S.singleton key)
--
--     getSpecial xs = do
--       let specials = List.groupBy ((==) `on` fst) xs
--       forM specials $ \special -> do
--         let rep = fst $ head special
--             keySet = S.unions $ map snd special
--         alt <- Env.get rep
--         return (keySet, alt)
--
--
-- -- -- | Unify an open feature structure with a closed one.
-- -- unifyFS' :: (Monad m, Ord k, Ord v) => FS k v -> ClosedFS k v -> EnvT v m (FS k v)
-- -- unifyFS' fs1 fs2 = do
-- --   fs2' <- reopen fs2
-- --   unifyFS fs1 fs2'


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
  a <- Env.var
  Env.set a $ S.fromList ["a"]
  let fs1 = M.fromList
        [ ("key1", a)
        , ("key2", x)
        , ("key4", q) ]
      fs2 = M.fromList
        [ ("key1", y)
        , ("key2", y)
        , ("key3", z)
        , ("key5", q) ]
  Env.set y $ S.fromList ["a", "b"]
  Env.set z $ S.fromList ["a", "b"]
  Env.equal y z
  fs <- unifyFS fs1 fs2
  close fs
