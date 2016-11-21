{-# LANGUAGE RecordWildCards #-}


-- | Monadic interface with environment support.


module NLP.Partage.Env
(
-- * Types
  Alt
, Var
-- , Env
, EnvT
, EnvM
-- * Primitives
, get
, set
, equal
-- * Running
, runEnvT
, runEnvM

-- * Provisional
, envTest
) where


import           Control.Monad              (guard, unless)
import qualified Control.Monad.State.Strict as E
import qualified Control.Monad.Trans.Maybe  as Y
import qualified Control.Monad.Identity     as I

import qualified Data.Partition as P
import qualified Data.Map.Strict as M
import qualified Data.Set as S


--------------------------------------------------
-- Types
--------------------------------------------------


-- | Alternative of values.
type Alt v = S.Set v


-- | Variable name.
type Var = Int


-- | Variable environment.
data Env v = Env
  { varMap :: M.Map Var (Alt v)
    -- ^ Values assigned to individual variables
  , varPar :: P.Partition Var
    -- ^ Disjoint set over variables
  } deriving (Show, Eq, Ord)


-- | Feature structure transformer.
type EnvT v m = Y.MaybeT (E.StateT (Env v) m)


-- | Feature structure monad.
type EnvM v = EnvT v I.Identity


--------------------------------------------------
-- Primitives
--------------------------------------------------


-- | Empty environment.
empty :: Env v
empty = Env M.empty P.empty


-- | Get value assigned to the variable.
get :: Monad m => Var -> EnvT v m (Maybe (Alt v))
get var = do
  Env{..} <- E.get
  let rep = P.rep varPar var
  return $ M.lookup rep varMap


-- | Assign value to the variable.
set :: (Monad m, Ord v) => Var -> Alt v -> EnvT v m ()
set var alt = do
  env@Env{..} <- E.get
  let rep = P.rep varPar var
  case M.lookup rep varMap of
    Nothing -> E.put $ env {varMap = M.insert rep alt varMap}
    Just oldAlt -> do
      let newAlt = S.intersection oldAlt alt
      guard . not $ S.null newAlt
      E.put $ env {varMap = M.insert rep newAlt varMap}


-- | Enforce equality between two variables.
equal :: (Monad m, Ord v) => Var -> Var -> EnvT v m ()
equal var1 var2 = do
  env@Env{..} <- E.get
  let rep1 = P.rep varPar var1
      rep2 = P.rep varPar var2
  unless (rep1 == rep2) $ do
    let alt1 = M.lookup rep1 varMap
        alt2 = M.lookup rep2 varMap
        par' = P.joinElems rep1 rep2 varPar
        rep  = P.rep par' rep1
    case (alt1, alt2) of
      (Nothing, Nothing) -> do
        E.put $ Env {varMap = varMap, varPar = par'}
      (Just x1, Nothing) -> do
        E.put $ Env {varMap = M.insert rep x1 varMap, varPar = par'}
      (Nothing, Just x2) -> do
        E.put $ Env {varMap = M.insert rep x2 varMap, varPar = par'}
      (Just x1, Just x2) -> do
        let alt = S.intersection x1 x2
        guard . not $ S.null alt
        E.put $ env {varMap = M.insert rep alt varMap, varPar = par'}


--------------------------------------------------
-- Running
--------------------------------------------------


-- | Run the FST transformer. Return `Nothing` in case of the failure of the
-- computation.
runEnvT :: Monad m => EnvT v m a -> m (Maybe a, Env v)
runEnvT = flip E.runStateT empty . Y.runMaybeT


-- | Run the FST monad. Return `Nothing` in case of the failure of the
-- computation.
runEnvM :: EnvM v a -> (Maybe a, Env v)
runEnvM = I.runIdentity . runEnvT


--------------------------------------------------
-- Tests
--------------------------------------------------


envTest :: IO ()
envTest = print $ runEnvM $ do
  set 1 $ S.singleton 'a'
  set 1 $ S.fromList ['a', 'b']
  set 2 $ S.singleton 'b'
  equal 1 2
  get 2
