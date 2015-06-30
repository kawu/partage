{-
 - Flat feature structures.
 -}


module NLP.LTAG.FlatFS where


import           Control.Applicative ((<$>))
import qualified Control.Monad.State.Strict as E

import qualified Data.Set                   as S
import qualified Data.Map.Strict            as M
import qualified Data.Partition             as R
import qualified Pipes                      as P


-- | A feature structure.
type FS x y v = M.Map x (Either y v)


-- | Environment stores information about variable values and
-- relations between them.
data Env y v = Env {
    -- | The partition represents an equality relation between
    -- variables.
      part :: Partition v
    -- | Valuation of variables.
    , eval :: M.Map v y
    } deriving (Show, Eq, Ord)


-- -- | A unification monad contains information about a feature
-- -- structure and a corresponding environment.
-- data UniSt y v = UniSt
-- 
-- 
-- -- | Unification transformer.
-- type UniT y v m = E.StateT (UniSt y v) m
-- 
-- 
-- -- | Run unification computation.
-- runUniT
--     :: FS x y v     -- ^ Feature structure
--     -> Env y v      -- ^ And a corresponding environment
--     -> UniT y v m a -- ^ Unification computation
--     -> m (Maybe (FS x y v, Env y v))
-- runUniT = undefined
-- 
-- 
-- -- | Assign value to a given variable.
-- assign :: Monad m => y -> v -> EnvT y v m ()
-- assign = undefined



-- | Envoironment transformer.
type EnvT y v m = E.StateT (Env y v) m


-- | Envoironment monad.
type EnvM y v = EnvT y v Identity


-- | Run computation within the environment monad.
runEnvM :: Env y v -> EnvM y v a -> Maybe (Env y v, a)
runEnvM = undefined


-- | Run computation within the environment transformer.
runEnvT :: Monad m => Env y v -> EnvT y v m a -> m (Maybe (Env y v, a))
runEnvT = undefined


-- | Assign value to a given variable.
assign :: Monad m => y -> v -> EnvT y v m ()
assign = undefined


-- | Mark that the two varialbes are equal.
egal :: Monad m => v -> v -> EnvT y v m ()
egal = undefined


-- | Regular unification with no enviroment sharing.  The
-- resulting environment will be the extension of the first
-- environment given as an argument.
unify
    :: (Ord x, Ord y, Ord v)
    => FS x y v     -- ^ The first FS
    -> Env y v      -- ^ And the corresponding environment
    -> FS x y v     -- ^ The second FS
    -> Env y v      -- ^ And the corresponding environment
    -> Maybe (FS x y b, Env y v)
unify fs1 env1 fs2 env2 =
    runEnvM env2 $ do
    runEnvT env1 $ do
    P.runListT $ do
        (attr, vals) <- each fs0
        case S.toList vals of 
            [val] -> return (attr, val)
            [Left x, Left y] -> do 
                liftEnv1 $ guard $ x == y
                return (attr, Left x)
            [Left x, Right v] -> do
                liftEnv2 $ assign x v

            _ -> error "unify: sth.'s wrong"
  where
    liftEnv1 = lift
    liftEnv2 = lift . lift
    fs0 = M.toList $ M.unionWith S.union
        (S.singleton <$> fs1)
        (S.singleton <$> fs2)


--         -- go over through all possible attributes
--         x <- each $ S.toList $ S.union
--             (M.keysSet fs1) (M.keysSet fs2)


--------------------------------------------------
-- UTILS
--------------------------------------------------


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each
