{-# LANGUAGE RecordWildCards #-}


-- | Support for generic (recursive) feature structures.


module NLP.Partage.FS.Generic
(
-- * Types
  Var
, FS (..)
, UniT
, UniM
-- * Primitives
, top
, bot
, var
, get
, rep
-- , set
-- * Running
, runUniT
, runUniM
-- * Unification
, unify

-- * Provisional
, fsTestGen1
, fsTestGen2
) where


import           Control.Monad              (guard, unless, forM_)
import qualified Control.Monad.State.Strict as E
import qualified Control.Monad.Trans.Maybe  as Y
import qualified Control.Monad.Identity     as I
-- import           Control.Monad.Trans.Class (lift)

-- import qualified Pipes as Pipes
-- import qualified Pipes.Prelude as Pipes

import qualified Data.Partition as P
import qualified Data.Map.Strict as M
import qualified Data.Set as S


--------------------------------------------------
-- FSs, variables and environment
--------------------------------------------------


-- -- | A disjunction of of values.
-- type Alt v = S.Set v


-- | Variable name.
newtype Var = Var {_unVar :: Int}
  deriving (Eq, Ord)

instance Show Var where
  show (Var i) = "V" ++ show i


-- | An open feature structures.
data FS k v
  = Leaf (S.Set v)
    -- ^ A leaf -- an alternative (disjunction) of values
  | Node (M.Map k Var)
    -- ^ An internal node -- a map from keys to variables
  deriving (Show, Eq, Ord)


-- | Bottom FS (unifies with everything)
bot :: FS k v
bot = Leaf S.empty


-- | Top FS (unifies with everything)
top :: FS k v
top = Node M.empty


-- | Variable environment.
data Env k v = Env
  { varPar :: P.Partition Var
    -- ^ Disjoint set over variables
  , varMap :: M.Map Var (FS k v)
    -- ^ Values assigned to individual variables
  , varNum :: Int
    -- ^ Variable counter (needed to create new variables)
  } deriving (Show, Eq, Ord)


-- | Empty environment.
empty :: Env k v
empty = Env P.empty M.empty 0


-- | Feature structure transformer.
type UniT k v m = Y.MaybeT (E.StateT (Env k v) m)


-- | Feature structure monad.
type UniM k v = UniT k v I.Identity


--------------------------------------------------
-- Environment-related primitives
--------------------------------------------------



-- | Create a new variable.
var :: (Monad m) => UniT k v m Var
var = do
  i <- E.gets varNum
  E.modify' $ \env -> env
    { varNum = varNum env + 1
    , varMap = M.insert (Var i) top (varMap env)
    }
  return $ Var i


-- | Get value assigned to the variable.
get :: Monad m => Var -> UniT k v m (FS k v)
get v = do
  Env{..} <- E.get
  let r = P.rep varPar v
  case M.lookup r varMap of
    Nothing -> error "get: impossible happened"
    Just fs -> return fs


-- | Get the representant of the variable.
rep :: Monad m => Var -> UniT k v m Var
rep v = do
  Env{..} <- E.get
  let r = P.rep varPar v
  return r


-- | Assign value to a variable.
set :: (Monad m, Ord v) => Var -> FS k v -> UniT k v m ()
set v fs = do
  env@Env{..} <- E.get
  let r = P.rep varPar v
  E.put $ env {varMap = M.insert r fs varMap}


-------------------------------------------------
-- Unification
--------------------------------------------------


-- | Unify two variables.
unify :: (Monad m, Ord k, Ord v) => Var -> Var -> UniT k v m ()
unify var1 var2 = do
  env@Env{..} <- E.get
  let rep1 = P.rep varPar var1
      rep2 = P.rep varPar var2
  unless (rep1 == rep2) $ do
    -- detemine the corresponding FS values
    fs1 <- get rep1
    fs2 <- get rep2
    -- perform one-level (flat) unification of the corresponding FSs
    fs <- flatUnifyFS fs1 fs2
    -- create the new partition
    let par' = P.joinElems rep1 rep2 varPar
        -- representant of the new partition
        rep'  = P.rep par' rep1
        -- element of {rep1, rep2} which is *not* the resulting representant
        nrep = if rep1 == rep' then rep2 else rep1
        -- the new variable map with not-a-representant removed
        varMap' = M.delete nrep varMap
    -- update the environment
    E.put $ env {varMap = varMap', varPar = par'}
    set rep' fs
    -- perform recursive unification
    recUnifyFS fs1 fs2


-- | Unify two open feature structures.
flatUnifyFS
  :: (Monad m, Ord k, Ord v)
  => FS k v -> FS k v -> UniT k v m (FS k v)
flatUnifyFS (Leaf x1) (Leaf x2) = do
  let y = S.intersection x1 x2
  guard . not $ S.null y
  return $ Leaf y
flatUnifyFS (Leaf alt) (Node mp) = do
  guard $ M.null mp -- eq. to `Node mp == top`
  return $ Leaf alt
flatUnifyFS (Node mp) (Leaf alt) = do
  guard $ M.null mp -- eq. to `Node mp == top`
  return $ Leaf alt
flatUnifyFS (Node mp1) (Node mp2) =
  -- we chose arbitrarily (using `fst`) the target variable for each key
  return . Node $ M.unionWith (curry fst) mp1 mp2


-- | Unify two open feature structures.
recUnifyFS
  :: (Monad m, Ord k, Ord v)
  => FS k v -> FS k v -> UniT k v m ()
-- recUnifyFS (Node mp1) (Node mp2) = Pipes.runEffect . Pipes.enumerate $ do
--   let keys = S.intersection (M.keysSet mp1) (M.keysSet mp2)
--   key <- each $ S.toList keys
--   case (M.lookup key mp1, M.lookup key mp2) of
--     (Just v1, Just v2) -> lift $ unify v1 v2
--     _ -> error "unifyFS: impossible happened"
recUnifyFS (Node mp1) (Node mp2) = do
  let keys = S.intersection (M.keysSet mp1) (M.keysSet mp2)
  forM_ (S.toList keys) $ \key -> case (M.lookup key mp1, M.lookup key mp2) of
    (Just v1, Just v2) -> unify v1 v2
    _ -> error "unifyFS: impossible happened"
recUnifyFS _ _ = return ()


--------------------------------------------------
-- Running
--------------------------------------------------


-- | Run the FST transformer. Return `Nothing` in case of the failure of the
-- computation.
runUniT :: Monad m => UniT k v m a -> m (Maybe a, Env k v)
runUniT = flip E.runStateT empty . Y.runMaybeT


-- | Run the FST monad. Return `Nothing` in case of the failure of the
-- computation.
runUniM :: UniM k v a -> (Maybe a, Env k v)
runUniM = I.runIdentity . runUniT


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- -- | ListT from a list.
-- each :: Monad m => [a] -> Pipes.ListT m a
-- each = Pipes.Select . Pipes.each
--
--
-- -- | Run a ListT computation (unidiomatic Haskell?).
-- runListT :: (Monad m) => Pipes.ListT m a -> m [a]
-- runListT = Pipes.toListM . Pipes.enumerate


--------------------------------------------------
-- Testing
--------------------------------------------------


fsTestGen1 :: IO ()
fsTestGen1 = print . runUniM $ do
  x <- var
  y <- var
  z <- var
  q <- var
  a <- var

  set a . Leaf $ S.fromList ["a"]
  set y . Leaf $ S.fromList ["a", "b"]
  set z . Leaf $ S.fromList ["a"]

  fs1 <- var
  fs2 <- var

  set fs1 . Node $ M.fromList
    [ ("key1", a)
    , ("key2", x)
    , ("key4", q) ]
  set fs2 . Node $ M.fromList
    [ ("key1", y)
    , ("key2", y)
    , ("key3", z)
    , ("key5", q) ]

  _ <- unify y z
  unify fs1 fs2
  -- close fs


fsTestGen2 :: IO ()
fsTestGen2 = print . runUniM $ do
  let value = Leaf . S.singleton
      node = Node . M.fromList

  const <- var
  set const $ value ()

  x1 <- var
  x2 <- var
  y1 <- var

  set x1 $ node [("k1", x2)]
  set x2 $ node [("k2", x1)]
  -- set y1 $ node [("k1", y1), ("k2", const)]
  set y1 $ node [("k1", y1)]

  unify x1 y1
