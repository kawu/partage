{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


-- | A monad for defining elementary trees with FS unification.


module NLP.Partage.Test
( theTest
) where


import           Control.Monad (guard, foldM, forM_)

-- import qualified Control.Monad.State.Strict as E
import qualified Data.Text as T
import qualified Data.Tree as R
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Maybe (fromJust, mapMaybe)

import qualified NLP.Partage.FS as FS
import qualified NLP.Partage.Env as Env
import qualified NLP.Partage.DAG as DAG
import qualified NLP.Partage.Tree.Comp as C
import qualified NLP.Partage.Tree.Other as O
import           NLP.Partage.Earley.Base (Unify(..))
import qualified NLP.Partage.Earley as Earley


--------------------------------------------------
-- Core
--------------------------------------------------


compile :: Env.EnvM T.Text FSTree -> C.Comp ClosedFS
compile ofsTreeM cfsTree = fst . Env.runEnvM $ do
  ofsTree <- fmap snd <$> ofsTreeM
  let fsTree = zipTree ofsTree cfsTree
  fsTree' <- mapM (uncurry doit) fsTree
  FS.close $ R.rootLabel fsTree'
  where
    doit ofs Nothing = return ofs
    doit ofs (Just cfs) = do
      ofs' <- FS.reopen cfs
      FS.unifyFS ofs ofs'


extract :: Env.EnvM T.Text FSTree -> Maybe Tree
extract ofsTreeM = fst . Env.runEnvM $ do
  fmap fst <$> ofsTreeM


zipTree :: R.Tree a -> R.Tree b -> R.Tree (a, b)
zipTree (R.Node x xs) (R.Node y ys) = R.Node
  (x, y)
  (map (uncurry zipTree) (zip xs ys))


--------------------------------------------------
-- Tests
--------------------------------------------------


-- | A closed feature structure.
type FS = FS.FS T.Text T.Text
type ClosedFS = FS.ClosedFS T.Text T.Text

instance Unify ClosedFS where
  unify x0 y0 = fst . Env.runEnvM $ do
    x <- FS.reopen x0
    y <- FS.reopen y0
    z <- FS.unifyFS x y
    FS.close z


-- | An elementary tree.
type Tree = R.Tree (O.Node T.Text T.Text)


-- | An elementary tree with the accompanying feature structures.
type FSTree = R.Tree (O.Node T.Text T.Text, FS)


-- | Some smart constructors.
node x fs = R.Node (O.NonTerm x, fs)
leaf x fs = R.Node (O.NonTerm x, fs) []
term x fs = R.Node (O.Term x, fs) []
foot x = R.Node (O.Foot x, M.empty) []
-- node x = R.Node (O.NonTerm x)
-- leaf x = R.Node (O.NonTerm x) []
-- term x = R.Node (O.Term x) []
-- foot x = R.Node (O.Foot x) []


num, sg3 :: T.Text
num = "num"
sg3 = "sg3"


girl :: Env.EnvM T.Text FSTree
girl = do
  numVar <- FS.Var <$> Env.var
  sg3Var <- FS.Var <$> Env.var
  let fs = M.fromList
        [ (num, numVar)
        , (sg3, sg3Var) ]
  return $
    node "NP" fs
    [ node "N" fs
      [ term "girl" fs]
    ]


-- sleep :: Tree
-- sleep =
--   node "S"
--   [ leaf "NP"
--   , node "VP"
--     [ node "V"
--       [term "sleep"]
--     ]
--   ]

sleep :: Env.EnvM T.Text FSTree
sleep = do
  sg3Var <- FS.Var <$> Env.var
  let no = M.empty
      fs = M.fromList
        [ (sg3, sg3Var) ]
  return $
    node "S" no
    [ leaf "NP" fs
    , node "VP" fs
      [ node "V" fs
        [term "sleep" fs]
      ]
    ]


-- many :: Tree
-- many =
--   node "N"
--   [ node "Adj" [term "many"]
--   , foot "N"
--   ]

many :: Env.EnvM T.Text FSTree
many = do
  numVar <- FS.Var <$> Env.var
  let fs = M.fromList [(num, numVar)]
  return $
    node "N" fs
    [ node "Adj" fs [term "many" fs]
    , foot "N"
    ]


-- | A simple TAG grammar.
gram :: [(Tree, C.Comp ClosedFS)]
gram = mapMaybe process
  [girl, sleep, many]
  where
    process source = do
      let comp = compile source
      tree <- extract source
      return (tree, comp)


theTest :: IO ()
theTest = do
  let dag = DAG.mkGram gram
  trees <- Earley.parse dag "S" $ Earley.fromList
    [ ("many", [mkPair num "pl"])
    , ("girl", [mkPair sg3 "-", mkPair num "pl"])
    , ("sleep", [mkPair sg3 "-"]) ]
  mapM_ printTree trees
  where
    printTree = putStrLn . R.drawTree . fmap show . O.encode . Left


--------------------------------------------------
-- Utils
--------------------------------------------------


mkPair x y = (S.singleton x, Just $ S.singleton y)


-- | Get the FS under the given path.
under :: [Int] -> R.Tree (Maybe [a]) -> [a]
under path t = maybe [] id $ do
  subTree <- follow path t
  R.rootLabel subTree


-- | Follow the path to a particular subtree.
follow :: [Int] -> R.Tree a -> Maybe (R.Tree a)
follow = flip $ foldM step


-- | Follow one step of the `Path`.
step :: R.Tree a -> Int -> Maybe (R.Tree a)
step t k = R.subForest t !? k


-- | Maybe a k-th element of a list.
(!?) :: [a] -> Int -> Maybe a
(x:xs) !? k
    | k > 0     = xs !? (k-1)
    | otherwise = Just x
[] !? _ = Nothing
