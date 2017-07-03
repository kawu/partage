{-# LANGUAGE OverloadedStrings #-}


-- | A monad for defining elementary trees with FS unification.


module NLP.Partage.Test
( theTest
) where


import           Control.Arrow (first)
-- import           Control.Monad (foldM)

-- import qualified Control.Monad.State.Strict as E
import qualified Data.Text as T
import qualified Data.Tree as R
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Maybe (mapMaybe)

import qualified NLP.Partage.DAG as DAG
import qualified NLP.Partage.Tree.Other as O

import qualified NLP.Partage.FS.Flat as FS
import qualified NLP.Partage.FS.Flat.FSTree2 as FST
-- import           NLP.Partage.FS.Flat.FSTree2 (FSTree, node, leaf, foot, term)
import qualified NLP.Partage.FS.Flat.Env as Env

import qualified NLP.Partage.Auto.Trie as Trie

import qualified NLP.Partage.Earley.Comp as C
import qualified NLP.Partage.Earley as Earley


--------------------------------------------------
-- Utility types
--------------------------------------------------


type Tree n t = R.Tree (O.Node n t)


-- type FSTree n t k = FST.OFSTree n t k


--------------------------------------------------
-- Tests
--------------------------------------------------


-- | Non-terminal.
type N = T.Text

-- | Terminal.
type T = T.Text

-- | FS key.
type K = T.Text

-- | FS value.
type V = T.Text


-- | Predefined keys
num, sg3 :: K
num = "num"
sg3 = "sg3"


girl :: Env.EnvM V (FST.OFSTree N T K)
girl = do
  numVar <- Env.var
  sg3Var <- Env.var
  let fs = mkFS
        [ (num, numVar)
        , (sg3, sg3Var) ]
  return $
    node "NP" fs
    [ node "N" fs
      [ term "girl" fs ]
    ]


sleep :: Env.EnvM V (FST.OFSTree N T K)
sleep = do
  sg3Var <- Env.var
  let no = M.empty
      fs = mkFS
        [ (sg3, sg3Var) ]
  return $
    node "S" no
    [ leaf "NP" fs
    , node "VP" fs
      [ node "V" fs
        [ term "sleep" fs ]
      ]
    ]


many :: Env.EnvM V (FST.OFSTree N T K)
many = do
  numVar <- Env.var
  let fs = mkFS [(num, numVar)]
  return $
    node "N" fs
    [ node "Adj" fs [term "many" fs]
    , foot "N"
    ]


-- | A simple TAG grammar.
gram :: [(Tree N T, C.Comp (FST.CFS K V))]
-- gram :: [(FST.CFSTree N T K V, C.Comp (FST.CFS K V))]
gram = mapMaybe process
  [girl, sleep, many]
  where
    process source = do
      let comp = FST.compile "?" source
      tree <- fmap FST.treeNode <$> FST.extract source
      -- tree <- FST.extract source
      return (tree, comp)


--------------------------------------------------
-- Main
--------------------------------------------------


theTest :: IO ()
theTest = do
  let dag = DAG.mkGramWith C.or gram
      tri = Trie.fromGram (DAG.factGram dag)
      aut = Earley.mkAuto (DAG.dagGram dag) tri
  trees <- Earley.parseAuto aut "S" $ Earley.fromList
    [ ("many", mkFS [(num, val 0 "pl")])
    , ("girl", mkFS [(sg3, val 0 "-"), (num, val 1 "pl")])
    , ("sleep", mkFS [(sg3, val 0 "-")]) ]
  mapM_ printTree trees
  where
    printTree = putStrLn . R.drawTree . fmap show . O.encode . Left
    -- mkPair x y = (x, Just $ S.singleton y)
    val i = FS.Val i . Just . S.singleton


--------------------------------------------------
-- Utils
--------------------------------------------------


-- -- | Get the FS under the given path.
-- under :: [Int] -> R.Tree (Maybe [a]) -> [a]
-- under path t = maybe [] id $ do
--   subTree <- follow path t
--   R.rootLabel subTree
--
--
-- -- | Follow the path to a particular subtree.
-- follow :: [Int] -> R.Tree a -> Maybe (R.Tree a)
-- follow = flip $ foldM step
--
--
-- -- | Follow one step of the `Path`.
-- step :: R.Tree a -> Int -> Maybe (R.Tree a)
-- step t k = R.subForest t !? k
--
--
-- -- | Maybe a k-th element of a list.
-- (!?) :: [a] -> Int -> Maybe a
-- (x:xs) !? k
--     | k > 0     = xs !? (k-1)
--     | otherwise = Just x
-- [] !? _ = Nothing


--------------------------------------------------
-- Smart constructors
--------------------------------------------------


-- | Create an internal node.
node :: n -> FST.OFS k -> [FST.OFSTree n t k] -> FST.OFSTree n t k
node x fs = R.Node $
  let nod = simple (O.NonTerm x)
  in  nod {FST.featStr = fs}


-- | Create a leaf node.
leaf :: n -> FST.OFS k -> FST.OFSTree n t k
leaf x fs = node x fs []


term :: t -> FST.OFS k -> FST.OFSTree n t k
term x fs =
  let nod = (simple (O.Term x)) {FST.featStr = fs}
  in  R.Node nod []


foot :: n -> FST.OFSTree n t k
foot x =
  let nod = simple (O.Foot x)
  in  R.Node nod []


-- | Construct fs-node with default values: empty FS and no null-adjunction
-- constraint.
simple :: O.Node n t -> FST.Node n t (FST.OFS k)
simple nod = FST.Node
  { FST.treeNode = nod
  , FST.featStr = M.empty
  , FST.nullAdj = False
  }


-- | Create a top-FS.
mkFS :: (Ord a) => [(a, b)] -> M.Map (FST.Loc a) b
mkFS = M.fromList . map (first FST.Top)
