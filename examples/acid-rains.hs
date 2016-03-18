{-# LANGUAGE TupleSections #-}


import           Control.Monad            (void)
import qualified Data.MemoCombinators     as Memo
import qualified Data.Set                 as S
import qualified Data.Tree                as T

import qualified NLP.Partage.Auto         as A
import qualified NLP.Partage.AStar        as E
import qualified NLP.Partage.Auto.WeiTrie as W
import qualified NLP.Partage.DAG          as DAG
import qualified NLP.Partage.Tree.Other   as O


-- | Memoization for terminals.
memoTerm = Memo.list Memo.char


-- | Some smart constructors.
node x = T.Node (O.NonTerm x)
leaf x = T.Node (O.NonTerm x) []
term x = T.Node (O.Term x) []
foot x = T.Node (O.Foot x) []


-- | A sample TAG grammar.
trees =
  [ node "NP" [node "N" [term "acid"]]
  , node "S"
    [ leaf "NP"
    , node "VP" [node "V" [term "rains"]] ]
  , node "NP"
    [ node "N" [term "acid"]
    , node "N" [term "rains"] ]
  ]


main = do
  let gram = DAG.mkGram (map (,1) trees)
      dag = DAG.dagGram gram
      ruleMap = DAG.factGram gram
      wei = W.fromGram ruleMap
      auto = E.mkAuto gram
      recognize s = E.recognizeFromAuto memoTerm auto s . E.Input
  mapM_
    (\i -> print (i, DAG.label i dag, DAG.value i dag, DAG.edges i dag))
    (S.toList (DAG.nodeSet dag))
  putStrLn "========="
  mapM_ print $ A.allEdges $ A.fromWei wei
  putStrLn "========="
  void $ recognize "S" ["acid", "rains"]
