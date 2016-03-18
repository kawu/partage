{-# LANGUAGE TupleSections #-}

import qualified Data.Set                 as S
import qualified Data.Tree                as T
import qualified Data.MemoCombinators     as Memo

import qualified NLP.Partage.AStar        as E
import qualified NLP.Partage.Auto.WeiTrie as W
-- import           NLP.Partage.FactGram   (flattenWithSharing)
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
  [ node "NP" [node "N" [term "Tom"]]
  , node "S"
    [ leaf "NP"
    , node "VP" [node "V" [term "sleeps"]] ]
  , node "S"
    [ leaf "NP"
    , node "VP"
      [ node "V" [term "caught"]
      , leaf "NP" ] ]
  , node "V" [node "Ad" [term "almost"] , foot "V"]
  , node "D" [term "a"]
  , node "NP" [leaf "D", node "N" [term "mouse"]]
  ]


main = do
  let gram = DAG.mkGram (map (,1) trees)
      auto = E.mkAuto gram
      recognize s = E.recognizeFromAuto memoTerm auto s . E.Input
  print =<< recognize "S" ["Tom", "caught", "Tom"]
  print =<< recognize "S" ["Tom", "caught", "a", "Tom"]
  print =<< recognize "S" ["caught", "a", "mouse"]
