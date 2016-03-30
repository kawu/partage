{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}


-- | Testing the automata-based Earley-style TAG parser.


module Parser where


import           Control.Applicative ((<$>))
import           Control.Monad (forM_)
import           Test.Tasty (TestTree)

import qualified Data.Set as S
import qualified Data.MemoCombinators as Memo

import qualified NLP.Partage.Earley as E
import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.DAG as DAG
import qualified NLP.Partage.AStar as A

import qualified TestSet as T


-- | All the tests of the parsing algorithm.
testEarley :: TestTree
testEarley = T.testTree "Earley"
    recFrom (Just parseFrom)
  where
    recFrom gram start input = do
        let dag = mkGram gram
        E.recognizeFrom dag start (E.fromList input)
    parseFrom gram start input = do
        let dag = mkGram gram
        fmap S.fromList
            . E.parse dag start
            . E.fromList
            $ input
    mkGram = DAG.mkGram . map mkTree
    mkTree (t, w) = (O.encode t, w)


-- | All the tests of the parsing algorithm.
testAStar :: TestTree
testAStar = T.testTree "A*"
    recFrom Nothing
  where
    recFrom gram start
        = A.recognizeFrom memoTerm (map mkTree gram) start
        . A.fromList
    memoTerm = Memo.list Memo.char
    mkTree (t, w) = (O.encode t, w)
