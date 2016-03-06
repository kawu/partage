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
import qualified NLP.Partage.FactGram.DAG as DAG
-- import qualified NLP.Partage.Earley.Prob.AutoAP as A
-- import qualified NLP.Partage.FactGram as F
    -- (Rule, flattenWithSharing)
-- import qualified NLP.Partage.FactGram.Weighted as W

import qualified TestSet as T


-- | All the tests of the parsing algorithm.
testEarley :: TestTree
testEarley = T.testTree "Earley"
    recFrom Nothing -- (Just parseFrom)
  where
    recFrom gram start input = do
        let dag = DAG.mkGram gram
        E.recognizeFrom dag start (E.fromList input)
--     parseFrom gram start
--         = fmap S.fromList
--         . E.parse (compile gram) start
--         . E.fromList
--     compile = F.flattenWithSharing


-- -- | All the tests of the parsing algorithm.
-- testAStar :: TestTree
-- testAStar = T.testTree "A*"
--     recFrom Nothing
--   where
--     recFrom gram start
--         = A.recognizeFrom memoTerm (map (,1) gram) start
--         . A.fromList
--     memoTerm = Memo.list Memo.char
