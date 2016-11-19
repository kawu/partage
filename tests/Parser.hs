{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}


-- | Testing the automata-based Earley-style TAG parser.


module Parser where


import           Control.Applicative     ((<$>))
import           Control.Monad           (forM_, void)
import           Test.Tasty              (TestTree)

import qualified Data.MemoCombinators    as Memo
import qualified Data.Set                as S

import qualified Pipes                   as P

-- import qualified NLP.Partage.AStar       as A
-- import qualified NLP.Partage.AStar.Deriv as D
import qualified NLP.Partage.DAG         as DAG
import qualified NLP.Partage.Earley      as E
import qualified NLP.Partage.Tree.Other  as O

import qualified TestSet                 as T


-- | All the tests of the parsing algorithm.
testEarley :: TestTree
testEarley =
  T.testTree "Earley" parser
  where
    parser = T.dummyParser
      { T.recognize = Just recFrom
      , T.parsedTrees = Just parseFrom }
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
    -- mkGram = DAG.mkDummy . map mkTree
    -- <- dummy DAG cannot work with the current implementation of the Earley parser;
    --    the Earley parser assumes e.g. that there is at most one node with a given
    --    terminal, which is not true in dummy DAG.
    mkTree (t, w) = (O.encode t, w)


-- -- | All the tests of the parsing algorithm.
-- testAStar :: TestTree
-- testAStar =
--   T.testTree "A*" parser
--   where
--     parser = T.dummyParser
--       { T.recognize = Just recFrom
--       , T.parsedTrees = Just parseFrom
--       , T.derivTrees = Just derivFrom
--       , T.encodes    = Just encodesFrom
--       , T.derivPipe  = Just derivPipe }
--     recFrom gram start
--       = A.recognizeFrom memoTerm (map mkTree gram) start
--       . A.fromList
--     parseFrom gram start input = do
--       let dag = mkGram gram
--           auto = A.mkAuto memoTerm dag
--           onTerm f (O.Term x) = O.Term (f x)
--           onTerm _ (O.NonTerm x) = O.NonTerm x
--           onTerm _ (O.Foot x) = O.Foot x
--       hype <- A.earleyAuto auto (A.fromList input)
--       return
--         . S.fromList
--         -- below we just map (Tok t -> t) but we have to also
--         -- do the corresponding encoding/decoding
--         . map (O.mkTree . fmap (onTerm A.terminal) . O.unTree)
--         $ A.parsedTrees hype start (length input)
--     derivFrom gram start input = do
--       let dag = mkGram gram
--           auto = A.mkAuto memoTerm dag
--       hype <- A.earleyAuto auto (A.fromList input)
--       return $ D.derivTrees hype start (length input)
--     encodesFrom hype start input = D.encodes hype start (length input)
--     derivPipe gram start sent =
--       let dag = mkGram gram
--           auto = A.mkAuto memoTerm dag
--           input = A.fromList sent
--           conf = D.DerivR
--             { D.startSym = start
--             , D.sentLen = length sent }
--       in  A.earleyAutoP auto input P.>-> D.derivsPipe conf
--
--     mkGram = DAG.mkGram . map mkTree
--     memoTerm = Memo.list Memo.char
--     mkTree (t, w) = (O.encode t, w)
