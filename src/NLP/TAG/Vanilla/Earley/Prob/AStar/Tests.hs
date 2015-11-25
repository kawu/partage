{-# LANGUAGE OverloadedStrings #-}


module NLP.TAG.Vanilla.Earley.Prob.AStar.Tests where


import           Control.Monad (forM_)

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           Test.Tasty (TestTree)

import qualified NLP.TAG.Vanilla.Earley.Prob.AStar as E
import qualified NLP.TAG.Vanilla.Tree as E
import qualified NLP.TAG.Vanilla.Tests as T
import qualified NLP.TAG.Vanilla.Rule as R
import qualified NLP.TAG.Vanilla.WRule as W


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.AStar"
    -- E.recognize simpleParse E.parse
    recognize
    (Just simpleParse)
    (Just E.parse)
  where
    recognize = E.recognize . weighGram
    simpleParse gram start =
        fmap M.keysSet . E.parse (weighGram gram) start
    weighGram gram = S.fromList
        [W.weighRule 0 rule | rule <- S.toList gram]


--------------------------------------------------
-- Testing by Hand
--------------------------------------------------


-- | A local test.
localTest :: IO ()
localTest = do
    gram <- T.mkGram4
    treeMap <- E.parse gram "S"
        ["almost", "make", "a", "cat", "drink"]
    putStrLn ""
    forM_ (M.toList treeMap) $ \(tree, cost) -> do
        putStr $ E.showTree' tree
        putStrLn $ " => " ++ show cost

