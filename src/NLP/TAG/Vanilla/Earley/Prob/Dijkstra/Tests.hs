{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


module NLP.TAG.Vanilla.Earley.Prob.Dijkstra.Tests where


import           Control.Monad (forM_)

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           Test.Tasty (TestTree)

import qualified NLP.TAG.Vanilla.Earley.Prob.Dijkstra as E
import qualified NLP.TAG.Vanilla.Tree as E
-- import qualified NLP.TAG.Vanilla.Earley.Prob.Tests as T
import qualified NLP.TAG.Vanilla.Tests as T
import qualified NLP.TAG.Vanilla.Rule as R
import qualified NLP.TAG.Vanilla.WRule as W


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.Dijkstra"
    -- E.recognize simpleParse E.parse
    recognize
    (Just simpleParse)
    (Just E.parse)
  where
    recognize = E.recognize . weighGram
    simpleParse gram start =
        fmap M.keysSet . E.parse (weighGram gram) start
    weighGram gram = S.fromList
        -- [(rule, 0) | rule <- S.toList gram]
        [W.weighRule 0 rule | rule <- S.toList gram]
--     weighRule R.Rule{..} = W.Rule
--         (weighLab headR)
--         (map weighLab bodyR)
--     weighLab R.NonT{..}    = W.NonT nonTerm labID
--     weighLab (R.Term t)    = W.Term t 0
--     weighLab R.AuxRoot{..} = W.AuxRoot nonTerm
--     weighLab R.AuxFoot{..} = W.AuxFoot nonTerm
--     weighLab R.AuxVert{..} = W.AuxVert nonTerm symID


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


-- -- | A local test.
-- localTest1 :: IO ()
-- localTest1 = do
--     gram <- T.mkGram1
--     treeSet <- E.parse gram "S"
--         (words "Tom almost caught a mouse")
--     putStrLn ""
--     mapM_ (putStrLn . E.showTree') (S.toList treeSet)
--     -- mapM_ (putStrLn . show) (S.toList treeSet)
--
--
-- -- | A local test.
-- localTest2 :: IO ()
-- localTest2 = do
--     gram <- T.mkGram2
--     treeSet <- E.parse gram "S"
--         (words "a b a b e a b a b")
--     putStrLn ""
--     mapM_ (putStrLn . E.showTree') (S.toList treeSet)


-- -- | A local test.
-- localTest3 :: IO ()
-- localTest3 = do
--     gram <- T.mkGram4
--     treeMap <- E.parse gram "S"
--         ["make", "a", "cat", "drink"]
--     putStrLn ""
--     forM_ (M.toList treeMap) $ \(tree, cost) -> do
--         putStr $ E.showTree' tree
--         putStrLn $ " => " ++ show cost
--     -- mapM_ (putStrLn . E.showTree') (S.toList treeSet)
