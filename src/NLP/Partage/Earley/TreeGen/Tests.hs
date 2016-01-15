{-# LANGUAGE OverloadedStrings #-}


module NLP.TAG.Vanilla.Earley.TreeGen.Tests where


import qualified Data.Set as S

import           Test.Tasty (TestTree)

import qualified NLP.TAG.Vanilla.Earley.TreeGen as E
import qualified NLP.TAG.Vanilla.Tree as E
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.TreeGen"
    E.recognize (Just E.parse) Nothing


--------------------------------------------------
-- Testing by Hand
--------------------------------------------------


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
-- 
-- 
-- -- | A local test.
-- localTest3 :: IO ()
-- localTest3 = do
--     gram <- T.mkGram4
--     treeSet <- E.parse gram "S"
--         ["make", "a", "cat", "drink"]
--     putStrLn ""
--     mapM_ (putStrLn . E.showTree') (S.toList treeSet)
