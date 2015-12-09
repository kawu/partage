{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


module NLP.TAG.Vanilla.Earley.Basic.Tests where


import qualified Data.Set as S

import           Test.Tasty (TestTree)

import qualified NLP.TAG.Vanilla.Rule as R
import           NLP.TAG.Vanilla.Earley.Basic (recognizeFrom)
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.Basic" recognizeFrom Nothing Nothing


--------------------------------------------------
-- Testing by Hand
--------------------------------------------------


-- | A local test.
localTest :: IO ()
localTest = do
    gram <- T.mkGramSetPoints

    mapM_ (\r -> R.printRule r >> putStrLn "") (S.toList gram)

--     recognizeFrom gram "S"
--         -- ["acid", "rains", "in", "Ghana"]
--         ["acid", "rains"]
--     return ()

--     putStrLn ""
--     forM_ (M.toList treeMap) $ \(tree, cost) -> do
--         putStr $ E.showTree' tree
--         putStrLn $ " => " ++ show cost
--         putStrLn ""
