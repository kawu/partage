{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


-- | Note: tests here are the same as the tests of the ordinary
-- `Earley` module.


module NLP.TAG.Vanilla.Earley.Auto.Tests where


import           Control.Applicative ((<$>))
import           Control.Monad (forM_)
import           Test.Tasty (TestTree)

import qualified NLP.TAG.Vanilla.Automaton  as A
import           NLP.TAG.Vanilla.Earley.Auto (recognizeFrom, earley)
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.Auto" recognizeFrom Nothing Nothing


--------------------------------------------------
-- Testing by Hand
--------------------------------------------------


-- | A local test.
localTest :: IO ()
localTest = do
    gram <- snd <$> T.mkGram6
    (_done, auto) <- earley gram
        ["acid", "rains"]

    forM_ (A.edges auto) $ print

--     mapM_ (\r -> R.printRule r >> putStrLn "") (S.toList gram)

--     recognizeFrom gram "S"
--         ["acid", "rains", "in", "rains"]
--     return ()

--     putStrLn ""
--     forM_ (M.toList treeMap) $ \(tree, cost) -> do
--         putStr $ E.showTree' tree
--         putStrLn $ " => " ++ show cost
--         putStrLn ""
