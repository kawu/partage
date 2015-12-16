{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


-- | Note: tests here are the same as the tests of the ordinary
-- `Earley` module.


module NLP.TAG.Vanilla.Earley.AutoAP.Tests where


import           Control.Applicative ((<$>))
import           Control.Monad (forM_)
import           Test.Tasty (TestTree)
import qualified Data.Set as S

import qualified NLP.TAG.Vanilla.Rule as R
import qualified NLP.TAG.Vanilla.Auto.DAWG  as A
import qualified NLP.TAG.Vanilla.Earley.AutoAP as E
import qualified NLP.TAG.Vanilla.Tree as E
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.AutoAP" E.recognizeFrom Nothing Nothing


--------------------------------------------------
-- Testing by Hand
--------------------------------------------------


-- | A local test.
localTest :: IO ()
localTest = do
    gram <- T.mkGramSetPoints

--     mapM_ (\r -> R.printRule r >> putStrLn "") (S.toList gram)

    treeSet <- E.parse gram "NP" ["set", "points"]
    putStrLn "\n## TREES ##\n"
    forM_ (S.toList treeSet) $ \tree -> do
        putStr $ E.showTree' tree ++ "\n"
