{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


module NLP.TAG.Vanilla.EarleyBasic.Tests where


import           Test.Tasty (TestTree)

import           NLP.TAG.Vanilla.EarleyBasic (recognizeFrom)
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.EarleyBasic" recognizeFrom
