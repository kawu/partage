{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


module NLP.TAG.Vanilla.Earley.New.Tests where


import           Test.Tasty (TestTree)

import           NLP.TAG.Vanilla.Earley.New (recognizeFrom)
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.New" recognizeFrom Nothing Nothing
