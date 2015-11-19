{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


-- | Note: tests here are the same as the tests of the ordinary
-- `Earley` module.
--
-- TODO: Move the test grammar to a common module.


module NLP.TAG.Vanilla.Earley.Auto.Tests where


import           Test.Tasty (TestTree)

import           NLP.TAG.Vanilla.Earley.Auto (recognizeFrom)
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.Auto" recognizeFrom Nothing
