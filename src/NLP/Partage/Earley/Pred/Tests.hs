{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


-- | Note: tests here are the same as the tests of the ordinary
-- `Earley` module.


module NLP.TAG.Vanilla.Earley.Pred.Tests where


import           Test.Tasty (TestTree)

import           NLP.TAG.Vanilla.Earley.Pred (recognize')
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.Pred" recognize' Nothing Nothing
