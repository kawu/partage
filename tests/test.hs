import           Test.Tasty (defaultMain, testGroup, localOption)
-- import           Test.Tasty.QuickCheck (QuickCheckTests (..))
-- import           Test.Tasty.SmallCheck (SmallCheckDepth (..))

import qualified NLP.TAG.Vanilla.EarleyBasic.Tests
import qualified NLP.TAG.Vanilla.EarleyPred.Tests
import qualified NLP.TAG.Vanilla.EarleyAuto.Tests
import qualified NLP.TAG.Vanilla.SubtreeSharing.Tests


main :: IO ()
-- main = defaultMain $ opts $ testGroup "Tests"
main = defaultMain $ testGroup "Tests"
    [ NLP.TAG.Vanilla.EarleyBasic.Tests.tests
    , NLP.TAG.Vanilla.EarleyPred.Tests.tests
    , NLP.TAG.Vanilla.EarleyAuto.Tests.tests
    , NLP.TAG.Vanilla.SubtreeSharing.Tests.tests
    ]
--   where
--     opts = localOption (QuickCheckTests 500)
