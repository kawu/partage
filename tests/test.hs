import           Test.Tasty (defaultMain, testGroup, localOption)
-- import           Test.Tasty.QuickCheck (QuickCheckTests (..))
-- import           Test.Tasty.SmallCheck (SmallCheckDepth (..))

import qualified NLP.TAG.Vanilla.Earley.Basic.Tests
import qualified NLP.TAG.Vanilla.Earley.Pred.Tests
import qualified NLP.TAG.Vanilla.Earley.Auto.Tests
import qualified NLP.TAG.Vanilla.Earley.AutoAP.Tests
import qualified NLP.TAG.Vanilla.SubtreeSharing.Tests


main :: IO ()
-- main = defaultMain $ opts $ testGroup "Tests"
main = defaultMain $ testGroup "Tests"
    [ NLP.TAG.Vanilla.Earley.Basic.Tests.tests
    , NLP.TAG.Vanilla.Earley.Pred.Tests.tests
    , NLP.TAG.Vanilla.Earley.Auto.Tests.tests
    , NLP.TAG.Vanilla.Earley.AutoAP.Tests.tests
    , NLP.TAG.Vanilla.SubtreeSharing.Tests.tests
    ]
--   where
--     opts = localOption (QuickCheckTests 500)
