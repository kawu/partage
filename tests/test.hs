import           Test.Tasty (defaultMain, testGroup, localOption)
-- import           Test.Tasty.QuickCheck (QuickCheckTests (..))
-- import           Test.Tasty.SmallCheck (SmallCheckDepth (..))

import qualified NLP.TAG.Vanilla.Earley.Tests


main :: IO ()
-- main = defaultMain $ opts $ testGroup "Tests"
main = defaultMain $ testGroup "Tests"
    [ NLP.TAG.Vanilla.Earley.Tests.tests
    ]
--   where
--     opts = localOption (QuickCheckTests 500)
