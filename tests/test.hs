import           Test.Tasty (defaultMain, testGroup, localOption)
-- import           Test.Tasty.QuickCheck (QuickCheckTests (..))
-- import           Test.Tasty.SmallCheck (SmallCheckDepth (..))

import           TestSet
import qualified Parser
-- import qualified NLP.TAG.Vanilla.Earley.Basic.Tests
-- import qualified NLP.TAG.Vanilla.Earley.Pred.Tests
-- import qualified NLP.TAG.Vanilla.Earley.Auto.Tests
-- import qualified NLP.TAG.Vanilla.Earley.AutoAP.Tests
-- import qualified NLP.TAG.Vanilla.SubtreeSharing.Tests
-- import qualified NLP.TAG.Vanilla.Earley.TreeGen.Tests
-- import qualified NLP.TAG.Vanilla.Earley.Prob.SymInf.Tests
-- import qualified NLP.TAG.Vanilla.Earley.Prob.Dijkstra.Tests
-- import qualified NLP.TAG.Vanilla.Earley.Prob.AStar.Tests
-- import qualified NLP.TAG.Vanilla.Earley.New.Tests


main :: IO ()
-- main = defaultMain $ opts $ testGroup "Tests"
main = defaultMain $ testGroup "Tests"
    [ Parser.tests
--     , NLP.TAG.Vanilla.Earley.Pred.Tests.tests
--     , NLP.TAG.Vanilla.Earley.Auto.Tests.tests
--     , NLP.TAG.Vanilla.Earley.AutoAP.Tests.tests
--     , NLP.TAG.Vanilla.SubtreeSharing.Tests.tests
--     , NLP.TAG.Vanilla.Earley.TreeGen.Tests.tests
--     , NLP.TAG.Vanilla.Earley.Prob.SymInf.Tests.tests
--     , NLP.TAG.Vanilla.Earley.Prob.Dijkstra.Tests.tests
--     , NLP.TAG.Vanilla.Earley.Prob.AStar.Tests.tests
--     , NLP.TAG.Vanilla.Earley.New.Tests.tests
    ]
--   where
--     opts = localOption (QuickCheckTests 500)
