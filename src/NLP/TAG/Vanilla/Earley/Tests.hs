{-# LANGUAGE OverloadedStrings #-}


module NLP.TAG.Vanilla.Earley.Tests where


import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (void, forM_)
import qualified Control.Monad.State.Strict as E

import qualified Data.IntMap as I
import qualified Data.Set as S
import           Data.List (sortBy)
import           Data.Ord (comparing)
import qualified Pipes as P
import qualified Pipes.Prelude as P

import           Test.Tasty (TestTree, testGroup) -- , localOptions)
import           Test.HUnit (Assertion, (@?=))
import           Test.Tasty.HUnit (testCase)

import           NLP.TAG.Vanilla.Tree
import           NLP.TAG.Vanilla.Rule
import           NLP.TAG.Vanilla.Earley


---------------------------------------------------------------------
-- Grammar1
---------------------------------------------------------------------


type Tr = Tree String String
type AuxTr = AuxTree String String
type Rl = Rule String String


tom :: Tr
tom = INode "NP"
    [ INode "N"
        [FNode "Tom"]
    ]


sleeps :: Tr
sleeps = INode "S"
    [ INode "NP" []
    , INode "VP"
        [INode "V" [FNode "sleeps"]]
    ]


caught :: Tr
caught = INode "S"
    [ INode "NP" []
    , INode "VP"
        [ INode "V" [FNode "caught"]
        , INode "NP" [] ]
    ]


almost :: AuxTr
almost = AuxTree (INode "V"
    [ INode "Ad" [FNode "almost"]
    , INode "V" []
    ]) [1]


a :: Tr
a = INode "D" [FNode "a"]


mouse :: Tr
mouse = INode "NP"
    [ INode "D" []
    , INode "N"
        [FNode "mouse"]
    ]


mkGram1 :: IO (S.Set Rl)
mkGram1 = S.fromList <$> compile
    [tom, sleeps, caught, a, mouse]
    [almost]


-- testGram :: [String] -> IO ()
-- testGram sent = do
--     rs <- flip E.evalStateT 0 $ P.toListM $ do
--         mapM_ (treeRules True) [tom, sleeps, caught, a, mouse]
--         -- mapM_ (treeRules True) [tom, caught]
--         mapM_ (auxRules True) [almost]
--     void $ earley (S.fromList rs) sent
--     -- forM_ rs $ \r -> printRule r >> putStrLn ""
--     -- return ()


---------------------------------------------------------------------
-- Tests
---------------------------------------------------------------------


tests :: TestTree
tests = testGroup "NLP.TAG.Vanilla.Early"
    [ testCase "Tom sleeps" testTom1 ]


testTom1 :: Assertion
testTom1 = do
    gram <- mkGram1
    recognizeFrom gram "S" ["Tom", "sleeps"]    @@?= True
    recognizeFrom gram "S" ["Tom"]              @@?= False
    recognize     gram     ["Tom"]              @@?= True


---------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------


(@@?=) :: (Show a, Eq a) => IO a -> a -> Assertion
mx @@?= y = do
    x <- mx
    x @?= y
