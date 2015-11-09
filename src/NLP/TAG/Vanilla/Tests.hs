{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


-- | A module collecting the toy grammars used for testing and
-- unit test examples themselves.


module NLP.TAG.Vanilla.Tests
( Test (..)
, mkGram1
, gram1Tests
, mkGram2
, gram2Tests

, Gram
, testTree
)  where


import           Control.Applicative ((<$>), (<*>))
import qualified Data.Set as S

import           Test.Tasty (TestTree, testGroup, withResource)
import           Test.HUnit (Assertion, (@?=))
import           Test.Tasty.HUnit (testCase)

import           NLP.TAG.Vanilla.Tree (Tree (..), AuxTree (..))
import           NLP.TAG.Vanilla.Rule (Rule)
import           NLP.TAG.Vanilla.SubtreeSharing (compile)


---------------------------------------------------------------------
-- Prerequisites
---------------------------------------------------------------------


type Tr = Tree String String
type AuxTr = AuxTree String String
type Rl = Rule String String


-- | The compiled grammar.
type Gram = S.Set Rl


---------------------------------------------------------------------
-- Tests
---------------------------------------------------------------------


-- | A single test case.
data Test = Test {
    -- | Starting symbol
      startSym  :: String
    -- | The sentence to parse (list of words)
    , testSent  :: [String]
    -- | The expected recognition result
    , testRes   :: Bool
    } deriving (Show, Eq, Ord)


---------------------------------------------------------------------
-- Grammar1
---------------------------------------------------------------------


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


-- | Compile the first grammar.
mkGram1 :: IO Gram
mkGram1 = compile $
    (map Left [tom, sleeps, caught, a, mouse]) ++
    (map Right [almost])


---------------------------------------------------------------------
-- Grammar1 Tests
---------------------------------------------------------------------


gram1Tests :: [Test]
gram1Tests =
    -- group 1
    [ Test "S" ["Tom", "sleeps"] True
    , Test "S" ["Tom"] False
    , Test "NP" ["Tom"] True
    -- group 2
    , Test "S" ["Tom", "almost", "caught", "a", "mouse"] True
    , Test "S" ["Tom", "caught", "almost", "a", "mouse"] False
    , Test "S" ["Tom", "caught", "a", "mouse"] True
    , Test "S" ["Tom", "caught", "Tom"] True
    , Test "S" ["Tom", "caught", "a", "Tom"] False
    , Test "S" ["Tom", "caught"] False
    , Test "S" ["caught", "a", "mouse"] False ]


---------------------------------------------------------------------
-- Grammar2
---------------------------------------------------------------------


alpha :: Tr
alpha = INode "S"
    [ FNode "p"
    , INode "X"
        [FNode "e"]
    , FNode "q" ]


beta1 :: AuxTr
beta1 = AuxTree (INode "X"
    [ FNode "a"
    , INode "X"
        [ INode "X" []
        , FNode "a" ] ]
    ) [1,0]


beta2 :: AuxTr
beta2 = AuxTree (INode "X"
    [ FNode "b"
    , INode "X"
        [ INode "X" []
        , FNode "b" ] ]
    ) [1,0]


mkGram2 :: IO Gram
mkGram2 = compile $
    (map Left [alpha]) ++
    (map Right [beta1, beta2])


---------------------------------------------------------------------
-- Grammar2 Tests
---------------------------------------------------------------------


-- | What we test is not really a copy language but rather a
-- language in which there is always the same number of `a`s and
-- `b`s on the left and on the right of the empty `e` symbol.
-- To model the real copy language with a TAG we would need to
-- use either adjunction constraints or feature structures.
gram2Tests :: [Test]
gram2Tests =
    [ Test "S" (words "p a b e a b q") True
    , Test "S" (words "p a b e a a q") False
    , Test "S" (words "p a b a b a b a b e a b a b a b a b q") True
    , Test "S" (words "p a b a b a b a b e a b a b a b a   q") False
    , Test "S" (words "p a b e b a q") True ]


---------------------------------------------------------------------
-- Resources
---------------------------------------------------------------------


-- | Compiled grammars.
data Res = Res
    { gram1 :: Gram
    , gram2 :: Gram }


-- | Construct the shared resource (i.e. the grammars) used in
-- tests.
mkGrams :: IO Res 
mkGrams = Res <$> mkGram1 <*> mkGram2


---------------------------------------------------------------------
-- Test Tree
---------------------------------------------------------------------


-- | All the tests of the parsing algorithm.
testTree
    :: String
        -- ^ Name of the tested module
    -> (Gram -> String -> [String] -> IO Bool)
        -- ^ Recognition function
    -> TestTree
testTree modName reco = withResource mkGrams (const $ return ()) $
    \resIO -> testGroup modName $
        -- testGroup "NLP.TAG.Vanilla.EarleyPred" $
        map (testIt resIO gram1) gram1Tests ++
        map (testIt resIO gram2) gram2Tests
  where
    testIt resIO getGram test@Test{..} = testCase (show test) $ do
        gram <- getGram <$> resIO
        -- recognize' gram startSym testSent @@?= testRes
        reco gram startSym testSent @@?= testRes


-- -- | Run the given test on the given grammar.
-- testIt
--     :: IO Res           -- ^ Grammar acquisition
--     -> (Res -> Gram)  -- ^ Grammar selection
--     -> Test           -- ^ The test to run
--     -> TestTree


---------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------


(@@?=) :: (Show a, Eq a) => IO a -> a -> Assertion
mx @@?= y = do
    x <- mx
    x @?= y
