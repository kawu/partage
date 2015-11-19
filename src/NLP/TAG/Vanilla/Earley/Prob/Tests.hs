{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


-- | A module collecting the toy grammars used for testing and
-- unit test examples themselves.
--
-- TODO: Move to `Earley` submodule.


module NLP.TAG.Vanilla.Earley.Prob.Tests
( Test (..)
, TestRes (..)
, mkGram1
, gram1Tests
, mkGram2
, gram2Tests
, mkGram3
, gram3Tests
, mkGram4
, gram4Tests

, Gram
, testTree
)  where


import           Control.Applicative ((<$>), (<*>))
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           Test.Tasty (TestTree, testGroup, withResource)
import           Test.HUnit (Assertion, (@?=))
import           Test.Tasty.HUnit (testCase)

import           NLP.TAG.Vanilla.Tree (Tree (..), AuxTree (..))
import           NLP.TAG.Vanilla.Rule (Rule)
import           NLP.TAG.Vanilla.SubtreeSharing (compile)


---------------------------------------------------------------------
-- Prerequisites
---------------------------------------------------------------------


type Tr    = Tree String String
type AuxTr = AuxTree String String
type Rl    = Rule String String


-- | The compiled grammar.
type Gram  = M.Map Rl Int


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
    , testRes   :: TestRes
    } deriving (Show, Eq, Ord)


-- | The expected test result.  The set of parsed trees can be optionally
-- specified.
data TestRes
    = No
    -- ^ No parse
    | Yes
    -- ^ Parse
    | Trees (S.Set Tr)
    -- ^ Parsing results
    deriving (Show, Eq, Ord)


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


quickly :: AuxTr
quickly = AuxTree (INode "V"
    [ INode "Ad" [FNode "quickly"]
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
mkGram1 = fmap addWeights . compile $
    map Left [tom, sleeps, caught, a, mouse] ++
    map Right [almost, quickly]


---------------------------------------------------------------------
-- Grammar1 Tests
---------------------------------------------------------------------


gram1Tests :: [Test]
gram1Tests =
    -- group 1
    [ Test "S" ["Tom", "sleeps"] . Trees . S.singleton $
        INode "S"
            [ INode "NP"
                [ INode "N"
                    [FNode "Tom"]
                ]
            , INode "VP"
                [INode "V" [FNode "sleeps"]]
            ]
    , Test "S" ["Tom"] No
    , Test "NP" ["Tom"] Yes
    -- group 2
    , Test "S" ["Tom", "almost", "caught", "a", "mouse"] . Trees . S.singleton $
        INode "S"
            [ INode "NP"
                [ INode "N"
                    [ FNode "Tom" ] ]
            , INode "VP"
                [ INode "V"
                    [ INode "Ad"
                        [FNode "almost"]
                    , INode "V"
                        [FNode "caught"]
                    ]
                , INode "NP"
                    [ INode "D"
                        [FNode "a"]
                    , INode "N"
                        [FNode "mouse"]
                    ]
                ]
            ]
    , Test "S" ["Tom", "caught", "almost", "a", "mouse"] No
    , Test "S" ["Tom", "quickly", "almost", "caught", "Tom"] Yes
    , Test "S" ["Tom", "caught", "a", "mouse"] Yes
    , Test "S" ["Tom", "caught", "Tom"] Yes
    , Test "S" ["Tom", "caught", "a", "Tom"] No
    , Test "S" ["Tom", "caught"] No
    , Test "S" ["caught", "a", "mouse"] No ]


---------------------------------------------------------------------
-- Grammar2
---------------------------------------------------------------------


alpha :: Tr
alpha = INode "S"
    [ INode "X"
        [FNode "e"] ]


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
mkGram2 = fmap addWeights . compile $
    map Left [alpha] ++
    map Right [beta1, beta2]


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
    [ Test "S" (words "a b e a b") Yes
    , Test "S" (words "a b e a a") No
    , Test "S" (words "a b a b a b a b e a b a b a b a b") Yes
    , Test "S" (words "a b a b a b a b e a b a b a b a  ") No
    , Test "S" (words "a b e b a") Yes
    , Test "S" (words "b e a") No
    , Test "S" (words "a b a b") No ]


---------------------------------------------------------------------
-- Grammar 3
---------------------------------------------------------------------


mkGram3 :: IO Gram
mkGram3 = fmap addWeights . compile $
    map Left [sent] ++
    map Right [xtree]
  where
    sent = INode "S"
        [ FNode "p"
        , INode "X"
            [FNode "e"]
        , FNode "b" ]
    xtree = AuxTree (INode "X"
        [ FNode "a"
        , INode "X" []
        , FNode "b" ]
        ) [1]


-- | Here we check that the auxiliary tree must be fully
-- recognized before it can be adjoined.
gram3Tests :: [Test]
gram3Tests =
    [ Test "S" (words "p a e b b") Yes
    , Test "S" (words "p a e b") No ]



---------------------------------------------------------------------
-- Grammar 4 (make a cat drink)
---------------------------------------------------------------------


make1 :: Tr
make1 = INode "S"
    [ INode "VP"
        [ INode "V" [FNode "make"]
        , INode "NP" [] ]
    ]


make2 :: Tr
make2 = INode "S"
    [ INode "VP"
        [ INode "V" [FNode "make"]
        , INode "NP" []
        , INode "VP" [] ]
    ]


cat :: Tr
cat = INode "NP"
    [ INode "D" []
    , INode "N"
        [FNode "cat"]
    ]


drink :: Tr
drink = INode "VP"
    [ INode "V"
        [FNode "drink"]
    ]


catDrink :: Tr
catDrink = INode "NP"
    [ INode "D" []
    , INode "N"
        [FNode "cat"]
    , INode "N"
        [FNode "drink"]
    ]


-- | Compile the first grammar.
mkGram4 :: IO Gram
mkGram4 = fmap addWeights . compile $
    map Left
        [ make1, make2, a, cat, mouse, tom
        , drink, catDrink ] ++
    map Right [almost, quickly]


-- | Here we check that the auxiliary tree must be fully
-- recognized before it can be adjoined.
gram4Tests :: [Test]
gram4Tests =
    [ Test "S" ["make", "a", "cat", "drink"] . Trees $ S.fromList
        [ INode "S"
          [ INode "VP"
            [ INode "V" [FNode "make"]
            , INode "NP"
              [ INode "D" [FNode "a"]
              , INode "N" [FNode "cat"] ]
            , INode "VP"
              [ INode "V" [FNode "drink"] ]
            ]
          ]
        , INode "S"
          [ INode "VP"
            [ INode "V" [FNode "make"]
            , INode "NP"
              [ INode "D" [FNode "a"]
              , INode "N" [FNode "cat"]
              , INode "N" [FNode "drink"] ]
            ]
          ]
        ]
    ]


---------------------------------------------------------------------
-- Resources
---------------------------------------------------------------------


-- | Compiled grammars.
data Res = Res
    { gram1 :: Gram
    , gram2 :: Gram
    , gram3 :: Gram
    , gram4 :: Gram }


-- | Construct the shared resource (i.e. the grammars) used in
-- tests.
mkGrams :: IO Res
mkGrams = Res <$> mkGram1 <*> mkGram2 <*> mkGram3 <*> mkGram4


---------------------------------------------------------------------
-- Test Tree
---------------------------------------------------------------------


-- | All the tests of the parsing algorithm.
testTree
    :: String
        -- ^ Name of the tested module
    -> (Gram -> String -> [String] -> IO Bool)
        -- ^ Recognition function
    -> (Gram -> String -> [String] -> IO (M.Map Tr a))
        -- ^ Parsing function (optional)
    -> TestTree
testTree modName reco parse = withResource mkGrams (const $ return ()) $
    \resIO -> testGroup modName $
        map (testIt resIO gram1) gram1Tests ++
        map (testIt resIO gram2) gram2Tests ++
        map (testIt resIO gram3) gram3Tests ++
        map (testIt resIO gram4) gram4Tests
  where
    testIt resIO getGram test = testCase (show test) $ do
        gram <- getGram <$> resIO
        doTest gram test

    doTest gram test@Test{..} = case testRes of
        Trees ts ->
            fmap M.keysSet (parse gram startSym testSent) @@?= ts
        _ ->
            reco gram startSym testSent @@?= simplify testRes
    simplify No         = False
    simplify Yes        = True
    simplify (Trees _)  = True

---------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------


(@@?=) :: (Show a, Eq a) => IO a -> a -> Assertion
mx @@?= y = do
    x <- mx
    x @?= y


-- | Default weights for grammar rules.
addWeights :: Ord a => S.Set a -> M.Map a Int
addWeights s = M.fromList
    [ (x, 1)
    | x <- S.toList s ]
