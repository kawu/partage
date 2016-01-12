{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}


-- | The module collects the sample grammars used for testing and
-- unit test examples themselves.


module TestSet
( Test (..)
, TestRes (..)
, mkGram1
, gram1Tests
, mkGram2
, gram2Tests
, mkGram3
, gram3Tests

, Gram
, testTree
)  where


import           Control.Applicative ((<$>), (<*>))

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           Test.Tasty (TestTree, testGroup, withResource)
import           Test.HUnit (Assertion, (@?=))
import           Test.Tasty.HUnit (testCase)

-- import           NLP.TAG.Vanilla.Core (Cost)
import           NLP.TAG.Vanilla.Tree (Tree (..), AuxTree (..))
import           NLP.TAG.Vanilla.Rule (Rule)
import qualified NLP.TAG.Vanilla.Rule  as R
-- import qualified NLP.TAG.Vanilla.WRule as W
import           NLP.TAG.Vanilla.SubtreeSharing (compile)


---------------------------------------------------------------------
-- Prerequisites
---------------------------------------------------------------------


type Tr    = Tree String String
type AuxTr = AuxTree String String
type Rl    = Rule String String
-- type WRl   = W.Rule String String


-- | A compiled grammar.
type Gram  = S.Set Rl

-- -- | A compiled grammar with weights.
-- type WeightedTree  = (Tr, Cost)
-- type WeightedAux   = (AuxTr, Cost)
-- type WeightedGram  = S.Set WRl


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
--     -- ^ Parsing results
--     | WeightedTrees (M.Map Tr Cost)
--     -- ^ Parsing results with weights
    deriving (Show, Eq, Ord)


---------------------------------------------------------------------
-- Grammar1
---------------------------------------------------------------------


tom :: Tr
tom = Branch "NP"
    [ Branch "N"
        [Leaf "Tom"]
    ]


sleeps :: Tr
sleeps = Branch "S"
    [ Branch "NP" []
    , Branch "VP"
        [Branch "V" [Leaf "sleeps"]]
    ]


caught :: Tr
caught = Branch "S"
    [ Branch "NP" []
    , Branch "VP"
        [ Branch "V" [Leaf "caught"]
        , Branch "NP" [] ]
    ]


almost :: AuxTr
almost = AuxTree (Branch "V"
    [ Branch "Ad" [Leaf "almost"]
    , Branch "V" []
    ]) [1]


quickly :: AuxTr
quickly = AuxTree (Branch "V"
    [ Branch "Ad" [Leaf "quickly"]
    , Branch "V" []
    ]) [1]


a :: Tr
a = Branch "D" [Leaf "a"]


mouse :: Tr
mouse = Branch "NP"
    [ Branch "D" []
    , Branch "N"
        [Leaf "mouse"]
    ]


-- | Compile the first grammar.
mkGram1 :: IO Gram
mkGram1 = compile $
    map Left [tom, sleeps, caught, a, mouse] ++
    map Right [almost, quickly]


---------------------------------------------------------------------
-- Grammar1 Tests
---------------------------------------------------------------------


gram1Tests :: [Test]
gram1Tests =
    -- group 1
    [ Test "S" ["Tom", "sleeps"] . Trees . S.singleton $
        Branch "S"
            [ Branch "NP"
                [ Branch "N"
                    [Leaf "Tom"]
                ]
            , Branch "VP"
                [Branch "V" [Leaf "sleeps"]]
            ]
    , Test "S" ["Tom"] No
    , Test "NP" ["Tom"] Yes
    -- group 2
    , Test "S" ["Tom", "almost", "caught", "a", "mouse"] . Trees . S.singleton $
        Branch "S"
            [ Branch "NP"
                [ Branch "N"
                    [ Leaf "Tom" ] ]
            , Branch "VP"
                [ Branch "V"
                    [ Branch "Ad"
                        [Leaf "almost"]
                    , Branch "V"
                        [Leaf "caught"]
                    ]
                , Branch "NP"
                    [ Branch "D"
                        [Leaf "a"]
                    , Branch "N"
                        [Leaf "mouse"]
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
alpha = Branch "S"
    [ Branch "X"
        [Leaf "e"] ]


beta1 :: AuxTr
beta1 = AuxTree (Branch "X"
    [ Leaf "a"
    , Branch "X"
        [ Branch "X" []
        , Leaf "a" ] ]
    ) [1,0]


beta2 :: AuxTr
beta2 = AuxTree (Branch "X"
    [ Leaf "b"
    , Branch "X"
        [ Branch "X" []
        , Leaf "b" ] ]
    ) [1,0]


mkGram2 :: IO Gram
mkGram2 = compile $
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
mkGram3 = compile $
    map Left [sent] ++
    map Right [xtree]
  where
    sent = Branch "S"
        [ Leaf "p"
        , Branch "X"
            [Leaf "e"]
        , Leaf "b" ]
    xtree = AuxTree (Branch "X"
        [ Leaf "a"
        , Branch "X" []
        , Leaf "b" ]
        ) [1]


-- | Here we check that the auxiliary tree must be fully
-- recognized before it can be adjoined.
gram3Tests :: [Test]
gram3Tests =
    [ Test "S" (words "p a e b b") Yes
    , Test "S" (words "p a e b") No ]


---------------------------------------------------------------------
-- Resources
---------------------------------------------------------------------


-- | Compiled grammars.
data Res = Res
    { gram1 :: Gram
    , gram2 :: Gram
    , gram3 :: Gram }


-- | Construct the shared resource (i.e. the grammars) used in
-- tests.
mkGrams :: IO Res
mkGrams = Res <$> mkGram1 <*> mkGram2 <*> mkGram3


---------------------------------------------------------------------
-- Test Tree
---------------------------------------------------------------------


-- | All the tests of the parsing algorithm.
testTree
    :: String
        -- ^ Name of the tested module
    -> (Gram -> String -> [String] -> IO Bool)
        -- ^ Recognition function
    -> Maybe (Gram -> String -> [String] -> IO (S.Set Tr))
        -- ^ Parsing function (optional)
    -> TestTree
testTree modName reco parse = withResource mkGrams (const $ return ()) $
    \resIO -> testGroup modName $
        map (testIt resIO gram1) gram1Tests ++
        map (testIt resIO gram2) gram2Tests ++
        map (testIt resIO gram3) gram3Tests
  where
    testIt resIO getGram test = testCase (show test) $ do
        gram <- getGram <$> resIO
        doTest gram test

    doTest gram test@Test{..} = case (parse, testRes) of
        (Nothing, _) ->
            reco gram startSym testSent @@?= simplify testRes
        (Just pa, Trees ts) ->
            pa gram startSym testSent @@?= ts
        _ ->
            reco gram startSym testSent @@?= simplify testRes

    simplify No         = False
    simplify Yes        = True
    simplify (Trees _)  = True
--     simplify (WeightedTrees _)
--                         = True

---------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------


(@@?=) :: (Show a, Eq a) => IO a -> a -> Assertion
mx @@?= y = do
    x <- mx
    x @?= y
