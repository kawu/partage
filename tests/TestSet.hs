{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}


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

-- , Gram
, TagParser (..)
, dummyParser
, testTree
)  where


import           Control.Applicative       ((<$>), (<*>))
import           Control.Arrow             (first)
-- import           Control.Monad.Morph       as Morph
import           Control.Monad.Trans.Class (lift)

import           Data.IORef
import qualified Data.Map.Strict           as M
import qualified Data.Set                  as S

import           Test.HUnit                (Assertion, (@?=))
import           Test.Tasty                (TestTree, testGroup, withResource)
import           Test.Tasty.HUnit          (testCase)

import qualified Pipes                     as P

import qualified NLP.Partage.AStar.Deriv   as Deriv
import           NLP.Partage.DAG           (Weight)
import           NLP.Partage.Tree          (AuxTree (..), Tree (..))
import qualified NLP.Partage.Tree.Other    as O


---------------------------------------------------------------------
-- Prerequisites
---------------------------------------------------------------------


type Tr    = Tree String String
type AuxTr = AuxTree String String
type Other = O.SomeTree String String
type Deriv = Deriv.Deriv String String
type ModifDerivs = Deriv.ModifDerivs String String
-- type Rl    = Rule String String
-- type WRl   = W.Rule String String


-- | A compiled grammar.
-- type Gram  = S.Set Rl

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
      startSym :: String
    -- | The sentence to parse (list of words)
    , testSent :: [String]
    -- | The expected recognition result
    , testRes  :: TestRes
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
mkGram1 :: [(Other, Weight)]
mkGram1 = map (,1) $
    map Left [tom, sleeps, caught, a, mouse] ++
    map Right [almost, quickly]


---------------------------------------------------------------------
-- Grammar1 Tests
---------------------------------------------------------------------


gram1Tests :: [Test]
gram1Tests =
    -- group 1
--     [ Test "S" ["Tom", "sleeps"] Yes ]
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


mkGram2 :: [(Other, Weight)]
mkGram2 = map (,1) $
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


mkGram3 :: [(Other, Weight)]
mkGram3 = map (,1) $
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
-- Grammar 4
---------------------------------------------------------------------


mkGram4 :: [(Other, Weight)]
mkGram4 =
    map (first Left) [(ztree, 1), (stree, 10)] ++
    map (first Right) [(atree, 5)]
  where
    stree = Branch "S"
        [ Branch "A"
          [ Branch "B"
            [Leaf "a"] ] ]
    ztree = Branch "Z"
        [ Branch "Z" []
        , Branch "A"
            [Leaf "a"] ]
    atree = AuxTree (Branch "A"
        [ Leaf "x"
        , Branch "A" []
        , Leaf "y" ]
        ) [1]


-- | The purpose of this test is to test the inversed root adjoin
-- inference operation.
gram4Tests :: [Test]
gram4Tests =
    [ Test "S" (words "x a y") Yes ]


---------------------------------------------------------------------
-- Resources
---------------------------------------------------------------------


-- | Compiled grammars.
data Res = Res
    { gram1 :: [(Other, Weight)]
    , gram2 :: [(Other, Weight)]
    , gram3 :: [(Other, Weight)]
    , gram4 :: [(Other, Weight)] }


-- | Construct the shared resource (i.e. the grammars) used in
-- tests.
-- mkGrams :: IO Res
mkGrams :: Res
mkGrams =
    Res mkGram1 mkGram2 mkGram3 mkGram4


---------------------------------------------------------------------
-- Test Tree
---------------------------------------------------------------------


-- | An abstract TAG parser.
data TagParser = TagParser
  { recognize   :: Maybe ([(Other, Weight)] -> String -> [String] -> IO Bool)
    -- ^ Recognition function
  , parsedTrees :: Maybe ([(Other, Weight)] -> String -> [String] -> IO (S.Set Tr))
    -- ^ Function which retrieves derived trees
  , derivTrees :: Maybe ([(Other, Weight)] -> String -> [String] -> IO [Deriv])
    -- ^ Function which retrieves derivation trees; the result is a set of
    -- derivations but it takes the form of a list so that derivations can be
    -- generated gradually; the property that the result is actually a set
    -- should be verified separately.
  , derivPipe :: Maybe
    ( [(Other, Weight)] -> String -> [String] ->
      (P.Producer ModifDerivs IO ())
    )
    -- ^ A pipe (producer) which generates derivations on-the-fly
  }


-- | Dummy parser which doesn't provide anything.
dummyParser :: TagParser
dummyParser = TagParser Nothing Nothing Nothing Nothing


-- | All the tests of the parsing algorithm.
testTree
  :: String
        -- ^ Name of the tested module
--     -> ([(Other, Weight)] -> String -> [String] -> IO Bool)
--         -- ^ Recognition function
--     -> Maybe ([(Other, Weight)] -> String -> [String] -> IO (S.Set Tr))
--         -- ^ Parsing function (optional)
  -> TagParser
  -> TestTree
-- testTree modName reco parse =
testTree modName TagParser{..} =
  withResource (return mkGrams) (const $ return ()) $
    \resIO -> testGroup modName $
        map (testIt resIO gram1) gram1Tests ++
        map (testIt resIO gram2) gram2Tests ++
        map (testIt resIO gram3) gram3Tests ++
        map (testIt resIO gram4) gram4Tests
  where
    testIt resIO getGram test = testCase (show test) $ do
        gram <- getGram <$> resIO
        testRecognition gram test
        testParsing gram test
        testDerivsIsSet gram test
        testFlyingDerivsIsSet gram test
        testDerivsEqual gram test

    -- Check if the recognition result is as expected
    testRecognition gram Test{..} = case recognize of
      Just reco -> reco gram startSym testSent @@?= simplify testRes
      _ -> return ()

    -- Check if the set of parsed trees is as expected
    testParsing gram Test{..} = case (parsedTrees, testRes) of
        (Just pa, Trees ts) -> pa gram startSym testSent @@?= ts
        _ -> return ()

    -- Here we only check (for the moment) if the list of derivations
    -- is actually a set
    testDerivsIsSet gram Test{..} = case derivTrees of
        Just derivs -> do
          ds <- derivs gram startSym testSent
          length ds @?= length (nub ds)
        _ -> return ()

    -- Like `testDerivsIsSet` but for on-the-fly generated derivations
    testFlyingDerivsIsSet gram Test{..} = case derivPipe of
        Just mkPipe -> do
          derivsRef <- newIORef []
          let pipe = mkPipe gram startSym testSent
          P.runEffect . P.for pipe $ \(_modif, derivs) -> do
            lift $ modifyIORef' derivsRef (++ derivs)
          ds <- readIORef derivsRef
          length ds @?= length (nub ds)
        _ -> return ()

    -- Test if `testDerivsIsSet` and `testFlyingDerivsIsSet`
    -- give equal results
    testDerivsEqual gram Test{..} = case (derivTrees, derivPipe) of
      (Just derivs, Just mkPipe) -> do
        derivsRef <- newIORef []
        let pipe = mkPipe gram startSym testSent
        P.runEffect . P.for pipe $ \(_modif, modifDerivs) -> do
          lift $ modifyIORef' derivsRef (++ modifDerivs)
        ds1 <- readIORef derivsRef
        ds2 <- derivs gram startSym testSent
        S.fromList ds1 @?= S.fromList ds2
      _ -> return ()

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


-- | Remove duplicates (not stable).
nub :: Ord a => [a] -> [a]
nub = S.toList . S.fromList
