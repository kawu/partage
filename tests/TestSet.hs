{-# LANGUAGE CPP               #-}
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
import           Control.Monad             (forM_, guard, void)
-- import           Control.Monad.Morph       as Morph
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (..))

import           Data.IORef
import qualified Data.Map.Strict           as M
import qualified Data.Set                  as S
import qualified Data.Tree                 as R

import           Test.HUnit                (Assertion, (@?=))
import           Test.Tasty                (TestTree, testGroup, withResource)
import           Test.Tasty.HUnit          (testCase)

import qualified Pipes                     as P

-- import           NLP.Partage.AStar         (Tok)
-- import qualified NLP.Partage.AStar         as AStar
-- import qualified NLP.Partage.AStar.Deriv   as Deriv
import           NLP.Partage.DAG           (Weight)
import           NLP.Partage.Tree          (AuxTree (..), Tree (..))
import qualified NLP.Partage.Tree.Other    as O


---------------------------------------------------------------------
-- Prerequisites
---------------------------------------------------------------------


type Tr    = Tree String String
type AuxTr = AuxTree String String
type Other = O.SomeTree String String
-- type Hype  = AStar.Hype String String
-- type Deriv = Deriv.Deriv String (Tok String)
-- type ModifDerivs = Deriv.ModifDerivs String String


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
      -- ^ Parsing results
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


quickly' :: AuxTr
quickly' = AuxTree (Branch "V"
    [ Branch "V" []
    , Branch "Ad" [Leaf "quickly"]
    ]) [0]


with :: AuxTr
with = AuxTree (Branch "VP"
    [ Branch "VP" []
    , Branch "PP"
      [ Branch "P" [Leaf "with"]
      , Branch "NP" [] ]
    ]) [0]


a :: Tr
a = Branch "D" [Leaf "a"]


mouse :: Tr
mouse = Branch "NP"
    [ Branch "D" []
    , Branch "N"
        [Leaf "mouse"]
    ]


-- poPL :: AuxTr
-- poPL = AuxTree (Branch "V"
--     [ Branch "V" []
--     , Branch "PP"
--       [ Branch "P" [Leaf "po"]
--       , Branch "NP" [] ]
--     ]) [0]
--
--
-- prostuPL :: Tr
-- prostuPL = Branch "NP"
--     [ Branch "N"
--         [Leaf "prostu"]
--     ]
--
--
-- poProstuPL :: AuxTr
-- poProstuPL = AuxTree (Branch "V"
--     [ Branch "V" []
--     , Branch "PP"
--       [ Branch "P" [Leaf "po"]
--       , Branch "NP" [Branch "N" [Leaf "prostu"]] ]
--     ]) [0]


dot :: AuxTr
dot = AuxTree (Branch "S"
    [ Branch "S" []
    , Branch "I"
      [ Leaf "." ]
    ]) [0]

dots :: AuxTr
dots = AuxTree (Branch "S"
    [ Branch "S" []
    , Branch "I"
      [ Leaf "."
      , Leaf "." ]
    ]) [0]


-- | Compile the first grammar.
mkGram1 :: [(Other, Weight)]
mkGram1 = map (,1) $
    map Left [tom, sleeps, caught, a, mouse] ++ --, prostuPL] ++
    map Right [almost, quickly, quickly', with, dot, dots] --, poPL, poProstuPL ]


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
    , Test "S" ["caught", "a", "mouse"] No
    , Test "S" ["Tom", "caught", "Tom", ".", "."] Yes ]
    -- , Test "S" ["Tom", "caught", "po", "prostu", "a", "mouse", ".", ".", "."] Yes ]
    -- , Test "S" ["Tom", "quickly", "quickly", "caught", "quickly", "quickly", "Tom"] Yes ]


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


-- | What we test is not really a copy language but rather a language in which
-- there is always the same number of `a`s and `b`s on the left and on the right
-- of the empty `e` symbol. To model the real copy language with a TAG we would
-- need to use either adjunction constraints or feature structures.
--
-- UPDATE 08/06/2018: The description above seems not true anymore. When
-- multiple adjunction is not allowed, this grammar seems to model precisely the
-- copy language.
gram2Tests :: [Test]
gram2Tests =
    [ Test "S" (words "a b e a b") Yes
    , Test "S" (words "a b e a a") No
    , Test "S" (words "a b a b a b a b e a b a b a b a b") Yes
    , Test "S" (words "a b a b a b a b e a b a b a b a") No
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
-- Grammar 5 (Sister Adjunction)
---------------------------------------------------------------------


-- | Some smart constructors.
node x = R.Node (O.NonTerm x)
leaf x = R.Node (O.NonTerm x) []
term x = R.Node (O.Term x) []
foot x = R.Node (O.Foot x) []
sister x = R.Node (O.Sister x)


mkGram5 :: [(O.Tree String String, Weight)]
mkGram5 = map (,1)
  [ben, eatsTra, eatsIntra, vigorously, pasta, tasty, a, plate]
  where
    ben =
      node "NP"
      [ node "N"
        [ term "Ben" ]
      ]
    a =
      node "NP"
      [ node "Det" [ term "a" ]
      , foot "NP"
      ]
    pasta =
      node "NP"
      [ node "N"
        [ term "pasta" ]
      ]
    -- transitive
    eatsTra =
      node "S"
      [ leaf "NP"
      , node "VP"
        [ node "V" [term "eats"]
        , leaf "NP" ]
      ]
    -- intransitive
    eatsIntra =
      node "S"
      [ leaf "NP"
      , node "VP"
        [ node "V" [term "eats"] ]
      ]
    vigorously =
      sister "VP"
      [ node "Adv"
        [ term "vigorously" ]
      ]
    tasty =
      sister "N"
      [ node "Adj"
        [ term "tasty" ]
      ]
    plate =
      node "NP"
      [ leaf "NP"
      , node "N"
        [ term "plate" ]
      ]


-- | The purpose of this test is to test the inversed root adjoin
-- inference operation.
gram5Tests :: [Test]
gram5Tests =
    [ Test "S" (words "Ben eats pasta") Yes
    , Test "S" (words "Ben eats") . Trees . S.singleton $
      Branch "S"
      [ Branch "NP"
        [ Branch "N" [Leaf "Ben"] ]
      , Branch "VP"
        [ Branch "V" [Leaf "eats"] ]
      ]
    , Test "S" (words "Ben vigorously eats pasta") . Trees . S.singleton $
      Branch "S"
      [ Branch "NP"
        [ Branch "N" [Leaf "Ben"] ]
      , Branch "VP"
        [ Branch "Adv" [Leaf "vigorously"]
        , Branch "V" [Leaf "eats"]
        , Branch "NP"
          [ Branch "N" [Leaf "pasta"] ] ]
      ]
    , Test "S" (words "Ben eats pasta vigorously") Yes
    , Test "S" (words "Ben eats vigorously pasta") Yes
    , Test "S" (words "vigorously Ben eats pasta") No
    , Test "S" (words "Ben vigorously eats tasty pasta") Yes
    , Test "S" (words "Ben vigorously eats a tasty pasta") Yes
    , Test "S" (words "Ben vigorously eats tasty a pasta") No
    , Test "S" (words "Ben vigorously a eats tasty pasta") No
    , Test "S" (words "Ben eats a tasty pasta plate") Yes

    -- These following should be perhaps excluded?

    -- Multiple adjunction
    , Test "S" (words "Ben vigorously eats a a tasty pasta") Yes
    -- Sister adjunction to the root of an auxiliary tree
    ]

-- To discuss:
-- * are there many types of sister-adjunction?
--     <- so far implemented only one
--     <- DECISION: YES (left sister-adjunction means that one can adjoin to a
--        sister which is placed on the left in the sense of word-order)
-- * allow sister adjunction to the root of a modifier (sister) tree?
--     <- DECISION: NO
--     <- OUTCOME: DONE
-- * allow sister adjunction to the root of an auxiliary tree?
--     <- DECISION: hard to say, we will see in practice
-- * allow multiple adjunction
--     <- DECISION: NO


---------------------------------------------------------------------
-- Resources
---------------------------------------------------------------------


-- | Compiled grammars.
data Res = Res
  { gram1 :: [(Other, Weight)]
  , gram2 :: [(Other, Weight)]
  , gram3 :: [(Other, Weight)]
  , gram4 :: [(Other, Weight)]
  , gram5 :: [(O.Tree String String, Weight)]
  }


-- | Construct the shared resource (i.e. the grammars) used in
-- tests.
-- mkGrams :: IO Res
mkGrams :: Res
mkGrams =
    Res mkGram1 mkGram2 mkGram3 mkGram4 mkGram5


---------------------------------------------------------------------
-- Test Tree
---------------------------------------------------------------------


-- | An abstract TAG parser.
data TagParser = TagParser
  { recognize   :: Maybe ([(O.Tree String String, Weight)] -> String -> [String] -> IO Bool)
    -- ^ Recognition function
  , parsedTrees :: Maybe ([(O.Tree String String, Weight)] -> String -> [String] -> IO (S.Set Tr))
    -- ^ Function which retrieves derived trees
--   , derivTrees :: Maybe ([(Other, Weight)] -> String -> [String] -> IO [Deriv])
--     -- ^ Function which retrieves derivation trees; the result is a set of
--     -- derivations but it takes the form of a list so that derivations can be
--     -- generated gradually; the property that the result is actually a set
--     -- should be verified separately.
--   , encodes :: Maybe (Hype -> String -> [String] -> Deriv -> Bool)
--     -- ^ Function which checks whether the given derivation is encoded in
--     -- the given hypergraph
--   , derivPipe :: Maybe
--     ( [(Other, Weight)] -> String -> [String] ->
--       (P.Producer ModifDerivs IO Hype)
--     )
--     -- ^ A pipe (producer) which generates derivations on-the-fly
  }


-- | Dummy parser which doesn't provide anything.
dummyParser :: TagParser
-- dummyParser = TagParser Nothing Nothing Nothing Nothing Nothing
dummyParser = TagParser Nothing Nothing


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
testTree modName TagParser{..} = do
  let encode = fmap $ map (first O.encode)
  withResource (return mkGrams) (const $ return ()) $
    \resIO -> testGroup modName $
        map (testIt resIO $ encode gram1) gram1Tests ++
        map (testIt resIO $ encode gram2) gram2Tests ++
        map (testIt resIO $ encode gram3) gram3Tests ++
        map (testIt resIO $ encode gram4) gram4Tests ++
        map (testIt resIO gram5) gram5Tests
  where
    testIt resIO getGram test = testCase (show test) $ do
        gram <- getGram <$> resIO
        testRecognition gram test
        testParsing gram test
--         testDerivsIsSet gram test
--         testFlyingDerivsIsSet gram test
--         testDerivsEqual gram test
--         testEachDerivEncoded gram test
--         testWeightsAscend gram test

    -- Check if the recognition result is as expected
    testRecognition gram Test{..} = case recognize of
      Just reco -> reco gram startSym testSent @@?= simplify testRes
      _ -> return ()

    -- Check if the set of parsed trees is as expected
    testParsing gram Test{..} = case (parsedTrees, testRes) of
        (Just pa, Trees ts) -> pa gram startSym testSent @@?= ts
        _ -> return ()

--     -- Here we only check if the list of derivations is actually a set
--     testDerivsIsSet gram Test{..} = case derivTrees of
--         Just derivs -> do
--           ds <- derivs gram startSym testSent
--           length ds @?= length (nub ds)
--         _ -> return ()

--     -- Like `testDerivsIsSet` but for on-the-fly generated derivations
--     testFlyingDerivsIsSet gram Test{..} = case derivPipe of
--         Just mkPipe -> do
--           derivsRef <- newIORef []
--           let pipe = mkPipe gram startSym testSent
--           void $ P.runEffect . P.for pipe $ \(_modif, derivs) -> do
--             lift $ modifyIORef' derivsRef (++ derivs)
--           ds <- readIORef derivsRef
--           length ds @?= length (nub ds)
--         _ -> return ()

--     -- Test if `testDerivsIsSet` and `testFlyingDerivsIsSet`
--     -- give the same results
--     testDerivsEqual gram Test{..} = case (derivTrees, derivPipe) of
--       (Just derivs, Just mkPipe) -> do
--         derivsRef <- newIORef []
--         let pipe = mkPipe gram startSym testSent
--         void $ P.runEffect . P.for pipe $ \(_modif, modifDerivs) -> do
--           lift $ modifyIORef' derivsRef (++ modifDerivs)
--         ds1 <- readIORef derivsRef
--         ds2 <- derivs gram startSym testSent
--         S.fromList ds1 @?= S.fromList ds2
--       _ -> return ()

--     -- Test if every output derivation is encoded in the final hypergraph
--     testEachDerivEncoded gram Test{..} = case (derivPipe, encodes) of
--         (Just mkPipe, Just enc) -> do
--           derivsRef <- newIORef []
--           let pipe = mkPipe gram startSym testSent
--           hype <- P.runEffect . P.for pipe $ \(_modif, derivs) -> do
--             lift $ modifyIORef' derivsRef (++ derivs)
--           ds <- readIORef derivsRef
--           forM_ ds $ \deriv ->
--             enc hype startSym testSent deriv @?= True
--         _ -> return ()

--     -- Check if the chart items are popped from the queue in the ascending
--     -- order of their weights; we assume here that weights are non-negative
--     testWeightsAscend gram Test{..} = case derivPipe of
--         Just mkPipe -> do
--           weightRef <- newIORef 0.0
--           let pipe = mkPipe gram startSym testSent
--           void $ P.runEffect . P.for pipe $ \(hypeModif, _derivs) -> void . lift . runMaybeT $ do
--             guard $ AStar.modifType hypeModif == AStar.NewNode
-- #ifdef NewHeuristic
-- #else
--             guard $ case AStar.modifItem hypeModif of
--               AStar.ItemA q -> AStar._gap (AStar._spanA q) == Nothing
--               AStar.ItemP p -> AStar._gap (AStar._spanP p) == Nothing
-- #endif
--             let trav = AStar.modifTrav hypeModif
--                 -- newWeight = AStar.priWeight trav + AStar.estWeight trav
--                 newWeight = AStar.totalWeight trav
--             lift $ do
--               curWeight <- readIORef weightRef
-- --             if newWeight < curWeight then do
-- --               putStr "NEW: " >> print newWeight
-- --               putStr "NEW: " >> print (roundTo newWeight 10)
-- --               putStr "CUR: " >> print curWeight
-- --               putStr "CUR: " >> print (curWeight `roundTo` 10)
-- --               else return ()
--               newWeight `roundTo` 10 >= curWeight `roundTo` 10 @?= True
--               writeIORef weightRef newWeight
--         _ -> return ()

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


-- | Round the floiting-point number to the given number of decimal digits.
roundTo :: Double -> Int -> Double
roundTo f n = (fromInteger $ round $ f * (10^n)) / (10.0^^n)
