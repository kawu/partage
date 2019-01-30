{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}


-- | The module collects the sample grammars used for testing and
-- unit test examples themselves.


module TestSet
( Test (..)
, TestRes (..)
, Term (..)
, mkGram1
, gram1Tests
-- , mkGram2
-- , gram2Tests
-- , mkGram3
-- , gram3Tests

-- , Gram
, TagParser (..)
, dummyParser
, testTree
)  where


import           Control.Applicative       ((<$>), (<*>))
import           Control.Arrow             (first)
import           Control.Monad             (forM_, guard, void, forever)
-- import           Control.Monad.Morph       as Morph
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (..))

import           Data.IORef
import qualified Data.Map.Strict           as M
import qualified Data.Set                  as S
import qualified Data.Tree                 as R
import           Data.List                 (intercalate)
import qualified Data.Text                 as T
import qualified Data.Text.Lazy            as L

import           Test.HUnit                (Assertion, (@?=))
import           Test.Tasty                (TestTree, testGroup, withResource)
import           Test.Tasty.HUnit          (testCase)

import qualified Pipes                     as P

import           NLP.Partage.AStar         (Tok)
import qualified NLP.Partage.AStar         as AStar
import qualified NLP.Partage.AStar.Deriv   as Deriv
import           NLP.Partage.DAG           (Weight)
import           NLP.Partage.Tree          (AuxTree (..), Tree (..))
import qualified NLP.Partage.Tree.Other    as O

import qualified NLP.Partage.Format.Brackets as Br


---------------------------------------------------------------------
-- Prerequisites
---------------------------------------------------------------------


-- | Local type aliases.
type Tr    = Tree String (Maybe Term)
type OTree = O.Tree String (Maybe Term)
-- type AuxTr = AuxTree String String
-- type Other = O.SomeTree String String
type Hype  = AStar.Hype String Term
type Deriv = Deriv.Deriv String (Tok Term)
type ModifDerivs = Deriv.ModifDerivs String Term


-- | A terminal/token.
data Term = Term 
  { orth :: String
    -- ^ The orthographic form
  , pos :: Maybe Int
    -- ^ The position (can be left underspecified)
  } deriving (Eq, Ord)

instance Show Term where
  show t = orth t ++
    case pos t of
      Nothing -> ""
      Just k -> ":" ++ show k


-- | Some smart constructors.
node x = R.Node (O.NonTerm x)
leaf x = R.Node (O.NonTerm x) []
term x = R.Node (O.Term x) []
foot x = R.Node (O.Foot x) []
sister x = R.Node (O.Sister x)


---------------------------------------------------------------------
-- Tests
---------------------------------------------------------------------


-- | A single test case.
data Test = Test {
    -- | Starting symbol
      startSym :: String
    -- | The sentence to parse (list of terminals)
    , testSent :: [Term]
    -- | Dependency weights/restrictions (to each position, the set of
    -- potential head together with the corresponding weights is given)
    , headMap :: M.Map Int (M.Map Int Weight)
    -- | The expected recognition result
    , testRes  :: TestRes
    } deriving (Eq, Ord)


instance Show Test where
  show Test{..}
    = "("
    ++ startSym
    ++ ", "
    ++ show testSent
    ++ showHeads
    ++ ", "
    ++ show testRes
    ++ ")"
      where
        showHeads =
          if M.null headMap
             then ""
             else ", " ++
               intercalate ";"
                [ show dep ++ ":" ++ show hed ++ "$" ++ show w
                | (dep, hedMap) <- M.toList headMap 
                , (hed, w) <- M.toList hedMap
                ]


-- | The expected test result.  The set of parsed trees can be optionally
-- specified.
data TestRes
    = No
      -- ^ No parse
    | Yes
      -- ^ Parse
    | Trees (S.Set Tr)
      -- ^ Parsing results
    deriving (Eq, Ord)


instance Show TestRes where
  show No = "No"
  show Yes = "Yes"
  show (Trees ts) =
    "{" ++ L.unpack lazyText ++ "}"
      where
        showOne = Br.showTree . fmap process . O.unTree
        lazyText = L.intercalate " " (map showOne $ S.toList ts)
        -- process (O.Term t) = O.Term . Just . T.pack $ show t
        process (O.Term (Just t)) = O.Term . Just . T.pack $ show t
        process (O.Term Nothing) = O.Term Nothing
        process (O.NonTerm x) = O.NonTerm $ T.pack x
        process (O.Sister x) = O.Sister $ T.pack x
        process (O.Foot x) = O.Foot $ T.pack x
    

---------------------------------------------------------------------
-- Grammar1
---------------------------------------------------------------------


-- -- | Compile the first grammar.
-- mkGram1 :: [(Other, Weight)]
-- mkGram1 = map (,1) $
--     map Left [tom, sleeps, caught, a, mouse] ++ --, prostuPL] ++
--     map Right [almost, quickly, quickly', with, dot, dots] --, poPL, poProstuPL ]


-- | Compile the first grammar.
mkGram1 :: [(OTree, Weight)]
mkGram1 = map (,1) $
  [tom, sleeps, caught, a, mouse] ++ --, prostuPL] ++
  [almost, quickly, quickly', with, dot, dots] --, poPL, poProstuPL ]
    where
      -- terminal with unspecified position
      term' t = term . Just $ Term t Nothing
      tom =
        node "NP"
        [ node "N"
          [ term' "Tom" ]
        ]
      sleeps =
        node "S"
        [ leaf "NP"
        , node "VP"
          [node "V" [term' "sleeps"]]
        ]
      caught = 
        node "S"
        [ leaf "NP"
        , node "VP"
          [ node "V" [term' "caught"]
          , leaf "NP" ]
        ]
      almost = 
        node "V"
        [ node "Ad" [term' "almost"]
        , foot "V"
        ]
      quickly = 
        node "V"
        [ node "Ad" [term' "quickly"]
        , foot "V"
        ]
      quickly' = 
        node "V"
        [ foot "V"
        , node "Ad" [term' "quickly"]
        ]
      with = node "VP"
        [ foot "VP"
        , node "PP"
          [ node "P" [term' "with"]
          , leaf "NP" ]
        ]
      a = node "D" [term' "a"]
      mouse = node "NP"
        [ leaf "D"
        , node "N"
            [term' "mouse"]
        ]
-- poPL :: AuxTr
-- poPL = AuxTree (Branch "V"
--     [ Branch "V" []
--     , Branch "PP"
--       [ Branch "P" [Leaf "po"]
--       , Branch "NP" [] ]
--     ]) [0]
-- prostuPL :: Tr
-- prostuPL = Branch "NP"
--     [ Branch "N"
--         [Leaf "prostu"]
--     ]
-- poProstuPL :: AuxTr
-- poProstuPL = AuxTree (Branch "V"
--     [ Branch "V" []
--     , Branch "PP"
--       [ Branch "P" [Leaf "po"]
--       , Branch "NP" [Branch "N" [Leaf "prostu"]] ]
--     ]) [0]
      dot = node "S"
        [ foot "S"
        , node "I"
          [ term' "." ]
        ]
      dots = node "S"
        [ foot "S"
        , node "I"
          [ term' "."
          , term' "." ]
        ]


---------------------------------------------------------------------
-- Grammar1 Tests
---------------------------------------------------------------------


gram1Tests :: [Test]
gram1Tests =
    -- group 1
    [ test "S" ["Tom", "sleeps"] Yes
    , test "S" ["Tom", "sleeps"] . Trees . S.singleton $
        Branch "S"
            [ Branch "NP"
                [ Branch "N"
                    [mkLeaf "Tom"]
                ]
            , Branch "VP"
                [Branch "V" [mkLeaf "sleeps"]]
            ]
    , test "S" ["Tom"] No
    , test "NP" ["Tom"] Yes
    -- group 2
    , test "S" ["Tom", "almost", "caught", "a", "mouse"] . Trees . S.singleton $
        Branch "S"
            [ Branch "NP"
                [ Branch "N"
                    [ mkLeaf "Tom" ] ]
            , Branch "VP"
                [ Branch "V"
                    [ Branch "Ad"
                        [mkLeaf "almost"]
                    , Branch "V"
                        [mkLeaf "caught"]
                    ]
                , Branch "NP"
                    [ Branch "D"
                        [mkLeaf "a"]
                    , Branch "N"
                        [mkLeaf "mouse"]
                    ]
                ]
            ]
    , test "S" ["Tom", "caught", "almost", "a", "mouse"] No
    , test "S" ["Tom", "quickly", "almost", "caught", "Tom"] No
    , test "S" ["Tom", "caught", "a", "mouse"] Yes
    , test "S" ["Tom", "caught", "Tom"] Yes
    , test "S" ["Tom", "caught", "a", "Tom"] No
    , test "S" ["Tom", "caught"] No
    , test "S" ["caught", "a", "mouse"] No
    , test "S" ["Tom", "caught", "Tom", ".", "."] Yes
    -- , Test "S" ["Tom", "caught", "po", "prostu", "a", "mouse", ".", ".", "."] Yes ]
    -- , Test "S" ["Tom", "quickly", "quickly", "caught", "quickly", "quickly", "Tom"] Yes ]
    ]
      where
        test start sent res = Test start (map tok sent) M.empty res
        tok t = Term t Nothing
        mkLeaf = Leaf . Just . tok


---------------------------------------------------------------------
-- Grammar1_1
---------------------------------------------------------------------


-- | A variant of the first grammar.
mkGram1_1 :: [(OTree, Weight)]
mkGram1_1 = map (,1) $
  [root, tom, almost, almost', caught, a, mouse]
    where
      term' t k = term . Just $ Term t (Just k)
      root = node "ROOT"
        [ term' "root" 0
        , leaf "S"
        ]
      tom =
        node "NP"
        [ node "N"
          [ term' "Tom" 1 ]
        ]
      almost = 
        node "V"
        [ node "Ad" [term' "almost" 2]
        , foot "V"
        ]
      -- yes, the tree below doesn't make a lot of sense
      almost' =
        node "N"
        [ foot "N"
        , node "Ad" [term' "almost" 2]
        ]
      caught =
        node "S"
        [ leaf "NP"
        , node "VP"
          [ node "V" [term' "caught" 3]
          , leaf "NP" ]
        ]
      a = node "D" [term' "a" 4]
      mouse = node "NP"
        [ leaf "D"
        , node "N"
            [term' "mouse" 5]
        ]


---------------------------------------------------------------------
-- Grammar1_1 Tests
---------------------------------------------------------------------


gram1_1Tests :: [Test]
gram1_1Tests =
    [ test "ROOT" ["root", "Tom", "almost", "caught", "a", "mouse"] Yes
    , test "ROOT" ["root", "Tom", "almost", "caught", "a", "mouse"] . Trees . S.fromList $
      [ Branch "ROOT"
          [ mkLeaf "root" 0
          , Branch "S"
            [ Branch "NP"
                [ Branch "N"
                    [ mkLeaf "Tom" 1 ] ]
            , Branch "VP"
                [ Branch "V"
                    [ Branch "Ad"
                        [mkLeaf "almost" 2]
                    , Branch "V"
                        [mkLeaf "caught" 3]
                    ]
                , Branch "NP"
                    [ Branch "D"
                        [mkLeaf "a" 4]
                    , Branch "N"
                        [mkLeaf "mouse" 5]
                    ]
                ]
            ]
          ]
      , Branch "ROOT"
          [ mkLeaf "root" 0
          , Branch "S"
            [ Branch "NP"
                [ Branch "N"
                    [ Branch "N"
                        [mkLeaf "Tom" 1]
                    , Branch "Ad"
                        [mkLeaf "almost" 2]
                    ]
                ]
            , Branch "VP"
                [ Branch "V"
                    [ mkLeaf "caught" 3 ]
                , Branch "NP"
                    [ Branch "D"
                        [mkLeaf "a" 4]
                    , Branch "N"
                        [mkLeaf "mouse" 5]
                    ]
                ]
            ]
          ]
      ]
    , testDep "ROOT" ["root", "Tom", "almost", "caught", "a", "mouse"] Yes $ M.fromList
        [ (1, M.fromList [(3, 1)])
        , (2, M.fromList [(3, 1)])
        , (3, M.fromList [(0, 1)])
        , (4, M.fromList [(5, 1)])
        , (5, M.fromList [(3, 1)])
        ]
    , testDep "ROOT" ["root", "Tom", "almost", "caught", "a", "mouse"] Yes $ M.fromList
        [ (2, M.fromList [(1, 2), (3, 1)])
        ]
    , testDep "ROOT" ["root", "Tom", "almost", "caught", "a", "mouse"] No $ M.fromList
        [ (3, M.fromList [(2, 1)])
        ]
    ]
      where
        test start sent res = testDep start sent res M.empty
        testDep start sent res hedMap = Test
          start
          [tok x k | (x, k) <- zip sent [0..]] 
          hedMap
          res
        tok t k = Term t (Just k)
        mkLeaf t k = Leaf . Just $ tok t k


---------------------------------------------------------------------
-- Grammar2
---------------------------------------------------------------------


mkGram2 :: [(OTree, Weight)]
mkGram2 = map (,1) $
  [alpha, beta1, beta2]
    where
      term' t = term . Just $ Term t Nothing
      alpha =
        node "S"
        [ node "X"
          [ term' "e" ]
        ]
      beta1 =
        node "X"
        [ term' "a"
        , node "X"
          [ foot "X"
          , term' "a"
          ]
        ]
      beta2 =
        node "X"
        [ term' "b"
        , node "X"
          [ foot "X"
          , term' "b"
          ]
        ]


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
  [ test "S" ("a b e a b") Yes
  , test "S" ("a b e a a") No
  , test "S" ("a b a b a b a b e a b a b a b a b") Yes
  , test "S" ("a b a b a b a b e a b a b a b a") No
  , test "S" ("a b e b a") No
  , test "S" ("b e a") No
  , test "S" ("a b a b") No 
  ]
    where
      test start sent res = Test start (toks sent) M.empty res
      toks = map tok . words
      tok t = Term t Nothing


---------------------------------------------------------------------
-- Grammar 3
---------------------------------------------------------------------


mkGram3 :: [(OTree, Weight)]
mkGram3 = map (,1) $
  [sent, xtree]
    where
      term' t = term . Just $ Term t Nothing
      sent = node "S"
        [ term' "p"
        , node "X"
            [term' "e"]
        , term' "b" 
        ]
      xtree = node "X"
        [ term' "a"
        , foot "X"
        , term' "b"
        ]


-- | Here we check that the auxiliary tree must be fully
-- recognized before it can be adjoined.
gram3Tests :: [Test]
gram3Tests =
  [ test "S" ("p a e b b") Yes
  , test "S" ("p a e b") No ]
    where
      test start sent res = Test start (toks sent) M.empty res
      toks = map tok . words
      tok t = Term t Nothing


---------------------------------------------------------------------
-- Grammar 4
---------------------------------------------------------------------


mkGram4 :: [(OTree, Weight)]
mkGram4 =
  [(ztree, 1), (stree, 10), (atree, 5)]
    where
      term' t = term . Just $ Term t Nothing
      stree = node "S"
        [ node "A"
          [ node "B"
            [term' "a"]
          ]
        ]
      ztree = node "Z"
        [ node "Z" []
        , node "A"
            [term' "a"]
        ]
      atree = node "A"
        [ term' "x"
        , foot "A"
        , term' "y"
        ]


-- | The purpose of this test is to test the inversed root adjoin
-- inference operation.
gram4Tests :: [Test]
gram4Tests =
  [ test "S" ("x a y") Yes ]
    where
      test start sent res = Test start (toks sent) M.empty res
      toks = map tok . words
      tok t = Term t Nothing


---------------------------------------------------------------------
-- Grammar 5 (Sister Adjunction)
---------------------------------------------------------------------


mkGram5 :: [(OTree, Weight)]
mkGram5 = map (,1)
  [ben, eatsTra, eatsIntra, vigorously, pasta, tasty, a, plate]
  where
    term' t = term . Just $ Term t Nothing
    ben =
      node "NP"
      [ node "N"
        [ term' "Ben" ]
      ]
    a =
      node "NP"
      [ node "Det" [ term' "a" ]
      , foot "NP"
      ]
    pasta =
      node "NP"
      [ node "N"
        [ term' "pasta" ]
      ]
    -- transitive
    eatsTra =
      node "S"
      [ leaf "NP"
      , node "VP"
        [ node "V" [term' "eats"]
        , leaf "NP" ]
      ]
    -- intransitive
    eatsIntra =
      node "S"
      [ leaf "NP"
      , node "VP"
        [ node "V" [term' "eats"] ]
      ]
    vigorously =
      sister "VP"
      [ node "Adv"
        [ term' "vigorously" ]
      ]
    tasty =
      sister "N"
      [ node "Adj"
        [ term' "tasty" ]
      ]
    plate =
      node "NP"
      [ leaf "NP"
      , node "N"
        [ term' "plate" ]
      ]


-- | The purpose of this test is to test the inversed root adjoin
-- inference operation.
gram5Tests :: [Test]
gram5Tests =
    [ test "S" ("Ben eats pasta") Yes
    , test "S" ("Ben eats") . Trees . S.singleton $
      Branch "S"
      [ Branch "NP"
        [ Branch "N" [mkLeaf "Ben"] ]
      , Branch "VP"
        [ Branch "V" [mkLeaf "eats"] ]
      ]
    , test "S" ("Ben vigorously eats pasta") . Trees . S.singleton $
      Branch "S"
      [ Branch "NP"
        [ Branch "N" [mkLeaf "Ben"] ]
      , Branch "VP"
        [ Branch "Adv" [mkLeaf "vigorously"]
        , Branch "V" [mkLeaf "eats"]
        , Branch "NP"
          [ Branch "N" [mkLeaf "pasta"] ] ]
      ]
    , test "S" ("Ben eats pasta vigorously") Yes
    , test "S" ("Ben eats vigorously pasta") Yes
    , test "S" ("vigorously Ben eats pasta") No
    , test "S" ("Ben vigorously eats tasty pasta") Yes
    , test "S" ("Ben vigorously eats a tasty pasta") Yes
    , test "S" ("Ben vigorously eats tasty a pasta") No
    , test "S" ("Ben vigorously a eats tasty pasta") No
    , test "S" ("Ben eats a tasty pasta plate") Yes
    -- Should fail because of multiple adjunction
    , test "S" ("Ben vigorously eats a a tasty pasta") No
    ]
    where
      test start sent res = Test start (toks sent) M.empty res
      toks = map tok . words
      tok t = Term t Nothing
      mkLeaf = Leaf . Just . tok

-- To discuss (May 2018):
-- * allow sister adjunction to the root of a modifier (sister) tree?
--     <- DECISION: NO
--     <- OUTCOME: DONE
-- * allow multiple adjunction
--     <- DECISION: NO
--     <- OUTCOME: DONE
-- * are there many types of sister-adjunction?
--     <- so far implemented only one
--     <- DECISION: YES (left sister-adjunction means that one can adjoin to a
--        sister which is placed on the left in the sense of word-order)
-- * allow sister adjunction to the root of an auxiliary tree?
--     <- DECISION: hard to say, we will see in practice


---------------------------------------------------------------------
-- Test 6
---------------------------------------------------------------------


mkGram6 :: [(OTree, Weight)]
mkGram6 = map (,1) $
  [en, excuser]
    where
      term' t = term . Just $ Term t Nothing
      en = 
        node "DUMMY"
          [ node "CL"
            [term' "en"]
          ]
      excuser = 
        node "S"
          [ leaf "CL"
          , term' "excuser"
          ]


-- | Make sure that substitution doesn't work with a tree that is not fully
-- recognized.
gram6Tests :: [Test]
gram6Tests =
  [ test "S" ("en excuser") No ]
    where
      test start sent res = Test start (toks sent) M.empty res
      toks = map tok . words
      tok t = Term t Nothing


---------------------------------------------------------------------
-- Test 7
---------------------------------------------------------------------


mkGram7 :: [(OTree, Weight)]
mkGram7 =
  [(cine, 1.0), (et, 1.0), (lect, 1.0)]
    where
      term' t k = term . Just $ Term t (Just k)
      cine =
        node "NP"
          [ node "N"
            [term' "cine" 0]
          ]
      et =
        sister "NP"
          [ node "COORD"
            [ node "C" [term' "et" 1]
            , leaf "NP"
            ]
          ]
      lect =
        node "NP"
          [ node "N"
            [term' "lect" 2]
          ]


-- | Make sure that substitution doesn't work with a tree that is not fully
-- recognized.
gram7Tests :: [Test]
gram7Tests =
  [ testDep "NP" ["cine", "et", "lect"] Yes $
      M.fromList
        [ (1, M.fromList [(0, 1)])
        , (2, M.fromList [(1, 1)])
        ]
  ]
    where
      testDep start sent res hedMap = Test
        start
        [tok x k | (x, k) <- zip sent [0..]] 
        hedMap
        res
      tok t k = Term t (Just k)
      -- mkLeaf t k = Leaf . Just $ tok t k


---------------------------------------------------------------------
-- Test 8
---------------------------------------------------------------------


mkGram8 :: [(OTree, Weight)]
mkGram8 =
  [(cine, 0.0), (cine', 1.0), (et, 0.0), (lect, 0.0)]
    where
      term' t k = term . Just $ Term t (Just k)
      cine =
        node "DUMMY"
          [ node "N"
            [term' "cine" 0]
          ]
      cine' =
        node "NP"
          [ node "N"
            [term' "cine" 0]
          , leaf "NP"
          ]
      et =
        sister "NP"
          [ node "COORD"
            [ node "C" [term' "et" 1]
            , leaf "NP"
            ]
          ]
      lect =
        node "NP"
          [ node "N"
            [term' "lect" 2]
          ]


-- | Make sure that substitution doesn't work with a tree that is a
-- sister-tree.
gram8Tests :: [Test]
gram8Tests =
  [ testDep "NP" ["cine", "et", "lect"] No $
      M.fromList
        [ (1, M.fromList [(0, 0)])
        , (2, M.fromList [(1, 0)])
        ]
  ]
    where
      testDep start sent res hedMap = Test
        start
        [tok x k | (x, k) <- zip sent [0..]] 
        hedMap
        res
      tok t k = Term t (Just k)


---------------------------------------------------------------------
-- Test 9
---------------------------------------------------------------------


-- | A grammar sprinkled with empty terminals
mkGram9 :: [(OTree, Weight)]
mkGram9 = map (,0)
  [main, aux]
    where
      term' t = term . Just $ Term t Nothing
      empty = term Nothing
      main =
        node "S"
          [ empty
          , node "A" [empty, term' "a"]
          , empty
          , node "X" [empty]
          , empty
          , node "B" [term' "b", empty]
          , empty
          ]
      aux =
        sister "X" [term' "a"]


gram9Tests :: [Test]
gram9Tests =
  [ test "S" (words "a a b") Yes
  ] where
      test start sent res = Test start (map tok sent) M.empty res
      tok t = Term t Nothing
      -- mkLeaf = Leaf . Just . tok
        
        
---------------------------------------------------------------------
-- Test 10
---------------------------------------------------------------------


-- | A grammar sprinkled with empty terminals
mkGram10 :: [(OTree, Weight)]
mkGram10 = map (,0)
  [seen, shaking]
    where
      term' t = term . Just $ Term t Nothing
      empty = term Nothing
      seen =
        node "S"
          [ node "V" [term' "seen"]
          , node "S" []
          ]
      shaking =
        node "S"
          [ node "NP" [empty]
          , term' "shaking"
          ]


gram10Tests :: [Test]
gram10Tests =
  [ test "S" (words "seen shaking") Yes
  ] where
      test start sent res = Test start (map tok sent) M.empty res
      tok t = Term t Nothing


---------------------------------------------------------------------
-- Resources
---------------------------------------------------------------------


-- | Compiled grammars.
data Res = Res
  { gram1 :: [(OTree, Weight)]
  , gram1_1 :: [(OTree, Weight)]
  , gram2 :: [(OTree, Weight)]
  , gram3 :: [(OTree, Weight)]
  , gram4 :: [(OTree, Weight)]
  , gram5 :: [(OTree, Weight)]
  , gram6 :: [(OTree, Weight)]
  , gram7 :: [(OTree, Weight)]
  , gram8 :: [(OTree, Weight)]
  , gram9 :: [(OTree, Weight)]
  , gram10 :: [(OTree, Weight)]
  }


-- | Construct the shared resource (i.e. the grammars) used in
-- tests.
-- mkGrams :: IO Res
mkGrams :: Res
mkGrams =
  Res mkGram1 mkGram1_1 mkGram2 mkGram3 mkGram4
      mkGram5 mkGram6 mkGram7 mkGram8 mkGram9
      mkGram10


---------------------------------------------------------------------
-- Test Tree
---------------------------------------------------------------------


-- | Recognition
type RecoP 
  = [(OTree, Weight)]
    -- ^ Weighted grammar
  -> String
    -- ^ Start symbol
  -> [Term]
    -- ^ Sentence to parse
  -> M.Map Int (M.Map Int Weight)
    -- ^ Head map
  -> IO Bool


-- | Parsed trees
type ParsedP 
  = [(OTree, Weight)]
    -- ^ Weighted grammar
  -> String
    -- ^ Start symbol
  -> [Term]
    -- ^ Sentence to parse
  -> M.Map Int (M.Map Int Weight)
    -- ^ Head map
  -> IO (S.Set Tr)


-- | Derivation trees
type DerivP
  = [(OTree, Weight)]
    -- ^ Weighted grammar
  -> String
    -- ^ Start symbol
  -> [Term]
    -- ^ Sentence to parse
  -> M.Map Int (M.Map Int Weight)
    -- ^ Head map
  -> IO [Deriv]
-- type DerivP = [(Other, Weight)] -> String -> [String] -> IO [Deriv]


-- | Derivation pipe
type DerivPipeP
  = [(OTree, Weight)]
  -> String
  -> [Term]
  -> M.Map Int (M.Map Int Weight)
  -- -> P.Producer ModifDerivs IO Hype
  -> (P.Consumer ModifDerivs IO Hype -> IO Hype)


-- | Encoding check
type EncodeP = Hype -> String -> [Term] -> Deriv -> Bool


-- | An abstract TAG parser.
data TagParser = TagParser
  { recognize   :: Maybe RecoP
    -- ^ Recognition function
  , parsedTrees :: Maybe ParsedP
    -- ^ Function which retrieves derived trees
  , derivTrees :: Maybe DerivP
    -- ^ Function which retrieves derivation trees; the result is a set of
    -- derivations but it takes the form of a list so that derivations can be
    -- generated gradually; the property that the result is actually a set
    -- should be verified separately.
  , encodes :: Maybe EncodeP
    -- ^ Function which checks whether the given derivation is encoded in
    -- the given hypergraph
  , derivPipe :: Maybe DerivPipeP
    -- ^ A pipe (producer) which generates derivations on-the-fly
  , dependencySupport :: Bool
    -- ^ Does the parser provide support for dependency constraints?
  }


-- | Dummy parser which doesn't provide anything.
dummyParser :: TagParser
dummyParser = TagParser Nothing Nothing Nothing Nothing Nothing
  True


-- | All the tests of the parsing algorithm.
testTree
  :: String
        -- ^ Name of the tested module
  -> TagParser
  -> TestTree
testTree modName TagParser{..} = do
  -- let encode = fmap $ map (first O.encode)
  withResource (return mkGrams) (const $ return ()) $
    \resIO -> testGroup modName $
        map (testIt resIO gram1) gram1Tests ++
        map (testIt resIO gram1_1) gram1_1Tests ++
        map (testIt resIO gram2) gram2Tests ++
        map (testIt resIO gram3) gram3Tests ++
        map (testIt resIO gram4) gram4Tests ++
        map (testIt resIO gram5) gram5Tests ++
        map (testIt resIO gram6) gram6Tests ++
        map (testIt resIO gram7) gram7Tests ++
        map (testIt resIO gram8) gram8Tests ++
        map (testIt resIO gram9) gram9Tests ++
        map (testIt resIO gram10) gram10Tests
  where
    testIt resIO getGram test =
      -- make sure that headMap is empty if no dependency support
      if (not dependencySupport <= M.null (headMap test))
         then testCase (show test) $ do
           gram <- getGram <$> resIO
           testRecognition gram test
           testParsing gram test
           testDerivsIsSet gram test
           testFlyingDerivsIsSet gram test
           testDerivsEqual gram test
           testWeightsAscend gram test
           testEachDerivEncoded gram test
         else testCase ("IGNORING: " ++ show test ) $ return ()

    -- Check if the recognition result is as expected
    testRecognition gram Test{..} = case recognize of
      Just reco -> reco gram startSym testSent headMap @@?= simplify testRes
      _ -> return ()

    -- Check if the set of parsed trees is as expected
    testParsing gram Test{..} = case (parsedTrees, testRes) of
        (Just pa, Trees ts) -> pa gram startSym testSent headMap @@?= ts
        _ -> return ()

    -- Here we only check if the list of derivations is actually a set
    testDerivsIsSet gram Test{..} = case derivTrees of
        Just derivs -> do
          ds <- derivs gram startSym testSent headMap
          -- putStrLn ""
          -- forM_ ds $ putStrLn . R.drawTree . fmap show . Deriv.deriv4show
          length ds @?= length (nub ds)
        _ -> return ()

    -- Like `testDerivsIsSet` but for on-the-fly generated derivations
    testFlyingDerivsIsSet gram Test{..} = case derivPipe of
        Just mkPipe -> do
          derivsRef <- newIORef []
          let pipe = mkPipe gram startSym testSent headMap
          pipe . forever $ do
            (_modif, derivs) <- P.await
            lift $ modifyIORef' derivsRef (++ derivs)
--           void $ P.runEffect . P.for pipe $ \(_modif, derivs) -> do
--             lift $ modifyIORef' derivsRef (++ derivs)
          ds <- readIORef derivsRef
          length ds @?= length (nub ds)
        _ -> return ()

    -- Test if `testDerivsIsSet` and `testFlyingDerivsIsSet`
    -- give the same results
    testDerivsEqual gram Test{..} = case (derivTrees, derivPipe) of
      (Just derivs, Just mkPipe) -> do
        derivsRef <- newIORef []
        let pipe = mkPipe gram startSym testSent headMap
        pipe . forever $ do
          (_modif, modifDerivs) <- P.await
          lift $ modifyIORef' derivsRef (++ modifDerivs)
        ds1 <- readIORef derivsRef
        ds2 <- derivs gram startSym testSent headMap
        S.fromList ds1 @?= S.fromList ds2
      _ -> return ()

    -- Test if every output derivation is encoded in the final hypergraph
    testEachDerivEncoded gram Test{..} = case (derivPipe, encodes) of
        (Just mkPipe, Just enc) -> do
          derivsRef <- newIORef []
          let pipe = mkPipe gram startSym testSent headMap
          hype <- pipe . forever $ do
            (_modif, derivs) <- P.await
            lift $ modifyIORef' derivsRef (++ derivs)
          ds <- readIORef derivsRef
          forM_ ds $ \deriv ->
            enc hype startSym testSent deriv @?= True
        _ -> return ()

    -- Check if the chart items are popped from the queue in the ascending
    -- order of their weights; we assume here that weights are non-negative
    testWeightsAscend gram Test{..} = case derivPipe of
        Just mkPipe -> do
          weightRef <- newIORef 0.0
          let pipe = mkPipe gram startSym testSent headMap
          void . pipe . forever $ do
            (hypeModif, _derivs) <- P.await
            void . lift . runMaybeT $ do
              guard $ AStar.modifType hypeModif == AStar.NewNode
#ifdef NewHeuristic
#else
              guard $ case AStar.modifItem hypeModif of
                AStar.ItemA q -> AStar._gap (AStar._spanA q) == Nothing
                AStar.ItemP p -> AStar._gap (AStar._spanP p) == Nothing
#endif
              let trav = AStar.modifTrav hypeModif
                  newWeight = AStar.totalWeight trav
              lift $ do
                curWeight <- readIORef weightRef
--               if newWeight < curWeight then do
--                 putStr "NEW: " >> print newWeight
--                 putStr "NEW: " >> print (roundTo newWeight 10)
--                 putStr "CUR: " >> print curWeight
--                 putStr "CUR: " >> print (curWeight `roundTo` 10)
--               else return ()
                newWeight `roundTo` 10 >= curWeight `roundTo` 10 @?= True
                writeIORef weightRef newWeight
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


-- | Round the floiting-point number to the given number of decimal digits.
roundTo :: Double -> Int -> Double
roundTo f n = (fromInteger $ round $ f * (10^n)) / (10.0^^n)
