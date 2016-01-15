module NLP.TAG.Vanilla.SubtreeSharing.Tests where


import           Control.Applicative ((<$>))

import qualified Data.Set as S

import           Test.Tasty (TestTree, testGroup) -- , localOptions)
import           Test.HUnit (Assertion, (@?=))
import           Test.Tasty.HUnit (testCase)


import           NLP.TAG.Vanilla.Tree (Tree (..), AuxTree (..))
import           NLP.TAG.Vanilla.Earley.Basic (recognize, recognizeFrom)
import           NLP.TAG.Vanilla.Rule (Rule)
import qualified NLP.TAG.Vanilla.Rule as R
import           NLP.TAG.Vanilla.SubtreeSharing (compile)


---------------------------------------------------------------------
-- Prerequisites
---------------------------------------------------------------------


type Tr = Tree String String
type AuxTr = AuxTree String String
type Rl = Rule String String


---------------------------------------------------------------------
-- Grammar 1
---------------------------------------------------------------------


tree1 :: Tr
tree1 = INode "S"
    [ abc
    , INode "D"
        [ abc
        , INode "E" [] ]
    ]
  where
    abc = INode "A"
        [ INode "B" []
        , INode "C" [] ]


tree2 :: Tr
tree2 = INode "S"
    [ INode "D"
        [ abc
        , INode "E" [] ]
    , abc
    ]
  where
    abc = INode "A"
        [ INode "B" []
        , INode "C" [] ]


tree3 :: Tr
tree3 = INode "D"
    [ abc
    , INode "E" [] ]
  where
    abc = INode "A"
        [ INode "B" []
        , INode "C" [] ]


mkGram1 :: IO (S.Set Rl)
mkGram1 = compile (map Left [tree1, tree2, tree3])


---------------------------------------------------------------------
-- Grammar 2
---------------------------------------------------------------------


aux1 :: AuxTr
aux1 = AuxTree (INode "A"
    [ INode "B" []
    , INode "C"
        [ INode "A" []
        , INode "D" [] ]
    ]) [1, 0]


aux2 :: AuxTr
aux2 = AuxTree (INode "A"
    [ INode "C"
        [ INode "A" []
        , INode "D" [] ]
    , INode "B" []
    ]) [0, 0]


aux3 :: Tr
aux3 = INode "A"
    [ INode "B" []
    , INode "C"
        [ INode "A" []
        , INode "D" [] ]
    ]


-- | Note: tree identical to `aux3`!
aux4 :: Tr
aux4 = INode "A"
    [ INode "B" []
    , INode "C"
        [ INode "A" []
        , INode "D" [] ]
    ]


mkGram2 :: IO (S.Set Rl)
mkGram2 = compile $
    (map Left [aux3, aux4]) ++
    (map Right [aux1, aux2])


---------------------------------------------------------------------
-- Tests
---------------------------------------------------------------------


tests :: TestTree
tests = testGroup "NLP.TAG.Vanilla.SubtreeSharing"
    [ testCase "Subtree Sharing (Initial)" testShareInit
    , testCase "Subtree Sharing (Auxiliary)" testShareAux ]


testShareInit :: Assertion
testShareInit = do
    gram <- mkGram1
    S.size gram @?= 5


testShareAux :: Assertion
testShareAux = do
    gram <- mkGram2
    S.size gram @?= 5


localTest :: Assertion
localTest = do
    gram <- mkGram1
    mapM_ print $ S.toList gram


-- ---------------------------------------------------------------------
-- -- Utils
-- ---------------------------------------------------------------------
--
--
-- (@@?=) :: (Show a, Eq a) => IO a -> a -> Assertion
-- mx @@?= y = do
--     x <- mx
--     x @?= y
