module NLP.LTAG.Early3.Test3 where


import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (void)

import qualified Data.IntMap as I
import qualified Data.Set as S
import           Data.List (sortBy)
import           Data.Ord (comparing)

import           NLP.LTAG.Tree (AuxTree(AuxTree), Tree(FNode, INode))
import           NLP.LTAG.Early3


alpha :: Tree String String
alpha = INode "S"
    [ FNode "p"
    , INode "X"
        [FNode "e"]
    , FNode "q" ]


beta1 :: AuxTree String String
beta1 = AuxTree (INode "X"
    [ FNode "a"
    , INode "X"
        [ INode "X" []
        , FNode "a" ] ]
    ) [1,0]


beta2 :: AuxTree String String
beta2 = AuxTree (INode "X"
    [ FNode "b"
    , INode "X"
        [ INode "X" []
        , FNode "b" ] ]
    ) [1,0]


testGram :: [String] -> IO ()
testGram sent = do
    -- void $ earley gram sent
    mapM_ print $ S.toList gram
  where
    gram = S.fromList $ snd $ runRM $ do
        mapM_ (treeRules True) [alpha]
        mapM_ (auxRules True) [beta1, beta2]
