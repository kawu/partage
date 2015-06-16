module NLP.LTAG.Early3.Test1 where


import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (void)

import qualified Data.IntMap as I
import qualified Data.Set as S
import           Data.List (sortBy)
import           Data.Ord (comparing)

import           NLP.LTAG.Tree (AuxTree(AuxTree), Tree(FNode, INode))
import           NLP.LTAG.Early3


jean :: Tree String String
jean = INode "N" [FNode "jean"]


dort :: Tree String String
dort = INode "S"
    [ INode "N" []
    , INode "V"
        [FNode "dort"] ]


aime :: Tree String String
aime = INode "S"
    [ INode "N" []
    , INode "V"
        [FNode "aime"]
    , INode "N" [] ]


souvent :: AuxTree String String
souvent = AuxTree (INode "V"
    [ INode "V" []
    , INode "Adv"
        [FNode "souvent"] ]
    ) [0]


nePas :: AuxTree String String
nePas = AuxTree (INode "V"
    [ FNode "ne"
    , INode "V" []
    , FNode "pas" ]
    ) [1]


treeRules' :: Tree String String -> IO ()
treeRules' = mapM_ print . snd . runRM . treeRules True


auxRules' :: AuxTree String String -> IO ()
auxRules' = mapM_ print . snd . runRM . auxRules True


testGram :: [String] -> IO ()
testGram sent = do
    -- xs <- S.toList <$> earley gram sent
    -- mapM_ print $ sortBy (comparing ((-) <$> end <*> beg)) xs
    void $ earley gram sent
--     mapM_ print $ S.toList gram
  where
    gram = S.fromList $ snd $ runRM $ do
        mapM_ (treeRules True) [jean, dort, aime]
        mapM_ (auxRules True) [souvent, nePas]
