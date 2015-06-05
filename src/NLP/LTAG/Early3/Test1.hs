module NLP.LTAG.Early3.Test1 where


import qualified Data.IntMap as I

import           NLP.LTAG.Tree (AuxTree(AuxTree), Tree(FNode, INode))
import           NLP.LTAG.Early3.Rule


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
treeRules' = mapM_ print . snd . runRM . treeRules False


auxRules' :: AuxTree String String -> IO ()
auxRules' = mapM_ print . snd . runRM . auxRules False
