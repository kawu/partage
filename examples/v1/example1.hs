import           NLP.LTAG.V1
import qualified Data.Set as S


-- | The set of initial trees.
ltag :: LTAG String String
ltag = LTAG
    { startSym  = "S"
    , iniTrees  = S.fromList
        [ INode "S"
            [ FNode (Right "a")
            , INode "T"
                [ FNode (Right "a")
                , FNode (Right "b") ]
            , FNode (Right "b") ] ]
    , auxTrees  = S.fromList
        [ AuxTree (INode "T"
            [ INode "S"
                [ FNode (Right "a")
                , FNode (Left "T")
                , FNode (Right "b") ]
            , FNode (Right "a") ]) [0, 1]
        , AuxTree (INode "S"
            [ FNode (Right "a")
            , INode "T"
                [ FNode (Right "a")
                , FNode (Right "b") ]
            , FNode (Right "b") ]) [1, 0] ] }
