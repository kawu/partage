import           NLP.LTAG.V1
import qualified Data.Set as S


-- | The set of initial trees.
ltag :: LTAG String String
ltag = LTAG
    { startSym = "S"
    , iniTrees = S.fromList
        [ INode "S"
            [ FNode (Right "e") ] ]
    , auxTrees  = S.fromList
        [ AuxTree (INode "S"
            [ FNode (Right "a")
            , INode "T"
                [ FNode (Right "S")
                , FNode (Right "b") ] ]) [1, 0]
        , AuxTree (INode "T"
            [ FNode (Right "a")
            , INode "S"
                [ FNode (Right "T")
                , FNode (Right "b") ] ]) [1, 0] ] }
