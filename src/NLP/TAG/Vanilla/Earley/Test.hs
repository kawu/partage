{-# LANGUAGE OverloadedStrings #-}


module NLP.TAG.Vanilla.Early.Test where


import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (void, forM_)
import qualified Control.Monad.State.Strict as E

import qualified Data.IntMap as I
import qualified Data.Set as S
import           Data.List (sortBy)
import           Data.Ord (comparing)
import qualified Pipes as P
import qualified Pipes.Prelude as P

import           NLP.TAG.Vanilla.Tree
import           NLP.TAG.Vanilla.Rule
import           NLP.TAG.Vanilla.Earley



---------------------------------------------------------------------
-- Grammar
---------------------------------------------------------------------


type Tr = Tree String String
type AuxTr = AuxTree String String


-- tom :: Tr
-- tom = INode "NP"
--         [FNode "Tom"]

tom :: Tr
tom = INode "NP"
    [ INode "N"
        [FNode "Tom"]
    ]


sleeps :: Tr
sleeps = INode "S"
    [ INode "NP" []
    , INode "VP"
        [INode "V" [FNode "sleeps"]]
    ]


caught :: Tr
caught = INode "S"
    [ INode "NP" []
    , INode "VP"
        [ INode "V" [FNode "caught"]
        , INode "NP" [] ]
    ]


almost :: AuxTr
almost = AuxTree (INode "V"
    [ INode "Ad" [FNode "almost"]
    , INode "V" []
    ]) [1]


a :: Tr
a = INode "D" [FNode "a"]


mouse :: Tr
mouse = INode "NP"
    [ INode "D" []
    , INode "N"
        [FNode "mouse"]
    ]


testGram :: [String] -> IO ()
testGram sent = do
    rs <- flip E.evalStateT 0 $ P.toListM $ do
        -- mapM_ (treeRules True) [tom, sleeps, caught, a, mouse]
        mapM_ (treeRules True) [tom, caught]
        mapM_ (auxRules True) [almost]
    let gram = S.fromList rs
    void $ earley gram sent
    -- forM_ rs $ \r -> printRule r >> putStrLn ""
    -- return ()
