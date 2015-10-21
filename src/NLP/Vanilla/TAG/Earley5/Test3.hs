{-# LANGUAGE OverloadedStrings #-}


module NLP.LTAG.Early5.Test3 where


import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (void)
import qualified Control.Monad.State.Strict as E

import qualified Data.IntMap as I
import qualified Data.Set as S
import           Data.List (sortBy)
import           Data.Ord (comparing)
import qualified Pipes as P
import qualified Pipes.Prelude as P

import qualified NLP.FeatureStructure.Tree as FS
import qualified NLP.FeatureStructure.AVM as A

import           NLP.LTAG.Tree2
import           NLP.LTAG.Rule
import           NLP.LTAG.Earley5


---------------------------------------------------------------------
-- AVM utilities
---------------------------------------------------------------------


type FN = FS.FN String String String


-- | An empty feature tree.
empty :: FN
empty = A.avm A.empty


-- | Red attribute value.
red :: FN
red = A.avm $ A.feat "col" "red" 


-- | Black attribute value.
black :: FN
black = A.avm $ A.feat "col" "black" 


-- | Variable 'x' color.
colX :: FN
colX = A.avm $ A.feat "col" "?x"
-- colX = A.avm $ A.feat "col" $ A.empty


---------------------------------------------------------------------
-- Grammar
---------------------------------------------------------------------


type Tr = Tree String String String String String
type AuxTr = AuxTree String String String String String


alpha :: Tr
alpha = INode "S" colX empty
    [ LNode "p"
    , INode "X" colX empty
        [LNode "e"]
    , LNode "q" ]


beta1 :: AuxTr
beta1 = AuxTree (INode "X" red red
    [ LNode "a"
    , INode "X" empty empty
        [ INode "X" black black []
        , LNode "a" ] ]
    ) [1,0]


beta2 :: AuxTr
beta2 = AuxTree (INode "X" red red
    [ LNode "b"
    , INode "X" empty empty
        [ INode "X" black black []
        , LNode "b" ] ]
    ) [1,0]


testGram :: [String] -> IO ()
testGram sent = do
    rs <- flip E.evalStateT 0 $ P.toListM $ do
        mapM_ (treeRules True) [alpha]
        mapM_ (auxRules True) [beta1, beta2]
    let gram = S.fromList $ map compile rs
    void $ earley gram sent
