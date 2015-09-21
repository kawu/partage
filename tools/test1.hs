{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}



import           Prelude hiding ((^))
import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (void)
import qualified Control.Monad.State.Strict as E
import           System.Environment (getArgs)

import qualified Data.IntMap as I
import qualified Data.Set as S
import           Data.List (sortBy, intersperse)
import           Data.Ord (comparing)
import qualified Pipes as P
import qualified Pipes.Prelude as P

import qualified NLP.FeatureStructure.Tree as FS
import qualified NLP.FeatureStructure.AVM as A
import           NLP.FeatureStructure.AVM ((##))

import qualified NLP.LTAG.Tree2 as T
import qualified NLP.LTAG.GenTree as G
import           NLP.LTAG.Rule
import           NLP.LTAG.Earley5
import           NLP.LTAG.Earley5.Draw (drawState)

import           Diagrams.Prelude hiding ((##), (|>), end)
import           Diagrams.Backend.SVG.CmdLine


---------------------------------------------------------------------
-- AVM utilities
---------------------------------------------------------------------


type FN = FS.FN String String String


-- | An empty feature tree.
empty :: FS.FN i f a
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


type GenTr = G.GenTree String String String String String
-- type Tr = T.Tree String String String String String
-- type AuxTr = T.AuxTree String String String String String


-- | Make a regular interior or substitution node with empty feature
-- structures.
mkN :: n -> [G.GenTree n l i f a] -> G.GenTree n l i f a
mkN x = G.Node x empty empty . Just


-- -- | Make a regular interior or substitution node with non-empty
-- -- bottom feature structures.
-- mkB :: n -> FS.FN i f a -> [G.GenTree n l i f a] -> G.GenTree n l i f a
-- mkB x f = G.Node x empty empty . Just


-- | Make a foot node.
mkF :: n -> G.GenTree n l i f a
mkF x = G.Node x empty empty Nothing


-- | Make a leaf node.
mkL :: l -> G.GenTree n l i f a
mkL = G.Leaf


-- | Assign top FS.
top :: A.AVM i f a -> G.GenTree n l i f a -> G.GenTree n l i f a
top x n@G.Node{} = n { G.topFS = A.avm x }


-- | Assign bottom FS.
bot :: A.AVM i f a -> G.GenTree n l i f a -> G.GenTree n l i f a
bot x n@G.Node{} = n { G.botFS = A.avm x }


-- | Function application with reverse syntax.
(^$) :: a -> (a -> b) -> b
x ^$ f = f x
infixl 0 ^$


-- | Function composition (.) with reverse (left) associativity.
(^) :: (a -> b) -> (b -> c) -> (a -> c)
f ^ g = \x -> g (f x)
infixl 0 ^


-- | Function application ($) with reverse (left) associativity.
(|>) :: (a -> b) -> a -> b
f |> x = f x
infixl 0 |>


---------------------------------------------------------------------
-- Grammar Proper
---------------------------------------------------------------------


jean :: GenTr
jean = mkN "N"
    ^ bot ( do
        "det"   ## "+"
        "pers"  ## "3"
        "num"   ## "sing"
        "genre" ## "masc"
    ) |>
    [ mkL "Jean" ]


belle :: GenTr
belle = mkN "N"
    ^ bot ( do
        "modif" ## "+"
        "num"   ## "?x"
        "genre" ## "?y"
        "det"   ## "-"
    ) |>
    [ mkN "A"
        ^ top ( do
            "num"   ## "?x"
            "genre" ## "?y"
        )
        ^ bot ( do
            "num"   ## "sing"
            "genre" ## "fem"
        ) |>
        [ mkL "belle" ]
    , mkF "N"
        ^$ top ( do
            "num"   ## "?x"
            "genre" ## "?y"
            "det"   ## "-"
        )
    ]


beaucoup :: GenTr
beaucoup = mkN "V"
    ^ bot ( do
        "mode"  ## "?z"
        "num"   ## "?x"
        "pers"  ## "?y"
        "modif" ## "+"
    ) |>
    [ mkF "V"
      ^$ top ( do
          "mode"  ## "?z"
          "num"   ## "?x"
          "pers"  ## "?y" )
    , mkN "Adv"
        [ mkL "beaucoup" ]
    ]


dort :: GenTr
dort = mkN "P"
    [ mkN "N"
        ^ top ( do
          "num"     ## "?x"
          "pers"    ## "?y"
          "det"     ## "+" ) |> []
    , mkN "V"
        ^ top ( do
          "num"     ## "?x"
          "pers"    ## "?y"
        )
        ^ bot ( do
          "mode"    ## "ind"
          "pers"    ## "3"
          "num"     ## "sing"
        )
        |> [ mkL "dort" ]
    ]


main :: IO ()
main = do
    sent <- words <$> getContents
    rs <- flip E.evalStateT 0 $ P.toListM $ do
        mapM_ (getRules . G.toTree) [jean, belle, beaucoup, dort]
    let gram = S.fromList $ map compile rs
    -- The set of done states (entirely processed rules)
    done <- earley gram sent
    -- Sort the diagrams appropriately
    let doneSorted = sortBy (comparing sortKey) (S.toList done)
    -- Draw all the state diagrams
    let statDiags = flip map doneSorted $ \(StateE p) ->
            drawState p # centerY -- # showOrigin
        statDiags' = flip intersperse statDiags $ hrule 50
    mainWith (vcat' (with & sep .~ 10) statDiags' :: Diagram B)
  where
    getRules (Left x)  = treeRules True x
    getRules (Right x) = auxRules  True x
    sortKey (StateE p) = (end p, end p - beg p)


-- doTest = do
-- --     let x = beaucoup
-- --     print $ fmap T.auxTree $ G.toTree x
-- --     print $ fmap T.auxFoot $ G.toTree x
--     print $ G.toTree jean
