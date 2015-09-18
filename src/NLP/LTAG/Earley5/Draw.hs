{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | A module which allows to draw parsing states under the form
-- of diagrams (and using precisely the "diagrams" framework).


module NLP.LTAG.Earley5.Draw where


-- import qualified Data.Set as S
-- import qualified Data.Map.Strict as M
-- import qualified Control.Monad.State.Strict as ST
import           Data.List (intersperse)


import           Diagrams.Prelude hiding (gap, end)
import           Data.String.ToString (toString, ToString)


import qualified NLP.FeatureStructure.Graph as FS
import qualified NLP.FeatureStructure.Graph.Draw as D


import           NLP.LTAG.Core
import           NLP.LTAG.Earley5 (Lab(..), State(..))


-- | Construct a diagram from a label witin the context of the
-- given graph.
drawLab
    :: ( VOrd i, Ord f, ToString f
       , ToString a, ToString n, ToString t
       , Renderable (Path V2 Double) b )
    => FS.Graph i f a
    -> Lab n t i
    -> D.Diag i (QDiagram b V2 Double Any)
drawLab graph NonT{..} = do
    let nt = D.drawText' labelSize black $ toString nonTerm ++ case labID of
            Nothing -> ""
            Just x  -> "(" ++ show x ++ ")"
    tp <- D.drawNode graph topID
    bt <- D.drawNode graph botID
    return $ nt ||| ((tp === bt) # centerY)
drawLab _graph (Term t) = return $
    D.drawText' labelSize black $ "\"" ++ toString t ++ "\""
drawLab graph AuxRoot{..} = do
    let nt = D.drawText' labelSize black $ toString nonTerm
    tp  <- D.drawNode graph topID
    bt  <- D.drawNode graph botID
    ftp <- D.drawNode graph topID
    fbt <- D.drawNode graph botID
    return $ nt ||| (((tp === bt) ||| (ftp === fbt)) # centerY)
drawLab _graph AuxFoot{..} = return $
    D.drawText' labelSize black $ toString nonTerm
drawLab graph AuxVert{..} = do
    let nt = D.drawText' labelSize black $ toString nonTerm ++ "(" ++ show symID ++ ")"
    tp <- D.drawNode graph topID
    bt <- D.drawNode graph botID
    return $ nt ||| ((tp === bt) # centerY)


-- | Construct a diagram from a given state.
drawState
    :: ( VOrd i, Ord f, ToString f
       , ToString a, ToString n, ToString t
       , Renderable (Path V2 Double) b )
    => State n t i f a
    -- -> FS.Diag i (QDiagram b V2 Double Any)
    -> QDiagram b V2 Double Any
drawState State{..} = D.runDiag $ do
    rootDiag  <- drawLab' root
    leftDiag  <- mapM drawLab' left
    rightDiag <- mapM drawLab' right
    return $ hcat' (with & sep .~ 5) $ 
        [ rootDiag, D.drawText' labelSize black "->"
        , hcat (divide leftDiag)
        , circle 3 # fc black # lw none
        , hcat (divide rightDiag) ]
  where
    drawLab' = drawLab graph
--     drawLab' x = do
--         y <- drawLab graph x
--         return $ y # centerXY # showOrigin
    divide = intersperse $ strutX 5
    -- vrule 20


--------------------------
-- Utilities
--------------------------


-- | Label (non-)terminal size. 
labelSize :: Double
labelSize = 1.5 * D.featSize
