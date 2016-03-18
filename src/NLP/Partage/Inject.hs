{-# LANGUAGE RecordWildCards #-}


module NLP.Partage.Inject
( injectWeights
, weights
) where


import Control.Monad (msum)
import qualified Data.Set               as S
import qualified Data.Map.Strict               as M

import qualified NLP.Partage.Auto              as A
import qualified NLP.Partage.FactGram.DAG      as D
import qualified NLP.Partage.FactGram.Weighted as W
import qualified NLP.Partage.Tree.Other        as O


 -- | Inject weights from automaton back to the underlying DAG.
injectWeights
  :: A.WeiGramAuto n t
  -> D.DAG (O.Node n t) w
  -> D.DAG (O.Node n t) W.Weight
injectWeights auto dag =
  dag {D.nodeMap = nodeMap}
  where
    nodeMap = M.fromList
      [ (i, mkNode i n)
      | (i, n) <- M.toList (D.nodeMap dag) ]
    -- mkNode i n =
    mkNode i n
      | D.isLeaf i dag =
          n {D.nodeValue = 0, D.nodeEdges = []}
      | otherwise = embed (weights (mkRule i) auto) n
    mkRule i = map A.Body (D.children i dag) ++ [A.Head i]
    embed ws n = case reverse ws of
      [] -> error "embed: empty list"
      headW : bodyW -> n
        { D.nodeValue = headW
        , D.nodeEdges =
            [ (i, w)
            | ((i, _), w) <-
              zip (D.nodeEdges n) bodyW ]
        }


-- | Retrieve the weights of the given path in the automaton.
weights :: [a] -> A.WeiAuto a -> [W.Weight]
weights path A.WeiAuto{..} =
  check "weights: no such path" $ msum
    [ go i path
    | i <- S.toList rootsWei ]
  where
    go i (x : xs) = do
      (w, j) <- followWei i x
      ws <- go j xs
      return (w : ws)
    go _ [] = Just []


-- | Error messange on Nothing.
check :: String -> Maybe a -> a
check e Nothing  = error e
check _ (Just x) = x
