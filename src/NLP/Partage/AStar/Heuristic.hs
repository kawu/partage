{-# LANGUAGE CPP #-}


module NLP.Partage.AStar.Heuristic
(
#ifdef NewHeuristic
  module NLP.Partage.AStar.HeuristicNew
#else
  module NLP.Partage.AStar.HeuristicOld
#endif
) where

#ifdef NewHeuristic
import NLP.Partage.AStar.HeuristicNew
#else
import NLP.Partage.AStar.HeuristicOld
#endif
