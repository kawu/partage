-- | Earley-style TAG parsing based on automata, with a distinction
-- between active and passive items.


module NLP.TAG.Vanilla.Earley
(
-- * Earley-style parsing
-- $earley
  recognize
, recognizeFrom
, parse
, earley
-- ** With automata precompiled
, recognizeAuto
, recognizeFromAuto
, parseAuto
, earleyAuto

-- * Parsing trace (hypergraph)
, EarSt
-- ** Extracting parsed trees
, parsedTrees
-- ** Stats
, hyperNodesNum
, hyperEdgesNum
-- ** Printing
, printHype
) where


import           NLP.TAG.Vanilla.Earley.AutoAP

{- $earley
  All the parsing functions described below employ the 
  "NLP.TAG.Vanilla.Auto.DAWG" grammar representation.
  You can also pre-compile your own automaton and use it with
  e.g. `parseAuto`.
-}
