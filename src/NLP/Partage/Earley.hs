-- | Earley-style TAG parsing based on automata, with a distinction
-- between active and passive items.


module NLP.Partage.Earley
(
-- * Earley-style parsing
  Input (..)
, fromList
, fromSets
-- ** With a factorized grammar
-- $earley
-- , recognize
, recognizeFrom
, parse
, earley
-- ** With automata precompiled
-- , recognizeAuto
, recognizeFromAuto
, parseAuto
, earleyAuto
-- ** Automaton
, Auto
, mkAuto

-- * Parsing trace (hypergraph)
, Hype
-- ** Extracting parsed trees
, parsedTrees
-- ** Stats
, hyperNodesNum
, hyperEdgesNum
-- -- ** Printing
-- , printHype
) where


import           NLP.Partage.Earley.Parser

{- $earley
  All the parsing functions described in this section transform the
  input factorized grammar into the "NLP.Partage.Auto.DAWG" grammar
  representation.
  You can also pre-compile your own automaton and use it with
  e.g. `parseAuto`.
-}
