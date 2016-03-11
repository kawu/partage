{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | Abstract implementation of an automaton (or a set of automata,
-- in general).  `Auto` provides a minimal interface needed to
-- use automata in parsing and thus allows to use one of the
-- concrete implementations provided by the library:
--
--  * "NLP.Partage.Auto.DAWG": directed acyclic word graph
--  * "NLP.Partage.Auto.Trie": prefix tree
--  * "NLP.Partage.Auto.WeiTrie": weighted prefix tree
--  * "NLP.Partage.Auto.List": set of lists
--  * "NLP.Partage.Auto.Set": set of automata, one automaton per
--      `Head` non-terminal


module NLP.Partage.Auto
(
-- * Edge
  Edge (..)
, ruleSeq

-- * Automata
, Auto (..)
, GramAuto
-- ** Weighted
, WeiAuto (..)
, WeiGramAuto
-- ** Conversion
, fromWei
, toWei

-- * Utilities
, allIDs
, allEdges
) where


import qualified Control.Monad.State.Strict as E

import qualified Data.Set                   as S

import           Data.DAWG.Ord (ID)
import           NLP.Partage.FactGram.DAG (DID(..), Rule(..))
-- import qualified NLP.Partage.FactGram.DAG as DAG
import           NLP.Partage.FactGram.Weighted (Weight)


-- | A datatype used to distinguish head non-terminals from body
-- non-terminals in automata-based grammar representation.
data Edge a
    = Head a
    | Body a
    deriving (Show, Eq, Ord)


-- | Transform the rule into the corresponding sequence
-- (to be added to an automaton).
ruleSeq :: Rule -> [Edge DID]
ruleSeq Rule{..} = map Body bodyR ++ [Head headR]


-- | Minimal automaton implementation.
-- Multiple roots are allowed in order to account for
-- list implementation of an automaton.
data Auto a = Auto
    { roots     :: S.Set ID
    -- ^ Set of automata roots
    , follow    :: ID -> a -> Maybe ID
    -- ^ Follow a transition with the given symbol from the given node
    , edges     :: ID -> [(a, ID)]
    -- ^ List of outgoing edges (transitions)
    }


-- | Automaton type specialized to represent grammar rules.
type GramAuto = Auto (Edge DID)


-- | Extract the set of underlying IDs.
allIDs :: Ord a => Auto a -> S.Set ID
allIDs d = S.fromList $ concat
    [[i, j] | (i, _, j) <- allEdges d]


-- | Return the list of automaton transitions.
allEdges :: Ord a => Auto a -> [(ID, a, ID)]
allEdges = S.toList . walk


-- | Traverse  the automaton and collect all the edges.
walk :: Ord a => Auto a -> S.Set (ID, a, ID)
walk Auto{..} =
    flip E.execState S.empty $
        flip E.evalStateT S.empty $
            mapM_ doit (S.toList roots)
  where
    -- The embedded state serves to store the resulting set of
    -- transitions; the surface state serves to keep track of
    -- already visited nodes.
    doit i = do
        b <- E.gets $ S.member i
        E.when (not b) $ do
            E.modify $ S.insert i
            E.forM_ (edges i) $ \(x, j) -> do
                E.lift . E.modify $ S.insert (i, x, j)
                doit j


--------------------------------------------------
-- Weighted Automaton
--------------------------------------------------


-- | Minimal weighted automaton implementation.
data WeiAuto a = WeiAuto
    { rootsWei  :: S.Set ID
    -- ^ Set of automata roots
    , followWei :: ID -> a -> Maybe (Weight, ID)
    -- ^ Follow a transition with the given symbol from the given node
    , edgesWei  :: ID -> [(a, Weight, ID)]
    -- ^ List of outgoing edges (transitions)
    }


-- | Weighted automaton type specialized to represent grammar rules.
type WeiGramAuto n t = WeiAuto (Edge DID)


-- | Convert the weighted automaton to a regular one.
fromWei :: WeiAuto a -> Auto a
fromWei WeiAuto{..} = Auto
    { roots = rootsWei
    , follow = \i x -> do
        (_, j) <- followWei i x
        return j
    , edges = \i ->
        [(x, j) | (x, _, j) <- edgesWei i]
    }


-- | Convert the regular automaton to a weighted one with
-- all weights equal to 0.
toWei :: Auto a -> WeiAuto a
toWei Auto{..} = WeiAuto
    { rootsWei = roots
    , followWei = \i x -> do
        j <- follow i x
        return (0, j)
    , edgesWei = \i ->
        [(x, 0, j) | (x, j) <- edges i]
    }
