{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards  #-}


-- | Abstract implementation of an automaton (or a set of automata,
-- in general).  `Auto` provides a minimal interface needed to
-- use automata in parsing and thus allows to use one of the
-- concrete implementations provided by the library:
--
--  * "NLP.Partage.Auto.DAWG": directed acyclic word graph
--  * "NLP.Partage.Auto.Trie": prefix tree
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

-- * Utilities
, allIDs
, allEdges
) where


import           Control.Monad              (msum)
import qualified Control.Monad.State.Strict as E

import qualified Data.Set                   as S

import           Data.DAWG.Ord              (ID)
import           NLP.Partage.DAG            (DID (..), Rule (..))


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
    { roots  :: S.Set ID
    -- ^ Set of automata roots
    , follow :: ID -> a -> Maybe ID
    -- ^ Follow a transition with the given symbol from the given node
    , edges  :: ID -> [(a, ID)]
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
-- Utils
--------------------------------------------------


-- | Error messange on Nothing.
check :: String -> Maybe a -> a
check e Nothing  = error e
check _ (Just x) = x
