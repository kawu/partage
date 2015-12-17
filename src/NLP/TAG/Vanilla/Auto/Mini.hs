{-# LANGUAGE RecordWildCards      #-}


-- | Automaton -- minimal implementation.


module NLP.TAG.Vanilla.Auto.Mini
( Auto (..)
, allIDs
, allEdges
, AutoR
) where


import qualified Control.Monad.State.Strict as E

import qualified Data.Set                   as S

import           Data.DAWG.Gen.Types (ID)
import           NLP.TAG.Vanilla.Rule (Lab(..))
import           NLP.TAG.Vanilla.Auto.Edge (Edge(..))


-- | Minimal automaton implementation.
-- Multiple roots are allowed in order to account for
-- list implementation of an automaton.
data Auto a = Auto
    { roots     :: S.Set ID
    -- ^ Root node
    , follow    :: ID -> a -> Maybe ID
    -- ^ Follow the given symbol from the given node
    , edges     :: ID -> [(a, ID)]
    -- ^ List of outgoing edges
    }


-- | Automaton type specialized to represent grammar rules.
type AutoR n t = Auto (Edge (Lab n t))


-- | Extract the set of underlying IDs.
allIDs :: Ord a => Auto a -> S.Set ID
allIDs d = S.fromList $ concat
    [[i, j] | (i, _, j) <- allEdges d]


-- | Return the list of automaton transitions.
allEdges :: Ord a => Auto a -> [(ID, a, ID)]
allEdges = S.toList . traverse


-- | Traverse  the automaton and collect all the edges.
traverse :: Ord a => Auto a -> S.Set (ID, a, ID)
traverse Auto{..} =
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
