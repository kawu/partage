{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | Automaton-based grammar representation.


module NLP.TAG.Vanilla.Auto.DAWG where


import qualified Control.Monad.State.Strict as E
-- import           Control.Monad.Trans.Class (lift)

import qualified Data.Set                   as S

import           Data.DAWG.Ord (ID)
import qualified Data.DAWG.Ord              as D

import           NLP.TAG.Vanilla.Rule
    ( Lab(..), Rule(..) )


import qualified NLP.TAG.Vanilla.Auto.Mini as A
-- import qualified NLP.TAG.Vanilla.Auto.Shell as Sh
import           NLP.TAG.Vanilla.Auto.Edge (Edge(..))


--------------------------------------------------
-- Interface
--------------------------------------------------


-- -- | DAWG as automat with one parameter.
-- newtype Auto a = Auto { unAuto :: D.DAWG a () }


shell :: (Ord n, Ord t) => DAWG n t -> A.AutoR n t
shell d = A.Auto
    { roots  = S.singleton (D.root d)
    , follow = \i x ->  D.follow i x d
    , edges  = flip D.edges d }


-- | A composition of `shell` and `buildAuto`.
mkAuto :: (Ord n, Ord t) => S.Set (Rule n t) -> A.AutoR n t
mkAuto = shell . buildAuto


--------------------------------------------------
-- Implementation
--------------------------------------------------


-- | The automaton-based representation of a factorized TAG
-- grammar.  Transitions contain non-terminals belonging to body
-- non-terminals while values contain rule heads non-terminals.
-- type DAWG n t = D.DAWG (Lab n t) (Lab n t)

-- | The automaton-based representation of a factorized TAG
-- grammar.  Left transitions contain non-terminals belonging to
-- body non-terminals while Right transitions contain rule heads
-- non-terminals.
type DAWG n t = D.DAWG (Edge (Lab n t)) ()


-- | Build automaton from the given grammar.
buildAuto :: (Ord n, Ord t) => S.Set (Rule n t) -> DAWG n t
buildAuto gram = D.fromLang
    [ map Body bodyR ++ [Head headR]
    | Rule{..} <- S.toList gram ]


-- | Return the list of automaton transitions.
edges :: (Ord n, Ord t) => DAWG n t -> [(ID, Edge (Lab n t), ID)]
edges = S.toList . walk


-- | Traverse  the automaton and collect all the edges.
--
-- TODO: it is provided in the general case in the `Mini` module.
-- Remove the version below.
walk
    :: (Ord n, Ord t)
    => DAWG n t
    -> S.Set (ID, Edge (Lab n t), ID)
walk dawg =
    flip E.execState S.empty $
        flip E.evalStateT S.empty $
            doit (D.root dawg)
  where
    -- The embedded state serves to store the resulting set of
    -- transitions; the surface state serves to keep track of
    -- already visited nodes.
    doit i = do
        b <- E.gets $ S.member i
        E.when (not b) $ do
            E.modify $ S.insert i
            E.forM_ (D.edges i dawg) $ \(x, j) -> do
                E.lift . E.modify $ S.insert (i, x, j)
                doit j
