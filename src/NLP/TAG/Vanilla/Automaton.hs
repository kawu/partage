{-# LANGUAGE RecordWildCards #-}


-- | Automaton-based grammar representation.


module NLP.TAG.Vanilla.Automaton where


import qualified Data.Set                   as S

import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.TAG.Vanilla.Rule
    ( Lab(..), Rule(..) )


-- | A datatype to distinguish root non-terminals from body
-- non-terminals.
data Edge a
    = Root a
    | Body a
    deriving (Show, Eq, Ord)


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
    [ map Body bodyR ++ [Root headR]
    | Rule{..} <- S.toList gram ]
