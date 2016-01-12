{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | TAG conversion into flat production rules.


module NLP.TAG.Vanilla.Rule
(
-- * Rule
  Rule (..)
, Lab (..)

-- * Grammar flattening
, compile
, compileWeights
) where


import           NLP.TAG.Vanilla.Rule.Internal
