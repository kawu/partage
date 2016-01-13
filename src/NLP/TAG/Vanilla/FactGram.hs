{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | TAG conversion into flat production rules.


module NLP.TAG.Vanilla.FactGram
(
-- * Factorized grammar
  FactGram
, Rule (..)
, Lab (..)

-- * Grammar flattening
, flattenNoSharing
, flattenWithSharing
) where


import           NLP.TAG.Vanilla.FactGram.Internal
import           NLP.TAG.Vanilla.SubtreeSharing
