{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}


-- | TAG conversion into flat production rules.


module NLP.Partage.FactGram
(
-- * Factorized grammar
  FactGram
, Rule (..)
, Lab (..)

-- * Grammar flattening
, flattenNoSharing
, flattenWithSharing
) where


import           NLP.Partage.FactGram.Internal
import           NLP.Partage.SubtreeSharing
