{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}


-- | Testing the automata-based Earley-style TAG parser.


module Parser where


import           Control.Applicative ((<$>))
import           Control.Monad (forM_)
import           Test.Tasty (TestTree)

import qualified Data.Set as S

import qualified NLP.Partage.Earley as E

import qualified TestSet as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "Parser"
    recFrom (Just parseFrom)
  where
    recFrom gram start
        = E.recognizeFrom gram start
        . E.fromList
    parseFrom gram start
        = fmap S.fromList
        . E.parse gram start
        . E.fromList
