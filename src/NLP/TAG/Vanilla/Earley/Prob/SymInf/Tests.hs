{-# LANGUAGE OverloadedStrings #-}


module NLP.TAG.Vanilla.Earley.Prob.SymInf.Tests where


import qualified Data.Set as S

import           Test.Tasty (TestTree)

import qualified NLP.TAG.Vanilla.Earley.Prob.SymInf as E
import qualified NLP.TAG.Vanilla.Tree as E
import qualified NLP.TAG.Vanilla.Tests as T


-- | All the tests of the parsing algorithm.
tests :: TestTree
tests = T.testTree "NLP.TAG.Vanilla.Earley.Prob.SymInf"
    E.recognize (Just E.parse)
