{-# LANGUAGE Rank2Types      #-}


-- | Internal automaton data type which, aparat from the automaton itself,
-- contains several other components useful for parsing.


module NLP.Partage.Earley.Auto
( Auto(..)
, mkAuto
) where


import           Data.DAWG.Ord               (ID)
import qualified Data.Map.Strict             as M
import           Data.Maybe                  (maybeToList)
import qualified Data.Set                    as S

import qualified NLP.Partage.Auto            as A

import           NLP.Partage.DAG             (DAG, DID)
import qualified NLP.Partage.DAG             as DAG
import qualified NLP.Partage.Tree.Other      as O


--------------------------------------------------
-- Local trie type
--------------------------------------------------


-- | Local automaton type based on `A.GramAuto`.
data Auto n t = Auto
    { gramDAG  :: DAG (O.Node n t) ()
    -- ^ The underlying grammar DAG
    , gramAuto :: A.GramAuto
    -- ^ The underlying grammar automaton
    , withBody :: M.Map DID (S.Set ID)
    -- , withBody  :: H.CuckooHashTable (Lab n t) (S.Set ID)
    -- ^ A data structure which, for each label, determines the
    -- set of automaton states from which this label goes out
    -- as a body transition.
    , termDID  :: M.Map t (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding terminals.
    , footDID  :: M.Map n (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding foot
    -- non-terminals.
    , leafDID  :: M.Map n (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding leaf
    -- non-terminals.
    }


-- | Construct `Auto` based on the underlying `A.GramAuto`.
mkAuto
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n)
    => DAG (O.Node n t) w
    -> A.GramAuto
    -> Auto n t
    -- -> IO Auto
mkAuto dag auto = Auto
    { gramDAG  = dag'
    , gramAuto = auto
    , withBody = mkWithBody auto
    , termDID  = mkTermDID dag'
    , footDID  = mkFootDID dag'
    , leafDID  = mkLeafDID dag' }
    where dag' = fmap (const ()) dag


-- | Create the `withBody` component based on the automaton.
mkWithBody :: A.GramAuto -> M.Map DID (S.Set ID)
mkWithBody dag = M.fromListWith S.union
  [ (x, S.singleton i)
  | (i, A.Body x, _j) <- A.allEdges dag ]


-- | Create the `termDID` component of the hypergraph.
mkTermDID
    :: (Ord t)
    => DAG (O.Node n t) w
    -> M.Map t (S.Set DID)
mkTermDID dag = M.fromListWith S.union
    [ (t, S.singleton i)
    | i <- S.toList (DAG.nodeSet dag)
    , O.Term t <- maybeToList (DAG.label i dag) ]


-- | Create the `footDID` component of the hypergraph.
mkFootDID
    :: (Ord n)
    => DAG (O.Node n t) w
    -> M.Map n (S.Set DID)
mkFootDID dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | i <- S.toList (DAG.nodeSet dag)
    , O.Foot x <- maybeToList (DAG.label i dag) ]


-- | Create the `leafDID` component of the hypergraph.
mkLeafDID
    :: (Ord n)
    => DAG (O.Node n t) w
    -> M.Map n (S.Set DID)
mkLeafDID dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | i <- S.toList (DAG.nodeSet dag)
    , DAG.isLeaf i dag
    , O.NonTerm x <- maybeToList (DAG.label i dag) ]
