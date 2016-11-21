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
import qualified NLP.Partage.Tree.Comp       as C


--------------------------------------------------
-- Local trie type
--------------------------------------------------


-- | Local automaton type based on `A.GramAuto`.
data Auto n t a = Auto
    { gramDAG  :: DAG (O.Node n t) (C.Comp a)
    -- ^ The underlying grammar DAG; computations should be assigned
    -- only to root nodes.
    , gramAuto :: A.GramAuto
    -- ^ The underlying grammar automaton
    , withBody :: M.Map DID (S.Set ID)
    -- ^ A data structure which, for each label, determines the
    -- set of automaton states from which this label goes out
    -- as a body transition.
    , termDID  :: M.Map t DID
    -- ^ A map which assigns DAG IDs to the corresponding terminals.
    -- Note that each grammar terminal is represented by exactly
    -- one grammar DAG node.
    , footDID  :: M.Map n DID
    -- ^ A map which assigns DAG IDs to the corresponding foot
    -- non-terminals.  Note that each grammar foot non-terminal
    -- is represented by exactly one grammar DAG node.
    , leafDID  :: M.Map n DID
    -- ^ A map which assigns DAG IDs to the corresponding leaf
    -- non-terminals.  Note that each grammar leaf non-terminal
    -- is represented by exactly one grammar DAG node.
    --
    -- TODO: Consider using hashtables to reresent termDID and
    -- footDID.
    }


-- | Construct `Auto` based on the underlying `A.GramAuto`.
mkAuto
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n)
    => DAG (O.Node n t) (C.Comp a)
    -> A.GramAuto
    -> Auto n t a
    -- -> IO Auto
mkAuto dag auto = Auto
    { gramDAG  = dag
    , gramAuto = auto
    , withBody = mkWithBody auto
    , termDID  = mkTermDID dag
    , footDID  = mkFootDID dag
    , leafDID  = mkLeafDID dag }


-- | Create the `withBody` component based on the automaton.
mkWithBody :: A.GramAuto -> M.Map DID (S.Set ID)
mkWithBody dag = M.fromListWith S.union
  [ (x, S.singleton i)
  | (i, A.Body x, _j) <- A.allEdges dag ]


-- | Create the `termDID` component of the hypergraph.
mkTermDID
    :: (Ord t)
    => DAG (O.Node n t) w
    -> M.Map t DID
mkTermDID dag = M.fromListWith
  (const $ error "Auto.mkTermDID: multiple nodes")
  -- the error above is related to the assumption of the parser that
  -- there is at most one DAG node with a given terminal; the same
  -- applies to `mkFootDID` and `mkLeafDID`
    [ (t, i)
    | i <- S.toList (DAG.nodeSet dag)
    , O.Term t <- maybeToList (DAG.label i dag) ]


-- | Create the `footDID` component of the hypergraph.
mkFootDID
    :: (Ord n)
    => DAG (O.Node n t) w
    -> M.Map n DID
mkFootDID dag = M.fromListWith
  (const $ error "Auto.mkFootDID: multiple nodes")
    [ (x, i)
    | i <- S.toList (DAG.nodeSet dag)
    , O.Foot x <- maybeToList (DAG.label i dag) ]


-- | Create the `leafDID` component of the hypergraph.
mkLeafDID
    :: (Ord n)
    => DAG (O.Node n t) w
    -> M.Map n DID
mkLeafDID dag = M.fromListWith
  (const $ error "Auto.mkLeafDID: multiple nodes")
    [ (x, i)
    | i <- S.toList (DAG.nodeSet dag)
    , DAG.isLeaf i dag
    , O.NonTerm x <- maybeToList (DAG.label i dag) ]
