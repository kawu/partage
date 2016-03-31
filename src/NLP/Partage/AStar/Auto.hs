{-# LANGUAGE Rank2Types      #-}


-- | Internal automaton data type which, aparat from the automaton itself,
-- contains several other components needed for parsing.


module NLP.Partage.AStar.Auto
( Auto(..)
, mkAuto
) where


import           Data.DAWG.Ord               (ID)
import qualified Data.Map.Strict             as M
import           Data.Maybe                  (maybeToList)
import qualified Data.MemoCombinators        as Memo
import qualified Data.Set                    as S

import qualified NLP.Partage.Auto            as A

import qualified NLP.Partage.AStar.Heuristic as H
-- import qualified NLP.Partage.AStar.Heuristic.Base as H
import qualified NLP.Partage.Auto.WeiTrie    as Trie
import           NLP.Partage.DAG             (DAG, DID, Gram, Weight)
import qualified NLP.Partage.DAG             as DAG
import qualified NLP.Partage.Tree.Other      as O


--------------------------------------------------
-- Local trie type
--------------------------------------------------


-- | Local automaton type based on `A.GramAuto`.
data Auto n t = Auto
    { gramDAG  :: DAG (O.Node n t) Weight
    -- ^ The underlying grammar DAG; the weights must be consistent
    -- with what is in the `gramAuto`
    , isSpine  :: DID -> Bool
    -- ^ Is the given DAG node a spine node?
    , gramAuto :: A.WeiGramAuto n t
    -- ^ The underlying grammar automaton
    , withBody :: M.Map DID (S.Set ID)
    -- , withBody  :: H.CuckooHashTable (Lab n t) (S.Set ID)
    -- ^ A data structure which, for each label, determines the
    -- set of automaton states from which this label goes out
    -- as a body transition.
    -- , termWei  :: M.Map t Weight
    -- ^ The lower bound estimates on reading terminal weights.
    -- Based on the idea that weights of the elementary trees are
    -- evenly distributed over its terminals.
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
    -- non-terminals.  Note that each grammar foot non-terminal
    -- is represented by exactly one grammar DAG node.
    , estiCost :: H.Esti t
    -- ^ Heuristic estimations.
    --
    -- TODO: Consider using hashtables to reresent termDID and
    -- footDID.
    }


-- | Construct `Auto` based on the weighted grammar.
mkAuto
  -- :: (Hashable t, Ord t, Hashable n, Ord n)
  :: (Ord t, Ord n)
  => Memo.Memo t        -- ^ Memoization strategy for terminals
  -> Gram n t
  -> Auto n t
mkAuto memoTerm gram =
    let auto = Trie.fromGram (DAG.factGram gram)
        -- dag0 = DAG.dagGram gram
        dag = DAG.dagGram gram
        -- here we need the DAG with injected weights because
        -- afterwards we use it to compute heuristic's values
        -- dag  = Inj.injectWeights auto dag0
    in  Auto
        { gramDAG  = dag
        , isSpine  = DAG.isSpine dag
        , gramAuto = auto
        , withBody = mkWithBody auto
        -- , termWei  = DAG.termWei gram
        , termDID  = mkTermDID dag
        , footDID  = mkFootDID dag
        , leafDID  = mkLeafDID dag
        , estiCost = H.mkEsti memoTerm gram auto }


-- | Create the `withBody` component based on the automaton.
mkWithBody
    :: A.WeiGramAuto n t
    -> M.Map DID (S.Set ID)
mkWithBody dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | (i, A.Body x, _j) <- A.allEdges (A.fromWei dag) ]


-- | Create the `termDID` component of the hypergraph.
mkTermDID
    :: (Ord t)
    => DAG (O.Node n t) w
    -> M.Map t DID
mkTermDID dag = M.fromList
    [ (t, i)
    | i <- S.toList (DAG.nodeSet dag)
    , O.Term t <- maybeToList (DAG.label i dag) ]


-- | Create the `footDID` component of the hypergraph.
mkFootDID
    :: (Ord n)
    => DAG (O.Node n t) w
    -> M.Map n DID
mkFootDID dag = M.fromList
    [ (x, i)
    | i <- S.toList (DAG.nodeSet dag)
    , O.Foot x <- maybeToList (DAG.label i dag) ]


-- | Create the `leafDID` component of the hypergraph.
mkLeafDID
    :: (Ord n)
    => DAG (O.Node n t) w
    -> M.Map n DID
mkLeafDID dag = M.fromList
    [ (x, i)
    | i <- S.toList (DAG.nodeSet dag)
    , DAG.isLeaf i dag
    , O.NonTerm x <- maybeToList (DAG.label i dag) ]
