{-# LANGUAGE Rank2Types      #-}


-- | Internal automaton data type which, aparat from the automaton itself,
-- contains several other components needed for parsing.


module NLP.Partage.AStar.Auto
( Auto(..)
, mkAuto

-- * Core
, NotFoot(..)
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
import qualified NLP.Partage.Auto.WeiSet     as WS
import           NLP.Partage.DAG             (DAG, DID, Gram, Weight)
import qualified NLP.Partage.DAG             as DAG
import qualified NLP.Partage.Tree.Other      as O


--------------------------------------------------
-- Core (TODO: Should be moved out of here?
--   Besides, it's also a copy of what is in
--   Early.Auto).
--------------------------------------------------


-- | Non-terminal which is not a foot.
data NotFoot n = NotFoot
  { notFootLabel :: n
    -- ^ The corresponding non-terminal
  , isSister :: Bool
    -- ^ Is the non-terminal marked for sister-adjunction?
  } deriving (Show, Eq, Ord)


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
    -- ^ A data structure which, for each label, determines the set of automaton
    -- states from which this label goes out as a body transition.
    -- , termWei  :: M.Map t Weight
    -- ^ The lower bound estimates on reading terminal weights. Based on the
    -- idea that weights of the elementary trees are evenly distributed over its
    -- terminals.
    , termDID  :: M.Map t (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding terminals. Note that
    -- each grammar terminal is represented by exactly one grammar DAG node.
    , footDID  :: M.Map n (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding foot non-terminals.
    -- Note that each grammar foot non-terminal is represented by exactly one
    -- grammar DAG node.
    , leafDID  :: M.Map n (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding leaf non-terminals.
    -- Note that each grammar leaf non-terminal is represented by exactly one
    -- grammar DAG node.
    , estiCost :: H.Esti t
    -- ^ Heuristic estimations.
    , lhsNonTerm :: M.Map ID (NotFoot n)
    -- ^ A map which uniquely determines the LHS corresponding to the rule
    -- containing the given ID. WARNING: The LHS can be uniquely determined only
    -- if one has a separate FSA/Trie for each such non-terminal!
    }


-- | Construct `Auto` based on the weighted grammar.
mkAuto
  -- :: (Hashable t, Ord t, Hashable n, Ord n)
  :: (Ord t, Ord n)
  => Memo.Memo t        -- ^ Memoization strategy for terminals
  -> Gram n t
  -> Auto n t
mkAuto memoTerm gram =
    let auto = WS.fromGram Trie.fromGram (DAG.factGram gram)
        dag = DAG.dagGram gram
        lhsMap = mkLhsNonTerm dag auto
    in  Auto
        { gramDAG  = dag
        , isSpine  = DAG.isSpine dag
        , gramAuto = auto
        , withBody = mkWithBody auto
        -- , termWei  = DAG.termWei gram
        , termDID  = mkTermDID dag
        , footDID  = mkFootDID dag
        , leafDID  = mkLeafDID dag
        , estiCost = H.mkEsti memoTerm gram auto
        , lhsNonTerm = lhsMap
        }


-- TODO: the code below is a copy of the code in 'Early.Auto'!


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


-- | Create the `lhsNonTerm` component.
mkLhsNonTerm
  :: DAG (O.Node n t) w
  -> A.WeiGramAuto n t
  -> M.Map ID (NotFoot n)
mkLhsNonTerm dag auto = M.fromList
  [ (i, pick $ lhs i)
  | i <- S.toList $ A.allIDs (A.fromWei auto)
  , (not . null) (A.edgesWei auto i) ]
  where
    -- lhs = Memo.wrap DID unDID Memo.integral lhs'
    lhs = Memo.integral lhs'
    lhs' i = concat
      [ case edge of
          A.Head did -> [label did]
          A.Body _ -> lhs j
      | (edge, _, j) <- A.edgesWei auto i
      ]
    label did =
      case DAG.label did dag >>= labNonTerm of
        Just x -> x
        Nothing -> error "Auto.mkLhsNonTerm: unknown DID"
    pick xs =
      case xs of
        [x] -> x
        _ -> error "Auto.mkLhsNonTerm: multiple LHS non-terminals per DID"
    labNonTerm (O.NonTerm y) = Just $ NotFoot
      { notFootLabel = y
      , isSister = False }
    labNonTerm (O.Sister y) = Just $ NotFoot
      { notFootLabel = y
      , isSister = True }
    labNonTerm _ = Nothing
