{-# LANGUAGE Rank2Types      #-}


-- | Internal automaton data type which, apart from the automaton itself,
-- contains several other components useful for parsing.


module NLP.Partage.Earley.Auto
( Auto(..)
, mkAuto

-- * Core
, NotFoot(..)
) where


-- import           Control.Monad ((>=>))
import           Data.DAWG.Ord               (ID)
import qualified Data.Map.Strict             as M
import           Data.Maybe                  (maybeToList)
import qualified Data.Set                    as S

import qualified Data.MemoCombinators    as Memo

import qualified NLP.Partage.Auto            as A

import           NLP.Partage.DAG             (DID(..))
import qualified NLP.Partage.DAG             as DAG
import qualified NLP.Partage.Tree.Other      as O

-- import Debug.Trace (trace)


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


-- | Each leaf contains a set of `Maybe t`s, which corresponds to the
-- possibility of representing (i) non-determinism and (ii) empty terminal
-- symbols.
type DAG n t w =
  DAG.DAG
    (O.Node n (S.Set (Maybe t)))
    w


-- | Local automaton type based on `A.GramAuto`.
data Auto n t = Auto
    { gramDAG  :: DAG n t ()
    -- ^ The underlying grammar DAG
    , gramAuto :: A.GramAuto
    -- ^ The underlying grammar automaton
    , withBody :: M.Map DID (S.Set ID)
    -- ^ A data structure which, for each label, determines the set of automaton
    -- states from which this label goes out as a body transition.
    , termDID  :: M.Map (Maybe t) (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding terminals.
    --
    -- NOTE: There can be actually many DAG IDs corresponding to a given
    -- terminal even with subtree sharing turned on, which is related to
    -- non-determinism at the level of terminals (see `gramDAG`).
    --
    , footDID  :: M.Map n (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding foot non-terminals.
    --
    -- NOTE: With subtree sharing, there should be one DAG ID corresponding to
    -- any given foot. This note applies to `leafDID` as well.
    --
    , leafDID  :: M.Map n (S.Set DID)
    -- ^ A map which assigns DAG IDs to the corresponding leaf non-terminals.
    , lhsNonTerm :: M.Map ID (NotFoot n)
    -- ^ A map which uniquely determines the LHS corresponding to the rule
    -- containing the given ID. WARNING: The LHS can be uniquely determined only
    -- if one has a separate FSA/Trie for each such non-terminal!
    }


-- | Construct `Auto` based on the underlying `A.GramAuto`.
mkAuto
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n)
    => DAG n t w
    -> A.GramAuto
    -> Auto n t
    -- -> IO Auto
mkAuto dag auto = M.size lhsMap `seq`
  Auto
  { gramDAG  = dag'
  , gramAuto = auto
  , withBody = mkWithBody auto
  , termDID  = mkTermDID dag'
  , footDID  = mkFootDID dag'
  , leafDID  = mkLeafDID dag'
  , lhsNonTerm = lhsMap
  }
  where
    dag' = fmap (const ()) dag
    lhsMap = mkLhsNonTerm dag' auto


-- | Create the `withBody` component based on the automaton.
mkWithBody :: A.GramAuto -> M.Map DID (S.Set ID)
mkWithBody dag = M.fromListWith S.union
  [ (x, S.singleton i)
  | (i, A.Body x, _j) <- A.allEdges dag ]


-- | Create the `termDID` component.
mkTermDID
    :: (Ord t)
    => DAG n t w
    -> M.Map (Maybe t) (S.Set DID)
mkTermDID dag = M.fromListWith S.union
    [ (t, S.singleton i)
    | i <- S.toList (DAG.nodeSet dag)
    , O.Term ts <- maybeToList (DAG.label i dag)
    , t <- S.toList ts
    ]


-- | Create the `footDID` component.
mkFootDID
    :: (Ord n)
    => DAG n t w
    -> M.Map n (S.Set DID)
mkFootDID dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | i <- S.toList (DAG.nodeSet dag)
    , O.Foot x <- maybeToList (DAG.label i dag) ]


-- | Create the `leafDID` component.
mkLeafDID
    :: (Ord n)
    => DAG n t w
    -> M.Map n (S.Set DID)
mkLeafDID dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | i <- S.toList (DAG.nodeSet dag)
    , DAG.isLeaf i dag
    , O.NonTerm x <- maybeToList (DAG.label i dag) ]


-- | Create the `lhsNonTerm` component.
mkLhsNonTerm
  :: DAG n t w
  -> A.GramAuto
  -> M.Map ID (NotFoot n)
mkLhsNonTerm dag auto = M.fromList
  [ (i, pick $ lhs i)
  | i <- S.toList $ A.allIDs auto
  , (not . null) (A.edges auto i) ]
  where
    -- lhs = Memo.wrap DID unDID Memo.integral lhs'
    lhs = Memo.integral lhs'
    lhs' i = concat
      [ case edge of
          A.Head did -> [label did]
          A.Body _ -> lhs j
      | (edge, j) <- A.edges auto i
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
