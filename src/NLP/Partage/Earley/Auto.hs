{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}


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
import           Data.Maybe                  (maybeToList, mapMaybe, catMaybes)
import qualified Data.Set                    as S

import qualified Data.MemoCombinators        as Memo

import qualified NLP.Partage.Auto            as A

import           NLP.Partage.DAG             (DID(..))
import qualified NLP.Partage.DAG             as DAG
import qualified NLP.Partage.Tree.Other      as O

-- import qualified NLP.Partage.Earley.Comp     as C

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


-- | TODO: Write what `S.Set t` means.  Probably alternative (non-determinism),
-- i.e., that the terminal at a given position of the sentence is not uniquely
-- determined.
type DAG n t a = DAG.DAG (O.Node n (S.Set t)) a


-- | Local automaton type based on `A.GramAuto`.
data Auto n t = Auto
    { gramDAG  :: DAG n t () -- (C.Comp a)
    -- ^ The underlying grammar DAG
    , gramAuto :: A.GramAuto
    -- ^ The underlying grammar automaton
    , withBody :: M.Map DID (S.Set ID)
    -- ^ A data structure which, for each label, determines the set of automaton
    -- states from which this label goes out as a body transition.
    , termDID  :: M.Map t (S.Set DID)
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
    -- if one has a separate FSA/Trie for each map value!
    --
    -- <<< NEW 12.11.2018 >>>
    --
    -- Note that the new data structures defined below do not intergrate with
    -- the rest of the code very well.  In particular, the remaining code is
    -- rather abstract and does not assume that it is possible to uniquely
    -- deterine the position corresponding to a `DID`. Indeed, this does not
    -- work with grammar compression in general.
    --
    , anchorPos :: M.Map DID Int
    -- ^ A map which determines the position of the attachment of the tree with
    -- the given `DID`.
    , anchorPos' :: M.Map ID Int
    -- ^ A map which determines the position of the attachment of the tree with
    -- the given `ID`.

--     , headPos :: M.Map Int Int
--     -- ^ A map which tells what is the head of the given word.  Both `Int`s
--     -- refer to positions in the input sentence.
--     -- TODO: there is a `Pos` type defined, but in the `Base` module which
--     -- relies on the `Auto` module...

    -- <<< NEW 27.12.2018 >>>

    , headPos :: M.Map Int (M.Map Int DAG.Weight)
    -- ^ A map which tells what are the *potential* heads of the given word.
    -- For each such potential head, the corresponding arc (non-negative)
    -- weight is assigned.  Both `Int`s refer to positions in the input
    -- sentence.
    -- TODO: there is a `Pos` type defined, but in the `Base` module which
    -- relies on the `Auto` module...
    }


-- | Construct `Auto` based on the underlying `A.GramAuto`.
mkAuto
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n)
    => DAG n t w
    -> A.GramAuto
    -> M.Map t Int   -- ^ Position map
    -> M.Map Int (M.Map Int DAG.Weight) -- ^ Head map
    -> Auto n t
    -- -> IO Auto
mkAuto dag auto posMap hedMap = M.size lhsMap `seq`
  Auto
  { gramDAG  = dag'
  , gramAuto = auto
  , withBody = mkWithBody auto
  , termDID  = mkTermDID dag'
  , footDID  = mkFootDID dag'
  , leafDID  = mkLeafDID dag'
  , lhsNonTerm = lhsMap
  , anchorPos = ancPos
  , anchorPos' = ancPos'
  , headPos = hedMap
  }
  where
    dag' = fmap (const ()) dag
    lhsMap = mkLhsNonTerm dag' auto
    (ancPos, ancPos') = mkAnchorPos dag' auto posMap


-- | Create the `withBody` component based on the automaton.
mkWithBody :: A.GramAuto -> M.Map DID (S.Set ID)
mkWithBody dag = M.fromListWith S.union
  [ (x, S.singleton i)
  | (i, A.Body x, _j) <- A.allEdges dag ]


-- | Create the `termDID` component.
mkTermDID
    :: (Ord t)
    => DAG n t w
    -> M.Map t (S.Set DID)
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
  -- -> M.Map ID DID
mkLhsNonTerm dag auto = M.fromList
  [ (i, pick $ lhs i)
  | i <- S.toList $ A.allIDs auto
  , (not . null) (A.edges auto i) ]
  where
    lhs = Memo.integral lhs'
    lhs' i = concat
      [ case edge of
          A.Head did -> [label did] -- [did]
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


-- | Create the `anchorPos` and `anchorPos'` components.
mkAnchorPos
  :: (Ord t)
  => DAG n t w
  -> A.GramAuto
  -> M.Map t Int   -- ^ Position map
  -> (M.Map DID Int, M.Map ID Int)
mkAnchorPos dag auto posMap = 

  (didRes, idRes)

  where
    
    idRes = M.fromList $ catMaybes
      [ (i,) <$> pick (idOn i)
      | i <- S.toList $ A.allIDs auto
      , (not . null) (A.edges auto i) ]
    didRes = M.fromList $ catMaybes
      [ (i,) <$> pick (didOn i)
      | i <- S.toList $ DAG.nodeSet dag ]

    idOn i = concat
      [ case edge of
          A.Head did -> didOn did
          A.Body did -> didOn did
      | (edge, _) <- A.edges auto i
      ]

    didOn = Memo.wrap DAG.DID DAG.unDID Memo.integral didOn'
    didOn' did =
      if DAG.isRoot did dag
         then down did 
         else concat
                [ didOn parDid
                | parDid <- S.toList $ DAG.parents did parMap
                ]

    down = Memo.wrap DAG.DID DAG.unDID Memo.integral down'
    down' did =
      case DAG.label did dag of
        Just (O.Term ts) -> nub . mapMaybe (flip M.lookup posMap) $ S.toList ts
        _ -> concat [down child | child <- DAG.children did dag]

    parMap = DAG.parentMap dag

    pick xs =
      case xs of
        [x] -> Just x
        [] -> Nothing
        _ -> error $ "Auto.mkAnchorPos: multiple choices -- " ++ show xs
        -- _ -> Nothing


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | Remove duplicates.
nub :: Ord a => [a] -> [a]
nub = S.toList . S.fromList
