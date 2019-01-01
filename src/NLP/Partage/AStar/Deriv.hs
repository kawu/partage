{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}


module NLP.Partage.AStar.Deriv
( Deriv
, ModifDerivs
, DerivNode (..)
, derivTrees
, derivTreesW
, fromPassive
, normalize
, deriv4show
, encodes

-- , RevHype (..)
-- , DerivR (..)
-- , derivsPipe
-- -- , parseAndPrint

  -- * Provisional
, isFinal_
, consumeDerivs
) where


import           Control.Monad             (forM_, guard, guard, void, when)
import           Control.Arrow             (second)
-- import           Control.Monad.IO.Class    (MonadIO (..), liftIO)
import qualified Control.Monad.RWS.Strict  as RWS
-- import qualified Control.Monad.State.Strict as E
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (..))
import qualified Control.Monad.Morph       as Morph

import           Data.Lens.Light
import qualified Data.Map.Strict           as M
import           Data.Maybe                (maybeToList, isJust)
import qualified Data.PSQueue              as Q
import qualified Data.Set                  as S
import qualified Data.Tree                 as R
import qualified Data.List                 as L
import           Data.Either               (lefts, rights)
import           Data.Ord                  (comparing)
-- import qualified Data.Traversable           as Trav

import qualified Pipes                     as P
import           Pipes                     ((>->))
-- import qualified Pipes.Prelude              as P

import           NLP.Partage.SOrd          (SOrd)
import qualified NLP.Partage.DAG as DAG
import           NLP.Partage.AStar         (Tok)
import qualified NLP.Partage.AStar         as A
import qualified NLP.Partage.AStar.Base    as Base
import qualified NLP.Partage.AStar.Item    as Item
import qualified NLP.Partage.AStar.Auto    as Auto
import           NLP.Partage.DAG           (Weight)
import qualified NLP.Partage.Tree.Other    as O

import Debug.Trace (trace)


---------------------------
-- Derivation Trees
---------------------------


-- | Derivation tree is similar to `O.Tree` but additionally includes
-- potential modifications aside the individual nodes.  Modifications
-- themselves take the form of derivation trees.  Whether the modification
-- represents a substitution or an adjunction can be concluded on the basis of
-- the type (leaf or internal) of the node.
--
-- UPDATE 09/06/2018: We now also have sister-adjunction. For the moment, it is
-- not represented as a modifier, but as a regular 'Sister' node.
type Deriv n t = R.Tree (DerivNode n t)


-- | A node of a derivation tree.
data DerivNode n t = DerivNode
  { node  :: O.Node n t
  , modif :: [Deriv n t]
  } deriving (Eq, Ord, Show)


-- | Normalize the derivation tree so that sister adjunction is modeled
-- properly using the `modif` field.
normalize :: Deriv n t -> Deriv n t
normalize =
  onTree
  where
    onTree t =
      let (children, sisters) = onChildren (R.subForest t)
          rootNode = DerivNode
            { node = node (R.rootLabel t)
            , modif = (map onTree . modif) (R.rootLabel t) ++ sisters }
       in R.Node
         { R.rootLabel = rootNode
         , R.subForest = children }
    onChildren ts = (,) <$> lefts <*> rights $
      [ case node (R.rootLabel t) of
          O.Sister _ -> Right (onTree t)
          _ -> Left (onTree t)
      | t <- ts ]


-- | PrintNode tells wheter the node in the pretiffied derivation tree
-- is a modifier or note.
data PrintNode a
  = Regular a
  | Dependent
  deriving (Eq, Ord)


instance Show a => Show (PrintNode a) where
  show (Regular x) = show x
  show Dependent = "<<Dependent>>"


-- -- | Transform the derivation tree into a tree which is easier
-- -- to draw using the standard `R.draw` function.
-- -- `fst` values in nodes are `False` for modifiers.
-- deriv4show :: Deriv n t -> R.Tree (PrintNode (O.Node n t))
-- deriv4show =
--   go False
--   where
--     go isMod t = addDep isMod $ R.Node
--       { R.rootLabel = Regular . node . R.rootLabel $ t
--       , R.subForest = map goSubtree (R.subForest t)
--                    ++ map (go True) (modif $ R.rootLabel t) }
--     goSubtree t =
--       case node (R.rootLabel t) of
--         O.Sister _ -> go True t
--         _ -> go False t
--     addDep isMod t
--       | isMod == True = R.Node Dependent [t]
--       | otherwise = t


-- | Transform the derivation tree into a tree which is easier
-- to draw using the standard `R.draw` function.
deriv4show :: Deriv n t -> R.Tree (PrintNode (O.Node n t))
deriv4show =
  go False
  where
    go isMod t = addDep isMod $ R.Node
      { R.rootLabel = Regular . node . R.rootLabel $ t
      , R.subForest = map (go False) (R.subForest t)
                   ++ map (go True) (modif $ R.rootLabel t) }
    addDep isMod t
      | isMod == True = R.Node Dependent [t]
      | otherwise = t


-- --------------------------------------------------
-- -- Tokens
-- --------------------------------------------------
--
--
-- -- | A token is a terminal enriched with information about the position
-- -- in the input sentence.
-- data Tok t = Tok
--   { position :: Int
--     -- ^ Position of the node in the dependency tree
--   , terminal :: t
--     -- ^ Terminal on the corresponding position
--   } deriving (Show, Eq, Ord)
--
--
-- -- | Tokenize derivation, i.e., replace terminals with the corresponding
-- -- tokens.  WARNING: this assumes that the parsing input is a list and
-- -- not a word-lattice, for example!
-- tokenize :: Deriv n t -> Deriv n (Tok t)
-- tokenize =
--   flip E.evalState (0 :: Int) . go
--   where
--     go R.Node{..} = undefined


--------------------------------------------------
-- Utilities for constructing derivations
--------------------------------------------------


-- | Construct a derivation tree on the basis of the underlying passive
-- item, current child derivation and previous children derivations.
mkTree
  :: A.Hype n t
  -> A.Passive n t
  -> [Deriv n (Tok t)]
  -> Deriv n (Tok t)
mkTree hype p ts = R.Node
  { R.rootLabel = mkRoot hype p
  , R.subForest = reverse ts }

-- | Inverse of `mkTree`.
-- mkTree h p ts == d => unTree h p d == Just ts
unTree
  :: (Ord n, Ord t)
  => A.Hype n t
  -> A.Passive n t
  -> Deriv n (Tok t)
  -> Maybe [Deriv n (Tok t)]
unTree hype p deriv = do
  guard $ R.rootLabel deriv == mkRoot hype p
  return . reverse $ R.subForest deriv

-- | Construct a derivation node with no modifier.
only :: O.Node n t -> DerivNode n t
only x = DerivNode {node = x, modif =  []}

-- | Several constructors which allow to build non-modified nodes.
mkRoot :: A.Hype n t -> A.Passive n t -> DerivNode n (Tok t)
-- mkRoot hype p = only $
--   case dagID of
--     Left notFoot ->
--       if Base.isSister notFoot
--       then O.Sister labNT
--       else O.NonTerm labNT
--     Right did -> O.NonTerm labNT
--   where
--     dagID = getL A.dagID p
--     labNT = A.nonTerm dagID hype
mkRoot hype p = only $
  if Base.isSister' dagID dag
     then O.Sister labNT
     else O.NonTerm labNT
  where
    dagID = getL A.dagID p
    auto  = A.automat hype
    dag   = Auto.gramDAG auto
    labNT = Item.nonTerm dagID auto


mkFoot :: n -> DerivNode n t
mkFoot x = only . O.Foot $ x

mkTerm :: t -> DerivNode n t
mkTerm = only . O.Term

-- | Build non-modified nodes of different types.
footNode :: n -> Deriv n t
footNode x = R.Node (mkFoot x) []

termNode :: t -> Deriv n t
termNode x = R.Node (mkTerm x) []

-- | Retrieve root non-terminal of a derivation tree.
derivRoot :: Deriv n t -> n
derivRoot R.Node{..} = case node rootLabel of
  O.NonTerm x -> x
  O.Foot _ -> error "passiveDerivs.getRoot: got foot"
  O.Sister _ -> error "passiveDerivs.getRoot: got sister"
  O.Term _ -> error "passiveDerivs.getRoot: got terminal"

-- | Construct substitution node stemming from the given derivation.
substNode :: A.Hype n t -> A.Passive n t -> Deriv n (Tok t) -> Deriv n (Tok t)
substNode hype p t
--   | A.isRoot (p ^. A.dagID) = flip R.Node [] $ DerivNode
--     { node = O.NonTerm (derivRoot t)
--     , modif   = [t] }
  | DAG.isRoot (p ^. A.dagID) dag = flip R.Node [] $ DerivNode
    { node = O.NonTerm (derivRoot t)
    , modif   = [t] }
  | otherwise = t
  where
    dag = Auto.gramDAG $ A.automat hype

-- | Inverse of `substNode`.
-- substNode p t == t' => unSubstNode o t' == Just t
unSubstNode :: (Eq n) => A.Hype n t -> A.Passive n t -> Deriv n (Tok t) -> Maybe (Deriv n (Tok t))
unSubstNode hype p t'
--   | A.isRoot (p ^. A.dagID) = do
--       R.Node DerivNode{..} [] <- return t'
--       [t] <- return modif
--       guard $ node == O.NonTerm (derivRoot t)
--       return t
  | DAG.isRoot (p ^. A.dagID) dag = do
      R.Node DerivNode{..} [] <- return t'
      [t] <- return modif
      guard $ node == O.NonTerm (derivRoot t)
      return t
  | otherwise = Just t'
  where
    dag = Auto.gramDAG $ A.automat hype

-- | Add the auxiliary derivation to the list of modifications of the
-- initial derivation.
adjoinTree :: Deriv n t -> Deriv n t -> Deriv n t
adjoinTree ini aux = R.Node
  { R.rootLabel = let root = R.rootLabel ini in DerivNode
    { node = node root
    , modif = aux : modif root }
  , R.subForest = R.subForest ini }

-- adjoinTree' :: Deriv n t -> Deriv n t -> Deriv n t
-- adjoinTree' ini aux = R.Node
--   { R.rootLabel = DerivNode
--     { node = node (R.rootLabel ini)
--     , modif = aux : modif (R.rootLabel ini) }
--   , R.subForest = R.subForest ini }

-- | Unverse of `adjoinTree`.
-- adjoinTree ini aux == cmb => unAjoinInit cmb == Just (ini, aux)
unAdjoinTree :: Deriv n t -> Maybe (Deriv n t, Deriv n t)
unAdjoinTree cmb = do
  subForestIni <- return (R.subForest cmb)
  DerivNode{..} <- return (R.rootLabel cmb)
  let nodeRootLabelIni = node
  aux : modifRootLabelIni <- return modif
  let rootLabelIni = DerivNode
        { node = nodeRootLabelIni
        , modif = modifRootLabelIni }
      ini = R.Node
        { R.rootLabel = rootLabelIni
        , R.subForest = subForestIni }
  return (ini, aux)


-------------------------------
-- Extracting Derivation Trees
-------------------------------


-- | Extract derivation trees obtained on the given input sentence. Should be
-- run on the final result of the earley parser.
--
-- WARNING: the results are not normalized, sister-adjunction trees are not
-- represented in the `modif` field.  Consider using `normalize`.
--
-- WARNING: the resulting derivations are not guaranteed to be given in an
-- ascending weight order!
--
derivTrees
    :: (Ord n, Ord t)
    => A.Hype n t   -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> [Deriv n (Tok t)]
derivTrees hype start n
  = concatMap (`fromPassive` hype)
  $ A.finalFrom start n hype


-- | Extract derivation trees represented by the given passive item
-- and the corresponding input traversal.
fromPassiveTrav
  :: (Ord n, Ord t)
  => A.Passive n t
  -> A.Trav n t
  -> A.Hype n t
  -> [Deriv n (Tok t)]
fromPassiveTrav p trav hype = case trav of
  A.Adjoin qa qm ->
    [ adjoinTree ini aux
    | aux <- passiveDerivs qa
    , ini <- passiveDerivs qm ]
  A.Deactivate q _ ->
    [ mkTree hype p ts
    | ts <- activeDerivs q ]
  _ ->
    error "Deriv.fromPassiveTrav: impossible happened"
  where
    passiveDerivs = flip fromPassive hype
    activeDerivs  = flip fromActive  hype


-- | Extract derivations represented by the given active item.
fromActive
  :: (Ord n, Ord t)
  => A.Active
  -> A.Hype n t
  -> [[Deriv n (Tok t)]]
fromActive active hype = 
  if S.null (A.prioTrav ext)
    then [[]]
    else concatMap
         (\trav -> fromActiveTrav active trav hype)
         (S.toList (A.prioTrav ext))
  where
    ext = activeTrav active hype


-- | Extract derivation trees represented by the given active item
-- and the corresponding input traversal.
fromActiveTrav
  :: (Ord n, Ord t)
  => A.Active
  -> A.Trav n t
  -> A.Hype n t
  -> [[Deriv n (Tok t)]]
fromActiveTrav _p trav hype = case trav of
  A.Scan q t _ ->
    [ termNode t : ts
    | ts <- activeDerivs q ]
  A.Foot q x _ ->
    [ footNode x : ts
    | ts <- activeDerivs q ]
  A.Subst qp qa _ ->
    [ substNode hype qp t : ts
    | ts <- activeDerivs qa
    , t  <- passiveDerivs qp ]
  A.SisterAdjoin qp qa ->
    [ t : ts
    | ts <- activeDerivs qa
    , t  <- passiveDerivs qp ]
  _ ->
    error "Deriv.fromActiveTrav: impossible happened"
  where
    activeDerivs = flip fromActive hype
    passiveDerivs = flip fromPassive hype


-- | Extract derivation trees represented by the given passive item.
fromPassive
  :: forall n t. (Ord n, Ord t)
  => A.Passive n t
  -> A.Hype n t
  -> [Deriv n (Tok t)]
fromPassive passive hype = concat
  [ fromPassiveTrav passive trav hype
  | trav <- S.toList (A.prioTrav ext) ]
  where
    ext = passiveTrav passive hype


-- | Extract the passive traversal set.
passiveTrav :: (Ord n, Ord t) => A.Passive n t -> A.Hype n t -> A.ExtWeight n t
passiveTrav passive hype = case A.passiveTrav passive hype of
  Nothing -> case Q.lookup (A.ItemP passive) (A.waiting hype) of
    Just _ -> error "fromPassive: passive item in the waiting queue"
    Nothing -> error "fromPassive: unknown passive item (not even in the queue)"
  Just ext -> ext


-- | Extract the passive traversal set.
activeTrav :: (Ord n, Ord t) => A.Active -> A.Hype n t -> A.ExtWeight n t
activeTrav active hype = case A.activeTrav active hype of
  Nothing  -> case Q.lookup (A.ItemA active) (A.waiting hype) of
    Just _ -> error $
      "fromActive: active item in the waiting queue"
      ++ "\n" ++ show active
    Nothing -> error $
      "fromActive: unknown active item (not even in the queue)"
      ++ "\n" ++ show active
  Just ext -> ext


-- | Inside weight of a given passive item.
passiveWeight :: (Ord n, Ord t) => A.Passive n t -> A.Hype n t -> Weight
passiveWeight pass = A.priWeight . passiveTrav pass


-- | Inside weight of a given passive item.
activeWeight :: (Ord n, Ord t) => A.Active -> A.Hype n t -> Weight
activeWeight act = A.priWeight . activeTrav act


-- | Inside weight of a given traversal.
travWeight
  :: (Ord n, Ord t)
  => A.Trav n t
  -> A.Hype n t
  -> Weight
travWeight trav h = 
  arcWeight trav + case trav of
    A.Scan q _t _ -> activeWeight q h
    A.Subst qp qa _ -> passiveWeight qp h + activeWeight qa h
    A.Foot q _x _ -> activeWeight q h
    A.SisterAdjoin qp qa -> passiveWeight qp h + activeWeight qa h
    A.Adjoin qa qm -> passiveWeight qa h + passiveWeight qm h
    A.Deactivate q _ -> activeWeight q h
    _ -> error "travWeight: cul-de-sac"


-- | Weight of an arc alone.
arcWeight :: A.Trav n t -> Weight
arcWeight arc =
  case arc of
    A.Adjoin{} -> 0
    A.SisterAdjoin{} -> 0
    _ -> A._weight arc


-----------------------------------------
-- Extracting Weighted Derivation Trees
-----------------------------------------


-- | Extract the least-weight derivation tree obtained on the given input
-- sentence. Should be run on the final result of the Earley parser.
--
-- WARNING: the resulting derivation is not normalized -- sister-adjunction
-- trees are not represented in the `modif` field.  Consider using `normalize`.
--
derivTreesW
    :: (Ord n, Ord t)
    => A.Hype n t   -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> Maybe (Deriv n (Tok t), Weight)
derivTreesW hype start n = do
  pass <- minimumBy
    (flip passiveWeight hype)
    (A.finalFrom start n hype)
  fromPassiveW pass hype


-- | Extract derivation trees represented by the given passive item.
fromPassiveW
  :: forall n t. (Ord n, Ord t)
  => A.Passive n t
  -> A.Hype n t
  -> Maybe (Deriv n (Tok t), Weight)
fromPassiveW passive hype = do
  let ext = passiveTrav passive hype
  trav <- minimumBy
    (flip travWeight hype)
    (S.toList $ A.prioTrav ext)
  fromPassiveTravW passive trav hype


-- | Extract derivation trees represented by the given passive item
-- and the corresponding input traversal.
fromPassiveTravW
  :: (Ord n, Ord t)
  => A.Passive n t
  -> A.Trav n t
  -> A.Hype n t
  -> Maybe (Deriv n (Tok t), Weight)
fromPassiveTravW p trav hype =
  second (+ arcWeight trav) <$> case trav of
    A.Adjoin qa qm -> do
      (aux, w) <- passiveDerivs qa
      (ini, w') <- passiveDerivs qm
      return (adjoinTree ini aux, w + w')
    A.Deactivate q _ -> do
      (ts, w) <- activeDerivs q
      return (mkTree hype p ts, w)
    _ ->
      error "Deriv.fromPassiveTrav: impossible happened"
  where
    passiveDerivs = flip fromPassiveW hype
    activeDerivs  = flip fromActiveW  hype


-- | Extract derivations represented by the given active item.
fromActiveW
  :: (Ord n, Ord t)
  => A.Active
  -> A.Hype n t
  -> Maybe ([Deriv n (Tok t)], Weight)
fromActiveW active hype = do
  let ext = activeTrav active hype
  if S.null (A.prioTrav ext)
     then return ([], 0)
     else do
       trav <- minimumBy
         (flip travWeight hype)
         (S.toList $ A.prioTrav ext)
       fromActiveTravW active trav hype


-- | Extract derivation trees represented by the given active item
-- and the corresponding input traversal.
fromActiveTravW
  :: (Ord n, Ord t)
  => A.Active
  -> A.Trav n t
  -> A.Hype n t
  -> Maybe ([Deriv n (Tok t)], Weight)
fromActiveTravW _p trav hype =
  second (+ arcWeight trav) <$> case trav of
    A.Scan q t _ -> do
      (ts, w) <- activeDerivs q
      return (termNode t : ts, w)
    A.Foot q x _ -> do
      (ts, w) <- activeDerivs q
      return (footNode x : ts, w)
    A.Subst qp qa _ -> do
      (ts, w) <- activeDerivs qa
      (t, w') <- passiveDerivs qp
      return (substNode hype qp t : ts, w + w')
    A.SisterAdjoin qp qa -> do
      (ts, w) <- activeDerivs qa
      (t, w') <- passiveDerivs qp
      return (t : ts, w + w')
    _ ->
      error "Deriv.fromActiveTrav: impossible happened"
  where
    activeDerivs = flip fromActiveW hype
    passiveDerivs = flip fromPassiveW hype


-- -- | Merge a given list of lists, each assumed to be sorted (w.r.t. the given
-- -- function), to a single sorted list.
-- mergeManyBy :: (Ord w) => (a -> w) -> [[a]] -> [a]
-- mergeManyBy f xss =
--   case xss of
--     [] -> []
--     [xs] -> xs
--     xs1 : rest -> mergeBy f xs1 (mergeManyBy f rest)
-- 
-- 
-- -- | Merge the two given lists, each assumed to be sorted (w.r.t. the given
-- -- function), to a single sorted list.
-- mergeBy :: (Ord w) => (a -> w) -> [a] -> [a] -> [a]
-- mergeBy f =
--   go
--   where
--     go xs [] = xs
--     go [] ys = ys
--     go (x:xs) (y:ys)
--       | f x <= f y = x : go xs (y:ys)
--       | otherwise  = y : go (x:xs) ys


-- | Find the minimal element according to the given comparison function.
minimumBy :: (Ord w) => (a -> w) -> [a] -> Maybe a
minimumBy f xs =
  case xs of
    [] -> Nothing
    _  -> Just $ L.minimumBy (comparing f) xs


--------------------------------------------------
-- Check if derivation trees is in the graph
--------------------------------------------------


-- | Check if the derivation is present in the chart.
--
-- TODO: The start symbol and the sentence length could be computed
-- automatically, based on the input derivation.
encodes
    :: (Ord n, Ord t)
    => A.Hype n t   -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> Deriv n (Tok t)
    -> Bool
encodes hype begSym sentLen deriv = or
  [ passiveEncodes p hype deriv
  | p <- A.finalFrom begSym sentLen hype ]
--   where
--     begSym = undefined
--     sentLen = undefined


-- | Check if the derivation is represented by the passive item.
passiveEncodes
  :: (Ord n, Ord t)
  => A.Passive n t
  -> A.Hype n t
  -> Deriv n (Tok t)
  -> Bool
passiveEncodes passive hype deriv = case A.passiveTrav passive hype of
  Nothing -> case Q.lookup (A.ItemP passive) (A.waiting hype) of
    Just _ -> error "fromPassive: passive item in the waiting queue"
    Nothing -> error "fromPassive: unknown passive item (not even in the queue)"
  Just ext -> or
    [ passiveTravEncodes passive trav hype deriv
    | trav <- S.toList (A.prioTrav ext) ]


-- | Check if the derivation is represented by the passive item
-- together with the corresponding traversal (hyperarc).
passiveTravEncodes
  :: (Ord n, Ord t)
  => A.Passive n t
  -> A.Trav n t
  -> A.Hype n t
  -> Deriv n (Tok t)
  -> Bool
passiveTravEncodes p trav hype root = case trav of

  A.Adjoin qa qm -> isJust $ do
    (ini, aux) <- unAdjoinTree root
    guard $ passiveEncodes qa hype aux
    guard $ passiveEncodes qm hype ini

--     [ adjoinTree ini aux
--     | aux <- passiveDerivs qa
--     , ini <- passiveDerivs qm ]

  A.Deactivate q _ -> isJust $ do
    ts <- unTree hype p root
    guard $ activeEncodes q hype ts

--     [ mkTree hype p ts
--     | ts <- activeDerivs q ]

  _ -> error "Deriv.passiveTravEncodes: impossible happened"


-- | Check if the derivation is represented by the active item.
activeEncodes
  :: (Ord n, Ord t)
  => A.Active
  -> A.Hype n t
  -> [Deriv n (Tok t)]
  -> Bool
activeEncodes active hype deriv = case A.activeTrav active hype of
  Nothing  -> case Q.lookup (A.ItemA active) (A.waiting hype) of
    Just _ -> error $
      "fromActive: active item in the waiting queue"
      ++ "\n" ++ show active
    Nothing -> error $
      "fromActive: unknown active item (not even in the queue)"
      ++ "\n" ++ show active
  Just ext -> if S.null (A.prioTrav ext)
    then deriv == []
    else or
         [ activeTravEncodes active trav hype deriv
         | trav <- S.toList (A.prioTrav ext) ]


-- | Check if the derivation is represented by the active item
-- together with the corresponding traversal (hyperarc).
activeTravEncodes
  :: (Ord n, Ord t)
  => A.Active
  -> A.Trav n t
  -> A.Hype n t
  -> [Deriv n (Tok t)]
  -> Bool
activeTravEncodes _p trav hype root = case trav of

  A.Scan q t _ -> isJust $ do
    deriv : ts <- return root
    guard $ deriv == termNode t
    guard $ activeEncodes q hype ts

--     [ termNode t : ts
--     | ts <- activeDerivs q ]

  A.Foot q x _ -> isJust $ do
    deriv : ts <- return root
    guard $ deriv == footNode x
    guard $ activeEncodes q hype ts

--     [ footNode x : ts
--     | ts <- activeDerivs q ]

  A.Subst qp qa _ -> isJust $ do
    deriv : ts <- return root
    t <- unSubstNode hype qp deriv
    guard $ passiveEncodes qp hype t
    guard $ activeEncodes qa hype ts

--     [ substNode qp t : ts
--     | ts <- activeDerivs qa
--     , t  <- passiveDerivs qp ]

  A.SisterAdjoin qp qa -> isJust $ do
    t : ts <- return root
    guard $ passiveEncodes qp hype t
    guard $ activeEncodes qa hype ts

--     [ t : ts
--     | ts <- activeDerivs qa
--     , t  <- passiveDerivs qp ]

  _ ->
    error "Deriv.activeTravEncodes: impossible happened"


----------------------------------------------------------------------
-- A reversed representation of a hypergraph
----------------------------------------------------------------------


-- | A reverse representation of a hypergraph, i.e., a representation in which
-- outgoing hyperarcs (applications of inference rules) are stored for the
-- individual nodes (chart items) in the hypergraph.
--
-- Only the processed part of the hypergraph is stored.
data RevHype n t = RevHype
  { doneReversed :: M.Map (A.Item n t) (S.Set (RevTrav n t)) }


-- | Empty `RevHype`.
emptyRevHype :: RevHype n t
emptyRevHype = RevHype M.empty


-- | An arc outgoing from a hypergraph node. A reversed representation w.r.t.
-- `A.Trav`.
--
-- NOTE: we could try to express relations between items in `doneReversed`
-- (which would be then rewritten using two data structures?) and types of
-- outgoing edges.  For the moment, each constructor is adorned with a suffix
-- 'A' or 'P' which tells whether the source item can be passive or active
-- (or both, if no corresponding 'A' or 'P' suffix).
data RevTrav n t
    = ScanA
        { outItemA :: A.Active
        -- ^ The output active item
        , scanTerm :: Tok t
        -- ^ The scanned terminal
        }
    -- ^ Scan: scan the leaf terminal with a terminal from the input
    | SubstP
        { outItemA :: A.Active
        -- ^ The output active or passive item
        , actArg   :: A.Active
        -- ^ The active argument of the action
        }
    -- ^ Pseudo substitution: match the source passive item against the leaf
    -- of the given active item
    | SubstA
        { passArg  :: A.Passive n t
        -- ^ The passive argument of the action
        , outItemA :: A.Active
        -- ^ The output active or passive item
        }
    -- ^ Pseudo substitution: substitute the leaf of the source item with
    -- the given passive item
    | FootA
        { outItemA :: A.Active
        -- ^ The output active or passive item
        , theFoot  :: n
        -- ^ The foot non-terminal
        }
    -- ^ Foot adjoin: match the foot of the source item with the given
    -- passive item
    | AdjoinP
        { outItemP :: A.Passive n t
        -- ^ The output passive item
        , passMod  :: A.Passive n t
        -- ^ The modified item
        }
    -- ^ Adjoin terminate: adjoin the source auxiliary item to
    -- the given passive item
    | ModifyP
        { passAdj  :: A.Passive n t
        -- ^ The adjoined item
        , outItemP :: A.Passive n t
        -- ^ The output passive item
        }
    -- ^ Adjoin terminate: modify the source passive item with the given
    -- auxiliary item
    | SisterAdjoinP
        { actArg   :: A.Active
        -- ^ The modified item
        , outItemA :: A.Active
        -- ^ The output acitve item
        }
    | SisterAdjoinA
        { passArg  :: A.Passive n t
        -- ^ The sister-adjoined item
        , outItemA :: A.Active
        -- ^ The output acitve item
        }
    | DeactivateA
        { outItemP :: A.Passive n t
        -- ^ The output passive item
        }
    deriving (Show, Eq, Ord)


---------------------------------
-- Extracting Derivation Trees...
--
-- ...going through the given arc
---------------------------------


-- | Extract derivations going through the given arc.
fromArc
  :: (Ord n, Ord t)
  => A.Item n t
     -- ^ Target node
  -> A.Trav n t
     -- ^ Arc ingoing to the target node
  -> A.Hype n t
     -- ^ The corresponding hypergraph
  -> RevHype n t
     -- ^ The reversed version of the hypergraph
  -> [Deriv n (Tok t)]
fromArc node arc hype revHype =
  case node of
    A.ItemP p ->
      let derivs _ = fromPassiveTrav p arc hype
      in  upFromPassive p derivs hype revHype
    A.ItemA p ->
      let derivs _ = fromActiveTrav p arc hype
      in  upFromActive p derivs hype revHype


-- -- | Depending of the type of the item to process, calls either `upFromPassive`
-- -- or `upFromActive`.
-- upFromItem
--   :: (Ord n, Ord t)
--   => A.Item n t
--   -> (() -> [[Deriv n (Tok t)]])
--   -- ^ Derivations corresponding to children items of the given item
--   -- (for a certain, fixed hyperarc)
--   -> A.Hype n t
--   -> RevHype n t
--   -> [Deriv n (Tok t)]
-- upFromItem item childDerivs hype revHype =
--   case item of
--     A.ItemP p ->
--       -- first construct actual derivation trees for the passive item
--       let derivs _ = map (mkTree hype p) (childDerivs ())
--       in  upFromPassive p derivs hype revHype
--     A.ItemA p -> upFromActive p childDerivs hype revHype


-- | Explor the hypergraph up in order to generate all final derivations which
-- go through the given item for which partial derivations are known.
upFromPassive
  :: (Ord n, Ord t)
  => A.Passive n t
     -- ^ Passive node
  -> (() -> [Deriv n (Tok t)])
     -- ^ The list of derivation corresponding to the passive node
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n (Tok t)]
upFromPassive passive passiveDerivs hype revHype =
  case M.lookup (A.ItemP passive) (doneReversed revHype) of
    Nothing -> error "upFromPassive: item with no respective entry in `RevHype`"
    Just revTravSet -> if S.null revTravSet
      then passiveDerivs () -- meaning that we got a final item, hopefully...
      else concat
           [ upFromPassiveTrav passive revTrav passiveDerivs hype revHype
           | revTrav <- S.toList revTravSet ]


upFromPassiveTrav
  :: (Ord n, Ord t)
  => A.Passive n t
     -- ^ Source hypernode (passive item)
  -> RevTrav n t
     -- ^ Traversal to be followed from the source node
  -> (() -> [Deriv n (Tok t)])
     -- ^ Derivation corresponding to the source node
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n (Tok t)]
upFromPassiveTrav source revTrav sourceDerivs hype revHype =
  case revTrav of
    SubstP{..} ->
      -- we now have a passive source, another active source, and an unknown target;
      -- based on that, we create a list of derivations of the source nodes.
      let combinedDerivs _ =
            [ substNode hype source t : ts
            | ts <- fromActive actArg hype
            , t  <- sourceDerivs () ]
      -- once we have the combined derivations of the source nodes, we proceed upwards
      -- by going to the unkown target item with the derivations we have
      in  upFromActive outItemA combinedDerivs hype revHype
    AdjoinP{..} ->
      let combinedDerivs _ =
            [ adjoinTree ini aux
            | aux <- sourceDerivs ()
            , ini <- fromPassive passMod hype ]
      in  upFromPassive outItemP combinedDerivs hype revHype
    ModifyP{..} ->
      let combinedDerivs _ =
            [ adjoinTree ini aux
            | aux <- fromPassive passAdj hype
            , ini <- sourceDerivs () ]
      in  upFromPassive outItemP combinedDerivs hype revHype
    SisterAdjoinP{..} ->
      let combinedDerivs _ =
            [ t : ts
            | ts <- fromActive actArg hype
            , t  <- sourceDerivs () ]
      in  upFromActive outItemA combinedDerivs hype revHype
    _ -> error "upFromPassiveTrav: got an 'active' traversal for a passive item"


-- | Explor the hypergraph up in order to generate all final derivations which
-- go through the given item for which partial derivations are known.
upFromActive
  :: (Ord n, Ord t)
  => A.Active
  -> (() -> [[Deriv n (Tok t)]])
  -- ^ Derivation corresponding to the active node
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n (Tok t)]
upFromActive active activeDerivs hype revHype = concat
  [ upFromActiveTrav active revTrav activeDerivs hype revHype
  | revTravSet <- maybeToList $ M.lookup (A.ItemA active) (doneReversed revHype)
  , revTrav <- S.toList revTravSet ]


upFromActiveTrav
  :: (Ord n, Ord t)
  => A.Active
     -- ^ Source hypernode (active item)
  -> RevTrav n t
     -- ^ Traversal to be followed from the source node
  -> (() -> [[Deriv n (Tok t)]])
     -- ^ Derivation corresponding to the source node
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n (Tok t)]
upFromActiveTrav _source revTrav sourceDerivs hype revHype =
  case revTrav of
    ScanA{..} ->
      let combinedDerivs _ =
            [ termNode scanTerm : ts
            | ts <- sourceDerivs () ]
      in  upFromActive outItemA combinedDerivs hype revHype
    SubstA{..} ->
      let combinedDerivs _ =
            [ substNode hype passArg t : ts
            | ts <- sourceDerivs () -- fromActive actArg hype
            , t  <- fromPassive passArg hype ]
      in  upFromActive outItemA combinedDerivs hype revHype
    FootA{..} ->
      let combinedDerivs _ =
            [ footNode theFoot : ts
            | ts <- sourceDerivs () ]
      in  upFromActive outItemA combinedDerivs hype revHype
    SisterAdjoinA{..} ->
      let combinedDerivs _ =
            [ t : ts
            | ts <- sourceDerivs ()
            , t  <- fromPassive passArg hype ]
      in  upFromActive outItemA combinedDerivs hype revHype
    DeactivateA{..} ->
      let combinedDerivs _ =
            [ mkTree hype outItemP ts
            | ts <- sourceDerivs () ]
          -- derivs _ = map (mkTree hype outItemP) (combinedDerivs ())
      in  upFromPassive outItemP combinedDerivs hype revHype
    _ -> error "upFromActiveTrav: got an 'passive' traversal for an active item"


--------------------------------------------------
-- Dynamic construction of `RevHype`
--------------------------------------------------


-- | Modifications corresponding to the given hypergraph modification.
type ModifDerivs n t = (A.HypeModif n t, [Deriv n (Tok t)])


-- | Derivation monad.
type DerivM n t m =
  P.Pipe
    (A.HypeModif n t)
    (ModifDerivs n t)
    (RWS.RWST (DerivR n) () (DerivS n t) m)
-- type DerivM n t m = RWS.RWST
--   (DerivR n) () (DerivS n t)
--   (P.Pipe (A.HypeModif n t) (ModifDerivs n t) m)


-- | Reader component of `DerivM`.
data DerivR n = DerivR
  { startSym :: n
    -- ^ Start symbol of the grammar
  , sentLen  :: Int
    -- ^ Length of the input sentence
  } deriving (Show, Eq, Ord)


-- | State component of `DerivM`.
-- data DerivS n t = DerivS
type DerivS n t = RevHype n t


-- -- | Utility function: parse the given sentence with the give grammar and print
-- -- the individual derivation trees (generated progressively).
-- parseAndPrint
--   :: (Ord t, Ord n, Show n, Show t)
--   => A.Auto n t
--   -> n -- ^ The start symbol
--   -> A.Input t
--   -> IO ()
-- parseAndPrint auto start input = void . P.runEffect $
--   P.for pipe $ \(_hypeModif, ts) -> forM_ ts $
--     lift . putStrLn . R.drawTree . fmap show . deriv4show
--   where
--     pipe = A.earleyAutoP auto input P.>-> derivsPipe conf
--     conf = DerivR
--       { startSym = start
--       , sentLen = length $ A.inputSent input }


-- | A pipe which transforms hypergraph modifications to the
-- corresponding derivations.
derivsPipe
  :: (Monad m, Ord n, Ord t)
  => DerivM n t m a
derivsPipe = loop
  where
    loop = do
      hypeModif <- P.await
      derivs <- procModif hypeModif
      P.yield (hypeModif, derivs)
      loop


-- -- | A pipe which transforms hypergraph modifications to the
-- -- corresponding derivations.
-- derivsPipe'
--   :: (Ord n, Ord t)
--   => A.Auto n t
--   -> A.Input t
--   -> n            -- ^ Start symbol
--   -> P.Producer (ModifDerivs n t) IO ()
-- derivsPipe' automat input start =
--   undefined
--   where
--     pipeL = Morph.hoist lift A.earleyAutoGen
--     conf = DerivR
--       { startSym = start
--       , sentLen = length $ A.inputSent input }


-- | A pipe which transforms hypergraph modifications to the
-- corresponding derivations.
derivsProd
  :: (SOrd n, SOrd t)
  => P.Producer
      (ModifDerivs n t)
      (RWS.RWST (DerivR n) () (DerivS n t)
        (A.Earley n t)
      ) (A.Hype n t)
derivsProd =
  pipeL >-> pipeR
    where
      pipeL = Morph.hoist lift A.earleyAutoGen
      pipeR = derivsPipe


-- | Compose the derivation producer `derivsProd` with the given consumer.
consumeDerivs
  :: (SOrd n, SOrd t)
  => A.Auto n t
  -> A.Input t
  -> n            -- ^ Start symbol
  -> P.Consumer (ModifDerivs n t) IO (A.Hype n t)
  -> IO (A.Hype n t)
consumeDerivs automat input start cons0 = do
  evalRWST input (A.mkHype automat) $ do
    evalRWST derivR emptyRevHype $ do
      P.runEffect $
        derivsProd >-> cons
  where
    evalRWST rd st rwst = fst <$> RWS.evalRWST rwst rd st
    cons = Morph.hoist lift . Morph.hoist lift $ cons0
    derivR = DerivR
      { startSym = start
      , sentLen = length $ A.inputSent input }


-- -- | A pipe which transforms hypergraph modifications to the
-- -- corresponding derivations.
-- derivsPipe
--   :: forall m n t a. (Monad m, Ord n, Ord t)
--   => DerivR n
--   -> P.Pipe (A.HypeModif n t) (ModifDerivs n t) m a
-- derivsPipe conf =
--   fst <$> RWS.evalRWST loop conf emptyRevHype
--   where
--     loop = do
--       hypeModif <- lift P.await
--       derivs <- procModif hypeModif
--       lift $ P.yield (hypeModif, derivs)
--       loop


-- | Process a hypergraph modification.
procModif
  :: forall m n t. (Monad m, Ord n, Ord t)
  => A.HypeModif n t
  -> DerivM n t m [Deriv n (Tok t)]
procModif A.HypeModif{..}
  | modifType == A.NewNode = fmap (maybe [] id) . runMaybeT $ do
      -- liftIO $ putStrLn "<<NewNode>>"
      A.ItemP p <- return modifItem
      guard =<< lift (isFinal modifHype p)
      -- liftIO $ putStrLn "<<NewNode->isFinal>>"
      lift $ goNode modifItem
      return $ fromPassive p modifHype
  | otherwise = do -- `modifType == A.NewArcs`
      -- rev <- RWS.gets doneReversed
      -- liftIO $ putStrLn $ "<<NewArcs>> " ++ show (M.size rev)
      -- check if the node is already in the reversed hypergraph; otherwise, it
      -- is not reachable from any final item so we can ignore it
      b <- hasNode modifItem
      if b then do
        -- liftIO $ putStrLn "<<NewArcs->hasNode>>"
        goChildren modifItem (A.prioTrav modifTrav)
        revHype <- RWS.get
        let derivs = concatMap
              (\arc -> fromArc modifItem arc modifHype revHype)
              (S.toList $ A.prioTrav modifTrav)
        -- liftIO . putStrLn $ "<<NewArcs->" ++
        --   show (length . S.toList $ A.prioTrav modifTrav) ++
        --   " arcs>>"
        -- liftIO . putStrLn $ "<<NewArcs->" ++ show (length derivs) ++ " derivs>>"
        return derivs
      else return []
  where
    -- Recursively explore the hypergraph starting from the given node and add
    -- all nodes and arcs to the inverse representation, if not present there
    -- yet.
    goNode :: A.Item n t -> DerivM n t m ()
--     goNode node = addNode node >> goChildren node
    goNode node = do
      b <- hasNode node
      -- liftIO $ putStrLn $ "goNode->hasNode: " ++ show b
      when (not b) $ do
        -- liftIO $ putStrLn "goNode->addNode"
        addNode node >> goChildren node (incomingArcs node modifHype)
    -- Explore arcs ingoing to the given target node.
    goChildren node arcs = mapM_ (goArc node) (S.toList arcs)
    -- Similar to `goNode`, but exploration begins with a specific arc
    -- leading to the corresponding target node.
    goArc node arc = addArc node arc << case arc of
      A.Scan{..} -> goNodeA scanFrom
      A.Subst{..} -> goNodeP passArg >> goNodeA actArg
      A.Foot{..} -> goNodeA actArg
      A.Adjoin{..} -> goNodeP passAdj >> goNodeP passMod
      A.SisterAdjoin{..} -> goNodeP passArg >> goNodeA actArg
      A.Deactivate{..} -> goNodeA actArg
      where m << n = n >> m
    -- Versions of `goNode` specialized to active and passive items
    goNodeA = goNode . A.ItemA
    goNodeP = goNode . A.ItemP


-- | Retrieve the set/list of arcs ingoing to the given hypergraph node.
incomingArcs
  :: (Ord n, Ord t)
  => A.Item n t
  -> A.Hype n t
  -> S.Set (A.Trav n t)
incomingArcs item hype = getTrav $ case item of
  A.ItemA a -> A.activeTrav a hype
  A.ItemP p -> A.passiveTrav p hype
  where
    getTrav = \case
      -- Nothing -> S.empty
      Nothing -> error
        "incomingArcs: no traversals corresponding to the given item"
      Just ew -> A.prioTrav ew


-- | Does the inversed representation of the hypergraph contain the given node?
hasNode :: (Monad m, Ord n) => A.Item n t -> DerivM n t m Bool
hasNode item = do
  rev <- RWS.gets doneReversed
  return $ M.member item rev


-- | Add a node to the inversed representation of the hypergraph. Nothing about
-- the ingoing or outgoing arcs is known at this moment.
addNode :: (Monad m, Ord n, Ord t) => A.Item n t -> DerivM n t m ()
addNode item = RWS.modify' $ \RevHype{..} ->
  let rev = M.insertWith S.union item S.empty doneReversed
  in  RevHype {doneReversed = rev}


-- | Add an arc to the inversed representation of the hypergraph.
addArc
  :: (Monad m, Ord n, Ord t)
  => A.Item n t
     -- ^ Node to which the arc leads
  -> A.Trav n t
     -- ^ Arc to add
  -> DerivM n t m ()
addArc item trav = RWS.modify' $ \RevHype{..} ->
  let rev = doneReversed `modifyWith`
            [addOne p t | (p, t) <- turnAround item trav]
            -- map (uncurry addOne) (turnAround item trav)
  in  RevHype {doneReversed = rev}
  where
    modifyWith = flip applyAll
    addOne revItem revTrav =
      M.insertWith S.union revItem (S.singleton revTrav)


-- | Apply a list of transformations to a given argument.
applyAll :: [a -> a] -> a -> a
applyAll funs x = case funs of
  f : fs -> f (applyAll fs x)
  [] -> x


-- | Retrieve outgoing arcs from the given ingoing arc.
turnAround
  :: A.Item n t
     -- ^ Target node
  -> A.Trav n t
     -- ^ Arc ingoing to the target node
  -> [(A.Item n t, RevTrav n t)]
turnAround item trav = case trav of
  A.Scan{..} ->
    [ (A.ItemA scanFrom, ScanA (act item) _scanTerm) ]
  A.Subst{..} ->
    [ (A.ItemP passArg, SubstP (act item) actArg)
    , (A.ItemA actArg, SubstA passArg (act item)) ]
  A.Foot{..} ->
    [ (A.ItemA actArg, FootA (act item) theFoot) ]
  A.Adjoin{..} ->
    let target = pass item in
    [ (A.ItemP passAdj, AdjoinP target passMod)
    , (A.ItemP passMod, ModifyP passAdj target) ]
  A.SisterAdjoin{..} ->
    let target = act item in
    [ (A.ItemP passArg, SisterAdjoinP actArg target)
    , (A.ItemA actArg, SisterAdjoinA passArg target) ]
  A.Deactivate{..} ->
    [ (A.ItemA actArg, DeactivateA (pass item)) ]
  where
    pass (A.ItemP p) = p
    pass _ = error "turnAround.pass: expected passive item, got active"
    act (A.ItemA q) = q
    act _ = error "turnAround.act: expected active item, got passive"


-- | Check whether the given passive item is final or not.
isFinal
  :: (Monad m, Eq n)
  => A.Hype n t
  -> A.Passive n t -- ^ The item to check
  -> DerivM n t m Bool
isFinal hype p = do
  DerivR{..} <- RWS.ask
  return $ isFinal_ hype startSym sentLen p


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | Check whether the given passive item is final or not.
-- TODO: Move to some core module?
isFinal_
  :: (Eq n)
  => A.Hype n t
  -> n             -- ^ The start symbol
  -> Int           -- ^ The length of the input sentence
  -> A.Passive n t -- ^ The item to check
  -> Bool
isFinal_ hype start n p =
  p ^. A.spanP ^. A.beg == 0 &&
  p ^. A.spanP ^. A.end == n &&
  p ^. A.spanP ^. A.gap == Nothing &&
  -- p ^. A.dagID == Left root &&
  DAG.isRoot dagID dag &&
  getLabel dagID == Just start
  where
    -- root = Base.NotFoot {notFootLabel=start, isSister=False}
    dag = Auto.gramDAG $ A.automat hype
    dagID = p ^. A.dagID
    getLabel did = Base.labNonTerm =<< DAG.label did dag


-- -- | ListT from a list.
-- each :: Monad m => [a] -> P.ListT m a
-- each = P.Select . P.each
