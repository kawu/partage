{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}


module NLP.Partage.AStar.Deriv
( Deriv
, DerivNode (..)
, derivTrees
, derivFromPassive
-- , deriv2tree
-- , expandDeriv
-- -- , fromPassive'
-- -- , fromActive'

, RevHype (..)
) where


import           Control.Monad             (guard, void, forM_, when)
import qualified Control.Monad.RWS.Strict  as RWS
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (..))

import           Data.Lens.Light
import qualified Data.Map.Strict           as M
import           Data.Maybe                (maybeToList)
import qualified Data.Set                  as S
import qualified Data.Tree                 as R

import qualified Pipes                     as P
-- import qualified Pipes.Prelude              as P

import qualified NLP.Partage.AStar         as A
-- import           NLP.Partage.DAG        (Weight)
import qualified NLP.Partage.Tree.Other    as O


---------------------------
-- Extracting Derivation Trees
--
-- Experimental version
---------------------------


-- | Derivation tree is similar to `O.Tree` but additionally includes
-- potential modifications aside the individual nodes.  Modifications
-- themselves take the form of derivation trees.  Whether the modification
-- represents a substitution or an adjunction can be concluded on the basis of
-- the type (leaf or internal) of the node.
type Deriv n t = R.Tree (DerivNode n t)


-- | A node of a derivation tree.
data DerivNode n t = DerivNode
  { node  :: O.Node n t
  , modif :: [Deriv n t]
  } deriving (Eq, Ord, Show)


-- | Extract derivation trees obtained on the given input sentence. Should be
-- run on the final result of the earley parser.
derivTrees
    :: (Ord n, Ord t)
    => A.Hype n t   -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> [Deriv n t]
derivTrees hype start n
    = concatMap (`derivFromPassive` hype)
    $ A.finalFrom start n hype


-- | Extract the set of the parsed trees w.r.t. to the given passive item.
derivFromPassive :: forall n t. (Ord n, Ord t) => A.Passive n t -> A.Hype n t -> [Deriv n t]
derivFromPassive passive hype = concat

  [ fromPassiveTrav passive trav
  | ext <- maybeToList $ A.passiveTrav passive hype
  , trav <- S.toList (A.prioTrav ext) ]

  where

    passiveDerivs = flip derivFromPassive hype

    fromPassiveTrav p (A.Scan q t _) =
        [ mkTree p (termNode t) ts
        | ts <- activeDerivs q ]
    fromPassiveTrav p (A.Foot q _p' _) =
        [ mkTree p (footNode p) ts
        | ts <- activeDerivs q ]
    fromPassiveTrav p (A.Subst qp qa _) =
        [ mkTree p (substNode t) ts
        | ts <- activeDerivs qa
        , t  <- passiveDerivs qp ]
    fromPassiveTrav _p (A.Adjoin qa qm) =
        [ adjoinTree ini aux
        | aux <- passiveDerivs qa
        , ini <- passiveDerivs qm ]

    -- Construct a derivation tree on the basis of the underlying passive
    -- item, current child derivation and previous children derivations.
    mkTree p t ts = R.Node
      { R.rootLabel = mkRoot p
      , R.subForest = reverse $ t : ts }

    -- Extract the set of the parsed trees w.r.t. to the given active item.
    activeDerivs active = case A.activeTrav active hype of
      Nothing  -> error "activeDerivs: unknown active item"
      Just ext -> if S.null (A.prioTrav ext)
        then [[]]
        else concatMap
             (fromActiveTrav active)
             (S.toList (A.prioTrav ext))

    fromActiveTrav _p (A.Scan q t _) =
        [ termNode t : ts
        | ts <- activeDerivs q ]
    fromActiveTrav _p (A.Foot q p _) =
        [ footNode p : ts
        | ts <- activeDerivs q ]
    fromActiveTrav _p (A.Subst qp qa _) =
        [ substNode t : ts
        | ts <- activeDerivs qa
        , t  <- passiveDerivs qp ]
    fromActiveTrav _p (A.Adjoin _ _) =
        error "activeDerivs.fromActiveTrav: called on a passive item"

    -- Construct substitution node stemming from the given derivation.
    substNode t = flip R.Node [] $ DerivNode
      { node = O.NonTerm (derivRoot t)
      , modif   = [t] }

    -- Add the auxiliary derivation to the list of modifications of the
    -- initial derivation.
    adjoinTree ini aux = R.Node
      { R.rootLabel = let root = R.rootLabel ini in DerivNode
        { node = node root
        , modif = aux : modif root }
      , R.subForest = R.subForest ini }

    -- Construct a derivation node with no modifier.
    only x = DerivNode {node = x, modif =  []}

    -- Several constructors which allow to build non-modified nodes.
    mkRoot p = only . O.NonTerm $ A.nonTerm (getL A.dagID p) hype
    mkFoot p = only . O.Foot $ A.nonTerm (getL A.dagID p) hype
    mkTerm = only . O.Term

    -- Build non-modified nodes of different types.
    footNode p = R.Node (mkFoot p) []
    termNode x = R.Node (mkTerm x) []

    -- Retrieve root non-terminal of a derivation tree.
    derivRoot :: Deriv n t -> n
    derivRoot R.Node{..} = case node rootLabel of
      O.NonTerm x -> x
      O.Foot _ -> error "passiveDerivs.getRoot: got foot"
      O.Term _ -> error "passiveDerivs.getRoot: got terminal"


--------------------------------------------------
-- A reversed representation of a hypergraph
--------------------------------------------------


-- | A reverse representation of a hypergraph, i.e., a representation in which
-- outgoing hyperarcs (applications of inference rules) are stored for the
-- individual nodes (chart items) in the hypergraph.
--
-- Only the processed part of the hypergraph is stored.
data RevHype n t = RevHype
  { doneReversed :: M.Map (A.Item n t) (S.Set (RevTrav n t)) }


-- | An arc outgoing from a hypergraph node. A reversed representation w.r.t.
-- `A.Trav`.
--
-- TODO: we could try to express relations between items in `doneReversed`
-- (which would be then rewritten using two data structures?) and types of
-- outgoing edges.  For the moment, each constructor is adorned with a suffix
-- 'A' or 'P' which tells whether the source item can be passive or active
-- (or both, if no corresponding 'A' or 'P' suffix).
data RevTrav n t
    = ScanA
        { _outItem  :: A.Item n t
        -- ^ The output active or passive item
        , _scanTerm :: t
        -- ^ The scanned terminal
        }
    -- ^ Scan: scan the leaf terminal with a terminal from the input
    | SubstP
        { _outItem :: A.Item n t
        -- ^ The output active or passive item
        , _actArg  :: A.Active
        -- ^ The active argument of the action
        }
    -- ^ Pseudo substitution: match the source passive item against the leaf
    -- of the given active item
    | SubstA
        { _passArg :: A.Passive n t
        -- ^ The passive argument of the action
        , _outItem :: A.Item n t
        -- ^ The output active or passive item
        }
    -- ^ Pseudo substitution: substitute the leaf of the source item with
    -- the given passive item
    | FootA
        { _outItem :: A.Item n t
        -- ^ The output active or passive item
        , _theFoot :: A.Passive n t
        -- ^ The passive argument of the action
        -- TODO: is it useful at all?  Maybe it only makes things more difficult?
        }
    -- ^ Foot adjoin: match the foot of the source item with the given
    -- passive item
    | AdjoinP
        { _outItemP :: A.Passive n t
        -- ^ The output passive item
        , _passMod  :: A.Passive n t
        -- ^ The modified item
        }
    -- ^ Adjoin terminate: adjoin the source item to the given passive item
    | ModifyP
        { _passAdj  :: A.Passive n t
        -- ^ The adjoined item
        , _outItemP :: A.Passive n t
        -- ^ The output passive item
        }
    -- ^ Adjoin terminate: modify the source passive item with the given
    -- auxiliary item
    deriving (Show, Eq, Ord)


--------------------------------------------------
-- Dynamic construction of `RevHype`
--------------------------------------------------


-- | Derivation monad.
type DerivM n t m = RWS.RWST
  (DerivR n) () (DerivS n t)
  (P.Producer (Deriv n t) m)


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


-- | Process a hypergraph modification.
procModif
  :: forall m n t. (Monad m, Ord n, Ord t)
  => A.HypeModif n t
  -> DerivM n t m ()
procModif A.HypeModif{..}
  | modifType == A.NewNode = void . runMaybeT $ do
      A.ItemP p <- return modifItem
      guard =<< lift (isFinal p)
      mapM_ (lift . lift . P.yield) $
        derivFromPassive p modifHype
  where
    -- Recursively explore the hypergraph starting from the new node and add all
    -- nodes and arcs to the inverse representation, if no present there yet.
    go :: A.Item n t -> DerivM n t m ()
    go node = do
      b <- hasNode node
      when (not b) $ do
        forM_ (S.toList $ ingoingArcs node modifHype) $ \trav -> do
          addArc node trav >> case trav of
            A.Scan{..} -> goA scanFrom
            A.Subst{..} -> goP passArg >> goA actArg
            -- TODO: below we don't explore the foot item
            A.Foot{..} -> goA actArg
            A.Adjoin{..} -> goP passAdj >> goP passMod
    -- Versions of `go` specialized to active and passive items
    goA = go . A.ItemA
    goP = go . A.ItemP


-- | Retrieve the set/list of arcs ingoing to the given hypergraph node.
ingoingArcs
  :: (Ord n, Ord t)
  => A.Item n t
  -> A.Hype n t
  -> S.Set (A.Trav n t)
ingoingArcs item hype = getTrav $ case item of
  A.ItemA a -> A.activeTrav a hype
  A.ItemP p -> A.passiveTrav p hype
  where
    getTrav = \case
      Nothing -> S.empty
      Just ew -> A.prioTrav ew


-- | Does the inversed representation of the hypergraph contain the given node?
hasNode :: (Monad m, Ord n) => A.Item n t -> DerivM n t m Bool
hasNode item = do
  rev <- RWS.gets doneReversed
  return $ M.member item rev


-- | Add a node to the inversed representation of the hypergraph. Nothing about
-- the ingoing or outgoing arcs is known at this moment.
addNode :: (Monad m, Ord n) => A.Item n t -> DerivM n t m ()
addNode item = RWS.modify' $ \RevHype{..} ->
  let rev = M.insert item S.empty doneReversed
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
    [ (A.ItemA scanFrom, ScanA item _scanTerm) ]
  A.Subst{..} ->
    [ (A.ItemP passArg, SubstP item actArg)
    , (A.ItemA actArg, SubstA passArg item) ]
  A.Foot{..} ->
    [ (A.ItemA actArg, FootA item _theFoot) ]
  A.Adjoin{..} ->
    let target = pass item in
    [ (A.ItemP passAdj, AdjoinP target passMod)
    , (A.ItemP passMod, ModifyP passAdj target) ]
  where
    pass (A.ItemP p) = p
    pass _ = error "turnAround.pass: expected passive item, got active"


-- -- | A producer which generates the subsequent derivations encoded in the
-- -- progressively constructed hypergraph represented by the input producer.
-- derivsPipe
--   :: (Monad m, Ord n, Ord t)
--   => n                 -- ^ The start symbol
--   -> Int               -- ^ The length of the input sentence
--   -> P.Producer (A.HypeModif n t) m a
--   -- ^ The producer representing dynamic construction of a hypergraph
--   -> P.Producer (Deriv n t) m a
-- derivsPipe start len modifPipe = P.for modifPipe (pipeDerivs start len)
--
--
-- -- | Generate derivations based on the given latest hypergraph modification.
-- --
-- -- TODO: at the moment the function doesn't guarantee to not to generate
-- -- duplicate derivations (in particular, it doesn't check the status of the
-- -- input hypergraph modification -- whether it is `A.NewNode` or `A.NewArcs`
-- -- only).
-- pipeDerivs
--   :: (Monad m, Ord n, Ord t)
--   => n                 -- ^ The start symbol
--   -> Int               -- ^ The length of the input sentence
--   -> A.HypeModif n t
--   -> P.Producer (Deriv n t) m ()
-- pipeDerivs start len A.HypeModif{..} = case modifItem of
--   A.ItemP p -> if isFinal start len p
--     then mapM_ P.yield $ derivFromPassive p modifHype
--     else return ()
--   _ -> return ()



--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | Check whether the given passive item is final or not.
isFinal
  :: (Monad m, Eq n)
  => A.Passive n t -- ^ The item to check
  -> DerivM n t m Bool
isFinal p = do
  DerivR{..} <- RWS.ask
  return $ isFinal_ startSym sentLen p


-- | Check whether the given passive item is final or not.
isFinal_
  :: (Eq n)
  => n             -- ^ The start symbol
  -> Int           -- ^ The length of the input sentence
  -> A.Passive n t -- ^ The item to check
  -> Bool
isFinal_ start n p =
  p ^. A.spanP ^. A.beg == 0 &&
  p ^. A.spanP ^. A.end == n &&
  p ^. A.dagID == Left start &&
  p ^. A.spanP ^. A.gap == Nothing
