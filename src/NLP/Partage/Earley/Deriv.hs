{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE DeriveFunctor       #-}


module NLP.Partage.Earley.Deriv
(
-- * Types
  Deriv
, TokDeriv
, DerivNode (..)

-- * Extracting derivations
, derivTrees

-- * Showing
, PrintNode (..)
, deriv4show
) where


-- import           Control.Monad             (guard)
-- import qualified Control.Monad.RWS.Strict  as RWS
-- import           Control.Monad.Trans.Class (lift)
-- import           Control.Monad.Trans.Maybe (MaybeT (..))

-- import           Data.Monoid              (Monoid)
-- import qualified Data.Monoid              as Monoid
-- import           Data.Function             (on)
import           Data.Lens.Light
-- import qualified Data.Map.Strict           as M
import           Data.Maybe                (maybeToList)
-- import qualified Data.PSQueue              as Q
import qualified Data.Set                  as S
import qualified Data.Tree                 as R
-- import qualified Data.Traversable           as Trav

-- import qualified Pipes                     as P
-- import qualified Pipes.Prelude              as P

import qualified NLP.Partage.DAG           as DAG
import qualified NLP.Partage.Earley.Base   as B
import           NLP.Partage.Earley.Trav   (Trav(..))
import qualified NLP.Partage.Earley.Parser as P
import qualified NLP.Partage.Earley.Auto   as Auto
import qualified NLP.Partage.Earley.Item   as I
import qualified NLP.Partage.Tree.Other    as O
import qualified NLP.Partage.Tree.Comp     as C
import qualified NLP.Partage.FSTree        as FSTree


---------------------------
-- Derivation Trees
---------------------------


-- | Derivation tree is similar to `O.Tree` but additionally includes
-- potential modifications aside the individual nodes.  Modifications
-- themselves take the form of derivation trees.  Whether the modification
-- represents a substitution or an adjunction can be concluded on the basis of
-- the type (leaf or internal) of the node.
type Deriv n t v = R.Tree (DerivNode n t v)


-- | A node of a derivation tree.
data DerivNode n t v = DerivNode
  { node  :: O.Node n t
  , value :: Maybe v
  , modif :: [Deriv n t v]
  } deriving (Eq, Ord, Show, Functor)


-- | Derivation based on tokens.
type TokDeriv n t v = Deriv n (B.Tok t) v


-- | PrintNode tells wheter the node in the pretiffied derivation tree
-- is a modifier or not.
data PrintNode a
  = Regular a
  | Dependent
  deriving (Eq, Ord)


instance Show a => Show (PrintNode a) where
  show (Regular x) = show x
  show Dependent = "<<Dependent>>"


-- | Transform the derivation tree into a tree which is easier
-- to draw using the standard `R.draw` function.
-- `fst` values in nodes are `False` for modifiers.
deriv4show :: Deriv n t v -> R.Tree (PrintNode (O.Node n t, Maybe v))
deriv4show =
  go False
  where
    go isMod t = addDep isMod $ R.Node
      { R.rootLabel = Regular . ((,) <$> node <*> value) . R.rootLabel $ t
      , R.subForest = map (go False) (R.subForest t)
                   ++ map (go True) (modif $ R.rootLabel t) }
    addDep isMod t
      | isMod == True = R.Node Dependent [t]
      | otherwise = t


--------------------------------------------------
-- Utilities for constructing derivations
--------------------------------------------------


-- | Construct a derivation tree on the basis of the underlying passive
-- item, current child derivation and previous children derivations.
mkTree :: a -> [R.Tree a] -> R.Tree a
mkTree x ts = R.Node
  { R.rootLabel = x
  , R.subForest = reverse ts }


-- | An inverse of `mkTree`:
-- mkTree x ts == t => unTree t == (x, ts)
unTree :: R.Tree a -> (a, [R.Tree a])
unTree (R.Node x ts) = (x, reverse ts)


-- -- | Inverse of `mkTree`.
-- -- mkTree h p ts == d => unTree h p d == Just ts
-- unTree
--   :: (Ord n)
--   => P.Hype n t v
--   -> I.Passive v
--   -> TokDeriv n t v
--   -> Maybe [TokDeriv n t v]
-- unTree hype p deriv = do
--   guard $ R.rootLabel deriv == mkRoot hype p
--   return . reverse $ R.subForest deriv

-- | Construct a derivation node with no modifier.
only :: Maybe v -> O.Node n t -> DerivNode n t v
only v x = DerivNode {node = x, value = v, modif = []}

-- | Several constructors which allow to build non-modified nodes.
mkRoot :: P.Hype n t v -> Maybe v -> I.Passive v -> DerivNode n (B.Tok t) v
mkRoot hype v p = only v . O.NonTerm $ nonTerm (getL I.dagID p) hype

mkFoot :: Maybe v -> n -> DerivNode n t v
mkFoot v = only v . O.Foot

mkTerm :: Maybe v -> t -> DerivNode n t v
mkTerm v = only v . O.Term

-- | Build non-modified nodes of different types.
footNode :: Maybe v -> n -> Deriv n t v
footNode v x = R.Node (mkFoot v x) []

termNode :: Maybe v -> t -> Deriv n t v
termNode v x = R.Node (mkTerm v x) []

-- | Retrieve root non-terminal of a derivation tree.
derivRoot :: Deriv n t v -> n
derivRoot R.Node{..} = case node rootLabel of
  O.NonTerm x -> x
  O.Foot _ -> error "passiveDerivs.getRoot: got foot"
  O.Term _ -> error "passiveDerivs.getRoot: got terminal"

-- | Construct substitution node stemming from the given derivation.
substNode :: Maybe v -> I.NonActive n v -> TokDeriv n t v -> TokDeriv n t v
substNode _ (Left _p) t = t
substNode v (Right _p) t = flip R.Node [] $ DerivNode
  { node  = O.NonTerm (derivRoot t)
  , value = v
  , modif = [t] }
--   | I.isRoot (p ^. E.dagID) = flip R.Node [] $ DerivNode
--     { node = O.NonTerm (derivRoot t)
--     , modif   = [t] }
--   | otherwise = t

-- -- | Inverse of `substNode`.
-- -- substNode p t == t' => unSubstNode o t' == Just t
-- -- TODO: reimplement this function so that (Eq t) is not needed (it isn't really).
-- unSubstNode :: (Eq n, Eq t) => I.NonActive n v -> Deriv n t -> Maybe (Deriv n t)
-- unSubstNode (Left _p) t' = Just t'
-- unSubstNode (Right p) t' = do
--   R.Node DerivNode{..} [] <- return t'
--   [t] <- return modif
--   guard $ node == O.NonTerm (derivRoot t)
--   return t
-- --   | E.isRoot (p ^. E.dagID) = do
-- --       R.Node DerivNode{..} [] <- return t'
-- --       [t] <- return modif
-- --       guard $ node == O.NonTerm (derivRoot t)
-- --       return t
-- --   | otherwise = Just t'

-- | Add the auxiliary derivation to the list of modifications of the
-- initial derivation.
adjoinTree :: v -> Deriv n t v -> Deriv n t v -> Deriv n t v
adjoinTree val ini aux = R.Node
  { R.rootLabel = let root = R.rootLabel ini in DerivNode
    { node  = node root
    , value = Just val
    , modif = aux : modif root }
  , R.subForest = R.subForest ini }

-- -- | Unverse of `adjoinTree`.
-- -- adjoinTree ini aux == cmb => unAjoinInit cmb == Just (ini, aux)
-- unAdjoinTree :: Deriv n t -> Maybe (Deriv n t, Deriv n t)
-- unAdjoinTree cmb = do
--   subForestIni <- return (R.subForest cmb)
--   DerivNode{..} <- return (R.rootLabel cmb)
--   let nodeRootLabelIni = node
--   aux : modifRootLabelIni <- return modif
--   let rootLabelIni = DerivNode
--         { node = nodeRootLabelIni
--         , modif = modifRootLabelIni }
--       ini = R.Node
--         { R.rootLabel = rootLabelIni
--         , R.subForest = subForestIni }
--   return (ini, aux)

-------------------------------
-- Extracting Derivation Trees
-------------------------------


-- | Extract derivation trees obtained on the given input sentence. Should be
-- run on the final result of the earley parser.
derivTrees
    :: (Ord t, Ord n, Ord v, B.Unify v)
    => P.Hype n t v -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> [TokDeriv n t v]
derivTrees hype start n
  = concatMap (\top -> fromTop (top ^. I.value) top hype)
  $ P.finalFrom start n hype


-- | Extract derivation trees represented by the given passive item.
fromTop
  :: (Ord t, Ord n, Ord v, B.Unify v)
  => v -- ^ The value percolating downwards
  -> I.Top n v
  -> P.Hype n t v
  -> [TokDeriv n t v]
fromTop topVal top hype = case P.topTrav top hype of
  Nothing -> error "fromTop: top item unknown"
  Just travSet -> concat
    [ fromTopTrav top trav
    | trav <- S.toList travSet ]
  where
    fromTopTrav _p (Fini q) = do
      let dag = Auto.gramDAG . P.automat $ hype
      C.Comp{..} <- maybeToList $ DAG.value (q ^. I.dagID) dag
      -- trace <- maybeToList $ FSTree.unifyRoot topVal (q ^. I.traceP)
      let trace = q ^. I.traceP
      -- let trace  = q ^. I.traceP
      let trace' = topDown topVal trace
      if R.rootLabel trace' == Nothing
        then error "fromTop.fromTopTrav: impossible happened 2"
        else return ()
      fromPassive trace' q hype
    fromTopTrav _p _ = error "fromTop.fromTopTrav: impossible happened"


-- | Extract derivation trees represented by the given passive item.
fromPassive
  :: (Ord n, Ord t, Ord v, B.Unify v)
  => C.Env v -- ^ The values percolating downwards
  -> I.Passive v
  -> P.Hype n t v
  -> [TokDeriv n t v]
fromPassive topEnv passive hype = case P.passiveTrav passive hype of
  Nothing -> error "fromPassive: passive item unknown"
  Just travSet -> concat
    [ fromPassiveTrav topEnv passive trav hype
    | trav <- S.toList travSet ]


-- | Extract derivation trees represented by the given passive item
-- and the corresponding input traversal.
fromPassiveTrav
  :: (Ord n, Ord t, Ord v, B.Unify v)
  => C.Env v -- ^ The values percolating downwards
  -> I.Passive v
  -> Trav n t v
  -> P.Hype n t v
  -> [TokDeriv n t v]
fromPassiveTrav topEnv p trav hype = case trav of
  Deact qa ->
    [ mkTree (mkRoot hype v p) ts
    | let (v, vs) = unTree topEnv
    , ts <- fromActive vs qa hype ]
  Adjoin qa qm ->
    [ adjoinTree rootVal ini aux
    | aux <- fromTop rootVal qa hype
    , ini <- fromPassive topEnv qm hype ]
  _ -> error "fromPassiveTrav: impossible happened"
  where
    rootVal = check $ R.rootLabel topEnv
    check may = case may of
      Just  x -> x
      Nothing -> error "fromPassiveTrav: impossible happened 2"


-- | Extract derivations represented by the given active item.
fromNonActive
  :: (Ord n, Ord t, Ord v, B.Unify v)
  => C.Env v -- ^ The values percolating downwards
  -> I.NonActive n v
  -> P.Hype n t v
  -> [TokDeriv n t v]
fromNonActive topEnv nonActive = case nonActive of
  Left p -> fromPassive topEnv p
  Right p -> fromTop (check $ R.rootLabel topEnv) p
  where
    check may = case may of
      Just  x -> x
      Nothing -> error "fromNonActive: impossible happened"


-- | Extract derivations represented by the given active item.
fromActive
  :: (Ord n, Ord t, Ord v, B.Unify v)
  => [C.Env v] -- ^ The values percolating downwards
  -> I.Active v
  -> P.Hype n t v
  -> [[TokDeriv n t v]]
fromActive topEnv active hype = case P.activeTrav active hype of
  Nothing  -> error "fromActive: active item unknown"
  Just travSet -> if S.null travSet
    then [[]]
    else concatMap
         (\trav -> fromActiveTrav topEnv active trav hype)
         (S.toList travSet)


-- | Extract derivation trees represented by the given active item
-- and the corresponding input traversal.
fromActiveTrav
  :: (Ord n, Ord t, Ord v, B.Unify v)
  => [C.Env v] -- ^ The values percolating downwards
  -> I.Active v
  -> Trav n t v
  -> P.Hype n t v
  -> [[TokDeriv n t v]]
fromActiveTrav topEnv _p trav hype = case trav of
  Scan q t ->
    [ termNode (R.rootLabel v) t : ts
    | ts <- fromActive vs q hype ]
  Subst qp qa ->
    [ substNode (R.rootLabel v) qp t : ts
    | ts <- fromActive vs qa hype
    , t  <- fromNonActive v qp hype ]
  Foot q x ->
    [ footNode (R.rootLabel v) x : ts
    | ts <- fromActive vs q hype ]
  _ -> error "fromActiveTrav: impossible happened"
  where
    (v, vs) = case topEnv of
      [] -> error "fromActiveTrav: impossible happened 2"
      x : xs -> (x, xs)


--------------------------------------------------
-- Check if derivation trees is in the graph
--------------------------------------------------


-- -- | Check if the derivation is present in the chart.
-- --
-- -- TODO: The start symbol and the sentence length could be computed
-- -- automatically, based on the input derivation.
-- encodes
--     :: (Ord n, Ord t)
--     => A.Hype n t   -- ^ Final state of the earley parser
--     -> n            -- ^ The start symbol
--     -> Int          -- ^ Length of the input sentence
--     -> Deriv n (Tok t)
--     -> Bool
-- encodes hype begSym sentLen deriv = or
--   [ passiveEncodes p hype deriv
--   | p <- A.finalFrom begSym sentLen hype ]
-- --   where
-- --     begSym = undefined
-- --     sentLen = undefined
--
--
-- -- | Check if the derivation is represented by the passive item.
-- passiveEncodes
--   :: (Ord n, Ord t)
--   => A.Passive n t
--   -> A.Hype n t
--   -> Deriv n (Tok t)
--   -> Bool
-- passiveEncodes passive hype deriv = case A.passiveTrav passive hype of
--   Nothing -> case Q.lookup (A.ItemP passive) (A.waiting hype) of
--     Just _ -> error "fromPassive: passive item in the waiting queue"
--     Nothing -> error "fromPassive: unknown passive item (not even in the queue)"
--   Just ext -> or
--     [ passiveTravEncodes passive trav hype deriv
--     | trav <- S.toList (A.prioTrav ext) ]
--
--
-- -- | Check if the derivation is represented by the passive item
-- -- together with the corresponding traversal (hyperarc).
-- passiveTravEncodes
--   :: (Ord n, Ord t)
--   => A.Passive n t
--   -> A.Trav n t
--   -> A.Hype n t
--   -> Deriv n (Tok t)
--   -> Bool
-- passiveTravEncodes p trav hype root = case trav of
--
--   A.Scan q t _ -> isJust $ do
--     deriv : ts <- unTree hype p root
--     guard $ deriv == termNode t
--     guard $ activeEncodes q hype ts
--
-- --     [ mkTree hype p (termNode t : ts)
-- --     | ts <- activeDerivs q ]
--
--   A.Foot q x _ -> isJust $ do
--     deriv : ts <- unTree hype p root
--     guard $ deriv == footNode x
--     guard $ activeEncodes q hype ts
--
-- --     [ mkTree hype p (footNode x : ts)
-- --     | ts <- activeDerivs q ]
--
--   A.Subst qp qa _ -> isJust $ do
--     deriv : ts <- unTree hype p root
--     t <- unSubstNode qp deriv
--     guard $ passiveEncodes qp hype t
--     guard $ activeEncodes qa hype ts
--
-- --     [ mkTree hype p (substNode qp t : ts)
-- --     | ts <- activeDerivs qa
-- --     , t  <- passiveDerivs qp ]
--
--   A.Adjoin qa qm -> isJust $ do
--     (ini, aux) <- unAdjoinTree root
--     guard $ passiveEncodes qa hype aux
--     guard $ passiveEncodes qm hype ini
--
-- --     [ adjoinTree ini aux
-- --     | aux <- passiveDerivs qa
-- --     , ini <- passiveDerivs qm ]
--
--
-- -- | Check if the derivation is represented by the active item.
-- activeEncodes
--   :: (Ord n, Ord t)
--   => A.Active
--   -> A.Hype n t
--   -> [Deriv n (Tok t)]
--   -> Bool
-- activeEncodes active hype deriv = case A.activeTrav active hype of
--   Nothing  -> case Q.lookup (A.ItemA active) (A.waiting hype) of
--     Just _ -> error $
--       "fromActive: active item in the waiting queue"
--       ++ "\n" ++ show active
--     Nothing -> error $
--       "fromActive: unknown active item (not even in the queue)"
--       ++ "\n" ++ show active
--   Just ext -> if S.null (A.prioTrav ext)
--     then deriv == []
--     else or
--          [ activeTravEncodes active trav hype deriv
--          | trav <- S.toList (A.prioTrav ext) ]
--
--
-- -- | Check if the derivation is represented by the active item
-- -- together with the corresponding traversal (hyperarc).
-- activeTravEncodes
--   :: (Ord n, Ord t)
--   => A.Active
--   -> A.Trav n t
--   -> A.Hype n t
--   -> [Deriv n (Tok t)]
--   -> Bool
-- activeTravEncodes _p trav hype root = case trav of
--
--   A.Scan q t _ -> isJust $ do
--     deriv : ts <- return root
--     guard $ deriv == termNode t
--     guard $ activeEncodes q hype ts
--
-- --     [ termNode t : ts
-- --     | ts <- activeDerivs q ]
--
--   A.Foot q x _ -> isJust $ do
--     deriv : ts <- return root
--     guard $ deriv == footNode x
--     guard $ activeEncodes q hype ts
--
-- --     [ footNode x : ts
-- --     | ts <- activeDerivs q ]
--
--   A.Subst qp qa _ -> isJust $ do
--     deriv : ts <- return root
--     t <- unSubstNode qp deriv
--     guard $ passiveEncodes qp hype t
--     guard $ activeEncodes qa hype ts
--
-- --     [ substNode qp t : ts
-- --     | ts <- activeDerivs qa
-- --     , t  <- passiveDerivs qp ]
--
--   A.Adjoin _ _ ->
--     error "fromActiveTrav: called on a passive item"
--
--
-- --------------------------------------------------
-- -- A reversed representation of a hypergraph
-- --------------------------------------------------
--
--
-- -- | A reverse representation of a hypergraph, i.e., a representation in which
-- -- outgoing hyperarcs (applications of inference rules) are stored for the
-- -- individual nodes (chart items) in the hypergraph.
-- --
-- -- Only the processed part of the hypergraph is stored.
-- data RevHype n t = RevHype
--   { doneReversed :: M.Map (A.Item n t) (S.Set (RevTrav n t)) }
--
--
-- -- | Empty `RevHype`.
-- emptyRevHype :: RevHype n t
-- emptyRevHype = RevHype M.empty
--
--
-- -- | An arc outgoing from a hypergraph node. A reversed representation w.r.t.
-- -- `A.Trav`.
-- --
-- -- TODO: we could try to express relations between items in `doneReversed`
-- -- (which would be then rewritten using two data structures?) and types of
-- -- outgoing edges.  For the moment, each constructor is adorned with a suffix
-- -- 'A' or 'P' which tells whether the source item can be passive or active
-- -- (or both, if no corresponding 'A' or 'P' suffix).
-- data RevTrav n t
--     = ScanA
--         { outItem  :: A.Item n t
--         -- ^ The output active or passive item
--         , scanTerm :: Tok t
--         -- ^ The scanned terminal
--         }
--     -- ^ Scan: scan the leaf terminal with a terminal from the input
--     | SubstP
--         { outItem :: A.Item n t
--         -- ^ The output active or passive item
--         , actArg  :: A.Active
--         -- ^ The active argument of the action
--         }
--     -- ^ Pseudo substitution: match the source passive item against the leaf
--     -- of the given active item
--     | SubstA
--         { passArg :: A.Passive n t
--         -- ^ The passive argument of the action
--         , outItem :: A.Item n t
--         -- ^ The output active or passive item
--         }
--     -- ^ Pseudo substitution: substitute the leaf of the source item with
--     -- the given passive item
--     | FootA
--         { outItem :: A.Item n t
--         -- ^ The output active or passive item
-- --         , theFoot :: A.Passive n t
-- --         -- ^ The passive argument of the action
--         , theFoot :: n
--         -- ^ The foot non-terminal
--         }
--     -- ^ Foot adjoin: match the foot of the source item with the given
--     -- passive item
--     | AdjoinP
--         { outItemP :: A.Passive n t
--         -- ^ The output passive item
--         , passMod  :: A.Passive n t
--         -- ^ The modified item
--         }
--     -- ^ Adjoin terminate: adjoin the source auxiliary item to
--     -- the given passive item
--     | ModifyP
--         { passAdj  :: A.Passive n t
--         -- ^ The adjoined item
--         , outItemP :: A.Passive n t
--         -- ^ The output passive item
--         }
--     -- ^ Adjoin terminate: modify the source passive item with the given
--     -- auxiliary item
--     deriving (Show, Eq, Ord)
--
--
-- ---------------------------------
-- -- Extracting Derivation Trees...
-- --
-- -- ...going through the given arc
-- ---------------------------------
--
--
-- -- | Extract derivations going through the given arc.
-- fromArc
--   :: (Ord n, Ord t)
--   => A.Item n t
--      -- ^ Target node
--   -> A.Trav n t
--      -- ^ Arc ingoing to the target node
--   -> A.Hype n t
--      -- ^ The corresponding hypergraph
--   -> RevHype n t
--      -- ^ The reversed version of the hypergraph
--   -> [Deriv n (Tok t)]
-- fromArc node arc hype revHype =
--   case node of
--     A.ItemP p ->
--       let derivs _ = fromPassiveTrav p arc hype
--       in  upFromPassive p derivs hype revHype
--     A.ItemA p ->
--       let derivs _ = fromActiveTrav p arc hype
--       in  upFromActive p derivs hype revHype
--
--
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
--
--
-- -- | Explor the hypergraph up in order to generate all final derivations which
-- -- go through the given item for which partial derivations are known.
-- upFromPassive
--   :: (Ord n, Ord t)
--   => A.Passive n t
--      -- ^ Passive node
--   -> (() -> [Deriv n (Tok t)])
--      -- ^ The list of derivation corresponding to the passive node
--   -> A.Hype n t
--   -> RevHype n t
--   -> [Deriv n (Tok t)]
-- upFromPassive passive passiveDerivs hype revHype =
--   case M.lookup (A.ItemP passive) (doneReversed revHype) of
--     Nothing -> error "upFromPassive: item with no respective entry in `RevHype`"
--     Just revTravSet -> if S.null revTravSet
--       then passiveDerivs () -- meaning that we got a final item, hopefully...
--       else concat
--            [ upFromPassiveTrav passive revTrav passiveDerivs hype revHype
--            | revTrav <- S.toList revTravSet ]
--
--
-- upFromPassiveTrav
--   :: (Ord n, Ord t)
--   => A.Passive n t
--      -- ^ Source hypernode (passive item)
--   -> RevTrav n t
--      -- ^ Traversal to be followed from the source node
--   -> (() -> [Deriv n (Tok t)])
--      -- ^ Derivation corresponding to the source node
--   -> A.Hype n t
--   -> RevHype n t
--   -> [Deriv n (Tok t)]
-- upFromPassiveTrav source revTrav sourceDerivs hype revHype =
--   case revTrav of
--     SubstP{..} ->
--       -- we now have a passive source, another active source, and an unknown target;
--       -- based on that, we create a list of derivations of the source nodes.
--       let combinedDerivs _ =
--             [ substNode source t : ts
--             | ts <- fromActive actArg hype
--             , t  <- sourceDerivs () ]
--       -- once we have the combined derivations of the source nodes, we proceed upwards
--       -- by going to the unkown target item with the derivations we have
--       in  upFromItem outItem combinedDerivs hype revHype
--     AdjoinP{..} ->
--       let combinedDerivs _ =
--             [ adjoinTree ini aux
--             | aux <- sourceDerivs ()
--             , ini <- fromPassive passMod hype ]
--       in  upFromPassive outItemP combinedDerivs hype revHype
--     ModifyP{..} ->
--       let combinedDerivs _ =
--             [ adjoinTree ini aux
--             | aux <- fromPassive passAdj hype
--             , ini <- sourceDerivs () ]
--       in  upFromPassive outItemP combinedDerivs hype revHype
--     _ -> error "upFromPassiveTrav: got an 'active' traversal for a passive item"
--
--
-- -- | Explor the hypergraph up in order to generate all final derivations which
-- -- go through the given item for which partial derivations are known.
-- upFromActive
--   :: (Ord n, Ord t)
--   => A.Active
--   -> (() -> [[Deriv n (Tok t)]])
--   -- ^ Derivation corresponding to the active node
--   -> A.Hype n t
--   -> RevHype n t
--   -> [Deriv n (Tok t)]
-- upFromActive active activeDerivs hype revHype = concat
--   [ upFromActiveTrav active revTrav activeDerivs hype revHype
--   | revTravSet <- maybeToList $ M.lookup (A.ItemA active) (doneReversed revHype)
--   , revTrav <- S.toList revTravSet ]
--
--
-- upFromActiveTrav
--   :: (Ord n, Ord t)
--   => A.Active
--      -- ^ Source hypernode (active item)
--   -> RevTrav n t
--      -- ^ Traversal to be followed from the source node
--   -> (() -> [[Deriv n (Tok t)]])
--      -- ^ Derivation corresponding to the source node
--   -> A.Hype n t
--   -> RevHype n t
--   -> [Deriv n (Tok t)]
-- upFromActiveTrav _source revTrav sourceDerivs hype revHype =
--   case revTrav of
--     ScanA{..} ->
--       let combinedDerivs _ =
--             [ termNode scanTerm : ts
--             | ts <- sourceDerivs () ]
--       in  upFromItem outItem combinedDerivs hype revHype
--     SubstA{..} ->
--       let combinedDerivs _ =
--             [ substNode passArg t : ts
--             | ts <- sourceDerivs () -- fromActive actArg hype
--             , t  <- fromPassive passArg hype ]
--       in  upFromItem outItem combinedDerivs hype revHype
--     FootA{..} ->
--       let combinedDerivs _ =
--             [ footNode theFoot : ts
--             | ts <- sourceDerivs () ]
--       in  upFromItem outItem combinedDerivs hype revHype
--     _ -> error "upFromActiveTrav: got an 'passive' traversal for an active item"


-- --------------------------------------------------
-- -- Dynamic construction of `RevHype`
-- --------------------------------------------------
--
--
-- -- | Modifications corresponding to the given hypergraph modification.
-- type ModifDerivs n t = (A.HypeModif n t, [Deriv n (Tok t)])
--
--
-- -- | Derivation monad.
-- type DerivM n t m = RWS.RWST
--   (DerivR n) () (DerivS n t)
--   (P.Pipe (A.HypeModif n t) (ModifDerivs n t) m)
--
--
-- -- | Reader component of `DerivM`.
-- data DerivR n = DerivR
--   { startSym :: n
--     -- ^ Start symbol of the grammar
--   , sentLen  :: Int
--     -- ^ Length of the input sentence
--   } deriving (Show, Eq, Ord)
--
--
-- -- | State component of `DerivM`.
-- -- data DerivS n t = DerivS
-- type DerivS n t = RevHype n t
--
--
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
--
--
-- -- NOTE: The function below has no right to exist. It runs the underlying State
-- -- monad whose results are immediately lost after the call. Such behavior is
-- -- unacceptable because the underlying state needs to be preserved throughout
-- -- the entire process of the Earley parsing algorithm.
-- --
-- -- CONCLUSION: we need to change the type of the `derivsPipe` so that it returns
-- -- not only the derivations but also the source hypergraph modifications. For
-- -- each hypergraph modification, a separate pipe should be created (why shouldn't
-- -- it be possible?) which enumerates the individual derivations corresponding for
-- -- this specific hypergraph modification.
-- --
-- -- -- | Generate derivation trees for a given hypergraph modification
-- -- -- and print them to stdin.
-- -- procAndPrint
-- --   :: (Ord t, Ord n, Show n, Show t)
-- --   => n -- ^ The start symbol
-- --   -> A.Input t
-- --   -> A.HypeModif n t
-- --   -> IO ()
-- -- procAndPrint start input modif = void . P.runEffect $
-- --   P.for pipe $ \t ->
-- --     lift . putStrLn . R.drawTree . fmap show . deriv4show $ t
-- --   where
-- --     pipe = P.yield modif P.>-> derivsPipe conf
-- --     conf = DerivR
-- --       { startSym = start
-- --       , sentLen = length $ A.inputSent input }
--
--
-- -- -- | A pipe which transforms hypergraph modifications to the
-- -- -- corresponding derivations.
-- -- derivsPipe
-- --   :: (MonadIO m, Ord n, Ord t)
-- --   => DerivR n
-- --   -> P.Pipe (A.HypeModif n t) (Deriv n t) m a
-- -- derivsPipe conf =
-- --   fst <$> RWS.evalRWST loop conf emptyRevHype
-- --   where
-- --     loop = do
-- --       hypeModif <- lift P.await
-- --       procModif hypeModif
-- --       loop
--
--
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
--
--
-- -- | Process a hypergraph modification.
-- procModif
--   :: forall m n t. (Monad m, Ord n, Ord t)
--   => A.HypeModif n t
--   -> DerivM n t m [Deriv n (Tok t)]
-- procModif A.HypeModif{..}
--   | modifType == A.NewNode = fmap (maybe [] id) . runMaybeT $ do
--       -- liftIO $ putStrLn "<<NewNode>>"
--       A.ItemP p <- return modifItem
--       guard =<< lift (isFinal p)
--       -- liftIO $ putStrLn "<<NewNode->isFinal>>"
--       lift $ goNode modifItem
--       return $ fromPassive p modifHype
--   | otherwise = do -- `modifType == A.NewArcs`
--       -- rev <- RWS.gets doneReversed
--       -- liftIO $ putStrLn $ "<<NewArcs>> " ++ show (M.size rev)
--       -- check if the node is already in the reversed hypergraph; otherwise, it
--       -- is not reachable from any final item so we can ignore it
--       b <- hasNode modifItem
--       if b then do
--         -- liftIO $ putStrLn "<<NewArcs->hasNode>>"
--         goChildren modifItem (A.prioTrav modifTrav)
--         revHype <- RWS.get
--         let derivs = concatMap
--               (\arc -> fromArc modifItem arc modifHype revHype)
--               (S.toList $ A.prioTrav modifTrav)
--         -- liftIO . putStrLn $ "<<NewArcs->" ++
--         --   show (length . S.toList $ A.prioTrav modifTrav) ++
--         --   " arcs>>"
--         -- liftIO . putStrLn $ "<<NewArcs->" ++ show (length derivs) ++ " derivs>>"
--         return derivs
--       else return []
--   where
--     -- Recursively explore the hypergraph starting from the given node and add
--     -- all nodes and arcs to the inverse representation, if not present there
--     -- yet.
--     goNode :: A.Item n t -> DerivM n t m ()
-- --     goNode node = addNode node >> goChildren node
--     goNode node = do
--       b <- hasNode node
--       -- liftIO $ putStrLn $ "goNode->hasNode: " ++ show b
--       when (not b) $ do
--         -- liftIO $ putStrLn "goNode->addNode"
--         addNode node >> goChildren node (ingoingArcs node modifHype)
--     -- Explore arcs ingoing to the given target node.
--     goChildren node arcs = mapM_ (goArc node) (S.toList arcs)
--     -- Similar to `goNode`, but exploration begins with a specific arc
--     -- leading to the corresponding target node.
--     goArc node arc = addArc node arc << case arc of
--       A.Scan{..} -> goNodeA scanFrom
--       A.Subst{..} -> goNodeP passArg >> goNodeA actArg
--       A.Foot{..} -> goNodeA actArg
--       A.Adjoin{..} -> goNodeP passAdj >> goNodeP passMod
--       where m << n = n >> m
--     -- Versions of `goNode` specialized to active and passive items
--     goNodeA = goNode . A.ItemA
--     goNodeP = goNode . A.ItemP
--
--
-- -- | Retrieve the set/list of arcs ingoing to the given hypergraph node.
-- ingoingArcs
--   :: (Ord n, Ord t)
--   => A.Item n t
--   -> A.Hype n t
--   -> S.Set (A.Trav n t)
-- ingoingArcs item hype = getTrav $ case item of
--   A.ItemA a -> A.activeTrav a hype
--   A.ItemP p -> A.passiveTrav p hype
--   where
--     getTrav = \case
--       -- Nothing -> S.empty
--       Nothing -> error
--         "ingoingArcs: no traversals corresponding to the given item"
--       Just ew -> A.prioTrav ew
--
--
-- -- | Does the inversed representation of the hypergraph contain the given node?
-- hasNode :: (Monad m, Ord n) => A.Item n t -> DerivM n t m Bool
-- hasNode item = do
--   rev <- RWS.gets doneReversed
--   return $ M.member item rev
--
--
-- -- | Add a node to the inversed representation of the hypergraph. Nothing about
-- -- the ingoing or outgoing arcs is known at this moment.
-- addNode :: (Monad m, Ord n, Ord t) => A.Item n t -> DerivM n t m ()
-- addNode item = RWS.modify' $ \RevHype{..} ->
--   let rev = M.insertWith S.union item S.empty doneReversed
--   in  RevHype {doneReversed = rev}
--
--
-- -- | Add an arc to the inversed representation of the hypergraph.
-- addArc
--   :: (Monad m, Ord n, Ord t)
--   => A.Item n t
--      -- ^ Node to which the arc leads
--   -> A.Trav n t
--      -- ^ Arc to add
--   -> DerivM n t m ()
-- addArc item trav = RWS.modify' $ \RevHype{..} ->
--   let rev = doneReversed `modifyWith`
--             [addOne p t | (p, t) <- turnAround item trav]
--             -- map (uncurry addOne) (turnAround item trav)
--   in  RevHype {doneReversed = rev}
--   where
--     modifyWith = flip applyAll
--     addOne revItem revTrav =
--       M.insertWith S.union revItem (S.singleton revTrav)
--
--
-- -- | Apply a list of transformations to a given argument.
-- applyAll :: [a -> a] -> a -> a
-- applyAll funs x = case funs of
--   f : fs -> f (applyAll fs x)
--   [] -> x
--
--
-- -- | Retrieve outgoing arcs from the given ingoing arc.
-- turnAround
--   :: A.Item n t
--      -- ^ Target node
--   -> A.Trav n t
--      -- ^ Arc ingoing to the target node
--   -> [(A.Item n t, RevTrav n t)]
-- turnAround item trav = case trav of
--   A.Scan{..} ->
--     [ (A.ItemA scanFrom, ScanA item _scanTerm) ]
--   A.Subst{..} ->
--     [ (A.ItemP passArg, SubstP item actArg)
--     , (A.ItemA actArg, SubstA passArg item) ]
--   A.Foot{..} ->
--     [ (A.ItemA actArg, FootA item theFoot) ]
--   A.Adjoin{..} ->
--     let target = pass item in
--     [ (A.ItemP passAdj, AdjoinP target passMod)
--     , (A.ItemP passMod, ModifyP passAdj target) ]
--   where
--     pass (A.ItemP p) = p
--     pass _ = error "turnAround.pass: expected passive item, got active"
--
--
-- -- -- | A producer which generates the subsequent derivations encoded in the
-- -- -- progressively constructed hypergraph represented by the input producer.
-- -- derivsPipe
-- --   :: (Monad m, Ord n, Ord t)
-- --   => n                 -- ^ The start symbol
-- --   -> Int               -- ^ The length of the input sentence
-- --   -> P.Producer (A.HypeModif n t) m a
-- --   -- ^ The producer representing dynamic construction of a hypergraph
-- --   -> P.Producer (Deriv n t) m a
-- -- derivsPipe start len modifPipe = P.for modifPipe (pipeDerivs start len)
-- --
-- --
-- -- -- | Generate derivations based on the given latest hypergraph modification.
-- -- --
-- -- -- TODO: at the moment the function doesn't guarantee to not to generate
-- -- -- duplicate derivations (in particular, it doesn't check the status of the
-- -- -- input hypergraph modification -- whether it is `A.NewNode` or `A.NewArcs`
-- -- -- only).
-- -- pipeDerivs
-- --   :: (Monad m, Ord n, Ord t)
-- --   => n                 -- ^ The start symbol
-- --   -> Int               -- ^ The length of the input sentence
-- --   -> A.HypeModif n t
-- --   -> P.Producer (Deriv n t) m ()
-- -- pipeDerivs start len A.HypeModif{..} = case modifItem of
-- --   A.ItemP p -> if isFinal start len p
-- --     then mapM_ P.yield $ fromPassive p modifHype
-- --     else return ()
-- --   _ -> return ()
--
--
--
-- --------------------------------------------------
-- -- Utilities
-- --------------------------------------------------
--
--
-- -- | Check whether the given passive item is final or not.
-- isFinal
--   :: (Monad m, Eq n)
--   => A.Passive n t -- ^ The item to check
--   -> DerivM n t m Bool
-- isFinal p = do
--   DerivR{..} <- RWS.ask
--   return $ isFinal_ startSym sentLen p
--
--
-- -- | Check whether the given passive item is final or not.
-- isFinal_
--   :: (Eq n)
--   => n             -- ^ The start symbol
--   -> Int           -- ^ The length of the input sentence
--   -> A.Passive n t -- ^ The item to check
--   -> Bool
-- isFinal_ start n p =
--   p ^. A.spanP ^. A.beg == 0 &&
--   p ^. A.spanP ^. A.end == n &&
--   p ^. A.dagID == Left start &&
--   p ^. A.spanP ^. A.gap == Nothing
--
--
-- -- -- | ListT from a list.
-- -- each :: Monad m => [a] -> P.ListT m a
-- -- each = P.Select . P.each


-- | Take the non-terminal of the underlying DAG node.
nonTerm :: DAG.DID -> P.Hype n t a -> n
nonTerm did = B.nonTerm did . P.automat
