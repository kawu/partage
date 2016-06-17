{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}


module NLP.Partage.AStar.Deriv
( Deriv
, DerivNode (..)
, derivTrees
, fromPassive
, deriv4show
-- , deriv2tree
-- , expandDeriv
-- -- , fromPassive'
-- -- , fromActive'

, RevHype (..)
, DerivR (..)
, derivsPipe
, parseAndPrint
-- , procAndPrint
) where


import           Control.Monad             (forM_, guard, void, when)
import           Control.Monad.IO.Class    (MonadIO (..), liftIO)
import qualified Control.Monad.RWS.Strict  as RWS
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe (MaybeT (..))

import           Data.Lens.Light
import qualified Data.Map.Strict           as M
import           Data.Maybe                (maybeToList)
import qualified Data.PSQueue              as Q
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



-- | NodeStatus tells wheter the node in the pretiffied derivation tree
-- is a modifier or note.
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


-- | Extract derivation trees obtained on the given input sentence. Should be
-- run on the final result of the earley parser.
derivTrees
    :: (Ord n, Ord t)
    => A.Hype n t   -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> [Deriv n t]
derivTrees hype start n
    = concatMap (`fromPassive` hype)
    $ A.finalFrom start n hype


-- | Extract the set of the parsed trees w.r.t. to the given passive item.
fromPassive :: forall n t. (Ord n, Ord t) => A.Passive n t -> A.Hype n t -> [Deriv n t]
fromPassive passive hype = case A.passiveTrav passive hype of
  Nothing -> case Q.lookup (A.ItemP passive) (A.waiting hype) of
    Just _ -> error "fromPassive: passive item in the waiting queue"
    Nothing -> error "fromPassive: unknown passive item (not even in the queue)"
  Just ext -> concat
    [ fromPassiveTrav passive trav hype
    | trav <- S.toList (A.prioTrav ext) ]

-- fromPassive passive hype = concat
--   [ fromPassiveTrav passive trav hype
--   | ext <- maybeToList $ A.passiveTrav passive hype
--   , trav <- S.toList (A.prioTrav ext) ]


fromPassiveTrav :: (Ord n, Ord t) => A.Passive n t -> A.Trav n t -> A.Hype n t -> [Deriv n t]
fromPassiveTrav p trav hype = case trav of
  A.Scan q t _ ->
    [ mkTree hype p (termNode t : ts)
    | ts <- activeDerivs q ]
  A.Foot q x _ ->
    [ mkTree hype p (footNode x : ts)
    | ts <- activeDerivs q ]
  A.Subst qp qa _ ->
    [ mkTree hype p (substNode qp t : ts)
    | ts <- activeDerivs qa
    , t  <- passiveDerivs qp ]
  A.Adjoin qa qm ->
    [ adjoinTree ini aux
    | aux <- passiveDerivs qa
    , ini <- passiveDerivs qm ]
  where
    passiveDerivs = flip fromPassive hype
    activeDerivs  = flip fromActive  hype


-- | Extract the set of the parsed trees w.r.t. to the given active item.
fromActive :: (Ord n, Ord t) => A.Active -> A.Hype n t -> [[Deriv n t]]
fromActive active hype = case A.activeTrav active hype of
  Nothing  -> case Q.lookup (A.ItemA active) (A.waiting hype) of
    Just _ -> error $
      "fromActive: active item in the waiting queue"
      ++ "\n" ++ show active
    Nothing -> error $
      "fromActive: unknown active item (not even in the queue)"
      ++ "\n" ++ show active
  Just ext -> if S.null (A.prioTrav ext)
    then [[]]
    else concatMap
         (\trav -> fromActiveTrav active trav hype)
         (S.toList (A.prioTrav ext))


fromActiveTrav :: (Ord n, Ord t) => A.Active -> A.Trav n t -> A.Hype n t -> [[Deriv n t]]
fromActiveTrav _p trav hype = case trav of
  A.Scan q t _ ->
    [ termNode t : ts
    | ts <- activeDerivs q ]
  A.Foot q x _ ->
    [ footNode x : ts
    | ts <- activeDerivs q ]
  A.Subst qp qa _ ->
    [ substNode qp t : ts
    | ts <- activeDerivs qa
    , t  <- passiveDerivs qp ]
  A.Adjoin _ _ ->
    error "fromActiveTrav: called on a passive item"
  where
    activeDerivs = flip fromActive hype
    passiveDerivs = flip fromPassive hype


-- | Construct a derivation tree on the basis of the underlying passive
-- item, current child derivation and previous children derivations.
mkTree
  :: A.Hype n t
  -> A.Passive n t
  -> [Deriv n t]
  -> Deriv n t
mkTree hype p ts = R.Node
  { R.rootLabel = mkRoot hype p
  , R.subForest = reverse ts }

-- | Construct a derivation node with no modifier.
only :: O.Node n t -> DerivNode n t
only x = DerivNode {node = x, modif =  []}

-- | Several constructors which allow to build non-modified nodes.
mkRoot :: A.Hype n t -> A.Passive n t -> DerivNode n t
mkRoot hype p = only . O.NonTerm $ A.nonTerm (getL A.dagID p) hype

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
  O.Term _ -> error "passiveDerivs.getRoot: got terminal"

-- | Construct substitution node stemming from the given derivation.
substNode :: A.Passive n t -> Deriv n t -> Deriv n t
substNode p t
  | A.isRoot (p ^. A.dagID) = flip R.Node [] $ DerivNode
    { node = O.NonTerm (derivRoot t)
    , modif   = [t] }
  | otherwise = t

-- Add the auxiliary derivation to the list of modifications of the
-- initial derivation.
adjoinTree :: Deriv n t -> Deriv n t -> Deriv n t
adjoinTree ini aux = R.Node
  { R.rootLabel = let root = R.rootLabel ini in DerivNode
    { node = node root
    , modif = aux : modif root }
  , R.subForest = R.subForest ini }


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


-- | Empty `RevHype`.
emptyRevHype :: RevHype n t
emptyRevHype = RevHype M.empty


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
        { outItem  :: A.Item n t
        -- ^ The output active or passive item
        , scanTerm :: t
        -- ^ The scanned terminal
        }
    -- ^ Scan: scan the leaf terminal with a terminal from the input
    | SubstP
        { outItem :: A.Item n t
        -- ^ The output active or passive item
        , actArg  :: A.Active
        -- ^ The active argument of the action
        }
    -- ^ Pseudo substitution: match the source passive item against the leaf
    -- of the given active item
    | SubstA
        { passArg :: A.Passive n t
        -- ^ The passive argument of the action
        , outItem :: A.Item n t
        -- ^ The output active or passive item
        }
    -- ^ Pseudo substitution: substitute the leaf of the source item with
    -- the given passive item
    | FootA
        { outItem :: A.Item n t
        -- ^ The output active or passive item
--         , theFoot :: A.Passive n t
--         -- ^ The passive argument of the action
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
    deriving (Show, Eq, Ord)


---------------------------------
-- Extracting Derivation Trees...
--
-- ...going through the given arc
---------------------------------


-- | Extract the derivation trees going through the given arc.
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
  -> [Deriv n t]
  -- -> P.ListT (DerivM n t m) ()
fromArc node arc hype revHype =
  case node of
    A.ItemP p ->
      let derivs = fromPassiveTrav p arc hype
      in  upFromPassive p derivs hype revHype
    A.ItemA p ->
      let derivs = fromActiveTrav p arc hype
      in  upFromActive p derivs hype revHype


-- | Depending of the type of the item to process, calls either `upFromPassive`
-- or `upFromActive`.
upFromItem
  :: (Ord n, Ord t)
  => A.Item n t
  -> [[Deriv n t]] -- ^ Derivations corresponding to source (children) items
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n t]
upFromItem item childDerivs hype revHype =
  case item of
    A.ItemP p ->
      -- first construct actual derivation trees for the passive item
      let derivs = map (mkTree hype p) childDerivs
      in  upFromPassive p derivs hype revHype
    A.ItemA p -> upFromActive p childDerivs hype revHype


-- | Explor the hypergraph up in order to generate all final derivations which
-- go through the given item for which partial derivations are known.
upFromPassive
  :: (Ord n, Ord t)
  => A.Passive n t
     -- ^ Passive node
  -> [Deriv n t]
     -- ^ The list of derivation corresponding to the passive node
     -- TODO: this may lead to a spaceleak!
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n t]
upFromPassive passive passiveDerivs hype revHype =
  case M.lookup (A.ItemP passive) (doneReversed revHype) of
    Nothing -> error "upFromPassive: item with no respective entry in `RevHype`"
    Just revTravSet -> if S.null revTravSet
      then passiveDerivs -- meaning that we got a final item, hopefully...
      else concat
           [ upFromPassiveTrav passive revTrav passiveDerivs hype revHype
           | revTrav <- S.toList revTravSet ]


upFromPassiveTrav
  :: (Ord n, Ord t)
  => A.Passive n t
     -- ^ Source hypernode (passive item)
  -> RevTrav n t
     -- ^ Traversal to be followed from the source node
  -> [Deriv n t]
     -- ^ Derivation corresponding to the source node
     -- TODO: this may lead to a spaceleak!
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n t]
upFromPassiveTrav source revTrav sourceDerivs hype revHype =
  case revTrav of
    SubstP{..} ->
      -- we now have a passive source, another active source, and an unknown target;
      -- based on that, we create a list of derivations of the source nodes.
      let combinedDerivs =
            [ substNode source t : ts
            | ts <- fromActive actArg hype
            , t  <- sourceDerivs ]
      -- once we have the combined derivations of the source nodes, we proceed upwards
      -- by going to the unkown target item with the derivations we have
      in  upFromItem outItem combinedDerivs hype revHype
    AdjoinP{..} ->
      let combinedDerivs =
            [ adjoinTree ini aux
            | aux <- sourceDerivs
            , ini <- fromPassive passMod hype ]
      in  upFromPassive outItemP combinedDerivs hype revHype
    ModifyP{..} ->
      let combinedDerivs =
            [ adjoinTree ini aux
            | aux <- fromPassive passAdj hype
            , ini <- sourceDerivs ]
      in  upFromPassive outItemP combinedDerivs hype revHype
    _ -> error "upFromPassiveTrav: got an 'active' traversal for a passive item"


-- | Explor the hypergraph up in order to generate all final derivations which
-- go through the given item for which partial derivations are known.
upFromActive
  :: (Ord n, Ord t)
  => A.Active
  -> [[Deriv n t]] -- ^ Derivation corresponding to the active node
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n t]
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
  -> [[Deriv n t]]
     -- ^ Derivation corresponding to the source node
  -> A.Hype n t
  -> RevHype n t
  -> [Deriv n t]
upFromActiveTrav _source revTrav sourceDerivs hype revHype =
  case revTrav of
    ScanA{..} ->
      let combinedDerivs =
            [ termNode scanTerm : ts
            | ts <- sourceDerivs ]
      in  upFromItem outItem combinedDerivs hype revHype
    SubstA{..} ->
      let combinedDerivs =
            [ substNode passArg t : ts
            | ts <- sourceDerivs -- fromActive actArg hype
            , t  <- fromPassive passArg hype ]
      in  upFromItem outItem combinedDerivs hype revHype
    FootA{..} ->
      let combinedDerivs =
            [ footNode theFoot : ts
            | ts <- sourceDerivs ]
      in  upFromItem outItem combinedDerivs hype revHype
    _ -> error "upFromActiveTrav: got an 'passive' traversal for an active item"


--------------------------------------------------
-- Dynamic construction of `RevHype`
--------------------------------------------------


-- | Modifications corresponding to the given hypergraph modification.
type ModifDerivs n t = (A.HypeModif n t, [Deriv n t])


-- | Derivation monad.
type DerivM n t m = RWS.RWST
  (DerivR n) () (DerivS n t)
  (P.Pipe (A.HypeModif n t) (ModifDerivs n t) m)


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


-- | Utility function: parse the given sentence with the give grammar and print
-- the individual derivation trees (generated progressively).
parseAndPrint
  :: (Ord t, Ord n, Show n, Show t)
  => A.Auto n t
  -> n -- ^ The start symbol
  -> A.Input t
  -> IO ()
parseAndPrint auto start input = void . P.runEffect $
  P.for pipe $ \(_hypeModif, ts) -> forM_ ts $
    lift . putStrLn . R.drawTree . fmap show . deriv4show
  where
    pipe = A.earleyAutoP auto input P.>-> derivsPipe conf
    conf = DerivR
      { startSym = start
      , sentLen = length $ A.inputSent input }


-- NOTE: The function below has no right to exist. It runs the underlying State
-- monad whose results are immediately lost after the call. Such behavior is
-- unacceptable because the underlying state needs to be preserved throughout
-- the entire process of the Earley parsing algorithm.
--
-- CONCLUSION: we need to change the type of the `derivsPipe` so that it returns
-- not only the derivations but also the source hypergraph modifications. For
-- each hypergraph modification, a separate pipe should be created (why shouldn't
-- it be possible?) which enumerates the individual derivations corresponding for
-- this specific hypergraph modification.
--
-- -- | Generate derivation trees for a given hypergraph modification
-- -- and print them to stdin.
-- procAndPrint
--   :: (Ord t, Ord n, Show n, Show t)
--   => n -- ^ The start symbol
--   -> A.Input t
--   -> A.HypeModif n t
--   -> IO ()
-- procAndPrint start input modif = void . P.runEffect $
--   P.for pipe $ \t ->
--     lift . putStrLn . R.drawTree . fmap show . deriv4show $ t
--   where
--     pipe = P.yield modif P.>-> derivsPipe conf
--     conf = DerivR
--       { startSym = start
--       , sentLen = length $ A.inputSent input }


-- -- | A pipe which transforms hypergraph modifications to the
-- -- corresponding derivations.
-- derivsPipe
--   :: (MonadIO m, Ord n, Ord t)
--   => DerivR n
--   -> P.Pipe (A.HypeModif n t) (Deriv n t) m a
-- derivsPipe conf =
--   fst <$> RWS.evalRWST loop conf emptyRevHype
--   where
--     loop = do
--       hypeModif <- lift P.await
--       procModif hypeModif
--       loop


-- | A pipe which transforms hypergraph modifications to the
-- corresponding derivations.
derivsPipe
  :: (MonadIO m, Ord n, Ord t)
  => DerivR n
  -> P.Pipe (A.HypeModif n t) (ModifDerivs n t) m a
derivsPipe conf =
  fst <$> RWS.evalRWST loop conf emptyRevHype
  where
    loop = do
      hypeModif <- lift P.await
      procModif hypeModif
      loop


-- | Process a hypergraph modification.
procModif
  :: forall m n t. (MonadIO m, Ord n, Ord t)
  => A.HypeModif n t
  -> DerivM n t m ()
procModif modif@A.HypeModif{..}
  | modifType == A.NewNode = void . runMaybeT $ do
      liftIO $ putStrLn "<<NewNode>>"
      A.ItemP p <- return modifItem
      guard =<< lift (isFinal p)
      liftIO $ putStrLn "<<NewNode->isFinal>>"
      lift $ goNode modifItem
      -- yield all derivations stemming from the final passive item
      -- mapM_ (lift . yield) $ fromPassive p modifHype
      lift . yield . (modif,) $ fromPassive p modifHype
  | otherwise = do -- `modifType == A.NewArcs`
      rev <- RWS.gets doneReversed
      liftIO $ putStrLn $ "<<NewArcs>> " ++ show (M.size rev)
      -- check if the node is already in the reversed hypergraph; otherwise, it
      -- is not reachable from any final item so we can ignore it
      b <- hasNode modifItem
      when b $ do
        liftIO $ putStrLn "<<NewArcs->hasNode>>"
        goChildren modifItem
        revHype <- RWS.get
        forM_ (nodeArcs modifItem) $ \arc -> do
          -- mapM_ yield $ fromArc modifItem arc modifHype revHype
          yield . (modif,) $ fromArc modifItem arc modifHype revHype
          -- fromArc modifItem arc modifHype
  where
    yield = lift . P.yield
    -- Recursively explore the hypergraph starting from the given node and add
    -- all nodes and arcs to the inverse representation, if not present there
    -- yet.
    goNode :: A.Item n t -> DerivM n t m ()
--     goNode node = addNode node >> goChildren node
    goNode node = do
      b <- hasNode node
      liftIO $ putStrLn $ "goNode->hasNode: " ++ show b
      when (not b) $ do
        liftIO $ putStrLn "goNode->addNode"
        addNode node >> goChildren node
    -- Explore arcs ingoing to the given target node.
    goChildren node = mapM_ (goArc node) (nodeArcs node)
    nodeArcs node = S.toList $ ingoingArcs node modifHype
    -- Similar to `goNode`, but exploration begins with a specific arc
    -- leading to the corresponding target node.
    goArc node arc = addArc node arc << case arc of
      A.Scan{..} -> goNodeA scanFrom
      A.Subst{..} -> goNodeP passArg >> goNodeA actArg
      A.Foot{..} -> goNodeA actArg
      A.Adjoin{..} -> goNodeP passAdj >> goNodeP passMod
      where m << n = n >> m
    -- Versions of `goNode` specialized to active and passive items
    goNodeA = goNode . A.ItemA
    goNodeP = goNode . A.ItemP


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
      -- Nothing -> S.empty
      Nothing -> error
        "ingoingArcs: no traversals corresponding to the given item"
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
    [ (A.ItemA scanFrom, ScanA item _scanTerm) ]
  A.Subst{..} ->
    [ (A.ItemP passArg, SubstP item actArg)
    , (A.ItemA actArg, SubstA passArg item) ]
  A.Foot{..} ->
    [ (A.ItemA actArg, FootA item theFoot) ]
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
--     then mapM_ P.yield $ fromPassive p modifHype
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


-- -- | ListT from a list.
-- each :: Monad m => [a] -> P.ListT m a
-- each = P.Select . P.each
