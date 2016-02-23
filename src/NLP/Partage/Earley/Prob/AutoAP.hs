{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}


-- | Earley-style TAG parsing based on automata, with a distinction
-- between active and passive items.


module NLP.Partage.Earley.Prob.AutoAP
(
-- * Earley-style parsing
-- ** Input
  Input (..)
, fromList
-- , fromSets

-- ** From a factorized grammar
-- , recognize
, recognizeFrom
-- , parse
-- , earley
-- ** With automata precompiled
-- , recognizeAuto
, recognizeFromAuto
-- , parseAuto
, earleyAuto
-- ** Automaton
, Auto
, mkAuto

-- * Parsing trace (hypergraph)
, Hype
-- -- ** Extracting parsed trees
-- , parsedTrees
-- -- ** Stats
-- , hyperNodesNum
-- , hyperEdgesNum
-- -- ** Printing
-- , printHype

-- * Sentence position
, Pos
) where


import           Prelude hiding             (init, span, (.))
import           Control.Applicative        ((<$>))
import qualified Control.Arrow as Arr
import           Control.Monad      (guard, void, (>=>), when, forM_)
import           Control.Monad.Trans.Class  (lift)
-- import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS
import           Control.Category ((>>>), (.))

import           Data.Function              (on)
import           Data.Maybe     ( isJust, isNothing, mapMaybe
                                , maybeToList )
import qualified Data.Map.Strict            as M
import           Data.Ord       ( comparing )
import           Data.List      ( sortBy )
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import           Data.Lens.Light
import qualified Data.Vector                as V
import           Data.Hashable (Hashable)
import qualified Data.HashTable.IO          as H
import qualified Data.MemoCombinators as Memo

import qualified Pipes                      as P
-- import qualified Pipes.Prelude              as P

import           Data.DAWG.Ord (ID)

import           NLP.Partage.SOrd
import           NLP.Partage.FactGram (FactGram)
import           NLP.Partage.FactGram.Internal
                                ( Lab(..), viewLab )
import qualified NLP.Partage.Auto as A
-- import qualified NLP.Partage.Auto.DAWG  as D
import qualified NLP.Partage.Auto.WeiTrie  as Trie
import qualified NLP.Partage.Tree       as T
import qualified NLP.Partage.Tree.Other as O

import           NLP.Partage.FactGram.Weighted
    (Weight, WeiFactGram)
import qualified NLP.Partage.FactGram.Weighted as W
import qualified NLP.Partage.Earley.Tmp as Tmp

-- For debugging purposes
#ifdef Debug
import qualified Data.Time              as Time
#endif


--------------------------------------------------
-- Input
--------------------------------------------------


-- | Input of the parser.
newtype Input t = Input {
    -- inputSent :: V.Vector (S.Set t)
      inputSent :: [t]
    -- ^ The input sentence
    }


-- -- | Input of the parser.
-- data Input t = Input {
--       inputSent :: V.Vector (S.Set t)
--     -- ^ The input sentence
--     , lexGramI  :: t -> S.Set t
--     -- ^ Lexicon grammar interface: each terminal @t@ in the
--     -- `inputSent` can potentially represent several different
--     -- terminals (anchors) at the level of the grammar.
--     -- If equivalent to `id`, no lexicon-grammar interface is used.
--     -- Otherwise, type @t@ represents both anchors and real terminals
--     -- (words from input sentences).
--     }


-- | Construct `Input` from a list of terminals.
fromList :: [t] -> Input t
fromList = Input
-- fromList = fromSets . map S.singleton


-- -- | Construct `Input` from a list of sets of terminals, each set
-- -- representing all possible interpretations of a given word.
-- fromSets :: [S.Set t] -> Input t
-- -- fromSets xs = Input (V.fromList xs) (\t -> S.singleton t)
-- fromSets xs = Input (V.fromList xs)


-- -- | Set the lexicon-grammar interface to
-- setLexGramI :: Input t ->


--------------------------------------------------
-- BASE TYPES
--------------------------------------------------


-- | A position in the input sentence.
type Pos = Int


data Span = Span {
    -- | The starting position.
      _beg   :: Pos
    -- | The ending position (or rather the position of the dot).
    , _end   :: Pos
    -- | Coordinates of the gap (if applies)
    , _gap   :: Maybe (Pos, Pos)
    } deriving (Show, Eq, Ord)
$( makeLenses [''Span] )


-- | Active chart item : state reference + span.
data Active = Active {
      _state :: ID
    , _spanA :: Span
    } deriving (Show, Eq, Ord)
$( makeLenses [''Active] )


-- | Passive chart item : label + span.
data Passive n t = Passive {
      _label :: Lab n t
    , _spanP :: Span
    } deriving (Show, Eq, Ord)
$( makeLenses [''Passive] )


-- | Does it represent regular rules?
regular :: Span -> Bool
regular = isNothing . getL gap


-- | Does it represent auxiliary rules?
auxiliary :: Span -> Bool
auxiliary = isJust . getL gap


-- | Print an active item.
printSpan :: Span -> IO ()
printSpan span = do
    putStr . show $ getL beg span
    putStr ", "
    case getL gap span of
        Nothing -> return ()
        Just (p, q) -> do
            putStr $ show p
            putStr ", "
            putStr $ show q
            putStr ", "
    putStr . show $ getL end span


-- | Print an active item.
printActive :: Active -> IO ()
printActive p = do
    putStr "("
    putStr . show $ getL state p
    putStr ", "
    printSpan $ getL spanA p
    putStrLn ")"


-- | Print a passive item.
printPassive :: (Show n, Show t) => Passive n t -> IO ()
printPassive p = do
    putStr "("
    putStr . viewLab $ getL label p
    putStr ", "
    printSpan $ getL spanP p
    putStrLn ")"


--------------------------------------------------
-- Traversal
--------------------------------------------------


-- | Traversal represents an action of inducing a new item on the
-- basis of one or two other chart items.  It can be seen as an
-- application of one of the inference rules specifying the parsing
-- algorithm.
--
-- TODO: Sometimes there is no need to store all the arguments of the
-- inference rules, it seems.  From one of the arguments the other
-- one could be derived.
data Trav n t
    = Scan
        { _scanFrom :: Active
        -- ^ The input active state
        , _scanTerm :: t
        -- ^ The scanned terminal
        , _weight   :: Weight
        -- ^ The traversal weight
        }
    | Subst
        { _passArg  :: Passive n t
        -- ^ The passive argument of the action
        , _actArg   :: Active
        -- ^ The active argument of the action
        , _weight   :: Weight
        -- ^ The traversal weight
        }
    -- ^ Pseudo substitution
    | Foot
        { _actArg   :: Active
        -- ^ The passive argument of the action
        -- , theFoot  :: n
        , _theFoot  :: Passive n t
        -- ^ The foot non-terminal
        , _weight   :: Weight
        -- ^ The traversal weight
        }
    -- ^ Foot adjoin
    | Adjoin
        { _passAdj  :: Passive n t
        -- ^ The adjoined item
        , _passMod  :: Passive n t
        -- ^ The modified item
        }
    -- ^ Adjoin terminate with two passive arguments
    deriving (Show, Eq, Ord)


-- -- | Print a traversal.
-- printTrav :: (Show n, Show t) => Item n t -> Trav n t -> IO ()
-- printTrav q' (Scan p x) = do
--     putStr "# " >> printActive p
--     putStr "+ " >> print x
--     putStr "= " >> printItem q'
-- printTrav q' (Subst p q) = do
--     putStr "# " >> printActive q
--     putStr "+ " >> printPassive p
--     putStr "= " >> printItem q'
-- printTrav q' (Foot q p) = do
--     putStr "# " >> printActive q
--     putStr "+ " >> printPassive p
--     putStr "= " >> printItem q'
-- printTrav q' (Adjoin p s) = do
--     putStr "# " >> printPassive p
--     putStr "+ " >> printPassive s
--     putStr "= " >> printItem q'


--------------------------------------------------
-- Weight (priority)
--------------------------------------------------


-- | Neutral element of the weight/priority.  Corresponds to the
-- logarithm of probability 1.
zeroWeight :: Weight
zeroWeight = 0


-- | Add two weights.
addWeight :: Weight -> Weight -> Weight
addWeight = (+)
{-# INLINE addWeight #-}


-- | Sum weights.
sumWeight :: [Weight] -> Weight
sumWeight = sum
{-# INLINE sumWeight #-}


-- | Minimum of two weights.
minWeight :: Weight -> Weight -> Weight
minWeight = min
{-# INLINE minWeight #-}


--------------------------------------------------
-- Extended Weight
--
-- NOTE: it forms a semiring?
--------------------------------------------------


-- | Extended priority which preserves information about the
-- traversal leading to the underlying chart item.  The best weight
-- (priority) of reaching the underlying item is preserved as well.
-- Note that traversals themselves do not introduce any weights.
data ExtWeight n t = ExtWeight
    { priWeight :: Weight
    -- ^ The actual priority.  In case of initial elements
    -- corresponds to weights (probabilities?) assigned to
    -- individual "elementary rules".
    , estWeight :: Weight
    -- ^ Estimated weight to the "end"
    , prioTrav  :: S.Set (Trav n t)
    -- ^ Traversal leading to the underlying chart item
    } deriving (Show)

instance (Eq n, Eq t) => Eq (ExtWeight n t) where
    (==) = (==) `on` (addWeight <$> priWeight <*> estWeight)
instance (Ord n, Ord t) => Ord (ExtWeight n t) where
    compare = compare `on` (addWeight <$> priWeight <*> estWeight)


-- | Construct an initial `ExtWeight`.  With an empty set of input
-- traversals, it corresponds to a start node in the underlying
-- hyper-graph.
extWeight0 :: Weight -> Weight -> ExtWeight n t
extWeight0 p initEst = ExtWeight p initEst S.empty


-- | Construct an `ExtWeight` with one incoming traversal
-- (traversal=hyper-edge).
extWeight :: Weight -> Weight -> Trav n t -> ExtWeight n t
extWeight p est = ExtWeight p est . S.singleton


-- | Join two extended priorities:
-- * The actual priority (cost) preserved is the lower of the two; we
-- are simply keeping the lowest cost of reaching the underlying
-- chart item.
-- * The traversals are unioned.
joinExtWeight
    :: (Ord n, Ord t)
    => ExtWeight n t
    -> ExtWeight n t
    -> ExtWeight n t
joinExtWeight x y = if estWeight x /= estWeight y
    then error "joinExtWeight: estimation costs differ!"
    else ExtWeight
        (minWeight (priWeight x) (priWeight y))
        (estWeight x)
        (S.union (prioTrav x) (prioTrav y))


--------------------------------------------------
-- Item Type
--------------------------------------------------


-- | Passive or active item.
data Item n t
    = ItemP (Passive n t)
    | ItemA Active
    deriving (Show, Eq, Ord)


-- | Print an active item.
printItem :: (Show n, Show t) => Item n t -> IO ()
printItem (ItemP p) = printPassive p
printItem (ItemA p) = printActive p


-- -- | Priority of an active item.  Crucial for the algorithm --
-- -- states have to be removed from the queue in a specific order.
-- prio :: Item n t -> Prio
-- prio (ItemP p) = prioP p
-- prio (ItemA p) = prioA p


--------------------------------------------------
-- Local automaton type
--------------------------------------------------


-- | Local automaton type based on `A.GramAuto`.
data Auto n t = Auto
    { gramAuto  :: A.WeiGramAuto n t
    -- ^ The underlying grammar as an automaton
    , withBody  :: H.CuckooHashTable (Lab n t) (S.Set ID)
    -- ^ A data structure which, for each label, determines the
    -- set of automaton states from which this label goes out
    -- as a body transition.
    , dagGram   :: W.DAG (O.Node n t) Weight
    -- ^ Grammar as a DAG (with subtree sharing)
    , termWei   :: M.Map t Weight
    -- ^ The lower bound estimates on reading terminal weights.
    -- Based on the idea that weights of the elementary trees are
    -- evenly distributed over its terminals.
    }


-- | Construct `Auto` based on the weighted grammar.
mkAuto
    :: (Hashable t, Ord t, Hashable n, Ord n)
    => W.Gram n t -> IO (Auto n t)
mkAuto gram = do
    let auto = Trie.fromGram (W.factGram gram)
    body <- H.fromList . M.toList $ mkWithBody auto
    return $ Auto
        { gramAuto  = auto
        , withBody  = body
        , dagGram   = W.dagGram gram
        , termWei   = W.termWei gram }
-- mkAuto
--     :: (Hashable t, Ord t, Hashable n, Ord n)
--     => A.WeiGramAuto n t -> IO (Auto n t)
-- mkAuto dag = do
--     theBody <- H.fromList . M.toList $ mkWithBody dag
--     return $ Auto
--         { gramAuto = dag
--         , withBody = theBody }


-- | Create the `withBody` component based on the automaton.
mkWithBody
    :: (Ord n, Ord t)
    => A.WeiGramAuto n t
    -> M.Map (Lab n t) (S.Set ID)
mkWithBody dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | (i, A.Body x, _j) <- A.allEdges (A.fromWei dag) ]


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | A hypergraph dynamically constructed during parsing.
data Hype n t = Hype
    { automat   :: Auto n t
    -- ^ The underlying automaton

    -- , minCosts  :: [Weight]
    -- ^ Minimal weight of parsing individual terminals

    , estiCost1  ::       Tmp.Bag t -> Weight
    , estiCost2  :: ID -> Tmp.Bag t -> Weight

    -- , doneActive  :: M.Map (ID, Pos) (S.Set (Active n t))
    , doneActive  :: M.Map Pos (M.Map ID
        -- (M.Map Active (S.Set (Trav n t))))
        (M.Map Active (ExtWeight n t)))
    -- ^ Processed active items partitioned w.r.t ending
    -- positions and state IDs.

    -- , donePassive :: S.Set (Passive n t)
    , donePassive :: M.Map (Pos, n, Pos)
        -- (M.Map (Passive n t) (S.Set (Trav n t)))
        (M.Map (Passive n t) (ExtWeight n t))
    -- ^ Processed passive items.

    , waiting     :: Q.PSQ (Item n t) (ExtWeight n t)
    -- ^ The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    }


-- | Make an initial `Hype` from a set of states.
mkHype
    :: (HOrd n, HOrd t)
    => (      Tmp.Bag t -> Weight)  -- ^ Heuristic
    -> (ID -> Tmp.Bag t -> Weight)  -- ^ Heuristic
    -> Auto n t
    -- -> M.Map Active Weight          -- ^ Initial active items
    -> Hype n t
-- mkHype initEst estiCost1 estiCost2 auto m = Hype
mkHype estiCost1 estiCost2 auto = Hype
    { automat  = auto
    , estiCost1 = estiCost1
    , estiCost2 = estiCost2
    , doneActive  = M.empty
    , donePassive = M.empty
    , waiting = Q.empty }
--     , waiting = Q.fromList
--         [ ItemA p :-> extWeight0 c initEst
--         | (p, c) <- M.toList m ] }


-- | Earley parser monad.  Contains the input sentence (reader)
-- and the state of the computation `Hype'.
type Earley n t = RWS.RWST (Input t) () (Hype n t) IO


-- | Read word from the given position of the input.
readInput :: Pos -> P.ListT (Earley n t) t
readInput i = do
    -- ask for the input
    sent <- RWS.asks inputSent
    -- just a safe way to retrieve the i-th element
    each $ take 1 $ drop i sent
    -- xs <- some $ sent V.!? i
    -- each $ S.toList xs


--------------------------------------------------
-- Automaton-Based Primitives
--------------------------------------------------


-- | Follow the given terminal in the underlying automaton.
followTerm :: (Ord n, Ord t)
           => ID -> t -> P.ListT (Earley n t) (Weight, ID)
followTerm i c = do
    -- get the underlying automaton
    auto <- RWS.gets $ gramAuto . automat
    -- follow the label
    some $ A.followWei auto i (A.Body $ Term c)


-- | Follow the given body transition in the underlying automaton.
-- It represents the transition function of the automaton.
--
-- TODO: merge with `followTerm`.
follow :: (Ord n, Ord t)
       => ID -> Lab n t -> P.ListT (Earley n t) (Weight, ID)
follow i x = do
    -- get the underlying automaton
    auto <- RWS.gets $ gramAuto . automat
    -- follow the label
    some $ A.followWei auto i (A.Body x)


-- | Rule heads outgoing from the given automaton state.
heads :: ID -> P.ListT (Earley n t) (Weight, Lab n t)
heads i = do
    auto <- RWS.gets $ gramAuto . automat
    let mayHead (x, w, _) = case x of
            A.Body _  -> Nothing
            A.Head y -> Just (w, y)
    each $ mapMaybe mayHead $ A.edgesWei auto i


-- | Rule body elements outgoing from the given automaton state.
elems :: ID -> P.ListT (Earley n t) (Lab n t, Weight, ID)
elems i = do
    auto <- RWS.gets $ gramAuto . automat
    let mayBody (x, w, j) = case x of
            A.Body y -> Just (y, w, j)
            A.Head _ -> Nothing
    each $ mapMaybe mayBody $ A.edgesWei auto i


-- | Check if any element leaves the given state.
hasElems :: ID -> Earley n t Bool
hasElems i = do
    auto <- RWS.gets $ gramAuto . automat
    let mayBody (x, _, _) = case x of
            A.Body y  -> Just y
            A.Head _ -> Nothing
    return
        . not . null
        . mapMaybe mayBody
        $ A.edgesWei auto i




--------------------------------------------------
-- Hypergraph stats
--------------------------------------------------


-- -- | Number of nodes in the parsing hypergraph.
-- hyperNodesNum :: Hype n t -> Int
-- hyperNodesNum e
--     = length (listPassive e)
--     + length (listActive e)
--
--
-- -- | Number of edges in the parsing hypergraph.
-- hyperEdgesNum :: forall n t. Hype n t -> Int
-- hyperEdgesNum earSt
--     = sumOver listPassive
--     + sumOver listActive
--   where
--     sumOver :: (Hype n t -> [(a, S.Set (Trav n t))]) -> Int
--     sumOver listIt = sum
--         [ S.size travSet
--         | (_, travSet) <- listIt earSt ]
--
--
-- -- | Extract hypergraph (hyper)edges.
-- hyperEdges :: Hype n t -> [(Item n t, Trav n t)]
-- hyperEdges earSt =
--     passiveEdges ++ activeEdges
--   where
--     passiveEdges =
--         [ (ItemP p, trav)
--         | (p, travSet) <- listPassive earSt
--         , trav <- S.toList travSet ]
--     activeEdges =
--         [ (ItemA p, trav)
--         | (p, travSet) <- listActive earSt
--         , trav <- S.toList travSet ]
--
--
-- -- | Print the hypergraph edges.
-- printHype :: (Show n, Show t) => Hype n t -> IO ()
-- printHype earSt =
--     forM_ edges $ \(p, trav) ->
--         printTrav p trav
--   where
--     edges  = sortIt (hyperEdges earSt)
--     sortIt = sortBy (comparing $ prio.fst)



--------------------
-- Active items
--------------------


-- -- | List all active done items together with the corresponding
-- -- traversals.
-- listActive :: Hype n t -> [(Active, S.Set (Trav n t))]
-- listActive = (M.elems >=> M.elems >=> M.toList) . doneActive


-- | Return the corresponding set of traversals for an active item.
activeTrav
    :: (Ord n, Ord t)
    => Active -> Hype n t
    -> Maybe (ExtWeight n t)
activeTrav p
    = (   M.lookup (p ^. spanA ^. end)
      >=> M.lookup (p ^. state)
      >=> M.lookup p )
    . doneActive


-- | Check if the active item is not already processed.
_isProcessedA :: (Ord n, Ord t) => Active -> Hype n t -> Bool
_isProcessedA p =
    check . activeTrav p
  where
    check (Just _) = True
    check _        = False


-- | Check if the active item is not already processed.
isProcessedA :: (Ord n, Ord t) => Active -> Earley n t Bool
isProcessedA p = _isProcessedA p <$> RWS.get


-- | Mark the active item as processed (`done').
saveActive
    :: (Ord t, Ord n)
    => Active
    -> ExtWeight n t
    -> Earley n t ()
saveActive p ts =
    RWS.modify' $ \s -> s {doneActive = newDone s}
  where
    newDone st =
        M.insertWith
            ( M.unionWith
                ( M.unionWith joinExtWeight ) )
            ( p ^. spanA ^. end )
            ( M.singleton (p ^. state)
                ( M.singleton p ts ) )
            ( doneActive st )


--------------------
-- Passive items
--------------------


-- -- | List all passive done items together with the corresponding
-- -- traversals.
-- listPassive :: Hype n t -> [(Passive n t, S.Set (Trav n t))]
-- listPassive = (M.elems >=> M.toList) . donePassive


-- | Return the corresponding set of traversals for a passive item.
passiveTrav
    :: (Ord n, Ord t)
    => Passive n t -> Hype n t
    -> Maybe (ExtWeight n t)
passiveTrav p
    = ( M.lookup
        ( p ^. spanP ^. beg
        , nonTerm $ p ^. label
        , p ^. spanP ^. end ) >=> M.lookup p )
    . donePassive


-- | Check if the state is not already processed.
_isProcessedP :: (Ord n, Ord t) => Passive n t -> Hype n t -> Bool
_isProcessedP x =
    check . passiveTrav x
  where
    check (Just _) = True
    check _        = False


-- | Check if the passive item is not already processed.
isProcessedP :: (Ord n, Ord t) => Passive n t -> Earley n t Bool
isProcessedP p = _isProcessedP p <$> RWS.get


-- | Mark the passive item as processed (`done').
savePassive
    :: (Ord t, Ord n)
    => Passive n t
    -> ExtWeight n t
    -> Earley n t ()
savePassive p ts =
    RWS.state $ \s -> ((), s {donePassive = newDone s})
  where
    newDone st =
        M.insertWith
            ( M.unionWith joinExtWeight )
            ( p ^. spanP ^. beg
            , nonTerm $ p ^. label
            , p ^. spanP ^. end )
            ( M.singleton p ts )
            ( donePassive st )


--------------------
-- Waiting Queue
--------------------


-- | Add the active item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushActive :: (Ord t, Ord n)
           => Active -> ExtWeight n t -> Earley n t ()
pushActive p new = isProcessedA p >>= \b -> if b
    then saveActive p new
    else modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinExtWeight (ItemA p) new


-- | Add the passive item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushPassive :: (Ord t, Ord n)
            => Passive n t
            -> ExtWeight n t
            -> Earley n t ()
pushPassive p new = isProcessedP p >>= \b -> if b
    then savePassive p new
    else modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinExtWeight (ItemP p) new
    -- newPrio = ExtPrio (prioP p) (S.singleton t)


-- | Add to the waiting queue all items induced from the given item.
pushInduced :: (Ord t, Ord n)
            => Active
            -> ExtWeight n t
            -> Earley n t ()
pushInduced p new = do
    hasElems (getL state p) >>= \b -> when b
        (pushActive p new)
    P.runListT $ do
        (headCost, x) <- heads (getL state p)
        -- while "reading" the head, we increase the weight of the
        -- current parse and decrease the estimated weight at the
        -- same time
        let new' = new
                { priWeight = priWeight new + headCost
                , estWeight = estWeight new - headCost }
        lift . flip pushPassive new' $
           Passive x (p ^. spanA)


-- | Remove a state from the queue.
popItem
    :: (Ord t, Ord n)
    => Earley n t
        (Maybe (Binding (Item n t) (ExtWeight n t)))
popItem = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (b, s) -> (Just b, st {waiting = s})


----------------------
-- Distance Estimation
----------------------


-- | Estimate the remaining distnance for a passive item.
estimateDistP :: (Ord t) => Passive n t -> Earley n t Weight
estimateDistP p = do
    tbag <- bagOfTerms (p ^. spanP)
    esti <- RWS.gets estiCost1
    return $ esti tbag


-- | Estimate the remaining distnance for an active item.
estimateDistA :: (Ord t) => Active -> Earley n t Weight
estimateDistA q = do
    tbag <- bagOfTerms (q ^. spanA)
    esti <- RWS.gets estiCost2
    return $ esti (q ^. state) tbag


-- | Compute the bag of terminals for the given span.
bagOfTerms :: (Ord t) => Span -> Earley n t (Tmp.Bag t)
bagOfTerms span = do
    n <- sentLen
    x <- estOn 0 (span ^. beg)
    y <- estOn (span ^. end) n
    z <- case span ^. gap of
        Nothing -> return Tmp.bagEmpty
        Just (i, j) -> estOn i j
    return $ x `Tmp.bagAdd` y `Tmp.bagAdd` z
  where
    sentLen = length <$> RWS.asks inputSent
    estOn i j = Tmp.bagFromList . over i j <$> RWS.asks inputSent


-- -- | Estimate the remaining distnance for an active item.
-- estimateDistA :: Active -> Earley n t Weight
-- estimateDistA q
--     = estimateDistSpan  (q ^. spanA)
--     -- + estimateDistState (q ^. state)
--
--
-- -- | Estimate the remaining distnance (the span component)
-- estimateDistSpan :: Span -> Earley n t Weight
-- estimateDistSpan span = do
--     n <- sentLen
--     x <- estOn 0 (span ^. beg)
--     y <- estOn (span ^. end) n
--     z <- case span ^. gap of
--         Nothing -> return zeroWeight
--         Just (i, j) -> estOn i j
--     return $ x + y + z
--   where
--     sentLen = length <$> RWS.asks inputSent
--     estOn i j = sumWeight . over i j <$> RWS.gets minCosts


---------------------------------
-- Extraction of Processed Items
---------------------------------


-- -- | Return all active processed items which:
-- -- * expect a given label,
-- -- * end on the given position.
-- expectEnd
--     :: (Ord n, Ord t) => Lab n t -> Pos
--     -> P.ListT (Earley n t) Active
-- expectEnd sym i = do
--     Hype{..} <- lift RWS.get
--     -- determine items which end on the given position
--     doneEnd <- some $ M.lookup i doneActive
--     -- determine automaton states from which the given label
--     -- leaves as a body transition
--     stateSet <- some $ M.lookup sym withBody
--     -- pick one of the states
--     stateID <- each $ S.toList stateSet
--     --
--     -- ALTERNATIVE: state <- each . S.toList $
--     --      stateSet `S.intersection` M.keySet doneEnd
--     --
--     -- determine items which refer to the chosen states
--     doneEndLab <- some $ M.lookup stateID doneEnd
--     -- return them all!
--     each $ M.keys doneEndLab


-- | Return all active processed items which:
-- * expect a given label,
-- * end on the given position.
-- Return the weights of reaching them as well.
expectEnd
    :: (HOrd n, HOrd t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Active, Weight)
expectEnd sym i = do
    Hype{..} <- lift RWS.get
    -- determine items which end on the given position
    doneEnd <- some $ M.lookup i doneActive
    -- determine automaton states from which the given label
    -- leaves as a body transition
    stateSet <- do
        maybeSet <- lift . lift $
            H.lookup (withBody automat) sym
        some maybeSet
    -- pick one of the states
    stateID <- each . S.toList $
         stateSet `S.intersection` M.keysSet doneEnd
    -- determine items which refer to the chosen states
    doneEndLab <- some $ M.lookup stateID doneEnd
    -- return them all!
    -- each $ M.keys doneEndLab
    each $
        [ (p, priWeight e)
        | (p, e) <- M.toList doneEndLab ]


-- | Check if a passive item exists with:
-- * the given root non-terminal value (but not top-level
--   auxiliary)
-- * the given span
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t, Weight)
rootSpan x (i, j) = do
    Hype{..} <- lift RWS.get
    -- listValues (i, x, j) donePassive
    each $ case M.lookup (i, x, j) donePassive of
        Nothing -> []
        Just m -> map (Arr.second priWeight) (M.toList m)


-- | List all processed passive items.
listPassive :: Hype n t -> [(Passive n t, ExtWeight n t)]
listPassive = (M.elems >=> M.toList) . donePassive


-- | Return all processed passive items which:
-- * provide a given label,
-- * begin on the given position.
provideBeg
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Passive n t, Weight)
provideBeg x i = do
    hype <- lift RWS.get
    each
        [ (q, priWeight e) | (q, e) <- listPassive hype
        , q ^. spanP ^. beg == i
        , q ^. label == x ]


-- | Return all processed items which:
-- * are fully parsed (i.e. passive)
-- * provide a label with a given non-terminal,
-- * begin on the given position,
--
-- (Note the similarity to `provideBeg`)
provideBeg'
    :: (Ord n, Ord t) => n -> Pos
    -> P.ListT (Earley n t) (Passive n t, Weight)
provideBeg' x i = do
    hype <- lift RWS.get
    each
        [ (q, priWeight e) | (q, e) <- listPassive hype
        , q ^. spanP ^.beg == i
        , nonTerm (q ^. label) == x ]


-- | Return all fully parsed items:
-- * top-level and representing auxiliary trees,
-- * modifying the given source non-terminal,
-- * with the given gap.
auxModifyGap
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Passive n t, Weight)
auxModifyGap x gapSpan = do
    hype <- lift RWS.get
    each
        [ (q, priWeight e) | (q, e) <- listPassive hype
        , q ^. spanP ^. gap == Just gapSpan
        , topLevel (q ^. label)
        , nonTerm  (q ^. label) == x ]


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- | Try to perform SCAN on the given active state.
tryScan :: (SOrd t, SOrd n) => Active -> Weight -> Earley n t ()
tryScan p cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- read the word immediately following the ending position of
    -- the state
    c <- readInput $ getL (spanA >>> end) p
    -- follow appropriate terminal transition outgoing from the
    -- given automaton state
    (termCost, j) <- followTerm (getL state p) c
    -- construct the resultant active item
    -- let q = p {state = j, end = end p + 1}
    let q = setL state j
          . modL' (spanA >>> end) (+1)
          $ p
    -- compute the estimated distance for the resulting state
    -- estDist <- lift . estimateDist $ q ^. spanA
    estDist <- lift . estimateDistA $ q
    -- push the resulting state into the waiting queue
    lift . pushInduced q
         . extWeight (addWeight cost termCost) estDist
         $ Scan p c termCost
#ifdef Debug
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[S]  " >> printActive p
        putStr "  :  " >> printActive q
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (addWeight cost termCost)
        putStr " #E  " >> print estDist
#endif


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the passive item `p` to complement
-- (=> substitution) other rules.
trySubst
    :: (SOrd t, SOrd n)
    => Passive n t
    -> Weight
    -> Earley n t ()
trySubst p cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pLab = getL label p
        pSpan = getL spanP p
    -- make sure that `p' represents regular rules
    guard . regular $ pSpan
    -- find active items which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    (q, cost') <- expectEnd pLab (getL beg pSpan)
    -- follow the transition symbol
    (tranCost, j) <- follow (q ^. state) pLab
    -- construct the resultant state
    -- let q' = q {state = j, spanA = spanA p {end = end p}}
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           $ q
    -- compute the estimated distance for the resulting state
    estDist <- lift . estimateDistA $ q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q'
         . extWeight (sumWeight [cost, cost', tranCost]) estDist
         $ Subst p q tranCost
#ifdef Debug
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[U]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (sumWeight [cost, cost', tranCost])
        putStr " #E  " >> print estDist
#endif


-- | Reversed `trySubst` version.  Try to completent the item with
-- another fully parsed item.
trySubst'
    :: (SOrd t, SOrd n)
    => Active
    -> Weight
    -> Earley n t ()
trySubst' q cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- Learn what non-terminals `q` actually expects.
    -- WARNING: in the automaton-based parser, this seems not
    -- particularly efficient in some edge cases...
    -- For instance, when `q` refers to the root node of an
    -- automaton.  Can we bypass this issue?
    (qLab@NonT{}, tranCost, j) <- elems (q ^. state)
    -- (r@NonT{}, _) <- some $ expects' (q ^. state)
    -- Find processed items which begin where `q` ends and which
    -- provide the non-terminal expected by `q`.
    (p, cost') <- provideBeg qLab (q ^. spanA ^. end)
    let pSpan = p ^. spanP
    -- construct the resultant state
    let q' = setL state j
           . setL (end . spanA) (pSpan ^. end)
           $ q
    -- compute the estimated distance for the resulting state
    estDist <- lift . estimateDistA $ q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q'
         . extWeight (sumWeight [cost, cost', tranCost]) estDist
         $ Subst p q tranCost
#ifdef Debug
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[U'] " >> printActive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (sumWeight [cost, cost', tranCost])
        putStr " #E  " >> print estDist
#endif


--------------------------------------------------
-- FOOT ADJOIN
--------------------------------------------------


-- | `tryAdjoinInit p q':
-- * `p' is a completed state (regular or auxiliary)
-- * `q' not completed and expects a *real* foot
tryAdjoinInit
    :: (SOrd n, SOrd t)
    => Passive n t
    -> Weight
    -> Earley n t ()
tryAdjoinInit p _cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- make sure that the corresponding rule is either regular or
    -- intermediate auxiliary ((<=) used as implication here)
    guard $ auxiliary pSpan <= not (topLevel pLab)
    -- find all active items which expect a foot with the given
    -- symbol and which end where `p` begins
    let foot = AuxFoot $ nonTerm pLab
    (q, cost) <- expectEnd foot (pSpan ^. beg)
    -- follow the foot
    (tranCost, j) <- follow (q ^. state) foot
    -- construct the resultant state
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (Just
                ( pSpan ^. beg
                , pSpan ^. end ))
           $ q
    -- compute the estimated distance for the resulting state
    estDist <- lift . estimateDistA $ q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q'
         . extWeight (addWeight cost tranCost) estDist
         -- $ Foot q (nonTerm foot) tranCost
         $ Foot q p tranCost
--     -- push the resulting state into the waiting queue
--     lift $ pushInduced q' $ Foot q p -- -- $ nonTerm foot
#ifdef Debug
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[A]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (addWeight cost tranCost)
        putStr " #E  " >> print estDist
#endif


-- | Reverse of `tryAdjoinInit` where the given state `q`
-- expects a real foot.
-- * `q' not completed and expects a *real* foot
-- * `p' is a completed state (regular or auxiliary)
tryAdjoinInit'
    :: (SOrd n, SOrd t)
    => Active
    -> Weight
    -> Earley n t ()
tryAdjoinInit' q cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- Retrieve the foot expected by `q`.
    (AuxFoot footNT, tranCost, j) <- elems (q ^. state)
    -- (AuxFoot footNT, _) <- some $ expects' q
    -- Find all fully passive items which provide the given source
    -- non-terminal and which begin where `q` ends.
    (p, _cost) <- provideBeg' footNT (q ^. spanA ^. end)
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- The retrieved items must not be auxiliary top-level.
    guard $ auxiliary pSpan <= not (topLevel pLab)
    -- construct the resultant state
--     let q' = setL (spanA >>> end) (pSpan ^. end)
--            . setL (spanA >>> gap) (Just
--                 ( pSpan ^. beg
--                 , pSpan ^. end ))
--            . modL' right tail
--            $ q
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (Just
                ( pSpan ^. beg
                , pSpan ^. end ))
           $ q
    -- compute the estimated distance for the resulting state
    estDist <- lift . estimateDistA $ q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q'
         . extWeight (addWeight cost tranCost) estDist
         $ Foot q p tranCost
#ifdef Debug
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[A'] " >> printActive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (addWeight cost tranCost)
        putStr " #E  " >> print estDist
#endif


--------------------------------------------------
-- INTERNAL ADJOIN
--------------------------------------------------


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
tryAdjoinCont
    :: (SOrd n, SOrd t)
    => Passive n t
    -> Weight
    -> Earley n t ()
tryAdjoinCont p cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- make sure the label is not top-level (internal spine
    -- non-terminal)
    guard . not $ topLevel pLab
    -- make sure that `p' is an auxiliary item
    guard . auxiliary $ pSpan
    -- find all rules which expect a spine non-terminal provided
    -- by `p' and which end where `p' begins
    (q, cost') <- expectEnd pLab (pSpan ^. beg)
    -- follow the spine non-terminal
    (tranCost, j) <- follow (q ^. state) pLab
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (pSpan ^. gap)
           $ q
    -- compute the estimated distance for the resulting state
    estDist <- lift . estimateDistA $ q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q'
         . extWeight (sumWeight [cost, cost', tranCost]) estDist
         $ Subst p q tranCost
--     -- push the resulting state into the waiting queue
--     lift $ pushInduced q' $ Subst p q
#ifdef Debug
    -- logging info
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[B]  " >> printPassive p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (sumWeight [cost, cost', tranCost])
        putStr " #E  " >> print estDist
#endif


-- | Reversed `tryAdjoinCont`.
tryAdjoinCont'
    :: (SOrd n, SOrd t)
    => Active
    -> Weight
    -> Earley n t ()
tryAdjoinCont' q cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- Retrieve the auxiliary vertebrea expected by `q`
    -- (qLab@AuxVert{}, _) <- some $ expects' q
    (qLab@AuxVert{}, tranCost, j) <- elems (q ^. state)
    -- Find all fully parsed items which provide the given label
    -- and which begin where `q` ends.
    (p, cost') <- provideBeg qLab (q ^. spanA ^. end)
    let pSpan = p ^. spanP
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (pSpan ^. gap)
           $ q
    -- compute the estimated distance for the resulting state
    estDist <- lift . estimateDistA $ q'
    -- push the resulting state into the waiting queue
    lift . pushInduced q'
         . extWeight (sumWeight [cost, cost', tranCost]) estDist
         $ Subst p q tranCost
#ifdef Debug
    -- logging info
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[B'] " >> printActive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (sumWeight [cost, cost', tranCost])
        putStr " #E  " >> print estDist
#endif


--------------------------------------------------
-- ROOT ADJOIN
--------------------------------------------------


-- | Adjoin a fully-parsed auxiliary state `p` to a partially parsed
-- tree represented by a fully parsed rule/state `q`.
tryAdjoinTerm
    :: (SOrd t, SOrd n)
    => Passive n t
    -> Weight
    -> Earley n t ()
tryAdjoinTerm q cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let qLab = q ^. label
        qSpan = q ^. spanP
    -- make sure the label is top-level
    guard $ topLevel qLab
    -- make sure that it is an auxiliary item (by definition only
    -- auxiliary states have gaps)
    (gapBeg, gapEnd) <- each $ maybeToList $ qSpan ^. gap
    -- take all passive items with a given span and a given
    -- root non-terminal (IDs irrelevant)
    (p, cost') <- rootSpan (nonTerm qLab) (gapBeg, gapEnd)
    let p' = setL (spanP >>> beg) (qSpan ^. beg)
           . setL (spanP >>> end) (qSpan ^. end)
           $ p
    -- lift $ pushPassive p' $ Adjoin q p
    -- compute the estimated distance for the resulting state
    estDist <- lift . estimateDistP $ p'
    -- push the resulting state into the waiting queue
    lift . pushPassive p'
         . extWeight (addWeight cost cost') estDist
         $ Adjoin q p
#ifdef Debug
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[C]  " >> printPassive q
        putStr "  +  " >> printPassive p
        putStr "  :  " >> printPassive p'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (addWeight cost cost')
        putStr " #E  " >> print estDist
#endif


-- | Reversed `tryAdjoinTerm`.
tryAdjoinTerm'
    :: (SOrd t, SOrd n)
    => Passive n t
    -> Weight
    -> Earley n t ()
tryAdjoinTerm' p cost = void $ P.runListT $ do
#ifdef Debug
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pLab = p ^. label
        pSpan = p ^. spanP
    -- Ensure that `p` is auxiliary but not top-level
    guard $ auxiliary pSpan <= not (topLevel pLab)
    -- Retrieve all completed, top-level items representing auxiliary
    -- trees which have a specific gap and modify a specific source
    -- non-terminal.
    (q, cost') <- auxModifyGap
        (nonTerm $ p ^. label)
        ( p ^. spanP ^. beg
        , p ^. spanP ^. end )
    let qSpan = q ^. spanP
    -- Construct the resulting state:
    let p' = setL (spanP >>> beg) (qSpan ^. beg)
           . setL (spanP >>> end) (qSpan ^. end)
           $ p
    -- compute the estimated distance for the resulting state
    estDist <- lift . estimateDistP $ p'
    -- push the resulting state into the waiting queue
    lift . pushPassive p'
         . extWeight (addWeight cost cost') estDist
         $ Adjoin q p
#ifdef Debug
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[C'] " >> printPassive p
        putStr "  +  " >> printPassive q
        putStr "  :  " >> printPassive p'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
        putStr " #W  " >> print (addWeight cost cost')
        putStr " #E  " >> print estDist
#endif


--------------------------------------------------
-- Earley step
--------------------------------------------------


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step
    :: (SOrd t, SOrd n)
    => Binding (Item n t) (ExtWeight n t)
    -> Earley n t ()
step (ItemP p :-> e) = do
    -- mapM_ ($ p)
    mapM_ (\f -> f p $ priWeight e)
      [ trySubst
      , tryAdjoinInit
      , tryAdjoinCont
      , tryAdjoinTerm
      , tryAdjoinTerm' ]
    savePassive p e -- $ prioTrav e
step (ItemA p :-> e) = do
    -- mapM_ ($ p)
    mapM_ (\f -> f p $ priWeight e)
      [ tryScan
      , trySubst'
      , tryAdjoinInit'
      , tryAdjoinCont' ]
    saveActive p e -- $ prioTrav e


---------------------------
-- Extracting Parsed Trees
---------------------------


-- -- | Extract the set of parsed trees obtained on the given input
-- -- sentence.  Should be run on the result of the earley parser.
-- parsedTrees
--     :: forall n t. (Ord n, Ord t)
--     => Hype n t     -- ^ Final state of the earley parser
--     -> n            -- ^ The start symbol
--     -> Int          -- ^ Length of the input sentence
--     -> [T.Tree n t]
-- parsedTrees earSt start n
--
--     = concatMap fromPassive
--     $ finalFrom start n earSt
--
--   where
--
--     fromPassive :: Passive n t -> [T.Tree n t]
--     fromPassive p = concat
--         [ fromPassiveTrav p trav
--         | travSet <- maybeToList $ passiveTrav p earSt
--         , trav <- S.toList travSet ]
--
--     fromPassiveTrav p (Scan q t) =
--         [ T.Branch
--             (nonTerm $ getL label p)
--             (reverse $ T.Leaf t : ts)
--         | ts <- fromActive q ]
--
-- --     fromPassiveTrav p (Foot q x) =
-- --         [ T.Branch
-- --             (nonTerm $ getL label p)
-- --             (reverse $ T.Branch x [] : ts)
-- --         | ts <- fromActive q ]
--
--     fromPassiveTrav p (Foot q _p') =
--         [ T.Branch
--             (nonTerm $ getL label p)
--             (reverse $ T.Branch (nonTerm $ p ^. label) [] : ts)
--         | ts <- fromActive q ]
--
--     fromPassiveTrav p (Subst qp qa) =
--         [ T.Branch
--             (nonTerm $ getL label p)
--             (reverse $ t : ts)
--         | ts <- fromActive qa
--         , t  <- fromPassive qp ]
--
--     fromPassiveTrav _p (Adjoin qa qm) =
--         [ replaceFoot ini aux
--         | aux <- fromPassive qa
--         , ini <- fromPassive qm ]
--
--     -- | Replace foot (the only non-terminal leaf) by the given
--     -- initial tree.
--     replaceFoot ini (T.Branch _ []) = ini
--     replaceFoot ini (T.Branch x ts) = T.Branch x $ map (replaceFoot ini) ts
--     replaceFoot _ t@(T.Leaf _)    = t
--
--
--     fromActive  :: Active -> [[T.Tree n t]]
--     fromActive p = case activeTrav p earSt of
--         Nothing -> error "fromActive: unknown active item"
--         Just travSet -> if S.null travSet
--             then [[]]
--             else concatMap
--                 (fromActiveTrav p)
--                 (S.toList travSet)
--
--     fromActiveTrav _p (Scan q t) =
--         [ T.Leaf t : ts
--         | ts <- fromActive q ]
--
--     fromActiveTrav _p (Foot q p) =
--         [ T.Branch (nonTerm $ p ^. label) [] : ts
--         | ts <- fromActive q ]
--
-- --     fromActiveTrav _p (Foot q x) =
-- --         [ T.Branch x [] : ts
-- --         | ts <- fromActive q ]
--
--     fromActiveTrav _p (Subst qp qa) =
--         [ t : ts
--         | ts <- fromActive qa
--         , t  <- fromPassive qp ]
--
--     fromActiveTrav _p (Adjoin _ _) =
--         error "parsedTrees: fromActiveTrav called on a passive item"
--
--
-- --------------------------------------------------
-- -- EARLEY
-- --------------------------------------------------
--
--
-- -- | Does the given grammar generate the given sentence?
-- -- Uses the `earley` algorithm under the hood.
-- recognize
-- #ifdef Debug
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => FactGram n t         -- ^ The grammar (set of rules)
--     -> Input t            -- ^ Input sentence
--     -> IO Bool
-- recognize gram input = do
--     auto <- mkAuto (D.fromGram gram)
--     recognizeAuto auto input


-- | Does the given grammar generate the given sentence from the
-- given non-terminal symbol (i.e. from an initial tree with this
-- symbol in its root)?  Uses the `earley` algorithm under the
-- hood.
recognizeFrom
#ifdef Debug
    :: (SOrd t, SOrd n)
#else
    :: (Hashable t, Ord t, Hashable n, Ord n)
#endif
    => Memo.Memo t             -- ^ Memoization strategy for terminals
    -> [ ( O.SomeTree n t
         , Weight ) ]          -- ^ Weighted grammar
    -> n                    -- ^ The start symbol
    -> Input t              -- ^ Input sentence
    -> IO Bool
-- recognizeFrom memoTerm gram dag termWei start input = do
recognizeFrom memoTerm gram start input = do
    auto <- mkAuto (W.mkGram gram)
    recognizeFromAuto memoTerm auto start input


-- -- | Parse the given sentence and return the set of parsed trees.
-- parse
-- #ifdef Debug
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => FactGram n t         -- ^ The grammar (set of rules)
--     -> n                    -- ^ The start symbol
--     -> Input t              -- ^ Input sentence
--     -> IO [T.Tree n t]
-- parse gram start input = do
--     auto <- mkAuto (D.fromGram gram)
--     parseAuto auto start input
--
--
-- -- | Perform the earley-style computation given the grammar and
-- -- the input sentence.
-- earley
-- #ifdef Debug
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => FactGram n t         -- ^ The grammar (set of rules)
--     -> Input t              -- ^ Input sentence
--     -> IO (Hype n t)
-- earley gram input = do
--     auto <- mkAuto (D.fromGram gram)
--     earleyAuto auto input


--------------------------------------------------
-- Parsing with automaton
--------------------------------------------------


-- -- | See `recognize`.
-- recognizeAuto
-- #ifdef Debug
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => Auto n t           -- ^ Grammar automaton
--     -> Input t            -- ^ Input sentence
--     -> IO Bool
-- recognizeAuto auto xs =
--     isRecognized xs <$> earleyAuto auto xs


-- | See `recognizeFrom`.
recognizeFromAuto
#ifdef Debug
    :: (SOrd t, SOrd n)
#else
    :: (Hashable t, Ord t, Hashable n, Ord n)
#endif
    => Memo.Memo t      -- ^ Memoization strategy for terminals
    -> Auto n t         -- ^ Grammar automaton
    -> n                -- ^ The start symbol
    -> Input t          -- ^ Input sentence
    -> IO Bool
recognizeFromAuto memoTerm auto start input = do
    hype <- earleyAuto memoTerm auto input
    -- let n = V.length (inputSent input)
    let n = length (inputSent input)
    return $ (not.null) (finalFrom start n hype)


-- -- | See `parse`.
-- parseAuto
-- #ifdef Debug
--     :: (SOrd t, SOrd n)
-- #else
--     :: (Hashable t, Ord t, Hashable n, Ord n)
-- #endif
--     => Auto n t           -- ^ Grammar automaton
--     -> n                  -- ^ The start symbol
--     -> Input t            -- ^ Input sentence
--     -> IO [T.Tree n t]
-- parseAuto auto start input = do
--     earSt <- earleyAuto auto input
--     let n = V.length (inputSent input)
--     return $ parsedTrees earSt start n


-- | See `earley`.
earleyAuto
#ifdef Debug
    :: (SOrd t, SOrd n)
#else
    :: (Hashable t, Ord t, Hashable n, Ord n)
#endif
    => Memo.Memo t      -- ^ Memoization strategy for terminals
    -> Auto n t         -- ^ Grammar automaton
    -> Input t          -- ^ Input sentence
    -> IO (Hype n t)
earleyAuto memoTerm auto input = do
    fst <$> RWS.execRWST (init >> loop) input st0
  where
    -- input length
    -- n = V.length (inputSent input)
    n = length (inputSent input)
    -- empty hypergraph
    st0 = mkHype esti1 esti2 auto
    -- the heuristic
    esti1 = Tmp.estiCost1 memoTerm (termWei auto)
    esti2 = Tmp.estiCost2 memoTerm
                (gramAuto auto)
                (dagGram auto)
                esti1
    -- initialize hypergraph with initial active items
    init = P.runListT $ do
        root <- each . S.toList
              . A.roots . A.fromWei
              . gramAuto $ auto
        i    <- each [0 .. n - 1]
        let q = Active root Span
                { _beg   = i
                , _end   = i
                , _gap   = Nothing }
        lift $ do
            estDist <- estimateDistA q
            pushActive q $ extWeight0 zeroWeight estDist
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popItem >>= \mp -> case mp of
        Nothing -> return ()
        Just p  -> step p >> loop


--------------------------------------------------
-- New utilities
--------------------------------------------------


-- | Return the list of final passive chart items.
finalFrom
    :: (Ord n, Eq t)
    => n            -- ^ The start symbol
    -> Int          -- ^ The length of the input sentence
    -> Hype n t     -- ^ Result of the earley computation
    -> [Passive n t]
finalFrom start n Hype{..} =
    case M.lookup (0, start, n) donePassive of
        Nothing -> []
        Just m ->
            [ p
            | p <- M.keys m
            , p ^. label == NonT start Nothing ]


-- -- -- | Return the list of final passive chart items.
-- -- final
-- --     :: (Ord n, Eq t)
-- --     -> Int          -- ^ The length of the input sentence
-- --     -> Hype n t    -- ^ Result of the earley computation
-- --     -> [Passive n t]
-- -- final start n Hype{..} =
-- --     case M.lookup (0, start, n) donePassive of
-- --         Nothing -> []
-- --         Just m ->
-- --             [ p
-- --             | p <- M.keys m
-- --             , p ^. label == NonT start Nothing ]
--
--
-- -- | Check whether the given sentence is recognized
-- -- based on the resulting state of the earley parser.
-- isRecognized
--     :: (SOrd t, SOrd n)
--     => Input t           -- ^ Input sentence
--     -> Hype n t          -- ^ Earley parsing result
--     -> Bool
-- isRecognized input Hype{..} =
--     (not . null)
--     (complete
--         (agregate donePassive))
--   where
--     n = V.length (inputSent input)
--     complete done =
--         [ True | item <- S.toList done
--         , item ^. spanP ^. beg == 0
--         , item ^. spanP ^. end == n
--         , isNothing (item ^. spanP ^. gap)
--         -- admit only *fully* recognized trees
--         , isRoot (item ^. label) ]
--     agregate = S.unions . map M.keysSet . M.elems
--     isRoot (NonT _ Nothing) = True
--     isRoot _ = False


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | Strict modify (in mtl starting from version 2.2).
modify' :: RWS.MonadState s m => (s -> s) -> m ()
modify' f = do
  x <- RWS.get
  RWS.put $! f x


-- -- | MaybeT transformer.
-- maybeT :: Monad m => Maybe a -> MaybeT m a
-- maybeT = MaybeT . return


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each


-- | ListT from a maybe.
some :: Monad m => Maybe a -> P.ListT m a
some = each . maybeToList


-- | Is the rule with the given head top-level?
topLevel :: Lab n t -> Bool
topLevel x = case x of
    NonT{..}  -> isNothing labID
    AuxRoot{} -> True
    _         -> False


-- | Get a range of the given list.
over :: Pos -> Pos -> [a] -> [a]
over i j = take (j - i) . drop i


-- -- | Pipe all values from the set corresponding to the given key.
-- listValues
--     :: (Monad m, Ord a)
--     => a -> M.Map a (S.Set b)
--     -> P.ListT m b
-- listValues x m = each $ case M.lookup x m of
--     Nothing -> []
--     Just s -> S.toList s
