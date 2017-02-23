{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}


-- | Earley-style TAG parsing based on automata, with a distinction
-- between active and passive items.


module NLP.Partage.Earley.Parser
(
-- * Earley-style parsing
-- ** Input
  Input (..)
, fromList
, fromSets
-- ** From a factorized grammar
-- , recognize
, recognizeFrom
, parse
, earley
-- ** With automata precompiled
-- , recognizeAuto
, recognizeFromAuto
, parseAuto
, earleyAuto
-- ** Automaton
, Auto
, mkAuto

-- * Hypergraph
, module NLP.Partage.Earley.Hypergraph

-- -- * Parsing trace (hypergraph)
-- , Hype
-- ** Extracting parsed trees
, parsedTrees
-- -- ** Stats
-- , hyperNodesNum
-- , hyperEdgesNum
-- -- -- ** Printing
-- -- , printHype

-- * Sentence position
, Pos

-- * Internal (should not be exported here?)
, finalFrom
, topTrav
, passiveTrav
, activeTrav
) where


import           Prelude hiding             (span, (.))
import           Control.Applicative        ((<$>))
import           Control.Monad      (guard, void)
import           Control.Monad.Trans.Class  (lift)
import qualified Control.Monad.RWS.Strict   as RWS
import           Control.Category ((>>>), (.))

import           Data.Maybe     ( mapMaybe , maybeToList )
import qualified Data.Map.Strict            as M
import qualified Data.Tree                  as Tree
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import           Data.Lens.Light
import qualified Data.Vector                as V
-- import           Data.Hashable (Hashable)
-- import qualified Data.HashTable.IO          as H

import qualified Pipes                      as P
-- import qualified Pipes.Prelude              as P

import           Data.DAWG.Ord (ID)
-- import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.Partage.SOrd
import           NLP.Partage.DAG (Gram(..), DID(..))
import qualified NLP.Partage.DAG as DAG
import qualified NLP.Partage.Auto as A
import qualified NLP.Partage.Auto.Trie  as D
import qualified NLP.Partage.Tree       as T

import           NLP.Partage.Earley.Auto (Auto(..), mkAuto)

import           NLP.Partage.Earley.Base -- hiding (nonTerm)
import           NLP.Partage.Earley.Item hiding (printPassive, fromNonActive)
import qualified NLP.Partage.Earley.Item as Item
import           NLP.Partage.Earley.Trav
import qualified NLP.Partage.Earley.Chart as Chart
import           NLP.Partage.Earley.Hypergraph
import           NLP.Partage.Earley.Monad
import qualified NLP.Partage.Earley.Comp  as C

-- For debugging purposes
#ifdef DebugOn
import qualified Data.Time              as Time
#endif


--------------------
-- Waiting Queue
--------------------


-- | Add the active item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushActive :: (Ord n, Ord v) => Active v -> Trav n t v -> Earley n t v ()
pushActive p t = isProcessedA p >>= \b -> if b
    then saveActive p $ S.singleton t
    else modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinPrio (ItemA p) newPrio
    newPrio = ExtPrio (prioA p) (S.singleton t)


-- | Push non-active item to the waiting queue.  Check first if it
-- is not already in the set of processed (`done') states.
pushNonActive :: (Ord n, Ord v) => NonActive n v -> Trav n t v -> Earley n t v ()
pushNonActive p t = isProcessedP p >>= \b -> if b
    then savePassive p $ S.singleton t
    else modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newItem = case p of
      Left x -> ItemP x
      Right x -> ItemT x
    newWait = Q.insertWith joinPrio newItem newPrio
    newPrio = ExtPrio (prio $ Item.fromNonActive p) (S.singleton t)


-- | Push passive item to the agenda.
pushPassive :: (Ord n, Ord v) => Passive v -> Trav n t v -> Earley n t v ()
pushPassive = pushNonActive . Left


-- | Push passive item to the agenda.
pushTop :: (Ord n, Ord v) => Top n v -> Trav n t v -> Earley n t v ()
pushTop = pushNonActive . Right


-- -- | Add the passive item to the waiting queue.  Check first if it
-- -- is not already in the set of processed (`done') states.
-- pushTopPassive :: (Ord t, Ord n) => TopPassive n -> Trav n t -> Earley n t v ()
-- pushTopPassive = undefined


-- | Remove a state from the queue.
--
-- prop> returned item is not top-passive
popItem :: (Ord n, Ord v) => Earley n t v (Maybe (Binding (Item n v) (ExtPrio n t v)))
popItem = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (b, s) -> (Just b, st {waiting = s})


---------------------------------
-- Extraction of Processed Items
---------------------------------


-- | See `Chart.expectEnd`.
expectEnd :: DID -> Pos -> P.ListT (Earley n t v) (Active v)
expectEnd = Chart.expectEnd automat chart


-- | Return all passive items with:
-- * the given root non-terminal value (but not top-level auxiliary)
-- * the given span
rootSpan :: (Ord n) => n -> (Pos, Pos) -> P.ListT (Earley n t v) (Passive v)
rootSpan = Chart.rootSpan chart


--------------------------------------------------
-- New Automaton-Based Primitives
--------------------------------------------------


-- | Follow the given terminal in the underlying automaton.
followTerm :: (Ord t) => ID -> t -> P.ListT (Earley n t v) ID
followTerm i c = do
    -- get the underlying automaton
    auto <- RWS.gets $ automat
    -- get the dag ID corresponding to the given terminal
    did  <- some $ M.lookup c (termDID auto)
    -- follow the label
    some $ A.follow (gramAuto auto) i (A.Body did)


-- | Follow the given body transition in the underlying automaton.
-- It represents the transition function of the automaton.
--
-- TODO: merge with `followTerm`.
follow :: ID -> DID -> P.ListT (Earley n t v) ID
follow i x = do
    -- get the underlying automaton
    auto <- RWS.gets $ gramAuto . automat
    -- follow the label
    some $ A.follow auto i (A.Body x)


-- | Rule heads outgoing from the given automaton state.
heads :: ID -> P.ListT (Earley n t v) DID
heads i = do
    auto <- RWS.gets $ gramAuto . automat
    let mayHead (x, _) = case x of
            A.Body _  -> Nothing
            A.Head y -> Just y
    each $ mapMaybe mayHead $ A.edges auto i


-- -- | Check if any (body) element leaves the given state.
-- hasElems :: ID -> Earley n t v Bool
-- hasElems i = do
--     auto <- RWS.gets $ gramAuto . automat
--     let mayBody (x, _) = case x of
--             A.Body y  -> Just y
--             A.Head _ -> Nothing
--     return
--         . not . null
--         . mapMaybe mayBody
--         $ A.edges auto i


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- | Try to perform SCAN on the given active state.
tryScan :: (SOrd t, SOrd n, SOrd v) => Active v -> Earley n t v ()
tryScan p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- read the word immediately following the ending position of
    -- the state (together with the value assigned to it)
    (tok@(Tok _ c), val) <- readInput $ getL (spanA >>> end) p
    -- follow appropriate terminal transition outgoing from the
    -- given automaton state
    j <- followTerm (getL state p) c
    -- construct the resultant active item
    let q = setL state j
          . modL' (spanA >>> end) (+1)
          . modL' traceA (C.leaf val :)
          $ p
    -- push the resulting state into the waiting queue
    lift $ pushActive q $ Scan p tok
#ifdef DebugOn
    -- print logging information
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[S]  " >> printActive p
        putStr "  :  " >> printActive q
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- DEACTIVATE
--------------------------------------------------


-- | Try to perform DEACTIVATE on the given active state.
tryDeactivate :: (SOrd t, SOrd n, SOrd v) => Active v -> Earley n t v ()
tryDeactivate p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    did <- heads (getL state p)
    let trace = Tree.Node Nothing (reverse (p ^. traceA))
        q = Passive did (p ^. spanA) trace
    lift . pushPassive q $ Deact p
#ifdef DebugOn
    -- print logging information
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[D]  " >> printActive p
        putStr "  :  " >> printPassive hype q
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- FINILIZE
--------------------------------------------------


-- | Try to perform DEACTIVATE on the given active state.
tryFinilize :: (SOrd t, SOrd n, SOrd v) => Passive v -> Earley n t v ()
tryFinilize p = void $ P.runListT $ do
#ifdef DebugOn
  begTime <- lift . lift $ Time.getCurrentTime
#endif
  let pDID = p ^. dagID
  dag <- RWS.gets (gramDAG . automat)
  guard $ DAG.isRoot pDID dag
  newItem <- some $ do
    labl <- DAG.label pDID dag
    x <- labNonTerm labl
    return $ Top (p ^. spanP) x
  q <- each $ do
    C.Comp{..} <- maybeToList $ DAG.value pDID dag
    valu <- up (p ^. traceP)
    return $ newItem valu
  lift . pushTop q $ Fini p
#ifdef DebugOn
    -- print logging information
  hype <- RWS.get
  lift . lift $ do
    endTime <- Time.getCurrentTime
    putStr "[F]  " >> printPassive hype p
    putStr "  :  " >> printTop q
    putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the passive item `p` to complement
-- (=> substitution) other rules.
trySubst :: (SOrd t, SOrd n, SOrd v) => NonActive n v -> Earley n t v ()
trySubst p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pSpan = spanN p
    -- make sure that `p' represents regular rules
    guard . regular $ pSpan
    -- the underlying leaf map
    leafMap <- RWS.gets (leafDID  . automat)
    -- now, we need to choose the DAG node to search for depending on
    -- whether the DAG node provided by `p' is a root or not
    theDID <- case p of
        -- pseudo-substitution
        Left  pas -> return $ pas ^. dagID
        -- real substitution
        Right top -> some $ M.lookup (top ^. label) leafMap
    -- determine the (head of the) trace for the new item
    traceHead <- return $ case p of
        -- pseudo-substitution
        Left  pas -> pas ^. traceP
        -- real substitution
        Right top -> C.leaf (top ^. value)
    -- find active items which end where `p' begins and which
    -- expect the DAG node provided by `p'
    q <- expectEnd theDID (getL beg pSpan)
    -- follow the DAG node
    j <- follow (getL state q) theDID
    -- construct the resultant state
    let q' = setL state j
           . setL (end . spanA) (getL end pSpan)
           . modL' traceA (traceHead :)
           $ q
    -- push the resulting state into the waiting queue
    -- lift $ pushInduced q' $ Subst p q
    lift $ pushActive q' $ Subst p q
#ifdef DebugOn
    -- print logging information
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[U]  " >> printNonActive hype p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- FOOT ADJOIN
--------------------------------------------------


-- | `tryAdjoinInit p q':
-- * `p' is a passive item (regular or auxiliary)
-- * `q' is not completed and expects a *real* foot
tryAdjoinInit :: (SOrd n, SOrd t, SOrd v) => Passive v -> Earley n t v ()
tryAdjoinInit p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    -- the underlying grammar
    auto <- RWS.gets automat
    let pSpan = p ^. spanP
        -- footNT = labelN p auto
        footNT = nonTerm (p ^. dagID) auto
        dag = gramDAG auto
        footMap = footDID auto
    -- make sure that the corresponding rule is either regular or intermediate
    -- auxiliary ((<=) used as an inverse of implication here)
    guard $ auxiliary pSpan <= not (DAG.isRoot (p ^. dagID) dag)
    -- guard $ auxiliary pSpan <= not (isTop p)
    -- what is the symbol in the p's DAG node?
    -- what is the corresponding foot DAG ID?
    footID <- some $ M.lookup footNT footMap
    -- find all active items which expect a foot with the given
    -- symbol and which end where `p` begins
    q <- expectEnd footID (getL beg pSpan)
    -- follow the foot
    j <- follow (getL state q) footID
    -- construct the resultant state
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (Just
                ( pSpan ^. beg
                , pSpan ^. end ))
           . modL' traceA (C.foot :)
           $ q
    -- push the resulting state into the waiting queue
    lift $ pushActive q' $ Foot q footNT
#ifdef DebugOn
    -- print logging information
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[A]  " >> printPassive hype p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- INTERNAL ADJOIN
--------------------------------------------------


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
tryAdjoinCont :: (SOrd n, SOrd t, SOrd v) => Passive v -> Earley n t v ()
tryAdjoinCont p = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let pDID = p ^. dagID
        pSpan = p ^. spanP
    -- make sure that `p' is an auxiliary item
    guard . auxiliary $ pSpan
    -- find all rules which expect a spine non-terminal provided
    -- by `p' and which end where `p' begins
    q <- expectEnd pDID (pSpan ^. beg)
    -- follow the spine non-terminal
    j <- follow (q ^. state) pDID
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = setL state j
           . setL (spanA >>> end) (pSpan ^. end)
           . setL (spanA >>> gap) (pSpan ^. gap)
           . modL' traceA (p ^. traceP :)
           $ q
    -- push the resulting state into the waiting queue
    -- lift $ pushInduced q' $ Subst p q
    lift $ pushActive q' $ Subst (Left p) q
#ifdef DebugOn
    -- logging info
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[B]  " >> printPassive hype p
        putStr "  +  " >> printActive q
        putStr "  :  " >> printActive q'
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- ROOT ADJOIN
--------------------------------------------------


-- -- | A class of types over which the unification computation can be performed.
-- class Unify v where
--   -- | Unification function.  It can fail with `Nothing`, which means that the
--   -- two given values do not unify.
--   unify :: v -> v -> Maybe v
--
-- instance Unify () where
--   unify _ _ = Just ()


-- | Adjoin a fully-parsed auxiliary tree represented by `q` to a partially
-- parsed tree represented by `p`.
tryAdjoinTerm :: (SOrd t, SOrd n, SOrd v, Unify v) => Top n v -> Earley n t v ()
tryAdjoinTerm q = void $ P.runListT $ do
#ifdef DebugOn
    begTime <- lift . lift $ Time.getCurrentTime
#endif
    let rootNT = q ^. label
        qSpan = q ^. spanT
    -- make sure that it is an auxiliary item (by definition only
    -- auxiliary states have gaps)
    (gapBeg, gapEnd) <- some $ qSpan ^. gap
    -- retrieve the underlying dag grammar
    dag <- RWS.gets (gramDAG . automat)
    -- take all passive items with a given span and a given
    -- root non-terminal (IDs irrelevant)
    p <- rootSpan rootNT (gapBeg, gapEnd)
    -- make sure that the corresponding rule is either regular or intermediate
    -- auxiliary ((<=) used as an inverse of implication here)
    guard $ auxiliary (p ^. spanP) <= not (DAG.isRoot (p ^. dagID) dag)
--     guard $ auxiliary (p ^. spanP) <= not (isTop p)
    -- compute new value assigned to the passive item
    let Tree.Node pValueMaybe ts = p ^. traceP
        qValue = q ^. value
    newValue <- some $ case pValueMaybe of
        Nothing -> Just qValue
        Just pValue -> unify qValue pValue
    -- create the resulting item
    let p' = setL (spanP >>> beg) (qSpan ^. beg)
           . setL (spanP >>> end) (qSpan ^. end)
           . setL traceP (Tree.Node (Just newValue) ts)
           $ p
    lift $ pushPassive p' $ Adjoin q p
#ifdef DebugOn
    hype <- RWS.get
    lift . lift $ do
        endTime <- Time.getCurrentTime
        putStr "[C]  " >> printTop q
        putStr "  +  " >> printPassive hype p
        putStr "  :  " >> printPassive hype p'
        putStr "  OLD VALUE: " >> print pValueMaybe
        putStr "  NEW VALUE: " >> print (Just newValue)
        putStr "  @  " >> print (endTime `Time.diffUTCTime` begTime)
#endif


--------------------------------------------------
-- Earley step
--------------------------------------------------


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step
    -- :: (SOrd t, SOrd n)
    :: (SOrd t, SOrd n, SOrd v, Unify v)
    => Binding (Item n v) (ExtPrio n t v)
    -> Earley n t v ()
step (ItemA p :-> e) = do
    mapM_ ($ p)
      [ tryScan
      , tryDeactivate ]
    saveActive p $ prioTrav e
step (ItemP p :-> e) = do
    mapM_ ($ p)
      [ trySubst . Left
      , tryAdjoinInit
      , tryAdjoinCont
      , tryFinilize ]
    savePassive (Left p) $ prioTrav e
step (ItemT p :-> e) = do
    mapM_ ($ p)
      [ trySubst . Right
      , tryAdjoinTerm ]
    savePassive (Right p) $ prioTrav e


---------------------------
-- Extracting Parsed Trees
---------------------------


-- | Extract the set of parsed trees obtained on the given input
-- sentence.  Should be run on the result of the earley parser.
parsedTrees
    :: forall n t v. (Ord n, Ord t, Ord v)
    => Hype n t v   -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> [T.Tree n t]
parsedTrees hype start n

    = concatMap fromTop
    $ finalFrom start n hype

  where


    auto = automat hype


    fromTop :: Top n v -> [T.Tree n t]
    fromTop p = concat
        [ fromTopTrav p trav
        | travSet <- maybeToList $ nonActiveTrav (Right p) hype
        , trav <- S.toList travSet ]
    fromTopTrav _p (Fini q) = fromPassive q
    fromTopTrav _p _ =
        error "parsedTrees.fromTopTrav: impossible happened"


    fromPassive :: Passive v -> [T.Tree n t]
    fromPassive p = concat
        [ fromPassiveTrav p trav
        | travSet <- maybeToList $ nonActiveTrav (Left p) hype
        , trav <- S.toList travSet ]

    fromPassiveTrav p (Deact q) =
        [ T.Branch
            (nonTerm (getL dagID p) auto)
            (reverse ts)
        | ts <- fromActive q ]

    fromPassiveTrav _p (Adjoin qa qm) =
        [ replaceFoot ini aux
        | aux <- fromTop qa
        , ini <- fromPassive qm ]

    fromPassiveTrav _p _ =
        error "parsedTrees.fromPassiveTrav: impossible happened"

    -- | Replace foot (the only non-terminal leaf) by the given
    -- initial tree.
    replaceFoot ini (T.Branch _ []) = ini
    replaceFoot ini (T.Branch x ts) = T.Branch x $ map (replaceFoot ini) ts
    replaceFoot _ t@(T.Leaf _)    = t


    fromActive  :: Active v -> [[T.Tree n t]]
    fromActive p = case activeTrav p hype of
        Nothing -> error "fromActive: unknown active item"
        Just travSet -> if S.null travSet
            then [[]]
            else concatMap
                (fromActiveTrav p)
                (S.toList travSet)

    fromActiveTrav _p (Scan q tok) =
        [ T.Leaf (terminal tok) : ts
        | ts <- fromActive q ]

    fromActiveTrav _p (Subst qp qa) =
        [ t : ts
        | ts <- fromActive qa
        , t  <- fromNonActive qp ]

    fromActiveTrav _p (Foot q p) =
        -- [ T.Branch (nonTerm (p ^. dagID) auto) [] : ts
        [ T.Branch p [] : ts
        | ts <- fromActive q ]

    fromActiveTrav _p _ =
        error "parsedTrees.fromActiveTrav: impossible happened"


    fromNonActive :: NonActive n v -> [T.Tree n t]
    fromNonActive x = case x of
      Left p  -> fromPassive p
      Right p -> fromTop p


-- --------------------------------------------------
-- -- EARLEY
-- --------------------------------------------------
--
--
-- -- | Does the given grammar generate the given sentence?
-- -- Uses the `earley` algorithm under the hood.
-- recognize
-- #ifdef DebugOn
--     :: (SOrd t, SOrd n)
-- #else
--     -- :: (Hashable t, Ord t, Hashable n, Ord n)
--     :: (Ord t, Ord n)
-- #endif
--     => DAG.Gram n t       -- ^ The grammar (set of rules)
--     -> Input t            -- ^ Input sentence
--     -> IO Bool
-- recognize DAG.Gram{..} input = do
--     let gram = D.fromGram (M.keysSet factGram)
--         auto = mkAuto dagGram gram
--     recognizeAuto auto input


-- | Does the given grammar generate the given sentence from the
-- given non-terminal symbol (i.e. from an initial tree with this
-- symbol in its root)?  Uses the `earley` algorithm under the
-- hood.
recognizeFrom
#ifdef DebugOn
    :: (SOrd t, SOrd n, SOrd v, Unify v)
#else
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n, Ord v, Unify v)
#endif
    => DAG.Gram n t (C.Comp v) -- ^ The grammar
    -> n                       -- ^ The start symbol
    -> Input t v               -- ^ Input sentence
    -> IO Bool
recognizeFrom DAG.Gram{..} start input = do
    let gram = D.fromGram factGram
        auto = mkAuto dagGram gram
    recognizeFromAuto auto start input


-- | Parse the given sentence and return the set of parsed trees.
parse
#ifdef DebugOn
    :: (SOrd t, SOrd n, SOrd v, Unify v)
#else
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n, Ord v, Unify v)
#endif
    => DAG.Gram n t (C.Comp v) -- ^ The grammar (set of rules)
    -> n                       -- ^ The start symbol
    -> Input t v               -- ^ Input sentence
    -> IO [T.Tree n t]
parse DAG.Gram{..} start input = do
    let gram = D.fromGram factGram
        auto = mkAuto dagGram gram
    parseAuto auto start input


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
#ifdef DebugOn
    :: (SOrd t, SOrd n, SOrd v, Unify v)
#else
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n, Ord v, Unify v)
#endif
    => DAG.Gram n t (C.Comp v) -- ^ The grammar (set of rules)
    -> Input t v               -- ^ Input sentence
    -> IO (Hype n t v)
earley DAG.Gram{..} input = do
    let gram = D.fromGram factGram
        auto = mkAuto dagGram gram
    earleyAuto auto input


--------------------------------------------------
-- Parsing with automaton
--------------------------------------------------


-- -- | See `recognize`.
-- recognizeAuto
-- #ifdef DebugOn
--     :: (SOrd t, SOrd n, SOrd v, Unify v)
-- #else
--     -- :: (Hashable t, Ord t, Hashable n, Ord n)
--     :: (Ord t, Ord n, Ord v, Unify v)
-- #endif
--     => Auto n t v         -- ^ Grammar automaton
--     -> Input t v          -- ^ Input sentence
--     -> IO Bool
-- recognizeAuto auto xs =
--     isRecognized xs <$> earleyAuto auto xs


-- | See `recognizeFrom`.
recognizeFromAuto
#ifdef DebugOn
    :: (SOrd t, SOrd n, SOrd v, Unify v)
#else
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n, Ord v, Unify v)
#endif
    => Auto n t v     -- ^ Grammar automaton
    -> n              -- ^ The start symbol
    -> Input t v      -- ^ Input sentence
    -> IO Bool
recognizeFromAuto auto start input = do
    hype <- earleyAuto auto input
    let n = V.length (inputSent input)
    return $ (not . null) (finalFrom start n hype)


-- | See `parse`.
parseAuto
#ifdef DebugOn
    :: (SOrd t, SOrd n, SOrd v, Unify v)
#else
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n, Ord v, Unify v)
#endif
    => Auto n t v         -- ^ Grammar automaton
    -> n                  -- ^ The start symbol
    -> Input t v          -- ^ Input sentence
    -> IO [T.Tree n t]
parseAuto auto start input = do
    earSt <- earleyAuto auto input
    let n = V.length (inputSent input)
    return $ parsedTrees earSt start n


-- | See `earley`.
earleyAuto
#ifdef DebugOn
    :: (SOrd t, SOrd n, SOrd v, Unify v)
#else
    -- :: (Hashable t, Ord t, Hashable n, Ord n)
    :: (Ord t, Ord n, Ord v, Unify v)
#endif
    => Auto n t v       -- ^ Grammar automaton
    -> Input t v        -- ^ Input sentence
    -> IO (Hype n t v)
earleyAuto auto input = do
    fst <$> RWS.execRWST loop input st0
  where
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkHype auto $ S.fromList
        [ Active root span0 []
        | i <- [0 .. n - 1]
        , root <- S.toList . A.roots $ gramAuto auto
        , let span0 = Span
                { _beg   = i
                , _end   = i
                , _gap   = Nothing } ]
    -- input length
    n = V.length (inputSent input)
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popItem >>= \mp -> case mp of
        Nothing -> return ()
        Just p  -> step p >> loop


--------------------------------------------------
-- New utilities
--------------------------------------------------


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
--         (agregate $ Chart.donePassive chart))
--   where
--     n = V.length (inputSent input)
--     complete done =
--         [ True | item <- S.toList done
--         , item ^. spanP ^. beg == 0
--         , item ^. spanP ^. end == n
--         , isNothing (item ^. spanP ^. gap)
--         -- admit only *fully* recognized trees
--         , isRoot (item ^. dagID) ]
--         -- , DAG.isRoot (item ^. dagID) (gramDAG automat) ]
--         -- , isRoot (item ^. label) ]
--     agregate = S.unions . map M.keysSet . M.elems
--     -- isRoot (NonT _ Nothing) = True
--     -- isRoot _ = False


--------------------------------------------------
-- New Utilities
--------------------------------------------------


-- | Return the corresponding set of traversals for an active item.
activeTrav
  :: (Ord v)
  => Active v
  -> Hype n t v
  -> Maybe (S.Set (Trav n t v))
activeTrav p h = Chart.activeTrav p (chart h)


-- | Return the corresponding set of traversals for a non-active item.
nonActiveTrav
  :: (Ord n, Ord v)
  => NonActive n v
  -> Hype n t v
  -> Maybe (S.Set (Trav n t v))
nonActiveTrav p h = Chart.passiveTrav p (automat h) (chart h)


-- | Return the corresponding set of traversals for a top item.
topTrav
  :: (Ord n, Ord v)
  => Top n v
  -> Hype n t v
  -> Maybe (S.Set (Trav n t v))
topTrav p = nonActiveTrav (Right p)


-- | Return the corresponding set of traversals for a passive item.
passiveTrav
  :: (Ord n, Ord v)
  => Passive v
  -> Hype n t v
  -> Maybe (S.Set (Trav n t v))
passiveTrav p = nonActiveTrav (Left p)


-- | Return the list of final, initial, passive chart items.
finalFrom
    :: (Ord n)
    => n            -- ^ The start symbol
    -> Int          -- ^ The length of the input sentence
    -> Hype n t v   -- ^ Result of the earley computation
    -> [Top n v]
finalFrom start n hype = Chart.finalFrom start n (chart hype)


--------------------------------------------------
-- Printing Item
--------------------------------------------------


#ifdef DebugOn
-- -- | Print a passive item.
-- printTop :: (Show n, Show v) => Top n v -> IO ()
-- printTop p = Item.printTop p


-- | Print a passive item.
printPassive :: (Show n, Show t) => Hype n t v -> Passive v -> IO ()
printPassive hype p = Item.printPassive p (automat hype)


-- | Print a passive item.
printNonActive :: (Show n, Show t, Show v) => Hype n t v -> NonActive n v -> IO ()
printNonActive hype x = case x of
  Left  p -> Item.printPassive p (automat hype)
  Right p -> printTop p


-- -- | Print an active item.
-- printItem :: (Show n, Show t) => Item n t -> Hype n t -> IO ()
-- printItem (ItemP p) h = printPassive p h
-- printItem (ItemA p) _ = printActive p
#endif


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


-- -- | Take the non-terminal of the underlying DAG node.
-- nonTerm :: Either n DID -> Hype n t a -> n
-- nonTerm i = Base.nonTerm i . automat
