{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}


-- | Earley-style parsing with automaton-based grammar
-- representation.


module NLP.TAG.Vanilla.Earley.Auto where


import           Control.Applicative        ((<$>))
import           Control.Monad              (guard, void, (>=>))
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Trans.Maybe  (MaybeT (..))
import qualified Control.Monad.RWS.Strict   as RWS

import           Data.Function              (on)
import           Data.Maybe     ( isJust, isNothing, mapMaybe
                                , listToMaybe, maybeToList)
import qualified Data.Map.Strict            as M
import qualified Data.Set                   as S
import qualified Data.PSQueue               as Q
import           Data.PSQueue (Binding(..))
import qualified Pipes                      as P

import           Data.DAWG.Gen.Types (ID)
import qualified Data.DAWG.Ord.Dynamic      as D

import           NLP.TAG.Vanilla.Core
import           NLP.TAG.Vanilla.Rule
                                ( Lab(..), Rule(..) )
import qualified NLP.TAG.Vanilla.Automaton  as A
import qualified NLP.TAG.Vanilla.Tree       as T



--------------------------------------------------
-- CHART ITEM
--------------------------------------------------


-- | Chart item.
data Item n t = Item {
    -- | State of the underlying automaton.
      state :: ID
    -- | The starting position.
    , beg   :: Pos
    -- | The ending position (or rather the position of the dot).
    , end   :: Pos
    -- | Coordinates of the gap (if applies)
    , gap   :: Maybe (Pos, Pos)
    } deriving (Show, Eq, Ord)


-- | Does it represent regular rules?
regular :: Item n t -> Bool
regular = isNothing . gap


-- | Does it represent auxiliary rules?
auxiliary :: Item n t -> Bool
auxiliary = isJust . gap


-- | Is the rule with the given head top-level?
topLevel :: Lab n t -> Bool
topLevel x = case x of
    NonT{..}  -> isNothing labID
    AuxRoot{} -> True
    _         -> False


-- | Print the state.
printItem :: (View n, View t) => Item n t -> IO ()
printItem Item{..} = do
    putStr "("
    putStr $ show state
    putStr ", "
    putStr $ show beg
    putStr ", "
    case gap of
        Nothing -> return ()
        Just (p, q) -> do
            putStr $ show p
            putStr ", "
            putStr $ show q
            putStr ", "
    putStr $ show end
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
        { scanFrom :: Item n t
        -- ^ The input active state
        , scanTerm :: t
        -- ^ The scanned terminal
        }
    | Subst
    -- ^ Pseudo substitution
        { passArg  :: Item n t
        -- ^ The passive argument of the action
        , actArg   :: Item n t
        -- ^ The active argument of the action
        , passRoot :: n
        -- ^ Root non-terminal of the passive item
        }
    | Foot
    -- ^ Foot adjoin
        { actArg   :: Item n t
        -- ^ The active argument of the action
        , theFoot  :: n
        -- ^ The foot non-terminal
        }
    | Adjoin
    -- ^ Adjoin terminate with two passive arguments
        { passAdj  :: Item n t
        -- ^ The adjoined item
        , passMod  :: Item n t
        -- ^ The modified item
        }
    deriving (Show, Eq, Ord)


--------------------------------------------------
-- Priority
--------------------------------------------------


-- | Priority type.
type Prio = Int



-- | Priority of a state.  Crucial for the algorithm -- states have
-- to be removed from the queue in a specific order.
prio :: Item n t -> Prio
prio p = end p


-- | Extended priority which preservs information about the traversal leading
-- to the underlying chart item.
data ExtPrio n t = ExtPrio
    { prioVal   :: Prio
    -- ^ The actual priority
    , prioTrav  :: S.Set (Trav n t)
    -- ^ Traversal leading to the underlying chart item
    } deriving (Show)

instance (Eq n, Eq t) => Eq (ExtPrio n t) where
    (==) = (==) `on` prioVal
instance (Ord n, Ord t) => Ord (ExtPrio n t) where
    compare = compare `on` prioVal


-- | Construct a new `ExtPrio`.
extPrio :: Prio -> ExtPrio n t
extPrio p = ExtPrio p S.empty


-- | Join two priorities:
-- * The actual priority preserved is the lower of the two,
-- * The traversals are unioned.
--
-- NOTE: at the moment, priority is strictly specified by the underlying chart
-- item itself so we know that both priorities must be equal.  Later when we
-- start using probabilities this statement will no longer hold.
joinPrio :: (Ord n, Ord t) => ExtPrio n t -> ExtPrio n t -> ExtPrio n t
joinPrio x y = ExtPrio
    (min (prioVal x) (prioVal y))
    (S.union (prioTrav x) (prioTrav y))


--------------------------------------------------
-- Set of Processed Items (Done Items)
--------------------------------------------------


-- | The set of processed items is stored as a map
-- * from `end` position to a map
--  * from `state` ID to a map
--   * from `beg` position to a set
--    * of the corresponding items
type Done n t =
    M.Map Pos
        ( M.Map ID
            ( M.Map Pos
                -- ( S.Set (Item n t) )
                ( M.Map (Item n t) (S.Set (Trav n t)) )
            )
        )


-- | List all done items.
listDone :: Done n t -> [Item n t]
listDone done = ($done) $
    M.elems >=> M.elems >=>
    M.elems >=> M.keys -- S.toList


-- | List all done items together with the corresponding traversals.
listDoneTrav :: Done n t -> [(Item n t, S.Set (Trav n t))]
listDoneTrav done = ($done) $
    M.elems >=> M.elems >=>
    M.elems >=> M.toList


-- | Return the corresponding set of traversals.
doneTrav
    :: (Ord n, Ord t)
    => Item n t -> Done n t
    -> Maybe (S.Set (Trav n t))
doneTrav x@Item{..}
    =   M.lookup end
    >=> M.lookup state
    >=> M.lookup beg
    >=> M.lookup x


-- | Check if the state is not already processed.
_isProcessed :: (Ord n, Ord t) => Item n t -> Done n t -> Bool
_isProcessed x =
    check . doneTrav x
  where
    check (Just _) = True
    check _        = False


--------------------------------------------------
-- Earley monad
--------------------------------------------------


-- | The state of the earley monad.
data EarSt n t = EarSt {
    -- | The underlying automaton.
      automat :: A.DAWG n t

    -- | A data structure which, for each label, determines the
    -- set of automaton states from which this label goes out
    -- as a body transition.
    , withBody :: M.Map (Lab n t) (S.Set ID)

    -- | A data structure which, for each source non-terminal,
    -- determines the set of automaton states from which this
    -- non-terminal goes out as a head transition.
    , withHead :: M.Map n (S.Set ID)

    -- | Processed items.
    , done     :: Done n t

    -- | The set of states waiting on the queue to be processed.
    -- Invariant: the intersection of `done' and `waiting' states
    -- is empty.
    , waiting :: Q.PSQ (Item n t) (ExtPrio n t) }


-- | Make an initial `EarSt` from a set of states.
mkEarSt
    :: (Ord n, Ord t)
    => A.DAWG n t
    -> S.Set (Item n t)
    -> (EarSt n t)
mkEarSt dag s = EarSt
    { automat = dag
    , withBody = mkWithBody dag
    , withHead = mkWithHead dag
    , done = M.empty
    , waiting = Q.fromList
        [ p :-> extPrio (prio p)
        | p <- S.toList s ] }


-- | Create the `withBody` component based on the automaton.
mkWithBody
    :: (Ord n, Ord t)
    => A.DAWG n t
    -> M.Map (Lab n t) (S.Set ID)
mkWithBody dag = M.fromListWith S.union
    [ (x, S.singleton i)
    | (i, A.Body x, _j) <- A.edges dag ]


-- | Create the `withHead` component based on the automaton.
mkWithHead
    :: (Ord n, Ord t)
    => A.DAWG n t
    -> M.Map n (S.Set ID)
mkWithHead dag = M.fromListWith S.union
    [ (nonTerm x, S.singleton i)
    | (i, A.Head x, _j) <- A.edges dag ]


-- | Earley parser monad.  Contains the input sentence (reader)
-- and the state of the computation `EarSt'.
type Earley n t = RWS.RWST [t] () (EarSt n t) IO


-- | Read word from the given position of the input.
readInput :: Pos -> MaybeT (Earley n t) t
readInput i = do
    -- ask for the input
    xs <- RWS.ask
    -- just a safe way to retrieve the i-th element
    maybeT $ listToMaybe $ drop i xs


--------------------------------------------------
-- Hypergraph stats
--------------------------------------------------


-- | Number of nodes in the parsing hypergraph.
hyperNodesNum :: EarSt n t -> Int
hyperNodesNum = length . listDone . done


-- | Number of edges in the parsing hypergraph.
hyperEdgesNum :: EarSt n t -> Int
hyperEdgesNum EarSt{..} = sum
    [ S.size travSet
    | (_, travSet) <- listDoneTrav done ]


---------------------------
-- Extracting Parsed Trees
---------------------------


-- | Extract the set of parsed trees obtained on the given input sentence.
-- Should be run on the result of the earley algorithm.
parsedTrees
    :: forall n t. (Ord n, Ord t, Show n, Show t)
    => EarSt n t    -- ^ Final state of the earley parser
    -- => Done n t     -- ^ `done` part of the final parsing state
    -> n            -- ^ The start symbol
    -> Int          -- ^ Length of the input sentence
    -> S.Set (T.Tree n t)
parsedTrees earSt@EarSt{..} start n

    = S.fromList
    $ concatMap (fromPassive start)
    $ final earSt start n

  where

    fromPassive :: n -> Item n t -> [T.Tree n t]
    fromPassive root p = concat
        [ fromPassiveTrav root trav
        | travSet <- maybeToList $ doneTrav p done
        -- | let travSet = donePassive M.! p
        , trav <- S.toList travSet ]

    fromPassiveTrav root (Scan q t) =
        [ T.INode
            root -- (nonTerm $ getL label p)
            (reverse $ T.FNode t : ts)
        | ts <- fromActive q ]

    fromPassiveTrav root (Foot q x) =
        [ T.INode
            root -- (nonTerm $ getL label p)
            (reverse $ T.INode x [] : ts)
        | ts <- fromActive q ]

    fromPassiveTrav root (Subst qp qa x) =
        [ T.INode
            root -- (nonTerm $ getL label p)
            (reverse $ t : ts)
        | ts <- fromActive qa
        , t  <- fromPassive x qp ]

    fromPassiveTrav root (Adjoin qa qm) =
        [ replaceFoot ini aux
        | aux <- fromPassive root qa
        , ini <- fromPassive root qm ]

    -- | Replace foot (the only non-terminal leaf) by the given initial tree.
    replaceFoot ini (T.INode _ []) = ini
    replaceFoot ini (T.INode x ts) = T.INode x $ map (replaceFoot ini) ts
    replaceFoot _ t@(T.FNode _)    = t


    fromActive  :: Item n t -> [[T.Tree n t]]
    fromActive p = case doneTrav p done of
        Nothing -> error "fromActive: unknown active item"
        Just travSet -> if S.null travSet
            then [[]]
            else concatMap
                (fromActiveTrav p)
                (S.toList travSet)

    fromActiveTrav _p (Scan q t) =
        [ T.FNode t : ts
        | ts <- fromActive q ]

    fromActiveTrav _p (Foot q x) =
        [ T.INode x [] : ts
        | ts <- fromActive q ]

    fromActiveTrav _p (Subst qp qa x) =
        [ t : ts
        | ts <- fromActive qa
        , t  <- fromPassive x qp ]

    fromActiveTrav _p (Adjoin _ _) =
        error "parsedTrees: fromActiveTrav called on a passive item"



--------------------
-- Processed Items
--------------------


-- | Check if the item is not already processed.
isProcessed :: (Ord n, Ord t) => Item n t -> Earley n t Bool
isProcessed p = _isProcessed p <$> RWS.gets done


-- | Add the state to the set of processed (`done') states.
saveItem 
    :: (Ord t, Ord n)
    => Item n t
    -> S.Set (Trav n t)
    -> Earley n t ()
saveItem p ts =
    RWS.state $ \s -> ((), s {done = newDone s})
  where
    newDone st =
        M.insertWith
            (M.unionWith (M.unionWith (M.unionWith S.union)))
            (end p)
            ( M.singleton (state p)
                ( M.singleton (beg p)
                    -- ( S.singleton p )
                    ( M.singleton p ts )
                    -- ( M.insertWith S.union p ts )
                )
            )
            (done st)


--------------------
-- Waiting Queue
--------------------


-- | Add item to the waiting queue.  Check first if it is
-- not already in the set of processed (`done') states.
pushItem :: (Ord t, Ord n) => Item n t -> Trav n t -> Earley n t ()
pushItem p t = isProcessed p >>= \b -> if b
    then saveItem p $ S.singleton t
    else RWS.modify' $ \s -> s {waiting = newWait (waiting s)}
  where
    newWait = Q.insertWith joinPrio p newPrio
    newPrio = ExtPrio (prio p) (S.singleton t)
-- pushItem p = RWS.state $ \s ->
--     let waiting' = if isProcessed p (done s)
--             then waiting s
--             else Q.insert p (prio p) (waiting s)
--     in  ((), s {waiting = waiting'})


-- | Remove an item from the queue.
popItem
    :: (Ord t, Ord n)
    => Earley n t
        (Maybe (Binding (Item n t) (ExtPrio n t)))
popItem = RWS.state $ \st -> case Q.minView (waiting st) of
    Nothing -> (Nothing, st)
    Just (b, s) -> (Just b, st {waiting = s})


---------------------------------
-- Extraction of Processed Items
---------------------------------


-- | Return all "done" items which:
-- * expect a given label,
-- * end on the given position.
expectEnd
    :: (Ord n, Ord t) => Lab n t -> Pos
    -> P.ListT (Earley n t) (Item n t)
expectEnd sym i = do
    EarSt{..} <- lift RWS.get
    -- determine items which end on the given position
    doneEnd <- some $ M.lookup i done
    -- determine automaton states from which the given label
    -- leaves as a body transition
    stateSet <- some $ M.lookup sym withBody
    -- pick one of the states
    state <- each $ S.toList stateSet
    --
    -- ALTERNATIVE: state <- each . S.toList $
    --      stateSet `S.intersection` M.keySet doneEnd
    --
    -- determine items which refer to the chosen states
    doneEndLab <- some $ M.lookup state doneEnd
    -- return them all!
    each [x | xs <- M.elems doneEndLab, x <- M.keys xs]


-- | Return all fully recognized "done" items with:
-- * the given root non-terminal value (but not top-level
--   auxiliary)
-- * the given span
--
-- NOTE: this function can be potentially slow.  `withHead` can
-- potentially contain a very high number of entries for a given
-- source non-terminal.  Only later the information about the span
-- beginning is taken into account.  As a result, a high number of
-- entries for a given source-non-terminal head can be extracted only
-- to be discarded in the next step.
rootSpan
    :: Ord n => n -> (Pos, Pos)
    -> P.ListT (Earley n t) (Item n t)
rootSpan x (i, j) = do
    EarSt{..} <- lift RWS.get
    -- determine items ending on the given position
    doneEnd <- some $ M.lookup j done
    -- determine automaton states from which the given label
    -- leaves as a head transition
    stateSet <- some $ M.lookup x withHead
    -- pick one of the states
    state <- each $ S.toList stateSet
    -- determine items which refer to the chosen state
    doneEndLab <- some $ M.lookup state doneEnd
    -- determine items begining on the given position
    doneEndLabBeg <- some $ M.lookup i doneEndLab
    -- return what's left
    each $ M.keys doneEndLabBeg


--------------------------------------------------
-- New Automaton-Based Primitives
--------------------------------------------------


-- | Follow the given terminal in the underlying automaton.
followTerm :: (Ord n, Ord t) => ID -> t -> MaybeT (Earley n t) ID
followTerm i c = do
    -- get the underlying automaton
    auto <- RWS.gets automat
    -- follow the label
    maybeT $ D.follow i (A.Body $ Term c) auto


-- | Follow the given body transition in the underlying automaton.
-- It represents the transition function of the automaton.
follow :: (Ord n, Ord t) => ID -> Lab n t -> P.ListT (Earley n t) ID
follow i x = do
    -- get the underlying automaton
    auto <- RWS.gets automat
    -- follow the label
    some $ D.follow i (A.Body x) auto


-- | Rule heads outgoing from the given automaton state.
heads :: ID -> P.ListT (Earley n t) (Lab n t)
heads i = do
    auto <- RWS.gets automat
    let mayHead (x, _) = case x of
            A.Body _  -> Nothing
            A.Head y -> Just y
    each $ mapMaybe mayHead $ D.edges i auto


-- | Rule body elements outgoing from the given automaton state.
elems :: ID -> P.ListT (Earley n t) (Lab n t)
elems i = do
    auto <- RWS.gets automat
    let mayBody (x, _) = case x of
            A.Body y  -> Just y
            A.Head _ -> Nothing
    each $ mapMaybe mayBody $ D.edges i auto


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- | Try to perform SCAN on the given state.
tryScan :: (VOrd t, VOrd n) => Item n t -> Earley n t ()
tryScan p = void $ runMaybeT $ do
    -- read the word immediately following the ending position of
    -- the state
    c <- readInput $ end p
    -- follow appropriate terminal transition outgoin from the
    -- given automaton state
    j <- followTerm (state p) c
    -- construct the resultant state
    let q = p {state = j, end = end p + 1}
    -- print logging information
--     lift . lift $ do
--         putStr "[S]  " >> printItem p
--         putStr "  :  " >> printItem q
    -- push the resulting state into the waiting queue
    lift $ pushItem q $ Scan p c


--------------------------------------------------
-- SUBST
--------------------------------------------------


-- | Try to use the state (only if fully parsed) to complement
-- (=> substitution) other rules.
trySubst :: (VOrd t, VOrd n) => Item n t -> Earley n t ()
trySubst p = void $ P.runListT $ do
    -- make sure that `p' represents regular rules
    guard $ regular p
    -- take all the head symbols outgoing from `p`
    x <- heads (state p)
    -- find items which end where `p' begins and which
    -- expect the non-terminal provided by `p' (ID included)
    q <- expectEnd x (beg p)
    -- follow the transition symbol
    j <- follow (state q) x
    -- construct the resultant state
    let q' = q {state = j, end = end p}
    -- print logging information
--     lift . lift $ do
--         putStr "[U]  " >> printItem p
--         putStr "  +  " >> printItem q
--         putStr "  :  " >> printItem q'
    -- push the resulting state into the waiting queue
    lift . pushItem q' $ Subst p q (nonTerm x)


--------------------------------------------------
-- FOOT ADJOIN
--------------------------------------------------


-- | `tryAdjoinInit p q':
-- * `p' is a completed state (regular or auxiliary)
-- * `q' not completed and expects a *real* foot
tryAdjoinInit :: (VOrd n, VOrd t) => Item n t -> Earley n t ()
tryAdjoinInit p = void $ P.runListT $ do
    -- take all head symbols outgoing from `p`
    x <- heads (state p)
    -- make sure that the corresponding rule is either regular or
    -- intermediate auxiliary ((<=) used as implication here)
    guard $ auxiliary p <= not (topLevel x)
    -- find all rules which expect a foot with the given symbol
    -- and which end where `p` begins
    let foot = AuxFoot $ nonTerm x
    q <- expectEnd foot (beg p)
    -- follow the foot
    j <- follow (state q) foot
    -- construct the resultant state
    let q' = q { state = j
               , gap = Just (beg p, end p)
               , end = end p }
    -- print logging information
--     lift . lift $ do
--         putStr "[A]  " >> printItem p
--         putStr "  +  " >> printItem q
--         putStr "  :  " >> printItem q'
    -- push the resulting state into the waiting queue
    lift $ pushItem q' $ Foot q $ nonTerm foot


--------------------------------------------------
-- INTERNAL ADJOIN
--------------------------------------------------


-- | `tryAdjoinCont p q':
-- * `p' is a completed, auxiliary state
-- * `q' not completed and expects a *dummy* foot
--
-- TODO: seems it can be merged quite easily with `trySubst`!
-- Just make the `topLevel x` check and the way resulting state
-- is constructed on the basis of the type of `p`.
tryAdjoinCont :: (VOrd n, VOrd t) => Item  n t -> Earley n t ()
tryAdjoinCont p = void $ P.runListT $ do
    -- make sure that `p' is an auxiliary item
    guard $ auxiliary p
    -- take all head symbols outgoing from `p` and make sure they
    -- are not top-level (internal spine non-terminals)
    x <- heads (state p)
    guard $ not $ topLevel x
    -- find all rules which expect a spine non-terminal provided
    -- by `p' and which end where `p' begins
    q <- expectEnd x (beg p)
    -- follow the spine non-terminal
    j <- follow (state q) x
    -- construct the resulting state; the span of the gap of the
    -- inner state `p' is copied to the outer state based on `q'
    let q' = q { state = j
               , gap = gap p
               , end = end p }
    -- logging info
--     lift . lift $ do
--         putStr "[B]  " >> printItem p
--         putStr "  +  " >> printItem q
--         putStr "  :  " >> printItem q'
    -- push the resulting state into the waiting queue
    lift $ pushItem q' $ Subst p q (nonTerm x)


--------------------------------------------------
-- ROOT ADJOIN
--------------------------------------------------


-- | Adjoin a fully-parsed auxiliary state `p` to a partially parsed
-- tree represented by a fully parsed rule/state `q`.
tryAdjoinTerm :: (VOrd t, VOrd n) => Item n t -> Earley n t ()
tryAdjoinTerm q = void $ P.runListT $ do
    -- make sure that it is an auxiliary item (by definition only
    -- auxiliary states have gaps)
    (gapBeg, gapEnd) <- each $ maybeToList $ gap q
    -- take all the head symbols outgoing from `q` and make sure
    -- that they are top-level
    x <- heads (state q)
    guard $ topLevel x
    -- take all completed rules with a given span
    -- and a given root non-terminal (IDs irrelevant)
    p <- rootSpan (nonTerm x) (gapBeg, gapEnd)
    -- construct the new state
    let p' = p { beg = beg q
               , end = end q }
--     lift . lift $ do
--         putStr "[C]  " >> printItem q
--         putStr "  +  " >> printItem p
--         putStr "  :  " >> printItem p'
    lift $ pushItem p' $ Adjoin q p


--------------------------------------------------
-- EARLEY
--------------------------------------------------


-- | Does the given grammar generate the given sentence?
-- Uses the `earley` algorithm under the hood.
recognize
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [t]                  -- ^ Input sentence
    -> IO Bool
recognize gram xs = do
    recognizeAuto (A.buildAuto gram) xs


-- | Does the given grammar generate the given sentence from the
-- given non-terminal symbol (i.e. from an initial tree with this
-- symbol in its root)?  Uses the `earley` algorithm under the
-- hood.
recognizeFrom
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> n                    -- ^ The start symbol
    -> [t]                  -- ^ Input sentence
    -> IO Bool
recognizeFrom gram start xs =
    recognizeFromAuto (A.buildAuto gram) start xs


-- | Parse the given sentence and return the set of parsed trees.
parse
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> n                    -- ^ The start symbol
    -> [t]                  -- ^ Input sentence
    -> IO (S.Set (T.Tree n t))
parse gram = parseAuto $ A.buildAuto gram


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earley
    :: (VOrd t, VOrd n)
    => S.Set (Rule n t)     -- ^ The grammar (set of rules)
    -> [t]                  -- ^ Input sentence
    -> IO (EarSt n t)
earley gram = earleyAuto (A.buildAuto gram)
--     let dawg = A.buildAuto gram
--     doneSet <- earleyAuto dawg xs
--     return (doneSet, dawg)


-- | Step of the algorithm loop.  `p' is the state popped up from
-- the queue.
step
    :: (VOrd t, VOrd n)
    => Binding (Item n t) (ExtPrio n t)
    -> Earley n t ()
step (p :-> e) = do
    mapM_ ($p)
      [ tryScan, trySubst
      , tryAdjoinInit
      , tryAdjoinCont
      , tryAdjoinTerm ]
    saveItem p $ prioTrav e


--------------------------------------------------
-- Alternative
--------------------------------------------------


-- | Alternative to `recognize`.
recognizeAuto
    :: (VOrd t, VOrd n)
    => A.DAWG n t           -- ^ Grammar automaton
    -> [t]                  -- ^ Input sentence
    -> IO Bool
recognizeAuto auto xs =
    flip isRecognized xs <$> earleyAuto auto xs
--     doneSet <- done <$> earleyAuto auto xs
--     return $ (not.null) (complete doneSet)
--   where
--     n = length xs
--     complete doneSet =
--         [ True | p <- listDone doneSet
--         , beg p == 0, end p == n
--         , gap p == Nothing ]


-- | Alternative to `recognizeFrom`.
recognizeFromAuto
    :: (VOrd t, VOrd n)
    => A.DAWG n t           -- ^ Grammar automaton
    -> n                    -- ^ The start symbol
    -> [t]                  -- ^ Input sentence
    -> IO Bool
recognizeFromAuto auto start xs = do
    earSt <- earleyAuto auto xs
    return $ (not.null) (final earSt start $ length xs)


-- | Parse the given sentence and return the set of parsed trees.
parseAuto
    :: (VOrd t, VOrd n)
    => A.DAWG n t           -- ^ Grammar automaton
    -> n                    -- ^ The start symbol
    -> [t]                  -- ^ Input sentence
    -> IO (S.Set (T.Tree n t))
parseAuto auto start xs = do
    earSt <- earleyAuto auto xs
    return $ parsedTrees earSt start (length xs)


-- | Perform the earley-style computation given the grammar and
-- the input sentence.
earleyAuto
    :: (VOrd t, VOrd n)
    => A.DAWG n t           -- ^ Grammar automaton
    -> [t]                  -- ^ Input sentence
    -> IO (EarSt n t)
earleyAuto dawg xs =
    fst <$> RWS.execRWST loop xs st0
  where
    -- we put in the initial state all the states with the dot on
    -- the left of the body of the rule (-> left = []) on all
    -- positions of the input sentence.
    st0 = mkEarSt dawg $ S.fromList
        [ Item
            { state = D.root dawg
            , beg   = i
            , end   = i
            , gap   = Nothing }
        | i <- [0 .. length xs - 1] ]
    -- the computation is performed as long as the waiting queue
    -- is non-empty.
    loop = popItem >>= \mp -> case mp of
        Nothing -> return ()
        Just p -> do
            step p >> loop


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | Return the list of final (passive) chart items.
final
    :: (Ord n, Ord t)
    => EarSt n t    -- ^ Final state of the earley parser
    -> n            -- ^ The start symbol
    -> Int          -- ^ The length of the input sentence
    -> [Item n t]
final EarSt{..} start n =
    [ p
    | p <- listDone done
    , beg p == 0, end p == n
    , isJust $ D.follow
        (state p)
        (A.Head $ NonT start Nothing)
        automat ]


-- | Check whether the given sentence is recognized
-- based on the resulting state of the earley parser.
isRecognized
    :: (VOrd t, VOrd n)
    => EarSt n t            -- ^ Earley parsing result
    -> [t]                  -- ^ Input sentence
    -> Bool
isRecognized EarSt{..} xs =
    not (null complete)
  where
    n = length xs
    complete =
        [ True | p <- listDone done
        , beg p == 0, end p == n
        , gap p == Nothing ]


-- | MaybeT transformer.
maybeT :: Monad m => Maybe a -> MaybeT m a
maybeT = MaybeT . return


-- | ListT from a list.
each :: Monad m => [a] -> P.ListT m a
each = P.Select . P.each


-- | ListT from a maybe.
some :: Monad m => Maybe a -> P.ListT m a
some = each . maybeToList
