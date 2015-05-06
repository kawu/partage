{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}


{- 
 - Early parser for TAGs.  Second tentative preliminary version.
 -}


module NLP.LTAG.Early2 where


import           Control.Applicative ((<$>), (<|>))
import           Control.Monad (guard)
import           Data.Maybe (mapMaybe)
import qualified Data.Set as S
import qualified Data.IntSet as IS
import qualified Data.IntMap as I

import qualified Data.Foldable as F
import qualified Data.Sequence as E
import           Data.Sequence ((<|), (|>), (><), ViewL(..),
                    ViewR(..))

-- For parsing
import qualified Text.ParserCombinators.Poly.Plain as P

import qualified NLP.LTAG.Tree as G

-- import           Debug.Trace (trace)


--------------------------------------------------
-- TRAVERSAL ELEMENT
--------------------------------------------------


-- | A traversal element.
data Elem a b
  = Leaf a
  | Open a
  | Close a -- TODO: we can probably get rid of the label here
  | Term b
  | Foot
  deriving (Show, Eq, Ord)


-- | Extract terminal label.
mayTerm :: Elem a b -> Maybe b
mayTerm t = case t of
    Term v -> Just v
    _ -> Nothing


-- | Extract opening non-terminal label.
mayLeaf :: Elem a b -> Maybe a
mayLeaf t = case t of
    Leaf x -> Just x
    _ -> Nothing


-- | Extract opening non-terminal label.
mayOpen :: Elem a b -> Maybe a
mayOpen t = case t of
    Open x -> Just x
    _ -> Nothing


-- | Is it a non-terminal opening tag?
isOpen :: Elem a b -> Bool
isOpen t = case t of
    Open _ -> True
    _ -> False

-- | Is it a non-terminal closing tag?
isClose :: Elem a b -> Bool
isClose t = case t of
    Close _ -> True
    _ -> False


-- | Is it an opening or closing tag-non-terminal?
isTag :: Elem a b -> Bool
isTag t = case t of
    Open _ -> True
    Close _ -> True
    _ -> False


-- | Is it a foot?
isFoot :: Elem a b -> Bool
isFoot t = case t of
    Foot -> True
    _ -> False


--------------------------------------------------
-- TRAVERSAL
--------------------------------------------------


-- | A traversal of a tree.
type Trav a b = E.Seq (Elem a b)


-- | Get traversal of the given tree.
treeTrav :: G.Tree a b -> Trav a b
treeTrav G.INode{..} = case subTrees of
    [] -> E.singleton (Leaf labelI)
    _  ->
        let xs = concatSeq $ map treeTrav subTrees
        in  Open labelI <| (xs |> Close labelI)
treeTrav G.FNode{..} = E.singleton $ Term labelF


-- | Get traversal of the given auxiliary tree.
auxTrav :: G.AuxTree a b -> Trav a b
auxTrav G.AuxTree{..} =
    doit auxTree auxFoot
  where
    doit (G.INode labelI []) [] =
        E.fromList [Open labelI, Foot, Close labelI]
    doit G.INode{..} (k:ks) =
        let onChild i subTree = if k == i
                then doit subTree ks
                else treeTrav subTree
            xs = concatSeq $ map (uncurry onChild) $ zip [0..] subTrees
        in  Open labelI <| (xs |> Close labelI)
    doit G.FNode{..} _ = E.singleton $ Term labelF
    doit _ _ = error "auxTrav: incorrect path"


-- | Make a tree from the traversal.  The foot-node is
-- ignored for the moment.
toTree :: Trav a b -> G.Tree a b
toTree = doParse readTree . F.toList

  where

    readTree = readNode <|> readTerm <|> readLeaf
    readNode = do
        x  <- readOpen
        ts <- readForest
        readClose
        return $ G.INode x ts
    readOpen = mayNext mayOpen
    readClose = P.satisfy isClose
    readForest = P.many1 readTree
    readTerm = do
        t <- mayNext mayTerm
        return $ G.FNode t
    readLeaf = do
        x <- mayNext mayLeaf
        return $ G.INode x []

    doParse p xs = case fst (P.runParser p xs) of
        Left err -> error $ "toTree error: " ++ err
        Right x  -> x

    mayNext may = do
        let pred t = case may t of
                Just _ -> True
                _ -> False
        t <- P.satisfy pred
        return $ case may t of
            Nothing -> error "toTree: impossible!" 
            Just x -> x


-- | Consume all subtrees and replace the closing non-terminal
-- with the given sequence.
replaceClose
    :: Trav a b -- ^ The sequence to be placed
    -> Trav a b -- ^ The sequence to be searched
    -> Trav a b
replaceClose new =
    go (0 :: Int)
  where
    go k sq = case E.viewl sq of
        x :< xs -> case x of
            Open _  -> x <| go (k + 1) xs
            Close _ -> if k > 0
                then x <| go (k - 1) xs
                else new >< xs
            _ -> x <| go k xs
        EmptyL -> error "replaceClose: empty traversal"


-- | Does the tree (represented as a traversal) has a specific
-- label in the root?
hasInRoot :: Eq a => Trav a b -> a -> Bool
hasInRoot sq x = case E.viewr sq of
    EmptyR -> False
    _ :> t -> case t of
        Open y -> x == y 
        _ -> False


--------------------------------------------------
-- GRAMMAR
--------------------------------------------------


-- | A grammar is just a set of traversal representations of
-- initial and auxiliary trees.
type Grammar a b = S.Set (Trav a b)


--------------------------------------------------
-- CHART STATE
--------------------------------------------------


-- | Parsing state: processed traversal elements and the elements
-- yet to process.
data State a b = Single {
    -- | The list of elements to process on the left.
      left  :: Trav a b
    -- | The list of processed elements.
    , done  :: Trav a b
    -- | The list of elements to process on the right.
    , right :: Trav a b }
    | DualL {
    -- | The list of processed elements on the left.
    -- By definition, all the elements on the left are processed.
      left  :: Trav a b
    -- | The list of processed elements on the right.
    , done  :: Trav a b
    -- | The list of elements to process on the right.
    , right :: Trav a b }
    | DualR {
    -- | The list of elements to process on the left.
      left  :: Trav a b
    -- | The list of processed elements on the left.
    , done  :: Trav a b
    -- | The list of processed elements on the right.
    -- By definition, all the elements on the left are processed.
    , right :: Trav a b
    } deriving (Show, Eq, Ord)


-- | Create a single state from an initial tree traversal given
-- its anchor.  A provisional function, should not be ultimately
-- used.  Raise error if traversal is not an initial tree.
mkSingle :: Eq b => b -> Trav a b -> State a b
mkSingle v sq =
    go E.empty sq
  where
    go acc sq = case E.viewl sq of
        x :< xs -> case x of
            Term w -> if v == w
                then Single
                    { left = acc
                    , done = E.singleton $ Term w
                    , right = xs }
                else go (acc |> x) xs
            _ -> go (acc |> x) xs
        EmptyL  -> error "mkSingle: not an initial tree"


--------------------------------------------------
-- CHART EXTENDING OPERATIONS
--
-- Note, that there is no "scan" operation yet.
-- We should account somehow for MWEs, however.
--------------------------------------------------


-- | Ignore the internal non-terminal -- no adjunction will take
-- place.
ignore :: State a b -> Maybe (State a b)

ignore Single{..} = do
    (ls, l) <- mayViewR left
    (r, rs) <- mayViewL right
    guard $ isOpen l
    guard $ isClose r
    return $ Single
        { left = ls
        , done = l <| (done |> r)
        , right = rs }

ignore dual@DualL{..} = do
    (r, rs) <- mayViewL right
    guard $ isTag r
    return $ dual
        { done = done |> r
        , right = rs }

ignore dual@DualR{..} = do
    (ls, l) <- mayViewR left
    guard $ isTag l
    return $ dual
        { done = l <| done
        , left = ls }




-- -- | Complete a leaf non-terminal with a parsed tree.
-- subst
--     :: Eq a
--     => State a b            -- ^ The parsed tree
--     -> State a b            -- ^ A state to complement
--     -> Maybe (State a b)
-- subst fin tre = do
--     -- Are you sure it's parsed?
--     guard $ null $ right fin
--     (treHead, treRest) <- decoList $ right tre
--     x <- mayLeaf treHead
--     guard $ noOverlap (ids fin) (ids tre)
--     guard $ left fin `hasInRoot` x  -- TODO: inefficient!
--     return $ State
--         { left = left fin ++ left tre
--         , ids = IS.union (ids fin) (ids tre)
--         , right = treRest }
-- 
-- 
-- -- | Try to complete an internal non-terminal with a partially
-- -- parsed auxiliary tree.  Check if the tree is partially parsed
-- -- indeed and remove the foot node.
-- adjoin
--     :: Eq a
--     => State a b    -- ^ Partially parsed auxiliary tree
--     -> State a b    -- ^ Tree to complement (adjoin)
--     -> Maybe (State a b)
-- adjoin aux tre = do
--     -- Check if the first element of the axuliary traversal
--     -- is a foot-node and skip it.
--     (auxHead, auxRest) <- decoList $ right aux
--     guard $ isFoot auxHead
--     -- Take the root label of the auxiliary tree (x) and the
--     -- internal label (y) of the tree to complement and check if
--     -- they match.
--     x <- mayOpen . fst =<< decoList (left aux)
--     (treHead, treRest) <- decoList $ right tre
--     y <- mayOpen treHead
--     guard $ x == y
--     -- Do not compose trees which have overlaping set of indices.
--     guard $ noOverlap (ids aux) (ids tre)
--     -- Construct the final result.
--     return $ State
--         { left = left aux ++ left tre
--         , ids = IS.union (ids aux) (ids tre)
--         , right = replaceClose auxRest treRest }
-- 
-- 
-- --------------------------------------------------
-- -- ENTRY
-- --
-- -- As well as entry elements
-- --------------------------------------------------
-- 
-- 
-- -- | A chart entry is a set of states together with information
-- -- about where their corresponding spans begin.
-- type Entry a b = S.Set (State a b, Int)
-- 
-- 
-- -- | A new state based on the traversal.
-- mkStatePos :: Int -> (ID, Trav a b) -> (State a b, Int)
-- mkStatePos k (i, t) = (,k) $ State
--     { left=[]
--     , ids=IS.singleton i
--     , right=t }
-- 
-- 
-- -- | Is it a final state/pos pair?
-- final :: (State a b, Int) -> Bool
-- final (State{..}, i) = null right && i == 0
-- 
-- 
-- -- | The parsed part of the state.
-- parsed :: (State a b, c) -> Trav a b
-- parsed (State{..}, _) = left
-- 
-- 
-- -- | Show the parsed part of the given state.
-- showParsed :: (Show a, Show b) => (State a b, c) -> String
-- showParsed = G.showTree' . toTree . reverse . parsed
-- 
-- 
-- -- | Show and print.
-- printParsed :: (Show a, Show b) => (State a b, c) -> IO ()
-- printParsed = putStr . showParsed
-- 
-- 
-- --------------------------------------------------
-- -- CHART
-- --------------------------------------------------
-- 
-- 
-- -- | A chart is a map from indiced to chart entries.
-- type Chart a b = I.IntMap (Entry a b)
-- 
-- 
-- -- | X-th position of the chart.
-- (!?) :: Chart a b -> Int -> Entry a b
-- chart !? k = case I.lookup k chart of
--     Just e  -> e
--     Nothing -> error $ "!?: no such index in the chart"
-- 
-- 
-- -- | Retrieve the last entry of the chart.  Error if chart is
-- -- empty.
-- lastEntry :: Chart a b -> Entry a b
-- lastEntry ch = if I.null ch
--     then error "lastEntry: null chart"
--     else snd $ I.findMax ch
-- 
-- 
-- -- | Show the final results of the early parsing.
-- chartFinal :: Chart a b -> [(State a b, Int)]
-- chartFinal = filter final . S.toList . lastEntry
-- 
-- 
-- -- | Scan input w.r.t. all the states of the specific entry of
-- -- the chart.  Once the Chart[i] is ready, we can run `scanAll`
-- -- on this chart just once to get the next chart entry, i.e.
-- -- Chart[i+1].  One has to remember to also add to Chart[i+1] all
-- -- the preliminary states (since we don't do prediction yet) at
-- -- some point.
-- scanAll
--     :: (Ord a, Ord b)
--     => b            -- ^ The next symbol on the input
--     -> Entry a b    -- ^ Previous chart entry (Chart[i])
--     -> Entry a b    -- ^ The scanned part of the entry Chart[i+1]
-- scanAll x curr =
--     let doit (st, k) = (,k) <$> scan x st
--     in  S.fromList $ mapMaybe doit (S.toList curr)
-- 
-- 
-- -- | We update the current entry by `ignore'ing the non-terminal
-- -- internal nodes where possible.  Note, that after performing
-- -- `ignoreAll' there may be new states in the entry which can be,
-- -- again, possibly ignored.
-- ignoreAll
--     :: (Ord a, Ord b)
--     => Entry a b        -- ^ The current chart entry
--     -> Entry a b
-- ignoreAll curr = S.union curr $
--     let doit (st, k) = (,k) <$> ignore st
--     in  S.fromList $ mapMaybe doit $ S.toList curr
-- 
-- 
-- -- | We try to complete states from previous chart entries given
-- -- the final (fully parsed) states from the current entry.  While
-- -- doing this we can obtain new final states and thus `substAll`
-- -- may be needed to run again.
-- substAll
--     :: (Ord a, Ord b)
--     => Entry a b        -- ^ The current chart entry Chart[i]
--     -> Chart a b        -- ^ The chart with previous entries
--     -> Entry a b
-- substAll curr chart
--     = S.union curr $ S.fromList
--     $ concatMap doit $ S.toList curr
--   where
--     doit (st, i) =
--         -- We do substitution only with respect to completed
--         -- parse trees.
--         if null (right st) then
--             -- Substitution on some previous state from Chart[i]
--             -- which starts on position j does not change its
--             -- position.
--             let substOn (xs, j) = (,j) <$> subst st xs
--             -- Below we know, that <i> refers to some previous
--             -- entry and not the current state because each tree
--             -- spans over at least one non-terminal. 
--             in  mapMaybe substOn $ S.toList $ chart !? i
--         -- Otherwise: no new states.
--         else []
-- 
-- 
-- -- | We try to complete states from previous chart entries given
-- -- the partially parsed auxiliary trees from the current entry.
-- adjoinAll
--     :: (Ord a, Ord b)
--     => Entry a b        -- ^ The current chart entry Chart[i]
--     -> Chart a b        -- ^ The chart with previous entries
--     -> Entry a b
-- adjoinAll curr chart
--     = S.union curr $ S.fromList $ concatMap doit
--     $ mapMaybe getRelevantAux $ S.toList curr
--   where
--     -- Check if the tree is relevant -- partially parsed (up to
--     -- the foot node) auxiliary tree.
--     getRelevantAux st@(State{..}, _) = do
--         (r, _) <- decoList right
--         guard $ isFoot r
--         return st
--     doit (aux, i) =
--         -- Adjoin on some previous state from Chart[i] which
--         -- starts on position j does not change its position.
--         let adjoinOn (st, j) = (,j) <$> adjoin aux st
--             -- TODO: this is kind of dangerous!  We assume here
--             -- that <i> values are always correct and thus, if
--             -- they are not in the chart, they refer to the
--             -- current entry.
--             entry = case I.lookup i chart of
--                 Just e  -> e
--                 Nothing -> curr
--         in  mapMaybe adjoinOn $ S.toList $ entry
-- 
-- 
-- -- | Update (i.e. perform the ignore, subst and adjoin
-- -- operations) the current entry of the chart.
-- updateOnce
--     :: (Ord a, Ord b)
--     => Entry a b        -- ^ The current chart entry Chart[i]
--     -> Chart a b        -- ^ The chart with previous entries
--     -> Entry a b
-- updateOnce curr chart
--     = flip adjoinAll chart
--     $ flip substAll chart
--     $ ignoreAll curr
-- 
-- 
-- -- | `Update' as long as the size of the current state grows.
-- updateLoop
--     :: (Ord a, Ord b)
--     => Entry a b        -- ^ The current chart entry Chart[i]
--     -> Chart a b        -- ^ The chart with previous entries
--     -> Entry a b
-- updateLoop curr chart =
--     let n = S.size curr
--         next = updateOnce curr chart
--         m = S.size next
--     in  if m > n
--             then updateLoop next chart
--             else next
-- 
-- 
-- -- | Perform early parsing.
-- early
--     :: (Ord a, Ord b)
--     => Grammar a b      -- ^ Grammar
--     -> [b]              -- ^ Input
--     -> Chart a b
-- early gram sent = earlyStep gram sent 1 $ I.singleton 0 $
--     let new = S.fromList $ map (mkStatePos 0) $ I.toList gram
--     in  updateLoop new I.empty
--     
-- 
-- -- | Early parsing step.
-- earlyStep
--     :: (Ord a, Ord b)
--     => Grammar a b      -- ^ Grammar
--     -> [b]              -- ^ Input still to process
--     -> Int              -- ^ Current position
--     -> Chart a b        -- ^ Previous entries
--     -> Chart a b        -- ^ With new entry
-- earlyStep gram (x:xs) k chart =
--     earlyStep gram xs (k+1) $ I.insert k entry chart
--   where
--     entry = updateLoop (new `S.union` scanned) chart
--     new = S.fromList $ map (mkStatePos k) $ I.toList gram
--     scanned = scanAll x (chart !? (k-1))
-- earlyStep _ [] _ chart = chart


--------------------------------------------------
-- UTILITIES
--------------------------------------------------


-- | Deconstruct list.  Utility function.
decoList :: [a] -> Maybe (a, [a])
decoList [] = Nothing
decoList (y:ys) = Just (y, ys)


-- | Viewr with maybe result.
mayViewL :: E.Seq a -> Maybe (a, E.Seq a)
mayViewL sq = case E.viewl sq of
    EmptyL  -> Nothing
    x :< xs -> Just (x, xs)


-- | Viewr with maybe result.
mayViewR :: E.Seq a -> Maybe (E.Seq a, a)
mayViewR sq = case E.viewr sq of
    EmptyR  -> Nothing
    xs :> x -> Just (xs, x)


concatSeq :: [E.Seq a] -> E.Seq a
concatSeq (x:xs) = x >< concatSeq xs
concatSeq [] = E.empty


-- -- | Is there no overlap between to IntSets?
-- noOverlap :: IS.IntSet -> IS.IntSet -> Bool
-- noOverlap x y = IS.null $ IS.intersection x y
