{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}


{- 
 - Early parser for TAGs.  Preliminary version.
 -}


module NLP.LTAG.Early
( early
, treeTrav 

-- Tests
, jean
, dort
-- , souvent
, nePas
, gram
) where


import           Control.Applicative ((<$>))
import           Data.Maybe (mapMaybe)
import qualified Data.Set as S
-- import qualified Data.Map as M
import qualified Data.IntMap as I

import qualified NLP.LTAG.Tree as G
import           NLP.LTAG.Tree (AuxTree(AuxTree), Tree(FNode, INode))

-- import           Debug.Trace (trace)


-- An alternative view of a TAG tree is a list of terminal or
-- non-terminal labels obtained with a traversal in which each
-- non-teminal occurs twice in the output -- once when the
-- subtree is entered, once when the traversal of the subtree is
-- done.


-- | A traversal element.
-- TODO: IDEA -- remove RightNTs completely?  Do we need them for
-- anything?
data TrElem a b
  = LeafNT
      { labelNT :: a
      -- | Is it a foot non-terminal?  It has only sense within
      -- the scope of auxiliary trees.
      , isFoot  :: Bool }
  | LeftNT
      { labelNT :: a
      -- | Distance to the right counterpart of the non-terminal
      -- (only if left counterpart).
      , rightDist :: Int }
  | RightNT
      { labelNT :: a }
  | Term
      { labelT  :: b }
  deriving (Show, Eq, Ord)


-- | A traversal of a tree.
type Trav a b = [TrElem a b]


-- | Get traversal of the given tree.
treeTrav :: G.Tree a b -> Trav a b
treeTrav G.INode{..} = case subTrees of
    [] -> [LeafNT labelI False]
    _  -> 
        let xs = concatMap treeTrav subTrees
        in  LeftNT labelI (length xs) : xs ++ [RightNT labelI]
treeTrav G.FNode{..} = [Term labelF]


-- | Get traversal of the given auxiliary tree.
auxTrav :: G.AuxTree a b -> Trav a b
auxTrav G.AuxTree{..} =
    doit auxTree auxFoot
  where
    doit (G.INode labelI []) [] = [LeafNT labelI True]
    doit G.INode{..} (k:ks) =
        let onChild i subTree = if k == i
                then doit subTree ks
                else treeTrav subTree
            xs = concatMap (uncurry onChild) $ zip [0..] subTrees
        in  LeftNT labelI (length xs) : xs ++ [RightNT labelI]
    doit G.FNode{..} _ = [Term labelF]
    doit _ _ = error "auxTrav: incorrect path"



-- -- | Get traversal of the given auxiliary tree.
-- auxTrav :: G.AuxTree a b -> Trav a b
-- auxTrav G.AuxTree{..} =
--     let trav = treeTrav auxTree
--     in  markFoot auxFoot trav


-- -- | Mark the foot in the traversal tree given the path of the foot
-- -- node in the original tree.
-- markFoot :: G.Path -> Trav a b -> Trav a b
-- markFoot (0:ks) (x:xs) = case x of
--     LeftNT _ _ -> markFoot 
-- markFoot [] (x:xs) = case x of
--     LeafNT v _ -> LeafNT v True : xs
--     _ -> error "markFoot: expected non-terminal leaf node"
-- markFoot _ [] = error "markFoot: empty traversal"


-- | A grammar is just a set of traversal representations of
-- initial and auxiliary trees.
type Grammar a b = S.Set (Trav a b)


-- | Does the tree (represented as a traversal) has a specific
-- label in the root?
--
-- TODO: stupid, we have to use reverse here...
hasInRoot :: Eq a => Trav a b -> a -> Bool
hasInRoot ts = hasInRoot' $ reverse ts
hasInRoot' (t:_) x = case t of
    LeftNT y _ -> x == y 
    _ -> False
hasInRoot' _ _ = False


-- | Parsing state: processed traversal elements and the elements
-- yet to process.  The first list is in the inverse order.
type State a b = (Trav a b, Trav a b)


-- | The scan operation: read a symbol from the input if it is
-- consistent with the non-terminal in the state.
scan
    :: Eq b
    => b                    -- ^ Terminal to scan
    -> State a b            -- ^ Within the context of the state
    -> Maybe (State a b)    -- ^ Output state
scan x (ls, r:rs) = case r of
    Term y  -> if x == y
        then Just (r:ls, rs)
        else Nothing
    _   -> Nothing
scan _ (_, []) = Nothing


-- | Ignore the internal non-terminal -- it will be not
-- adjoined.
ignore
    :: State a b
    -> Maybe (State a b)
ignore (ls, r:rs) = case r of
    -- TODO: (r:ls) or just (ls)?  What are we going to do with
    -- the left side next anyway?  If we want to have a traversal
    -- of a parsed tree on the left in the result, by removing
    -- the k-th element from `rs' we are losing the
    -- correspondence between left and right counterparts.
    -- But maybe this is not a severe problem?
    LeftNT _ k -> Just (r:ls, removeKth k rs)
    _ -> Nothing
ignore _ = Nothing


-- | Complete a leaf non-terminal with a parsed tree.
subst
    :: Eq a
    => Trav a b     -- ^ The parsed tree
    -> State a b    -- ^ A state to complement
    -> Maybe (State a b)
subst t (ls, r:rs) = case r of
    LeafNT x False  -> if t `hasInRoot` x
        then Just (t ++ ls, rs)
        else Nothing
    _ -> Nothing
subst _ _ = Nothing


-- -- | Try to complete a leaf non-terminal with a parsed tree.
-- -- That is, check if the tree is really parsed first.
-- trySubst
--     :: Eq a
--     => State a b    -- ^ The parsed tree
--     -> State a b    -- ^ A state to complement
--     -> Maybe (State a b)
-- trySubst (ls, []) = subst ls
-- trySubst _ = const Nothing


-- | Complete an internal non-terminal with a partially parsed
-- auxiliary tree (no foot node!).
--
-- TODO: we could easily take (see `tryAdjoin') a footnode label
-- as argument.
adjoin
    :: Eq a
    => Trav a b     -- ^ Parsed part of an auxiliary tree
    -> Trav a b     -- ^ Part of an auxiliary tree to be parsed
    -> State a b    -- ^ Tree to complement (adjoin)
    -> Maybe (State a b)
adjoin aux aux' (ls, r:rs) = case r of
    LeftNT x k -> if aux `hasInRoot` x
        then Just (aux ++ ls, replaceKth k aux' rs)
        else Nothing
    _ -> Nothing
adjoin _ _ _ = Nothing


-- | Try to complete an internal non-terminal with a partially
-- parsed auxiliary tree.  Check if the tree is partially parsed
-- indeed and remove the foot node.
tryAdjoin
    :: Eq a
    => State a b    -- ^ Partially parsed auxiliary tree
    -> State a b    -- ^ Tree to complement (adjoin)
    -> Maybe (State a b)
tryAdjoin (ls, r:rs) = case r of
    LeafNT _ True -> adjoin ls rs
    _ -> const Nothing
tryAdjoin _ = const Nothing


-- | Remove the k-th element of the list.
removeKth :: Int -> [a] -> [a]
removeKth k xs = take k xs ++ drop (k + 1) xs


-- | Replace the k-th element of the list.
replaceKth
    :: Int
    -> [a]  -- ^ What is placed on k-th position 
    -> [a]  -- ^ In which replace takes places
    -> [a]
replaceKth k x xs = take k xs ++ x ++ drop (k + 1) xs


-- | A chart entry is a set of states together with information
-- about where their corresponding spans begin.
type Entry a b = S.Set (State a b, Int)


-- | A new state based on the traversal.
mkStatePos :: Int -> Trav a b -> (State a b, Int)
mkStatePos k t = (([], t), k)


-- | A chart is a map from indiced to chart entries.
type Chart a b = I.IntMap (Entry a b)


-- | X-th position of the chart.
(!?) :: Chart a b -> Int -> Entry a b
chart !? k = case I.lookup k chart of
    Just e  -> e
    Nothing -> error $ "!?: no such index in the chart"


-- | Scan input w.r.t. all the states of the specific entry of
-- the chart.  Once the Chart[i] is ready, we can run `scanAll`
-- on this chart just once to get the next chart entry, i.e.
-- Chart[i+1].  One has to remember to also add to Chart[i+1] all
-- the preliminary states (since we don't do prediction yet) at
-- some point.
scanAll
    :: (Ord a, Ord b)
    => b            -- ^ The next symbol on the input
    -> Entry a b    -- ^ Previous chart entry (Chart[i])
    -> Entry a b    -- ^ The scanned part of the entry Chart[i+1]
scanAll x curr =
    let doit (st, k) = (,k) <$> scan x st
    in  S.fromList $ mapMaybe doit (S.toList curr)
--   where
--     doit (st, k) = do
--         -- First try to scan the input
--         st' <- scan x st
--         -- If success, we move the dot one position to the right.
--         return (st', k+1)


-- | We update the current entry by `ignore'ing the non-terminal
-- internal nodes where possible.  Note, that after performing
-- `ignoreAll' there may be new states in the entry which can be,
-- again, possibly ignored.
ignoreAll
    :: (Ord a, Ord b)
    => Entry a b        -- ^ The current chart entry
    -> Entry a b
ignoreAll curr = S.union curr $
    let doit (st, k) = (,k) <$> ignore st
    in  S.fromList $ mapMaybe doit $ S.toList curr


-- | We try to complete states from previous chart entries given
-- the final (fully parsed) states from the current entry.  While
-- doing this we can obtain new final states and thus `substAll`
-- may be needed to run again.
substAll
    :: (Ord a, Ord b)
    => Entry a b        -- ^ The current chart entry Chart[i]
    -> Chart a b        -- ^ The chart with previous entries
    -> Entry a b
substAll curr chart
    = S.union curr $ S.fromList
    $ concatMap doit $ S.toList curr
  where
    doit (st, i) = case st of
        -- We do substitution only with respect to completed
        -- parse trees.
        (ls, []) ->
            -- Substitution on some previous state from Chart[i]
            -- which starts on position j does not change its
            -- position.
            let substOn (xs, j) = (,j) <$> subst ls xs
            in  mapMaybe substOn $ S.toList $ chart !? i
        -- Otherwise: no new states.
        _        -> []


-- | We try to complete states from previous chart entries given
-- the partially parsed auxiliary tree from the current entry.
adjoinAll
    :: (Ord a, Ord b)
    => Entry a b        -- ^ The current chart entry Chart[i]
    -> Chart a b        -- ^ The chart with previous entries
    -> Entry a b
adjoinAll curr chart
    = S.union curr $ S.fromList $ concatMap doit
    $ mapMaybe getRelevantAux $ S.toList curr
  where
    -- Check if the tree is relevant -- partially parsed (up to
    -- the foot node) auxiliary tree.
    getRelevantAux st@((_, r:_), _) = case r of
        LeafNT _ True -> Just st
        _ -> Nothing
    getRelevantAux _ = Nothing
    doit (aux, i) =
        -- Adjoin on some previous state from Chart[i] which
        -- starts on position j does not change its position.
        let adjoinOn (st, j) = (,j) <$> tryAdjoin aux st
        in  mapMaybe adjoinOn $ S.toList $ chart !? i


-- | Update (i.e. perform the ignore, subst and adjoin
-- operations) the current entry of the chart.
updateOnce
    :: (Ord a, Ord b)
    => Entry a b        -- ^ The current chart entry Chart[i]
    -> Chart a b        -- ^ The chart with previous entries
    -> Entry a b
updateOnce curr chart
    = flip adjoinAll chart
    $ flip substAll chart
    $ ignoreAll curr


-- | `Update' as long as the size of the current state grows.
updateLoop
    :: (Ord a, Ord b)
    => Entry a b        -- ^ The current chart entry Chart[i]
    -> Chart a b        -- ^ The chart with previous entries
    -> Entry a b
updateLoop curr chart =
    let n = S.size curr
        next = updateOnce curr chart
        m = S.size next
    in  if m > n
            then updateLoop next chart
            else next


-- | Perform early parsing.
early
    :: (Ord a, Ord b)
    => Grammar a b      -- ^ Grammar
    -> [b]              -- ^ Input
    -> Chart a b
early gram sent = earlyStep gram sent 1 $ I.singleton 0 $
    let new = S.fromList $ map (mkStatePos 0) $ S.toList gram
    in  updateLoop new I.empty
    

-- | Early parsing step.
earlyStep
    :: (Ord a, Ord b)
    => Grammar a b      -- ^ Grammar
    -> [b]              -- ^ Input still to process
    -> Int              -- ^ Current position
    -> Chart a b        -- ^ Previous entries
    -> Chart a b        -- ^ With new entry
earlyStep gram (x:xs) k chart =
    earlyStep gram xs (k+1) $ I.insert k entry chart
  where
    entry = updateLoop (new `S.union` scanned) chart
    new = S.fromList $ map (mkStatePos k) $ S.toList gram
    scanned = scanAll x (chart !? (k-1))
earlyStep _ [] _ chart = chart


----------
-- TEST --
----------


jean :: Tree String String
jean = INode "N" [FNode "jean"]


dort :: Tree String String
dort = INode "S"
    [ INode "N" []
    , INode "V"
        [FNode "dort"] ]


-- souvent :: AuxTree String String
-- souvent = AuxTree (INode "V"
--     [ INode "V" []
--     , FNode "souvent" ]
--     ) [0]


nePas :: AuxTree String String
nePas = AuxTree (INode "V"
    [ FNode "ne"
    , INode "V" []
    , FNode "pas" ]
    ) [1]


gram = S.fromList
    $ map treeTrav [jean, dort]
   ++ map auxTrav [nePas]
