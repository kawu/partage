{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}


{- 
 - Early parser for TAGs.  Preliminary version.
 -}


module NLP.LTAG.Early
( early
, treeTrav 
, auxTrav
, final
, parsed

-- Tests
, jean
, dort
, souvent
, nePas
, gram
) where


import           Control.Applicative ((<$>))
import           Control.Monad (guard)
import           Data.Maybe (mapMaybe)
import qualified Data.Set as S
import qualified Data.IntSet as IS
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


-- | Identifier of an elementary tree.
type ID = Int


-- | Deconstruct list.  Utility function.
decoList :: [a] -> Maybe (a, [a])
decoList [] = Nothing
decoList (y:ys) = Just (y, ys)


-- | Is there no overlap between to IntSets?
noOverlap :: IS.IntSet -> IS.IntSet -> Bool
noOverlap x y = IS.null $ IS.intersection x y


-- | A traversal element.
data TrElem a b
  = LeafNT { labelNT :: a }
  | OpenNT { labelNT :: a }
  | CloseNT
  | Term { labelT  :: b }
  | Foot
  deriving (Show, Eq, Ord)


-- | Extract terminal label.
mayTerm :: TrElem a b -> Maybe b
mayTerm t = case t of
    Term v -> Just v
    _ -> Nothing


-- | Extract opening non-terminal label.
mayLeaf :: TrElem a b -> Maybe a
mayLeaf t = case t of
    LeafNT x -> Just x
    _ -> Nothing


-- | Extract opening non-terminal label.
mayOpen :: TrElem a b -> Maybe a
mayOpen t = case t of
    OpenNT x -> Just x
    _ -> Nothing


-- | Is it an opening or closing tag-non-terminal?
isTag :: TrElem a b -> Bool
isTag t = case t of
    OpenNT _ -> True
    CloseNT -> True
    _ -> False


-- | Is it a foot?
isFoot :: TrElem a b -> Bool
isFoot t = case t of
    Foot -> True
    _ -> False


-- | A traversal of a tree.
type Trav a b = [TrElem a b]


-- | Get traversal of the given tree.
treeTrav :: G.Tree a b -> Trav a b
treeTrav G.INode{..} = case subTrees of
    [] -> [LeafNT labelI]
    _  -> 
        let xs = concatMap treeTrav subTrees
        in  OpenNT labelI : xs ++ [CloseNT]
treeTrav G.FNode{..} = [Term labelF]


-- | Get traversal of the given auxiliary tree.
auxTrav :: G.AuxTree a b -> Trav a b
auxTrav G.AuxTree{..} =
    doit auxTree auxFoot
  where
    doit (G.INode labelI []) [] = [OpenNT labelI, Foot, CloseNT]
    doit G.INode{..} (k:ks) =
        let onChild i subTree = if k == i
                then doit subTree ks
                else treeTrav subTree
            xs = concatMap (uncurry onChild) $ zip [0..] subTrees
        in  OpenNT labelI : xs ++ [CloseNT]
    doit G.FNode{..} _ = [Term labelF]
    doit _ _ = error "auxTrav: incorrect path"


-- | A grammar is just a set of traversal representations of
-- initial and auxiliary trees.  Additionally, to each elementary
-- tree an index is assigned so that it can be checked if the
-- given tree has been already used in a derivation of the given
-- state.
type Grammar a b = I.IntMap (Trav a b)


-- | Does the tree (represented as a traversal) has a specific
-- label in the root?
--
-- TODO: stupid, we have to use reverse here...
hasInRoot :: Eq a => Trav a b -> a -> Bool
hasInRoot ts =
    hasInRoot' $ reverse ts
  where
    hasInRoot' (t:_) x = case t of
        OpenNT y -> x == y 
        _ -> False
    hasInRoot' _ _ = False


-- | Parsing state: processed traversal elements and the elements
-- yet to process.
data State a b = State {
    -- | The list of processed elements of the tree.  
    -- Stored in the inverse order.
      left  :: Trav a b
    -- | The set of indices of the rules used in `left' + the
    -- indice of the elementary tree itself.  In other words, the
    -- set of indices of all the trees used in the derivation of
    -- this particular state.
    , ids   :: IS.IntSet
    -- | The list of elements yet to process.
    , right :: Trav a b
    } deriving (Show, Eq, Ord)


-- | The scan operation: read a symbol from the input if it is
-- consistent with the non-terminal in the state.
scan
    :: Eq b
    => b                    -- ^ Terminal to scan
    -> State a b            -- ^ Within the context of the state
    -> Maybe (State a b)    -- ^ Output state
scan x st@State{..} = do
    (r, rs) <- decoList right
    y <- mayTerm r
    guard $ x == y
    return $ st {left  = r : left, right = rs}
  where


-- THE OLD VERSION:
-- scan x (ls, r:rs) = case r of
--     Term y  -> if x == y
--         then Just (r:ls, rs)
--         else Nothing
--     _   -> Nothing
-- scan _ (_, []) = Nothing


-- | Ignore the internal non-terminal -- no adjunction will take
-- place.
ignore :: State a b -> Maybe (State a b)
ignore st@State{..} = do
    (r, rs) <- decoList right
    guard $ isTag r
    return $ st {left = r:left, right = rs}


-- THE OLD VERSION:
-- -- | Ignore the internal non-terminal -- no adjunction will take
-- -- place.
-- ignore
--     :: State a b
--     -> Maybe (State a b)
-- ignore (ls, r:rs) = case r of
--     OpenNT _ -> Just (r:ls, rs)
--     CloseNT -> Just (r:ls, rs)
--     _ -> Nothing
-- ignore _ = Nothing


-- | Complete a leaf non-terminal with a parsed tree.
subst
    :: Eq a
    => (Trav a b, IS.IntSet)    -- ^ The parsed tree
    -> State a b                -- ^ A state to complement
    -> Maybe (State a b)
subst (t, ids') State{..} = do
    (r, rs) <- decoList right
    x <- mayLeaf r
    guard $ noOverlap ids ids'
    guard $ t `hasInRoot` x
    return $ State
        { left = t ++ left
        , ids = IS.union ids ids'
        , right = rs }


-- THE OLD VERSION:
-- -- | Complete a leaf non-terminal with a parsed tree.
-- subst
--     :: Eq a
--     => Trav a b     -- ^ The parsed tree
--     -> State a b    -- ^ A state to complement
--     -> Maybe (State a b)
-- subst t (ls, r:rs) = case r of
--     LeafNT x -> if t `hasInRoot` x
--         then Just (t ++ ls, rs)
--         else Nothing
--     _ -> Nothing
-- subst _ _ = Nothing


-- | Complete an internal non-terminal with a partially parsed
-- auxiliary tree (no foot node!).
--
-- TODO: we could easily take (see `tryAdjoin') a footnode label
-- as argument.
adjoin
    :: Eq a
    => Trav a b     -- ^ Parsed part of an auxiliary tree
    -> IS.IntSet    -- ^ IDs of the auxiliary tree
    -> Trav a b     -- ^ Part of an auxiliary tree to be parsed
    -> State a b    -- ^ Tree to complement (adjoin to)
    -> Maybe (State a b)
adjoin aux ids' aux' State{..} = do
    (r, rs) <- decoList right
    x <- mayOpen r
    guard $ noOverlap ids ids'
    guard $ aux `hasInRoot` x
    return $ State
        { left = aux ++ left
        , ids = IS.union ids ids'
        , right = replaceClose aux' rs }


-- THE OLD VERSION:
-- -- | Complete an internal non-terminal with a partially parsed
-- -- auxiliary tree (no foot node!).
-- --
-- -- TODO: we could easily take (see `tryAdjoin') a footnode label
-- -- as argument.
-- adjoin
--     :: Eq a
--     => Trav a b     -- ^ Parsed part of an auxiliary tree
--     -> Trav a b     -- ^ Part of an auxiliary tree to be parsed
--     -> State a b    -- ^ Tree to complement (adjoin)
--     -> Maybe (State a b)
-- adjoin aux aux' (ls, r:rs) = case r of
--     OpenNT x -> if aux `hasInRoot` x
--         then Just (aux ++ ls, replaceClose aux' rs)
--         else Nothing
--     _ -> Nothing
-- adjoin _ _ _ = Nothing


-- | Try to complete an internal non-terminal with a partially
-- parsed auxiliary tree.  Check if the tree is partially parsed
-- indeed and remove the foot node.
tryAdjoin
    :: Eq a
    => State a b    -- ^ Partially parsed auxiliary tree
    -> State a b    -- ^ Tree to complement (adjoin)
    -> Maybe (State a b)
tryAdjoin State{..} t = do
    (r, rs) <- decoList right
    guard $ isFoot r
    -- `rs' and not `right' because `adjoin' requires that there
    -- is no foot-node on the right.
    adjoin left ids rs t

-- 
-- tryAdjoin (ls, r:rs) = case r of
--     Foot -> adjoin ls rs
--     _ -> const Nothing
-- tryAdjoin _ = const Nothing


-- -- -- | Remove the k-th element of the list.
-- -- removeKth :: Int -> [a] -> [a]
-- -- removeKth k xs = take k xs ++ drop (k + 1) xs
-- 
-- 
-- -- | Replace the k-th element of the list.
-- replaceKth
--     :: Int
--     -> [a]  -- ^ What is placed on k-th position 
--     -> [a]  -- ^ In which replace takes places
--     -> [a]
-- replaceKth k x xs = take k xs ++ x ++ drop (k + 1) xs
-- 
-- 
-- | Consume all subtrees and replace the closing non-terminal
-- with the given sequence.  
replaceClose
    :: Trav a b -- ^ The sequence to be placed
    -> Trav a b -- ^ The sequence to be searched
    -> Trav a b
replaceClose new =
    go (0 :: Int)
  where
    go k (x:xs) = case x of
        OpenNT _ -> x : go (k + 1) xs
        CloseNT  -> if k > 0
            then x : go (k - 1) xs
            else new ++ xs
        _ -> x : go k xs
    go _ [] = error "replaceClose: empty list"


-- | A chart entry is a set of states together with information
-- about where their corresponding spans begin.
type Entry a b = S.Set (State a b, Int)


-- | Is it a final state/pos pair?
final :: (State a b, Int) -> Bool
final (State{..}, i) = null right && i == 0
-- final ((_, []), 0) = True
-- final _ = False


-- | The parsed part of the state.
parsed :: (State a b, Int) -> Trav a b
parsed (State{..}, _) = left
-- parsed ((ls, _), _) = ls


-- | A new state based on the traversal.
mkStatePos :: Int -> (ID, Trav a b) -> (State a b, Int)
mkStatePos k (i, t) = (,k) $ State
    { left=[]
    , ids=IS.singleton i
    , right=t }
-- mkStatePos k t = (([], t), k)


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
    doit (State{..}, i) =
        -- We do substitution only with respect to completed
        -- parse trees.
        if null right then
            -- Substitution on some previous state from Chart[i]
            -- which starts on position j does not change its
            -- position.
            let substOn (xs, j) = (,j) <$> subst (left, ids) xs
            -- Below we know, that <i> refers to some previous
            -- entry and not the current state because each tree
            -- spans over at least one non-terminal. 
            in  mapMaybe substOn $ S.toList $ chart !? i
        -- Otherwise: no new states.
        else []


-- | We try to complete states from previous chart entries given
-- the partially parsed auxiliary trees from the current entry.
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
    getRelevantAux st@(State{..}, _) = do
        (r, _) <- decoList right
        guard $ isFoot r
        return st
    doit (aux, i) =
        -- Adjoin on some previous state from Chart[i] which
        -- starts on position j does not change its position.
        let adjoinOn (st, j) = (,j) <$> tryAdjoin aux st
            -- TODO: this doesn't work as expected!
            entry = case I.lookup i chart of
                Just e  -> e
                Nothing -> curr 
        in  mapMaybe adjoinOn $ S.toList $ entry


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
    let new = S.fromList $ map (mkStatePos 0) $ I.toList gram
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
    new = S.fromList $ map (mkStatePos k) $ I.toList gram
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
--     [ INode "Adv"
--         [FNode "souvent"]
--     , INode "V" [] ]
--     ) [1]


souvent :: AuxTree String String
souvent = AuxTree (INode "V"
    [ INode "V" []
    , INode "Adv"
        [FNode "souvent"] ]
    ) [0]


nePas :: AuxTree String String
nePas = AuxTree (INode "V"
    [ FNode "ne"
    , INode "V" []
    , FNode "pas" ]
    ) [1]


gram = I.fromList $ zip [0..]
    $ map treeTrav [jean, dort]
   ++ map auxTrav [souvent, nePas]
