{-# LANGUAGE RecordWildCards #-}


{- 
 - Early parser for TAGs.  Preliminary version.
 -}


module NLP.LTAG.Early
(
)


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
  deriving (Eq, Ord)


-- | A traversal of a tree.
type Trav a b = [TrElem a b]


-- | Does the tree (represented as a traversal) has a specific
-- label in the root?
hasInRoot :: Trav a b -> a -> Bool
hasInRoot (t:ts) x = case t of
    LeftNT a _ -> True 
    _ -> False
hasInRoot _ _ = False


-- | Parsing state: processed traversal elements and the elements
-- yet to process.  The first list is in the inverse order.
type State a b = (Trav a b, Trav a b)


-- | The scan operation: read a symbol from the input if it is
-- consistent with the non-terminal in the state.
scan
    :: b                    -- ^ Terminal to scan
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
    LeftNT x k -> Just (r:ls, removeKth k rs)
    _ -> Nothing
ignore _ = Nothing


-- | Complete a leaf non-terminal with a parsed tree.
subst
    :: Trav a b     -- ^ The parsed tree
    -> State a b    -- ^ A state to complement
    -> Maybe (State a b)
subst t (ls, r:rs) = case r of
    LeafNT x False  -> if t `hasInRoot` x
        then Just (t ++ ls, rs)
        else Nothing
    _ -> Nothing
subst _ _ = Nothing


-- | Try to complete a leaf non-terminal with a parsed tree.
-- That is, check if the tree is really parsed first.
trySubst
    :: State a b    -- ^ The parsed tree
    -> State a b    -- ^ A state to complement
    -> Maybe (State a b)
trySubst (ls, []) = subst ls
trySubst _ = const Nothing


-- | Complete an internal non-terminal with a partially parsed
-- auxiliary tree (no foot node!).
--
-- TODO: we could easily take (see `tryAdjoin') a footnode label
-- as argument.
adjoin
    :: Trav a b     -- ^ Parsed part of an auxiliary tree
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
    :: State a b    -- ^ Partially parsed auxiliary tree
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


-- | An alternative view of a TAG tree -- a list of
-- terminal/non-terminal labels obtained with a traversal in
-- which each non-teminal occurs twice in the output -- once when
-- the subtree is entered, once when the traversal of the subtree
-- is done.
--
-- The two output non-terminals related to the same non-terminal
-- in the original tree are marked with L and R subscript
-- indices.  A TAG tree can be then seen as a regular CFG rule
-- with one (and important) exception that if the X_L
-- non-terminal of a rule is rewritten within an adjunction
-- operation, then the X_R non-terminal has to be rewritten as
-- well using the same operation.
--
-- Each auxiliary tree is thus represented as two CFG rules --
-- one which describes the rewriting on the left of the adjoined
-- node, the other one representing the rewriting on the right.
--
-- The idea is that when we rewrite a decoration string of a
-- given initial tree and if we rewrite a non-terminal X_L with a
-- specific left-hand-side rule related to a given auxiliary
-- tree, then we also have to rewrite the corresponding X_R
-- non-terminal with the right-hand-side rule corresponding to
-- the same auxiliary tree.
--
-- The tricky part is with the auxiliary trees themselves --
-- they can be modified (adjoined into) as well after all!
-- As a result, the simple idea described above doesn't really
-- work for auxiliary trees -- 
