{-# LANGUAGE RecordWildCards      #-}


-- | TAG conversion into flat production rules.
-- Due to subtree sharing provided by `flattenWithSharing`, a single
-- rule can be responsible for recognizing a subtree common to many
-- different elementary trees.
--


module NLP.Partage.FactGram.SubtreeSharing
(
-- * Grammar flattening
  flattenWithSharing
) where


import           Control.Applicative        ((<$>))
import           Control.Arrow              (second)
import           Control.Monad              (guard, forever)
import qualified Control.Monad.State.Strict as E
import           Control.Monad.Trans.Class  (lift)
import           Control.Monad.Identity     (Identity(..))
import           Control.Monad.Morph        (generalize)

import           Data.Function              (on)
import           Data.Monoid                (mappend, mconcat)
import           Data.Maybe                 (isJust)
import qualified Data.Set                   as S
import qualified Data.Partition             as Part
import qualified Pipes                      as P
import           Pipes                      (hoist, (>->))

import           NLP.Partage.FactGram.Internal
    ( FactGram, Lab(..), Rule(..), SymID )
import qualified NLP.Partage.FactGram.Internal as Rule
import qualified NLP.Partage.Tree as G


--------------------------------------------------
-- Compilation
--------------------------------------------------


-- | Compile the given grammar into the list of rules.
-- Common subtrees are shared.
flattenWithSharing
    :: (Functor m, Monad m, Ord n, Ord t)
    => [ Either
        (G.Tree n t)
        (G.AuxTree n t) ]
    -> m (FactGram n t)
flattenWithSharing ts =
    fmap snd $ runDupT $ Rule.runRM $ P.runEffect $
        P.for shared (const $ return ())
  where
    shared = hoist (hoist (hoist generalize))
        (   hoist (hoist lift) rules
        >-> hoist lift rmDups )
    rules = mapM_ getRules ts
    getRules (Left t)  = Rule.treeRules t
    getRules (Right t) = Rule.auxRules  t


--------------------------------------------------
-- Eq/Ord Instances for RuleP
--------------------------------------------------


-- | We define a newtype in order to define a custom Eq/Ord instances
-- take the symbol of the head into account in a different manner.
newtype RuleP n t = RuleP
    { unRuleP :: Rule n t
    } deriving (Show)


-- | Ordinary label equality.
labEq
    :: (Eq n, Eq t)
    => Lab n t -> Lab n t -> Bool
labEq p q = p == q


-- | Label equality.  Concerning the `SymID` values, it is only
-- checkes if either both are `Nothing` or both are `Just`.
labEq' :: (Eq n, Eq t) => Lab n t -> Lab n t -> Bool
labEq' p q =
    eq p q
  where
    eq x@NonT{} y@NonT{}
        =  eqOn nonTerm x y
        && eqOn (isJust . labID) x y
    eq x@AuxVert{} y@AuxVert{}
        =  eqOn nonTerm x y
    eq _ _ = p == q
    eqOn f x y = f x == f y


-- | Ordinary label comparison.
labCmp :: (Ord n, Ord t) => Lab n t -> Lab n t -> Ordering
labCmp p q = compare p q


-- | Label comparison.  Concerning the `SymID` values, it is only
-- checked if either both are `Nothing` or both are `Just`.
labCmp' :: (Ord n, Ord t) => Lab n t -> Lab n t -> Ordering
labCmp' p q =
    cmp p q
  where
    cmp x@NonT{} y@NonT{} =
        cmpOn nonTerm x y       `mappend`
        cmpOn (isJust . labID) x y
    cmp x@AuxVert{} y@AuxVert{} =
        cmpOn nonTerm x y
    cmp _ _ = compare p q
    cmpOn f x y = compare (f x) (f y)


instance (Eq n, Eq t) => Eq (RuleP n t) where
    r == s = (hdEq `on` headP) r s
        && ((==) `on` length.bodyP) r s
        && and [eq x y | (x, y) <- zip (bodyP r) (bodyP s)]
      where
        eq x y   = labEq  x y
        hdEq x y = labEq' x y
        headP    = headR . unRuleP
        bodyP    = bodyR . unRuleP


instance (Ord n, Ord t) => Ord (RuleP n t) where
    r `compare` s = (hdCmp `on` headP) r s    `mappend`
        (compare `on` length.bodyP) r s       `mappend`
        mconcat [cmp x y | (x, y) <- zip (bodyP r) (bodyP s)]
      where
        cmp x y   = labCmp  x y
        hdCmp x y = labCmp' x y
        headP     = headR . unRuleP
        bodyP     = bodyR . unRuleP


--------------------------------------------------
-- Substructure Sharing
--------------------------------------------------


-- | Duplication-removal state serves to share common
-- substructures.
--
-- The idea is to remove redundant rules equivalent to other
-- rules already present in the set of processed rules
-- `rulDepo`(sit).
--
-- Note that rules have to be processed in an appropriate order
-- so that lower-level rules are processed before the
-- higher-level rules from which they are referenced.
data DupS n t = DupS {
    -- | A disjoint set for `SymID`s
      symDisj   :: Part.Partition SymID
    -- | Rules already saved
    , rulDepo   :: S.Set (RuleP n t)
    }


-- Let us take a rule and let us assume that all identifiers it
-- contains references to rules which have already been processed
-- (for this assumption to be valid we just need to order the
-- input set of rules properly).  So we have a rule `r`, a set of
-- processed rules `rs` and a clustering (disjoint-set) over
-- `SymID`s present in `rs`.
--
-- Now we want to process `r` and, in particular, check if it is
-- not already in `rs` and update its `SymID`s.
--
-- First we translate the body w.r.t. the existing clustering of
-- `SymID`s (thanks to our assumption, these `SymID`s are already
-- known and processed).  The `SymID` in the root of the rule (if
-- present) is the new one and it should not yet have been mentioned
-- in `rs`.  Even when `SymID` is not present in the root, we can
-- still try to check if `r` is not present in `rs` -- after all,
-- there may be some duplicates in the input grammar.
--
-- Case 1: we have a rule with a `SymID` in the root.  We want to
-- check if there is already a rule in `rs` which:
-- * Has identical body (remember that we have already
--   transformed `SymID`s of the body of the rule in question)
-- * Has the same non-terminal in the root and some `SymID`
--
-- Case 2: the same as case 1 with the difference that we look
-- for the rules which have an empty `SymID` in the root.
--
-- For this to work we just need a specific comparison function
-- which works as specified in the two cases desribed above
-- (i.e. either there are some `SymID`s in the rule heads, or
-- there are no `SymID`s in both heads.)
--
-- Once we have this comparison (which is provided by the
-- function `labCmp'` above), we simply process the set of rules
-- incrementally.


-- | Duplication-removal transformer.
type DupT n t m = E.StateT (DupS n t) m


-- | Duplication-removal monad.
type DupM n t = DupT n t Identity


-- | Run the transformer.
runDupT
    :: (Functor m, Monad m, Ord t, Ord n)
    => DupT n t m b
    -> m (b, S.Set (Rule n t))
runDupT = fmap (second getRules) . flip E.runStateT
    (DupS Part.empty S.empty)
  where
    getRules
        = S.fromList . map unRuleP
        . S.toList. rulDepo


-- | Update the body of the rule by replacing old `SymID`s with
-- their representatives.
updateBody
    :: RuleP n t
    -> DupM n t (RuleP n t)
updateBody (RuleP r) = do
    d <- E.gets symDisj
    let body' = map (updLab d) (bodyR r)
    return . RuleP $ r { bodyR = body' }
  where
    updLab d x@NonT{..}     = x { labID = updSym d <$> labID }
    updLab d x@AuxVert{..}  = x { symID = updSym d symID }
    updLab _ x              = x
    updSym                  = Part.rep


-- | Find a rule if already present.
findRule
    :: (Ord n, Ord t)
    => RuleP n t
    -> DupM n t (Maybe (RuleP n t))
findRule x = do
    s <- E.gets rulDepo
    return $ lookupSet x s


-- | Join two `SymID`s.
joinSym :: SymID -> SymID -> DupM n t ()
joinSym x y = E.modify $ \s@DupS{..} -> s
    { symDisj = Part.joinElems x y symDisj }



-- | Save the rule in the underlying deposit.
keepRule
    :: (Ord n, Ord t)
    => RuleP n t
    -> DupM n t ()
keepRule r = E.modify $ \s@DupS{..} -> s
    { rulDepo = S.insert r rulDepo }


-- | Retrieve the symbol of the head of the rule.
headSym :: RuleP n t -> Maybe SymID
headSym r = case headR (unRuleP r) of
    NonT{..}    -> labID
    AuxVert{..} -> Just symID
    _           -> Nothing


-- | Removing duplicates updating `SymID`s at the same time.
-- WARNING: The pipe assumes that `SymID`s to which the present
-- rule refers have already been processed -- in other words,
-- that rule on which the present rule depends have been
-- processed earlier.
--
-- This function is responsible for basic sharing of common
-- subtrees.
rmDups
    :: (Ord n, Ord t)
    => P.Pipe
        (Rule n t)    -- Input
        (Rule n t)    -- Output
        (DupM n t)    -- Underlying state
        ()            -- No result
rmDups = forever $ do
    r <- P.await >>= lift . updateBody . RuleP
    lift (findRule r) >>= \mr -> case mr of
        Nothing -> do
            lift $ keepRule r
            P.yield $ unRuleP r
        Just r' -> case (headSym r, headSym r') of
            (Just x, Just y)    -> lift $ joinSym x y
            _                   -> return ()


--------------------------------------------------
-- Utilities
--------------------------------------------------


-- | Lookup an element in a set.
lookupSet :: Ord a => a -> S.Set a -> Maybe a
lookupSet x s = do
    y <- S.lookupLE x s
    guard $ x == y
    return y
