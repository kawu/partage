{-# LANGUAGE RecordWildCards #-}


-- | A version in which a separate automaton is built (according to
-- the underlying building function) for each distinct rule head
-- symbol, i.e. the set of rules is first partitioned w.r.t. the
-- heads of the individual rules, and then for each partition a
-- separate automaton is built.


module NLP.TAG.Vanilla.Auto.Set
(
-- -- AutoSet
--   AutoSet
-- , buildAutoSet
-- 
-- -- * Interface
-- , shell
  fromGram
) where


import           Control.Applicative ((<$>))
import           Control.Monad (forM)
import qualified Control.Monad.State.Strict as E
-- -- import           Control.Monad.Trans.Class (lift)

import           Data.List (foldl')
import           Data.Maybe (maybeToList)
import qualified Data.Set                   as S
import qualified Data.Map.Strict            as M

import           Data.DAWG.Ord (ID)

import           NLP.TAG.Vanilla.Rule
    ( Lab(..), Rule(..) )


import qualified NLP.TAG.Vanilla.Auto as A


--------------------------------------------------
-- Interface
--------------------------------------------------


-- | Abstract over the concrete implementation of automaton.
shell :: (Ord a) => AutoSet a -> A.Auto a
shell AutoSet{..} = A.Auto
    { roots  = S.fromList
             . map unExID
             . S.toList $ rootSet
             -- we could note in the specification of the
             -- `Mini.Auto` that it doesn't have to be very
             -- efficient because it is run only once per
             -- parsing session
    , follow = \e x -> do
        (autoID, i) <- M.lookup (ExID e) fromExID
        auto        <- M.lookup autoID autoMap
        j           <- A.follow auto i x
        unExID     <$> M.lookup (autoID, j) toExID
    , edges  = \e -> do
        let mtl = maybeToList
        (autoID, i) <- mtl $ M.lookup (ExID e) fromExID
        auto        <- mtl $ M.lookup autoID autoMap
        (x, j)      <- A.edges auto i
        e'          <- mtl $ M.lookup (autoID, j) toExID
        return (x, unExID e')
    }


-- | Build the set of automata from the given grammar.
fromGram
    :: (Ord n, Ord t)
    => (S.Set (Rule n t) -> A.GramAuto n t)
        -- ^ The underlying automaton construction method
    -> S.Set (Rule n t)
        -- ^ The grammar to compress
    -> A.GramAuto n t
fromGram mkOne = shell . buildAutoSet mkOne


--------------------------------------------------
-- Implementation
--------------------------------------------------


-- | An external identifier (in contrast to internal identifiers
-- which are local to individual component automata).
newtype ExID = ExID { unExID :: ID }
    deriving (Show, Eq, Ord)


-- | An automaton identifier.
newtype AutoID = AutoID { _unAutoID :: ID }
    deriving (Show, Eq, Ord)


-- | An ensemble of automata.
data AutoSet a = AutoSet
    { autoMap   :: M.Map AutoID (A.Auto a)
    -- ^ individual automata and their identifiers
    , rootSet   :: S.Set ExID
    -- ^ A set of roots of the ensemble
    , fromExID  :: M.Map ExID (AutoID, ID)
    -- ^ Map external IDs to internal ones
    , toExID    :: M.Map (AutoID, ID) ExID
    -- ^ Reverse of `fromEx`
    }


-- | An empty `AutoSet`.
emptyAS :: AutoSet a
emptyAS = AutoSet M.empty S.empty M.empty M.empty


-- | Assuming that two `AutoSet`s are disjoint (i.e. they have
-- disjoint sets of `AutoID`s and disjoin sets of `ExID`s), we can
-- union them easily.
unionAS :: AutoSet a -> AutoSet a -> AutoSet a
unionAS p q = AutoSet
    { autoMap   = M.union (autoMap p) (autoMap q)
    , rootSet   = S.union (rootSet p) (rootSet q)
    , fromExID  = M.union (fromExID p) (fromExID q)
    , toExID    = M.union (toExID p) (toExID q) }


-- | Union a list of `AutoSet`s.
unionsAS :: [AutoSet a] -> AutoSet a
unionsAS = foldl' unionAS emptyAS


-- | Build automata from the given grammar.
buildAutoSet
    :: (Ord n, Ord t)
    => (S.Set (Rule n t) -> A.GramAuto n t)
        -- ^ The underlying automaton construction method
    -> S.Set (Rule n t)
        -- ^ The grammar to compress
    -> AutoSet (A.Edge (Lab n t))
buildAutoSet mkOne gram = runM $
    unionsAS <$> sequence
        [ mkAutoSet
            (AutoID autoID)
            (mkOne ruleSet)
        | (autoID, ruleSet)
            <- zip [0..] (M.elems gramByHead) ]
  where
    -- grammar divided by rule heads
    gramByHead = M.fromListWith S.union
        [ (headR r, S.singleton r)
        | r <- S.toList gram ]
    -- build a single automatom
    mkAutoSet autoID auto = do
        rootMap <- mkNodeMap (A.roots auto)
        descMap <- mkNodeMap (A.allIDs auto S.\\ A.roots auto)
        let nodeMap = rootMap `M.union` descMap
        return AutoSet
            { autoMap   = M.singleton autoID auto
            , rootSet   = M.keysSet rootMap
            , fromExID  = nodeMap
            , toExID    = rev1to1 nodeMap }
      where
        mkNodeMap inNodeSet = fmap M.fromList $
            forM (S.toList inNodeSet) $ \i -> do
                e <- newExID
                return (e, (autoID, i))
    -- low-level monad-related functions
    runM = flip E.evalState (0 :: Int)
    newExID = E.state $ \k -> (ExID k, k + 1)
    -- reverse bijection
    rev1to1 = M.fromList . map swap . M.toList
    swap (x, y) = (y, x)
