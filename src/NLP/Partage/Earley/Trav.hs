module NLP.Partage.Earley.Trav
( Trav (..)

-- * Priority
, Prio
, prioA
, prioP
, prio
-- ** Extended
, ExtPrio (..)
, extPrio
, joinPrio
) where


import           Data.Function          (on)
import qualified Data.Set               as S

import           Prelude hiding             (span, (.))
import           Data.Lens.Light
import           Control.Category ((.))

import           NLP.Partage.Earley.Item


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
data Trav n t v
    = Scan
        { _scanFrom :: Active
        -- ^ The input active state
        , _scanTerm :: t
        -- ^ The scanned terminal
        }
    | Deact
        { _actArg   :: Active
        -- ^ The active argument of the action
        }
    | Subst
        { _passArg  :: NonActive n v
        -- ^ The passive argument of the action
        , _actArg   :: Active
        -- ^ The active argument of the action
        }
--     | Subst
--         { _compArg  :: Top n v
--         -- ^ The passive argument of the action
--         , _actArg   :: Active
--         -- ^ The active argument of the action
--         }
--     | Restore
--         { _passArg  :: Passive
--         -- ^ The passive argument of the action
--         , _actArg   :: Active
--         -- ^ The active argument of the action
--         }
    -- ^ Pseudo substitution
    | Foot
        { _actArg   :: Active
        -- ^ The passive argument of the action
        -- , theFoot  :: n
        , _theFoot  :: NonActive n v
        -- ^ The foot non-terminal
        }
    -- ^ Foot adjoin
    | Adjoin
        { _passAdj  :: Top n v
        -- ^ The adjoined item
        , _passMod  :: NonActive n v
        -- ^ The modified item
        }
    -- ^ Adjoin terminate with two passive arguments
    deriving (Show, Eq, Ord)


-- -- | Print a traversal.
-- printTrav :: (Show n, Show t) => Hype n t -> Item n t -> Trav n t -> IO ()
-- printTrav h q' (Scan p x) = do
--     putStr "# " >> printActive p
--     putStr "+ " >> print x
--     putStr "= " >> printItem q' h
-- printTrav h q' (Subst p q) = do
--     putStr "# " >> printActive q
--     putStr "+ " >> printPassive p h
--     putStr "= " >> printItem q' h
-- printTrav h q' (Foot q p) = do
--     putStr "# " >> printActive q
--     putStr "+ " >> printPassive p h
--     putStr "= " >> printItem q' h
-- printTrav h q' (Adjoin p s) = do
--     putStr "# " >> printPassive p h
--     putStr "+ " >> printPassive s h
--     putStr "= " >> printItem q' h


--------------------------------------------------
-- Priority
--------------------------------------------------


-- | Priority type.
--
-- NOTE: Priority has to be composed from two elements because
-- otherwise `tryAdjoinTerm` could work incorrectly.  That is,
-- the modified item could be popped from the queue after the
-- modifier (auxiliary) item and, as a result, adjunction would
-- not be considered.
type Prio = (Int, Int)


-- | Priority of an active item.
prioA :: Active -> Prio
prioA = prioGen . getL spanA
-- prioA p =
--     let i = getL (beg . spanA) p
--         j = getL (end . spanA) p
--     in  (j, j - i)


-- | Priority of a passive item.
prioP :: Passive -> Prio
prioP = prioGen . getL spanP
-- prioP p =
--     let i = getL (beg . spanP) p
--         j = getL (end . spanP) p
--     in  (j, j - i)


-- | Priority of a top-passive item.
prioT :: Top n v -> Prio
prioT = prioGen . getL spanT
-- prioT p =
--     let i = getL (beg . spanT) p
--         j = getL (end . spanT) p
--     in  (j, j - i)


-- -- | Priority of a non-active item.
-- prioN :: NonActtive n v -> Prio
-- prioN x = case x of
--   Left p -> prioP p
--   Right p -> prioT p


-- | Priority of aan item depending on its span. Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioGen :: Span -> Prio
prioGen s =
  let i = getL beg s
      j = getL end s
  in  (j, j - i)


-- | Priority of an active item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prio :: Item n v -> Prio
prio (ItemT p) = prioT p
prio (ItemP p) = prioP p
prio (ItemA p) = prioA p


-- | Extended priority which preservs information about the traversal
-- leading to the underlying chart item.
data ExtPrio n t v = ExtPrio
    { prioVal   :: Prio
    -- ^ The actual priority
    , prioTrav  :: S.Set (Trav n t v)
    -- ^ Traversal leading to the underlying chart item
    } deriving (Show)

instance Eq (ExtPrio n t v) where
    (==) = (==) `on` prioVal
instance Ord (ExtPrio n t v) where
    compare = compare `on` prioVal


-- | Construct a new `ExtPrio`.
extPrio :: Prio -> ExtPrio n t v
extPrio p = ExtPrio p S.empty


-- | Join two priorities:
-- * The actual priority preserved is the lower of the two,
-- * The traversals are unioned.
--
-- NOTE: at the moment, priority is strictly specified by the
-- underlying chart item itself so we know that both priorities must
-- be equal.  Later when we start using probabilities this statement
-- will no longer hold.
joinPrio :: (Ord n, Ord t, Ord v) => ExtPrio n t v -> ExtPrio n t v -> ExtPrio n t v
joinPrio x y = ExtPrio
    (min (prioVal x) (prioVal y))
    (S.union (prioTrav x) (prioTrav y))
