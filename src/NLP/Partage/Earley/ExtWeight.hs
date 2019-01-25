module NLP.Partage.Earley.ExtWeight
( Trav (..)

-- * Priority
, Prio
, prioA
, prioP
, ExtPrio (..)
, extPrio
, joinPrio
) where


import           Data.Function          (on)
import qualified Data.Set               as S

import           Prelude hiding             (span, (.))
import           Data.Lens.Light
import           Control.Category ((.))

-- import           NLP.Partage.Earley.Base
import           NLP.Partage.Earley.Item
-- import           NLP.Partage.DAG        (Weight)


--------------------------------------------------
-- Traversal
--------------------------------------------------


-- | Traversal represents an action of inducing a new item on the basis of one
-- or two other chart items. It can be seen as an application of one of the
-- inference rules specifying the parsing algorithm.
--
-- TODO: Sometimes there is no need to store all the arguments of the inference
-- rules, it seems. From one of the arguments the other one could be derived.
--
-- UPDATE 09.05.2018: This should be rather called an 'Arc' or something alike.
data Trav n t
    = Scan
        { _scanFrom :: Active
        -- ^ The input active state
        , _scanTerm :: t
        -- ^ The scanned terminal
        }
    | Empty
        { _scanFrom :: Active
        -- ^ The input active state
        }
    | Subst
        { _passArg  :: Passive n t
        -- ^ The passive argument of the action
        , _actArg   :: Active
        -- ^ The active argument of the action
        }
    -- ^ Pseudo substitution
    | Foot
        { _actArg   :: Active
        -- ^ The passive argument of the action
        -- , theFoot  :: n
        , _theFoot  :: Passive n t
        -- ^ The foot non-terminal
        }
    -- ^ Foot adjoin
    | Adjoin
        { _passAdj  :: Passive n t
        -- ^ The adjoined item
        , _passMod  :: Passive n t
        -- ^ The modified item
        }
    -- ^ Adjoin terminate with two passive arguments
    | SisterAdjoin
        { _passArg  :: Passive n t
        -- ^ The passive argument of the action
        , _actArg   :: Active
        -- ^ The active argument of the action
        }
    | Deactivate
        { _actArg   :: Active
        -- ^ The active argument of the action
        }
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


-- | Priority of an active item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioA :: Active -> Prio
prioA p =
    let i = getL (beg . spanA) p
        j = getL (end . spanA) p
    in  (j, j - i)


-- | Priority of a passive item.  Crucial for the algorithm --
-- states have to be removed from the queue in a specific order.
prioP :: Passive n t -> Prio
prioP p =
    let i = getL (beg . spanP) p
        j = getL (end . spanP) p
    in  (j, j - i)


-- | Extended priority which preservs information about the traversal
-- leading to the underlying chart item.
data ExtPrio n t = ExtPrio
    { prioVal   :: Prio
    -- ^ The actual priority
    , prioTrav  :: S.Set (Trav n t)
    -- ^ Traversal leading to the underlying chart item
    } deriving (Show)

instance Eq (ExtPrio n t) where
    (==) = (==) `on` prioVal
instance Ord (ExtPrio n t) where
    compare = compare `on` prioVal


-- | Construct a new `ExtPrio`.
extPrio :: Prio -> ExtPrio n t
extPrio p = ExtPrio p S.empty


-- | Join two priorities:
-- * The actual priority preserved is the lower of the two,
-- * The traversals are unioned.
--
-- NOTE: at the moment, priority is strictly specified by the
-- underlying chart item itself so we know that both priorities must
-- be equal.  Later when we start using probabilities this statement
-- will no longer hold.
joinPrio :: (Ord n, Ord t) => ExtPrio n t -> ExtPrio n t -> ExtPrio n t
joinPrio x y = ExtPrio
    (min (prioVal x) (prioVal y))
    (S.union (prioTrav x) (prioTrav y))
