module NLP.Partage.AStar.ExtWeight
  ( Trav (..)

  -- * Weight ops
  , zeroWeight
  , addWeight
  , sumWeight
  , minWeight

  -- * Extended Weight
  , ExtWeight (..)
  , extWeight0
  , extWeight
  , joinExtWeight
  , joinExtWeight'
  )
where


import           Data.Function          (on)
import qualified Data.Set               as S

import           NLP.Partage.AStar.Base
import           NLP.Partage.AStar.Item
import           NLP.Partage.DAG        (Weight)


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
--
-- TODO: Weight component can be extracted outside the Trav datatype.
data Trav n t
    = Scan
        { scanFrom  :: Active
        -- ^ The input active state
        , _scanTerm :: Tok t
        -- ^ The scanned terminal
        , _weight   :: Weight
        -- ^ The traversal weight
        }
    | Subst
        { passArg :: Passive n t
        -- ^ The passive argument of the action
        , actArg  :: Active
        -- ^ The active argument of the action
        , _weight :: Weight
        -- ^ The traversal weight
        }
    -- ^ Pseudo substitution
    | Foot
        { actArg  :: Active
        -- ^ The active argument of the action
        , theFoot :: n
        -- ^ The foot non-terminal
--         , _theFoot  :: Passive n t
--         -- ^ The passive argument of the action
        , _weight :: Weight
        -- ^ The traversal weight
        }
    -- ^ Foot adjoin
    | Adjoin
        { passAdj :: Passive n t
        -- ^ The adjoined item
        , passMod :: Passive n t
        -- ^ The modified item
        }
    -- ^ Adjoin terminate with two passive arguments
    deriving (Show, Eq, Ord)


--------------------------------------------------
-- Weight (priority)
--------------------------------------------------


-- | Neutral element of the weight/priority.  Corresponds to the
-- logarithm of probability 1.
zeroWeight :: Weight
zeroWeight = 0


-- | Add two weights.
addWeight :: Weight -> Weight -> Weight
addWeight = (+)
{-# INLINE addWeight #-}


-- | Sum weights.
sumWeight :: [Weight] -> Weight
sumWeight = sum
{-# INLINE sumWeight #-}


-- | Minimum of two weights.
minWeight :: Weight -> Weight -> Weight
minWeight = min
{-# INLINE minWeight #-}


--------------------------------------------------
-- Extended Weight
--------------------------------------------------


-- | Extended priority which preserves information about the
-- traversal leading to the underlying chart item.  The best weight
-- (priority) of reaching the underlying item is preserved as well.
-- Note that traversals themselves do not introduce any weights.
data ExtWeight n t = ExtWeight
    { priWeight :: Weight
    -- ^ The actual priority.  In case of initial elements
    -- corresponds to weights (probabilities?) assigned to
    -- individual "elementary rules".
    , estWeight :: Weight
    -- ^ Estimated weight to the "end"
    , prioTrav  :: S.Set (Trav n t)
    -- ^ Traversal leading to the underlying chart item
    } deriving (Show)

instance (Eq n, Eq t) => Eq (ExtWeight n t) where
    (==) = (==) `on` (addWeight <$> priWeight <*> estWeight)
instance (Ord n, Ord t) => Ord (ExtWeight n t) where
    compare = compare `on` (addWeight <$> priWeight <*> estWeight)


-- | Construct an initial `ExtWeight`.  With an empty set of input
-- traversals, it corresponds to a start node in the underlying
-- hyper-graph.
extWeight0 :: Weight -> Weight -> ExtWeight n t
extWeight0 p initEst = ExtWeight p initEst S.empty


-- | Construct an `ExtWeight` with one incoming traversal
-- (traversal=hyper-edge).
extWeight :: Weight -> Weight -> Trav n t -> ExtWeight n t
extWeight p est = ExtWeight p est . S.singleton


-- | Join two extended priorities:
-- * The actual priority (cost) preserved is the lower of the two; we
-- are simply keeping the lowest cost of reaching the underlying
-- chart item.
-- * The traversals are unioned.
joinExtWeight
    :: (Ord n, Ord t)
    => ExtWeight n t
    -> ExtWeight n t
    -> ExtWeight n t
joinExtWeight x y = if estWeight x /= estWeight y
    then error "joinExtWeight: estimation costs differ!"
    else ExtWeight
        (minWeight (priWeight x) (priWeight y))
        (estWeight x)
        (S.union (prioTrav x) (prioTrav y))


joinExtWeight'
    :: (Ord n, Ord t)
    => ExtWeight n t
    -> ExtWeight n t
    -> ExtWeight n t
joinExtWeight' new old =
  if estWeight new /= estWeight old
  then error "joinExtWeight[save active/passive]: estimation costs differ!"
  else
    if priWeight new < priWeight old
    then error "joinExtWeight[save active/passive]: new beta value lower than the old!"
    else
      ExtWeight
      (minWeight (priWeight new) (priWeight old))
      (estWeight new)
      (S.union (prioTrav new) (prioTrav old))
