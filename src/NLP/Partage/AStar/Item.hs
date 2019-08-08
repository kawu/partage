{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}


module NLP.Partage.AStar.Item
  ( Span (..)
  , beg
  , end
  , gap
  , Active (..)
  , state
  , spanA
  , Passive (..)
  , dagID
  , spanP
  , isAdjoinedTo
  , regular
  , auxiliary
  , isRoot

-- #ifdef DebugOn
  , printActive
  , printPassive
-- #endif

  -- * Provisional
  , nonTerm
  )
where


import           Data.Lens.Light
import           Data.Maybe             (isJust, isNothing)
import           Prelude                hiding (span)

import           Data.DAWG.Ord          (ID)

import           NLP.Partage.AStar.Base (Pos)
import           NLP.Partage.DAG        (DID)
import qualified NLP.Partage.DAG as DAG

import           NLP.Partage.AStar.Base (nonTerm')
import           NLP.Partage.AStar.Auto (Auto (..), NotFoot(..))


data Span = Span {
    -- | The starting position.
      _beg :: Pos
    -- | The ending position (or rather the position of the dot).
    , _end :: Pos
    -- | Coordinates of the gap (if applies)
    , _gap :: Maybe (Pos, Pos)
    } deriving (Show, Eq, Ord)
$( makeLenses [''Span] )


-- | Active chart item : state reference + span.
data Active = Active {
      _state :: ID
    , _spanA :: Span
    } deriving (Show, Eq, Ord)
$( makeLenses [''Active] )


-- | Passive chart item : label + span.
data Passive n t = Passive
  { _dagID :: DID
    -- ^ The `DID` of the elementary tree node
  , _spanP :: Span
    -- ^ Span of the chart item
  , _isAdjoinedTo :: Bool
    -- ^ Was the node represented by the item already adjoined to?
  } deriving (Show, Eq, Ord)
$( makeLenses [''Passive] )


-- | Does it represent regular rules?
regular :: Span -> Bool
regular = isNothing . getL gap


-- | Does it represent auxiliary rules?
auxiliary :: Span -> Bool
auxiliary = isJust . getL gap


-- | Does it represent a root?
isRoot :: Either n DID -> Bool
isRoot x = case x of
    Left _  -> True
    Right _ -> False


-- #ifdef DebugOn
-- | Print an active item.
printSpan :: Span -> IO ()
printSpan span = do
    putStr . show $ getL beg span
    putStr ", "
    case getL gap span of
        Nothing -> return ()
        Just (p, q) -> do
            putStr $ show p
            putStr ", "
            putStr $ show q
            putStr ", "
    putStr . show $ getL end span


-- | Print an active item.
printActive :: Active -> IO ()
printActive p = do
    putStr "("
    putStr . show $ getL state p
    putStr ", "
    printSpan $ getL spanA p
    putStrLn ")"


-- | Print a passive item.
printPassive :: (Show n, Show t) => Passive n t -> Auto n t -> IO ()
printPassive p auto = do
    let did = getL dagID p
    putStr "("
    putStr $
      show (DAG.unDID did) ++ "[" ++
      show (nonTerm did auto) ++ "]"
    putStr ", "
    putStr $ "root=" ++ show (DAG.isRoot did (gramDAG auto))
    putStr ", "
    printSpan $ getL spanP p
    putStrLn ")"
-- #endif


-- | Take the non-terminal of the underlying DAG node.
nonTerm :: DAG.DID -> Auto n t -> n
nonTerm i =
    check . nonTerm' i . gramDAG
  where
    check Nothing  = error "nonTerm: not a non-terminal ID"
    check (Just x) = x
