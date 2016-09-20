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
  , regular
  , auxiliary
  , isRoot

-- #ifdef DebugOn
  , printActive
  , printPassive
-- #endif
  )
where


import           Data.Lens.Light
import           Data.Maybe             (isJust, isNothing)
import           Prelude                hiding (span)

import           Data.DAWG.Ord          (ID)

import           NLP.Partage.AStar.Base (Pos)
import           NLP.Partage.DAG        (DID)
import qualified NLP.Partage.DAG as DAG

-- #ifdef DebugOn
import           NLP.Partage.AStar.Base (nonTerm)
import           NLP.Partage.AStar.Auto (Auto (..))
-- #endif


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
data Passive n t = Passive {
      _dagID :: Either n DID
    , _spanP :: Span
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
    putStr "("
    -- putStr . viewLab $ getL label p
    putStr $ case getL dagID p of
        Left rootNT -> show rootNT
        Right did   ->
          show (DAG.unDID did) ++ "[" ++
          show (nonTerm (getL dagID p) auto) ++ "]"
    putStr ", "
    printSpan $ getL spanP p
    putStrLn ")"
-- #endif
