{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

import Control.Monad (forM_, guard)
import Control.Arrow (first)
import Control.Monad.Trans.Maybe     (MaybeT (..))

import Data.Lens.Light
import Data.IORef

import qualified Data.Set                 as S
import qualified Data.Map.Strict          as M
import qualified Data.Tree                as R
import qualified Data.MemoCombinators     as Memo
import           Pipes

import qualified NLP.Partage.AStar        as A
import qualified NLP.Partage.AStar.Base   as Base
import qualified NLP.Partage.AStar.Item   as Item
import qualified NLP.Partage.AStar.Chart  as Chart
import qualified NLP.Partage.AStar.Deriv  as Deriv
import qualified NLP.Partage.Auto.WeiTrie as W
-- import           NLP.Partage.FactGram   (flattenWithSharing)
import qualified NLP.Partage.DAG          as DAG
import qualified NLP.Partage.Tree.Other   as O


-----------------------
-- Params
-----------------------


-- | Use subtree sharing or not?
subtreeSharing :: Bool
subtreeSharing = False


-- | Mark visited?
markVisited :: Bool
markVisited = False


-- -- | The grammar type to use.
-- useGramType :: GramType
-- useGramType = Trie
--
--
-- -- | Type of the grammar to use.
-- data GramType
--   = List
--   | Trie
--   | FSA
--   deriving (Show, Eq, Ord)


-----------------------
-- Grammar
-----------------------


-- | Non-terminal and terminal types.
type N = String
type T = String


-- | Memoization for terminals.
memoTerm = Memo.list Memo.char


-- | Some smart constructors.
node x = R.Node (O.NonTerm x)
leaf x = R.Node (O.NonTerm x) []
term x = R.Node (O.Term x) []
foot x = R.Node (O.Foot x) []


-- | A sample TAG grammar.
trees =
  [ node "NP"
    [ node "D" [term "the"]
    , foot "NP"
    ]
  , node "N"
    [ node "A" [term "prime"]
    , foot "N"
    ]
  , node "NP" [node "N" [term "minister"]]
  , node "S"
    [ leaf "NP"
    , node "VP"
      [ node "V" [term "made"]
      , leaf "NP" ]
    ]
  , node "NP" [node "N" [term "decisions"]]
  , node "NP"
    [ node "D" [term "a"]
    , foot "NP"
    ]
  , node "NP"
    [ node "D" [term "few"]
    , foot "NP"
    ]
  , node "N"
    [ node "D" [term "good"]
    , foot "N"
    ]
  , node "NP"
    [ node "A" [term "prime"]
    , node "N" [term "minister"]
    ]
  , node "NP"
    [ node "D" [term "a"]
    , node "D" [term "few"]
    , foot "NP"
    ]
  , node "S"
    [ leaf "NP"
    , node "VP"
      [ node "V" [term "made"]
      , node "NP" [node "N" [term "decisions"]]
      ]
    ]
  ]


-----------------------
-- Showing
-----------------------


data Arc = Arc
  { from :: S.Set (A.Item N T)
  , to :: A.Item N T
  , typ :: String
  , mark :: Bool
  } deriving (Show, Eq, Ord)


arcsFrom :: A.Item N T -> A.ExtWeight N T -> [Arc]
arcsFrom hd ext =
  [ Arc {from = S.fromList src, to = hd, typ = arcTyp, mark = False}
  | trav <- S.toList (A.prioTrav ext)
  , let (src, arcTyp) = tails trav ]
  where
    tails trav = case trav of
      A.Scan{..} -> ([A.ItemA scanFrom], "SC")
      A.Subst{..} -> ([A.ItemA actArg, A.ItemP passArg], "SU")
      A.Foot{..} -> ([A.ItemA actArg], "FA")
      A.Adjoin{..} -> ([A.ItemP passAdj, A.ItemP passMod], "AD")


itemsIn :: A.Hype N T -> [(A.Item N T, A.ExtWeight N T)]
itemsIn hype =
  let passive = map (first A.ItemP) . Chart.listPassive $ A.chart hype
      active = map (first A.ItemA) . Chart.listActive $ A.chart hype
  in  passive ++ active


printGraph
  :: A.Hype N T             -- ^ The hypergraph
  -> M.Map Int (A.Item N T) -- ^ Items with their IDs
  -> M.Map Int Arc          -- ^ Arcs with their IDs
  -> IO ()
printGraph hype nodeMap edgeMap = do

  let nodeMapRev = revMap nodeMap
      -- determine which nodes are visited in the smaller hype
      visitedItems = S.unions
        [ from arc `S.union` S.singleton (to arc)
        | arc <- M.elems edgeMap
        , mark arc ]

  let fillStyle = "style=filled" -- if markVisited then "style=filled" else "style=solid"
      green = if markVisited then "green" else "green"
      red = if markVisited then "red" else "green"
  putStrLn $ "digraph {"
  forM_ (M.toList nodeMap) $ \(nodeID, node) -> do
    let color = if S.member node visitedItems then green else red
        style = "[label=\"" ++ showItem (A.automat hype) node
                ++ "\", fillcolor=" ++ color ++ ", " ++ fillStyle ++ "]"
    putStrLn $ "  " ++ show nodeID ++ " " ++ style ++ ";"

  forM_ (M.toList edgeMap) $ \(edgeID, edge) -> do
    let color = if mark edge then green else red
        style = "[label=\"" ++ typ edge
                ++ "\", shape=diamond, fillcolor="
                ++ color ++ ", " ++ fillStyle ++ "]"
    putStrLn $ "  " ++ show edgeID ++ " " ++ style ++ ";"

  forM_ (M.toList edgeMap) $ \(edgeID, edge) -> do
    forM_ (S.toList $ from edge) $ \src -> do
      putStrLn $ "  " ++ show (nodeMapRev M.! src) ++ " -> " ++ show edgeID ++ ";"
    putStrLn $ "  " ++ show edgeID ++ " -> " ++ show (nodeMapRev M.! to edge) ++ ";"
  putStrLn "}"


printHype :: A.Hype N T -> IO ()
printHype hype = do
  -- let ts = A.parsedTrees hype start (length sent)
  -- forM_ ts $ putStrLn . R.drawTree . fmap show . O.unTree
  let items = itemsIn hype
      nodeMap = M.fromList . zip [0..] $ map fst items
      edges = concat $ map (uncurry arcsFrom) items
      regularNodeNum = M.size nodeMap
      edgeMap = M.fromList $ zip [regularNodeNum+1..] edges
  printGraph hype nodeMap edgeMap


printBoth
  :: A.Hype N T -- ^ First
  -> A.Hype N T -- ^ Full
  -> IO ()
printBoth hypeFirst hypeFull = do
  let edges0 = S.fromList . concat $ map (uncurry arcsFrom) (itemsIn hypeFirst)

      items = itemsIn hypeFull
      edges =
        [ edge {mark = S.member edge edges0}
        | edge <- concat $ map (uncurry arcsFrom) items ]

      nodeMap = M.fromList . zip [0..] $ map fst items
      regularNodeNum = M.size nodeMap
      edgeMap = M.fromList $ zip [regularNodeNum+1..] edges

  printGraph hypeFull nodeMap edgeMap


-----------------------
-- Parsing
-----------------------


analyzeSent :: DAG.Gram N T -> T -> [T] -> IO ()
analyzeSent gram start sent = do
  let input = A.fromList sent
      auto = A.mkAuto memoTerm gram
  printHype =<< A.earleyAuto auto input


-- | Parse the given sentence with the given compressed grammar.
parsePipe
  :: [T] -- ^ Input sentence
  -> T   -- ^ Start symbol
  -> DAG.Gram N T -- ^ Compressed TAG grammar
  -> Producer (Deriv.ModifDerivs N T) IO (A.Hype N T)
parsePipe sent begSym gram =
  let auto = A.mkAuto memoTerm gram
      input = A.fromList sent
      derivConf = Deriv.DerivR
        { Deriv.startSym = begSym
        , Deriv.sentLen = length sent }
  in  A.earleyAutoP auto input
      >-> Deriv.derivsPipe derivConf


analyzePipe :: DAG.Gram N T -> T -> [T] -> IO ()
analyzePipe gram start sent = do
  -- A predicate which tells when the passive item is final
  let final p =
        A._spanP p == A.Span 0 (length sent) Nothing &&
        A._dagID p == Left start
  -- Run the parsing pipe
  let pipe = parsePipe sent start gram
  -- Parsing end marker
  foundRef <- newIORef Nothing
  -- Start parsing
  hypeFini <- runEffect . for pipe $ \(hypeModif, _derivTrees) -> do
    let item = A.modifItem hypeModif
        itemWeight = A.modifTrav hypeModif
        hype = A.modifHype hypeModif
    void . runMaybeT $ do
      -- Check if the modification corresponds to a new node (item)
      -- popped from the parsing agenda.  New hyperarcs are of no
      -- interest to us here.
      guard (A.modifType hypeModif == A.NewNode)
      A.ItemP p <- return item
      guard (final p)
      liftIO . modifyIORef' foundRef $ \case
        Nothing -> Just hype
        Just h0 -> Just h0
  readIORef foundRef >>= \case
    Nothing -> printHype hypeFini
    Just h0 -> printBoth h0 hypeFini


-----------------------
-- Main
-----------------------


main = do
  let mkGram = case subtreeSharing of
        True  -> DAG.mkGram
        False -> DAG.mkDummy
      gram = mkGram $ map (,1) trees
      analyze = analyzePipe gram
  analyze "S" ["the", "prime", "minister", "made", "a", "few", "good", "decisions"]
  -- print =<< recognize "S" ["the", "prime", "minister", "made", "a", "few", "good", "decisions"]


-----------------------
-- Utils
-----------------------


revMap :: Ord b => M.Map a b -> M.Map b a
revMap =
  let swap (x, y) = (y, x)
  in  M.fromList . map swap . M.toList



showItem :: A.Auto N T -> A.Item N T -> String
showItem auto (A.ItemP x) = showPassive auto x
showItem _ (A.ItemA x) = showActive x


showActive :: A.Active -> String
showActive x = concat
  [ "("
  , show $ getL Item.state x
  , ", "
  , showSpan $ getL Item.spanA x
  , ")"
  ]


showPassive :: A.Auto N T -> A.Passive N T -> String
showPassive auto x = concat
  [ "("
  , case getL Item.dagID x of
        Left rootNT -> rootNT
        Right did   ->
          Base.nonTerm (getL Item.dagID x) auto
          ++ "[" ++ show (DAG.unDID did)  ++ "]"
  , ", "
  , showSpan $ getL Item.spanP x
  , ")"
  ]


showSpan :: Item.Span -> String
showSpan span = concat
  [ show $ getL Item.beg span
  , ", "
  , case getL Item.gap span of
      Nothing -> ""
      Just (p, q) -> concat
          [ show p
          , ", "
          , show q
          , ", " ]
  , show $ getL Item.end span ]
