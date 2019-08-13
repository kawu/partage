{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}


-- import           Prelude hiding (words)
import           Control.Monad (forM_, when, guard)
import qualified Control.Arrow as Arr
import qualified Control.Monad.RWS.Strict   as RWS

import           Data.Monoid ((<>))
import           Data.Maybe (catMaybes, maybeToList)
import           Options.Applicative
import qualified Data.Attoparsec.Text as Atto
import           Data.Ord (comparing)
import qualified Data.IORef as IORef
import qualified Data.Char as C
import qualified Data.List as List
import qualified Data.Foldable as F
import           Data.Monoid (Sum(..))
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Data.Tree as R
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as LIO
import qualified Data.MemoCombinators as Memo

import qualified Data.Time as Time
import qualified Pipes as P

import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.DAG as DAG
import qualified NLP.Partage.AStar as A
import qualified NLP.Partage.AStar.Chart as C
import qualified NLP.Partage.AStar.Deriv as D
import qualified NLP.Partage.AStar.Deriv.Gorn as DG
import qualified NLP.Partage.Earley as E
import qualified NLP.Partage.Format.Brackets as Br

-- import Debug.Trace (trace)


--------------------------------------------------
-- Attoparsec Utils
--------------------------------------------------


-- | Convert an attoparsec reader to `ReadM`.
attoReader :: Atto.Parser a -> ReadM a
attoReader p = eitherReader (Atto.parseOnly p . T.pack)


--------------------------------------------------
-- Global Options
--------------------------------------------------


data Command
    = Earley
      { inputPath :: Maybe FilePath
      , verbose :: Bool
      -- , withProb :: Bool
      , maxTags :: Maybe Int
      , minProb :: Maybe Double
      , betaParam :: Maybe Double
      , goldPath :: Maybe FilePath
      , startSym :: S.Set T.Text
      , showParses :: Maybe Int
      , showParseNum :: Maybe Int
      , brackets :: Bool
      , checkRepetitions :: Bool
      , maxLen :: Maybe Int
      }
    -- ^ Parse the input sentences using the Earley-style chart parser
    | AStar
      { inputPath :: Maybe FilePath
      , verbose :: Bool
      , maxTags :: Maybe Int
      , maxDeps :: Maybe Int
      , minProb :: Maybe Double
      , betaParam :: Maybe Double
      , startSym :: S.Set T.Text
      , fullHype :: Bool
      , maxLen :: Maybe Int
      , fullParse :: Bool
      -- , brackets :: Bool
      , useSoftMax :: Bool
--       , checkRepetitions :: Bool
      }
    -- ^ Parse the input sentences using the Earley-style A* chart parser
    | Dummy
      { inputPath :: Maybe FilePath
      }
    -- ^ Dummy parser?  Don't remember what was its purpose.
    | RemoveCol
      { colNum :: Int
      }
    -- ^ Remove the given column from .tsv file


--------------------------------------------------
-- Options
--------------------------------------------------


earleyOptions :: Parser Command
earleyOptions = Earley
  <$> (optional . strOption)
  ( long "input"
    <> short 'i'
    <> help "Input file with supertagging results"
  )
  <*> switch
  ( long "verbose"
    <> short 'v'
    <> help "Verbose reporting"
  )
--   <*> switch
--   ( long "with-prob"
--     -- <> short 'p'
--     <> help "Set on if the input file contains info about probabilities"
--   )
  <*> (optional . option auto)
  ( long "max-tags"
    <> short 't'
    <> help "Maximum number of supertags to take"
  )
  <*> (optional . option auto)
  ( long "min-prob"
    <> help "Minimum probability of a supertag to take"
  )
  <*> (optional . option auto)
  ( long "beta"
    <> help "Beta parameter à la Clark & Curran"
  )
  <*> (optional . strOption)
  ( long "gold"
    <> short 'g'
    <> help "Gold file with parsed trees"
  )
  -- <*> option (attoReader startSetP)
  <*> (fmap S.unions . some . option (attoReader startSetP))
  ( long "start"
    <> short 's'
    <> help "Start symbol"
  )
  <*> option (Just <$> auto)
  ( long "print-parses"
    <> short 'p'
    <> value Nothing
    <> help "Show the given number of parsed trees (at most)"
  )
  <*> option (Just <$> auto)
  ( long "print-parse-num"
    <> value Nothing
    <> help "Show the number of parsed trees (at most)"
  )
  <*> switch
  ( long "brackets"
    <> short 'b'
    <> help "Render trees in the bracketed format"
  )
  <*> switch
  ( long "check-repetitions"
    <> short 'r'
    <> help "Issue WARNINGs if there are repetitions among the parsed trees (requires -g)"
  )
  <*> (optional . option auto)
  ( long "max-len"
    <> help "Limit on sentence length"
  )


astarOptions :: Parser Command
astarOptions = AStar
  <$> (optional . strOption)
  ( long "input"
    <> short 'i'
    <> help "Input file with supertagging results"
  )
  <*> switch
  ( long "verbose"
    <> short 'v'
    <> help "Verbose reporting"
  )
  <*> (optional . option auto)
  ( long "max-tags"
    <> short 't'
    <> help "Maximum number of supertags to take"
  )
  <*> (optional . option auto)
  ( long "max-deps"
    <> short 'd'
    <> help "Maximum number of head arcs to take"
  )
  <*> (optional . option auto)
  ( long "min-prob"
    <> help "Minimum supertag/dependency probability"
  )
  <*> (optional . option auto)
  ( long "beta"
    <> help ( unwords
          [ "Beta parameter à la Clark & Curran"
          , "(for both supertags and dependencies)" 
          ] )
  )
  -- <*> (fmap (maybe S.empty id) . many . option (attoReader startSetP))
  <*> (fmap S.unions . many . option (attoReader startSetP))
  ( long "start"
    <> short 's'
    <> help "Start symbol"
  )
  <*> switch
  ( long "full-hype"
    <> help "Create a full hypergraph"
  )
  <*> (optional . option auto)
  ( long "max-len"
    <> help "Limit on sentence length"
  )
  <*> switch
  ( long "full-parse"
    <> short 'p'
    <> help "Show the full output parse tree"
  )
--   <*> switch
--   ( long "brackets"
--     <> short 'b'
--     <> help "Render trees in the bracketed format"
--   )
  <*> switch
  ( long "softmax"
    <> help "Apply softmax to dependency weights"
  )


dummyOptions :: Parser Command
dummyOptions = Dummy
  <$> (optional . strOption)
  ( long "input"
    <> short 'i'
    <> help "Input file with supertagging results"
  )


removeColOptions :: Parser Command
removeColOptions = RemoveCol
  <$> option auto
  ( long "colnum"
    <> short 'c'
    <> help "Column to remove"
  )


-- | Start symbol set parser
startSetP :: Atto.Parser (S.Set T.Text)
startSetP = do
  xs <- startSymP `Atto.sepBy` spacesP
  return (S.fromList xs)
  where
    -- startSymP = Atto.takeWhile1 C.isAlphaNum
    startSymP = Atto.takeTill C.isSpace
    spacesP = Atto.takeWhile1 C.isSpace


--------------------------------------------------
-- Global options
--------------------------------------------------


opts :: Parser Command
opts = subparser
  ( command "earley"
    (info (helper <*> earleyOptions)
      (progDesc "Parse the input grammar file with Earley")
    )
    <>
    command "astar"
    (info (helper <*> astarOptions)
      (progDesc "Parse the input grammar file with A*")
    )
    <>
    command "dummy"
    (info (helper <*> dummyOptions)
      (progDesc "Output the most probable input tags/deps")
    )
    <>
    command "remcol"
    (info (helper <*> removeColOptions)
      (progDesc "Remove the given column from the input .tsv file")
    )
  )


-- | Run program depending on the cmdline arguments.
run :: Command -> IO ()
run cmd =

  case cmd of

    Earley{..} -> do

      -- Read input supertagging file
      let parseSuper = Br.parseSuperProb
--             if withProb
--             then Br.parseSuperProb
--             else Br.parseSuper
          filterLen =
            case maxLen of
              Nothing -> id
              Just ml -> filter ((<=ml) . length)
      super <-
          filterLen
        . limitTagsProb minProb
        . limitTagsBeta betaParam
        . limitTagsNum maxTags
        . parseSuper
        <$> readInput inputPath

      -- Read the gold file
      gold <- case goldPath of
        Nothing -> return $ repeat Nothing
        Just path -> do
          file <- LIO.readFile path
          return . map
            ( Just
              . Br.anchor (error "An anchor in the gold file")
              . Br.parseTree'
              . L.toStrict
            )
            $ L.lines file

      forM_ (zip super gold) $ \(sent, goldTree) -> do

        let
          -- Add token IDs in order to distinguish tokens with identical word
          -- forms (which may have different supertags)
          input = zip [0 :: Int ..] (map Br.tokWord sent)

          -- Create the compressed grammar representation
          gram
            = DAG.mkGram
            . anchorTagsIgnoreProbs
            . zip [0 :: Int ..]
            $ sent

        -- Check against the gold file or perform simple recognition
        when verbose $ do
          putStr "# "
          TIO.putStr . T.unwords $ map snd input
          LIO.putStr " => "
        case goldTree of
          Just tree -> do
            parses <- map (fmap rmTokID . O.unTree) <$>
              E.parse gram startSym (E.fromList input)
            print (tree `elem` parses)
            when (checkRepetitions && length parses /= length (nub parses)) $ do
              putStrLn "WARNING: repetitions in the set of parsed trees!"
          Nothing -> do
            -- reco <- E.recognizeFrom gram startSym (E.fromList input)
            begTime <- Time.getCurrentTime
            hype <- E.earley gram (E.fromList input)
            let n = length input
                reco = (not.null) (E.finalFrom startSym n hype)
            when verbose $ do
              print reco
              endTime <- Time.getCurrentTime
              putStr (show n)
              putStr "\t"
              putStr (show $ E.hyperEdgesNum hype)
              putStr "\t"
              putStr (show $ endTime `Time.diffUTCTime` begTime)
            -- Show the number of parsed trees
            case showParseNum of
              Nothing -> return ()
              Just k -> do
                parses <- E.parse gram startSym (E.fromList input)
                putStr "# Parse num: "
                putStrLn . show $ sum
                  -- We have to evaluate them to alleviate the memory leak
                  [ L.length txtTree `seq` (1 :: Int)
                  | tree <- take k parses
                  , let txtTree = (Br.showTree . fmap rmTokID $ O.unTree tree)
                  ]

        -- Show the parsed trees
        let shorten = 
              case showParses of
                Just k  -> take k
                Nothing -> id
        parses <- E.parse gram startSym (E.fromList input)
        when (null parses) $ do
          putStr "# NO PARSE FOR: "
          TIO.putStrLn . T.unwords $ map snd input
        forM_ (shorten parses) $ \tree -> do
          when verbose $ do
            putStrLn ""
            putStrLn . R.drawTree . fmap show $ O.unTree tree
          LIO.putStrLn . Br.showTree . fmap rmTokID $ O.unTree tree
        putStrLn ""


    AStar{..} -> do

      -- Read input supertagging file
      let parseSuper = Br.parseSuperProb
          filterLen =
            case maxLen of
              Nothing -> id
              Just ml -> filter ((<=ml) . length)
      super <-
          filterLen
        . limitTagsProb minProb
        . limitDepsProb minProb
        . limitTagsBeta betaParam
        . limitDepsBeta betaParam
        . limitDepsNum maxDeps
        . limitTagsNum maxTags
        . parseSuper
        <$> readInput inputPath

      forM_ super $ \sent -> do

        let
          -- Add token IDs in order to distinguish tokens with identical word
          -- forms (which may have different supertags)
          input = zip [0 :: Int ..] (map Br.tokWord sent)
          inputVect = V.fromList (map Br.tokWord sent)

          -- Calculate the position map (mapping from tokens to their
          -- positions)
          posMap = M.fromList [(x, fst x) | x <- input]

          -- Create the corresponding dependency map
          depMap = mkDepMap' useSoftMax $ zip [0 :: Int ..] sent

          -- Create the compressed grammar representation
          gram
            = DAG.mkGram
            . anchorTags
            . zip [0 :: Int ..]
            $ sent
          automat =
            A.mkAuto
              memoTerm gram (A.fromList input) posMap depMap
          memoTerm = Memo.wrap
            (\i -> (i, inputVect V.! i))
            (\(i, _w) -> i)
            Memo.integral

        -- Check against the gold file or perform simple recognition
        when verbose $ do
          putStr "# "
          TIO.putStr . T.unwords $ map snd input
          LIO.putStr " => "

        begTime <- Time.getCurrentTime
        hypeRef <- IORef.newIORef Nothing
        let n = length input
            consume = do
              A.HypeModif{..} <- P.await
              -- modifHype <- RWS.get
              case (modifType, modifItem) of
                (A.NewNode, A.ItemP p) ->
                  -- if (D.isFinal_ modifHype startSym n p) then do
                  if (C.isFinal startSym n (A.automat modifHype) p) then do
                    semiTime <- P.liftIO Time.getCurrentTime
                    P.liftIO . IORef.writeIORef hypeRef $ Just (modifHype, semiTime)
                    if fullHype
                      then consume
                      else return modifHype
                  else consume
                _ -> consume
--         finalHype <- P.runEffect $
--           A.earleyAutoP automat (A.fromList input)
--           P.>-> consume
        finalHype <- A.earleyAutoP automat (A.fromList input) consume
        endTime <- Time.getCurrentTime
        (semiHype, semiTime) <- maybe (finalHype, endTime) id
          <$> IORef.readIORef hypeRef
        when verbose $ do
          let reco = (not.null) (A.finalFrom startSym n semiHype)
          print reco
          putStr (show n)
          putStr "\t"
          putStr (show $ A.hyperEdgesNum semiHype)
          putStr "\t"
          putStr $ show (semiTime `Time.diffUTCTime` begTime)
          if fullHype then do
            putStr "\t"
            putStr (show $ A.hyperEdgesNum finalHype)
            putStr "\t"
            print (endTime `Time.diffUTCTime` begTime)
          else do
            putStrLn ""

        -- Show the derivations
        let derivs = D.derivTreesW finalHype startSym (length input)
        when (null derivs) $ do
          putStr "# NO PARSE FOR: "
          TIO.putStrLn . T.unwords $ map snd input
        forM_ (maybeToList derivs) $ \(deriv, w) -> do
          if fullParse
             then do
               -- renderParse' deriv
               renderParse deriv
             else renderDeriv deriv
          when verbose $ do
            putStrLn ""
            putStrLn $ "# weight: " ++ show w
            putStrLn
              . R.drawTree . fmap show
              . D.deriv4show . D.normalize
              $ deriv
            putStrLn ""
        putStrLn ""


    Dummy{..} -> do
      super <- Br.parseSuperProb <$> readInput inputPath
      forM_ super $ \sent -> do
        renderInput $ zip [1 :: Int ..] sent
        putStrLn ""


    RemoveCol{..} -> do
      file <- LIO.getContents
      forM_ (L.lines file)
        $ LIO.putStrLn
        . L.intercalate "\t"
        . remove (colNum-1)
        . L.splitOn "\t"

  where

    -- Additional supertag-related constraints
    limitTagsNum = \case
      Nothing -> id
      Just m -> map . map $ \superTok -> superTok
        {Br.tokTags = takeBest m (Br.tokTags superTok)}
    limitTagsProb = \case
      Nothing -> id
      Just p -> map . map $ \superTok -> superTok
        {Br.tokTags = filter ((>=p) . snd) (Br.tokTags superTok)}
    limitTagsBeta = \case
      Nothing -> id
      Just beta -> map . map $ \superTok ->
        let maxProb = case map snd (Br.tokTags superTok) of
              [] -> 0.0
              xs -> maximum xs
            p = maxProb * beta
        in  superTok
            {Br.tokTags = filter ((>=p) . snd) (Br.tokTags superTok)}

    -- Additional dependency-related constraints
    limitDepsNum = \case
      Nothing -> id
      Just m -> map . map $ \superTok -> superTok
        {Br.tokDeph =
          (M.fromList . takeBest m . M.toList)
          (Br.tokDeph superTok)
        }
    limitDepsProb = \case
      Nothing -> id
      Just p -> map . map $ limitDepsProbFor p
    limitDepsBeta = \case
      Nothing -> id
      Just beta -> map . map $ \superTok ->
        let maxProb = case M.elems (Br.tokDeph superTok) of
              [] -> 0.0
              xs -> maximum xs
            p = maxProb * beta
        in  limitDepsProbFor p superTok
    limitDepsProbFor p superTok = superTok
      { Br.tokDeph
          = M.fromList
          . filter ((>=p) . snd)
          . M.toList
          $ Br.tokDeph superTok
      }

    takeBest k xs
      = take k . reverse
      $ List.sortBy (comparing snd) xs

    readInput mayPath =
      case mayPath of
        Nothing -> LIO.getContents
        Just path -> LIO.readFile path


main :: IO ()
main =
  execParser optsExt >>= run
  where
    optsExt =
      info (helper <*> opts)
      ( fullDesc
        <> progDesc "Parsing with ParTAGe"
        <> header "partage"
      )


--------------------------------------------------
-- Anchoring
--------------------------------------------------


-- | Local tree type
type Tree =
  O.Tree  
    T.Text
    (Maybe (S.Set (Int, T.Text)))


-- | Tag anchoring function which:
--
--   (a) Joins identical trees with different terminals
--   (b) Replaces the weights by 0s (stems from (a))
--
anchorTagsIgnoreProbs
  :: [(Int, Br.SuperTok)]
  -> [(Tree, DAG.Weight)]
anchorTagsIgnoreProbs xs = do
  (tag, termSet) <- M.toList tagMap
  return (anchorTag (Just termSet) onTerm tag, 0)
  where
    tagMap = M.fromListWith S.union $ do
      (tokID, Br.SuperTok{..}) <- xs
      (tag, _weight) <- tokTags
      return (tag, S.singleton (tokID, tokWord))
    onTerm = \case
      Nothing -> Nothing
      Just _ -> error "Cannot process a co-anchor terminal node"


-- | A version of `anchorTagsIgnoreProbs` which preserves probabilities, but
-- does not join identical supertags.  Besides, it replaces each probability
-- `p` by `-log(p)`.  
--
-- WARNING: At the end, the minimum weight of a tree becoming a dependendent is
-- added to the corresponding weight.  This allows the new definition of the
-- amortized weight.
anchorTags
  :: [(Int, Br.SuperTok)]
  -> [(O.Tree T.Text (Maybe (Int, T.Text)), DAG.Weight)]
anchorTags =
  concatMap (uncurry anchor)
  where
    anchor tokID Br.SuperTok{..} = map
      ( Arr.first (anchorTag (Just (tokID, tokWord)) onTerm)
      -- . Arr.second (\p -> - (log p + log maxDepProb))
      . Arr.second (\p -> - (log p))
      )
      tokTags
--         where
--           maxDepProb =
--             case M.elems tokDeph of
--               [] -> error
--                 "partage.anchorTags: dependency weights not specified"
--               xs -> maximum xs
    onTerm = \case
      Nothing -> Nothing
      Just _ -> error "Cannot process a co-anchor terminal node"


-- | Anchor the given elementary tree with the given anchor terminal symbol.
anchorTag
  :: t
    -- ^ To substitute the anchor
  -> (Maybe T.Text -> t)
    -- ^ To map over standard terminals
  -> Br.Tree
  -> O.Tree T.Text t
anchorTag x f tree =
  case getSum (anchorNum tree) of
    1 -> doAnchor tree
    n -> error $ "anchorTag: number of anchors = " ++ show n
  where
    doAnchor = fmap . O.mapTerm $ \case
      Br.Anchor -> x
      Br.Term t -> f t
    anchorNum = F.foldMap $ \case
      O.Term Br.Anchor -> Sum (1 :: Int)
      _ -> Sum 0


--------------------------------------------------
-- Dependency Map
--------------------------------------------------

-- | Create the dependency map corresponding to the given list of tokens.  Note
-- that the `Br.deph` values have to be handled carefully -- in the
-- corresponding format, tokens are numbered from 1 and not from 0.
--
-- TODO: we may want to take the dummy ROOT word into account!
--
-- mkDepMap :: [(Int, Br.SuperTok)] -> M.Map Int Int
-- mkDepMap toks = M.fromList
--   [ (dep, hed - 1)
--   | (dep, Br.SuperTok{..}) <- toks
--   , (hed, _weight) <- tokDeph ]


-- | A variant of `mkDepMap` which creates a map of possible head positions
-- together with the corresponding heads.  A stub so far, really.
mkDepMap'
  :: Bool -- ^ Apply softmax to get probabilities from weights first
  -> [(Int, Br.SuperTok)]
  -> M.Map Int (M.Map Int DAG.Weight)
mkDepMap' applySM toks = M.fromList $ catMaybes
  [ (dep,) <$> do
      guard . not $ M.null tokDeph
      return $ mapMap
        (\k -> k-1)
        (\p -> -log(p))
        (trySoftMax tokDeph)
    | (dep, Br.SuperTok{..}) <- toks
  ] where
    trySoftMax = if applySM then softMax else id


-- | Map a function over keys and values of the given map.
mapMap
  :: (Ord k')
  => (k -> k')
  -> (v -> v')
  -> M.Map k v
  -> M.Map k' v'
mapMap f g m = M.fromList
  [ (f key, g val)
    | (key, val) <- M.toList m
  ]


-- | Apply softmax to the given map.
softMax
  :: (Ord k)
  => M.Map k Double
  -> M.Map k Double
softMax m =
  fmap (\x -> exp x / normFact) m
  where
    normFact = sum . map exp $ M.elems m


--------------------------------------------------
-- Rendering input (dummy mode)
--------------------------------------------------


-- | Render the given derivation.
renderInput :: [(Int, Br.SuperTok)] -> IO ()
renderInput inp = do
  forM_ inp $ \(tokID, Br.SuperTok{..}) -> do
    let takeBest df xs = 
          case List.sortBy (comparing snd) xs of
            [] -> df
            ys -> fst . head $ reverse ys
        depHed = takeBest (-1) (M.toList tokDeph)
        supTag = Br.anchor tokWord $
          takeBest (error "renderInput: no supertags") tokTags
    LIO.putStr . L.pack . show $ tokID
    LIO.putStr "\t"
    LIO.putStr $ L.fromStrict tokWord
    LIO.putStr "\t"
    LIO.putStr . L.pack . show $ depHed
    LIO.putStr "\t"
    LIO.putStrLn $ Br.showTree supTag


--------------------------------------------------
-- Rendering derivation
--------------------------------------------------


-- | Render the given derivation.
renderDeriv 
  :: D.Deriv D.UnNorm T.Text (A.Tok (Int, T.Text))
  -> IO ()
renderDeriv deriv0 = do
  let deriv = DG.fromDeriv deriv0
      tagMap = tagsFromDeriv deriv
      depMap = depsFromDeriv deriv
      getPos = L.pack . show . (+1) . A.position
      getTerm = L.fromStrict . snd . A.terminal
  forM_ (M.toList tagMap) $ \(tok, et) -> do
    LIO.putStr . L.intercalate "," $
      map getPos (S.toList tok)
    LIO.putStr "\t"
    LIO.putStr . L.intercalate "," $
      map getTerm (S.toList tok)
    LIO.putStr "\t"
    LIO.putStr . L.intercalate "," $
        maybe ["0"] (map getPos . S.toList) $
          M.lookup tok depMap
    LIO.putStr "\t"
    LIO.putStrLn . Br.showTree $ fmap rmTokID et


-- | Render the given derivation.
renderParse 
  :: D.Deriv D.UnNorm T.Text (A.Tok (Int, T.Text))
  -> IO ()
renderParse deriv
  = printIt
  . check
  $ parse
  where
    -- printIt = putStrLn  . R.drawTree . fmap show
    printIt = LIO.putStr . Br.showTree . fmap rmTokID'
    parse = fst $ D.toParse deriv
    check t =
      let posList = map A.position (catMaybes $ O.project t) in
      -- let posList = map A.position (O.project t) in
      if posList == List.sort posList
         then t
         else error "partage.renderParse: words not in order!"


-- renderParse' 
--   :: D.Deriv T.Text (A.Tok (Int, T.Text))
--   -> IO ()
-- renderParse' =
--   putStrLn
--     . R.drawTree . fmap show
--     . D.deriv4show . D.normalize


--------------------------------------------------
-- ETs from derivation
--------------------------------------------------


-- | Complex token.
type Tok t = S.Set (A.Tok t)


-- | Retrieve the list of selected ETs for the individual tokens.
tagsFromDeriv
  :: DG.Deriv n (A.Tok t)
  -> M.Map (Tok t) (O.Tree n (Maybe t))
tagsFromDeriv =
  go
    where
      go DG.Deriv{..} =
        let tok = getTok rootET
            chMap = M.unions . map go . concat $ M.elems modifs
        in  M.insert tok (fmap (O.mapTerm $ fmap A.terminal) rootET) chMap


-- | Retrieve the map of selected dependency heads.
depsFromDeriv
  :: DG.Deriv n (A.Tok t)
  -- -> M.Map (Tok t) (S.Set (Tok t))
  -> M.Map (Tok t) (Tok t)
depsFromDeriv =
  snd . go
    where
      go DG.Deriv{..} =
        let tok = getTok rootET
            children = map go . concat $ M.elems modifs
            chToks = map fst children
            chMap = M.unions $ map snd children
            newMap = List.foldl' (\m dep -> M.insert dep tok m) chMap chToks
        in  (tok, newMap)


-- | Determine the position set in the given tree.
getPos :: O.Tree n (A.Tok t) -> S.Set A.Pos
getPos = S.fromList . map A.position . O.project


-- | Determine the token set in the given tree.
getTok :: O.Tree n (Maybe (A.Tok t)) -> S.Set (A.Tok t)
getTok = S.fromList . catMaybes . O.project


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | Remove the k-th element in the list.
remove :: Int -> [a] -> [a]
remove k xs = take k xs ++ drop (k+1) xs


-- | Remove info about token IDs.
-- rmTokID :: O.Node n (Maybe (Int, t)) -> O.Node n (Maybe t)
rmTokID :: O.Node n (Maybe (Int, t)) -> O.Node n (Maybe t)
rmTokID = \case
  O.Term (Just (_, x)) -> O.Term (Just x)
  O.Term Nothing -> O.Term Nothing
  O.NonTerm x -> O.NonTerm x
  O.Sister x -> O.Sister x
  O.Foot x -> O.Foot x


-- | Remove info about token IDs.
rmTokID' :: O.Node n (Maybe (A.Tok (Int, t))) -> O.Node n (Maybe t)
rmTokID' = \case
  -- O.Term tok -> O.Term . snd $ A.terminal tok
  O.Term (Just tok) -> O.Term . Just . snd $ A.terminal tok
  O.Term Nothing -> O.Term Nothing
  O.NonTerm x -> O.NonTerm x
  O.Sister x -> O.Sister x
  O.Foot x -> O.Foot x


-- | Remove the repeating elements from the input list.
nub :: Ord a => [a] -> [a]
nub = S.toList . S.fromList
