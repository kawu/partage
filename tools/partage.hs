{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}


-- import           Prelude hiding (words)
import           Control.Monad (forM_, when)
import qualified Control.Arrow as Arr
import           Data.Monoid ((<>))
import           Options.Applicative
import qualified Data.IORef as IORef
-- import qualified Data.List as List
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
import qualified NLP.Partage.AStar.Deriv as D
import qualified NLP.Partage.Earley as E
import qualified NLP.Partage.Format.Brackets as Br

-- import Debug.Trace (trace)


--------------------------------------------------
-- Global Options
--------------------------------------------------


data Command
    = Earley
      { inputPath :: FilePath
      , withProb :: Bool
      , maxTags :: Maybe Int
      , minProb :: Maybe Double
      , betaParam :: Maybe Double
      , goldPath :: Maybe FilePath
      , startSym :: T.Text
      , showParses :: Maybe Int
      , showParseNum :: Maybe Int
      , brackets :: Bool
      , checkRepetitions :: Bool
      , maxLen :: Maybe Int
      }
    -- ^ Parse the input sentences using the Earley-style chart parser
    | AStar
      { inputPath :: FilePath
      , maxTags :: Maybe Int
      , minProb :: Maybe Double
      , betaParam :: Maybe Double
      , startSym :: T.Text
      , fullHype :: Bool
      , maxLen :: Maybe Int
--       , showParses :: Maybe Int
--       , brackets :: Bool
--       , checkRepetitions :: Bool
      }
    -- ^ Parse the input sentences using the Earley-style A* chart parser
    | RemoveCol
      { colNum :: Int
      }
    -- ^ Remove the given column from .tsv file


--------------------------------------------------
-- Options
--------------------------------------------------


earleyOptions :: Parser Command
earleyOptions = Earley
  <$> strOption
  ( long "input"
    <> short 'i'
    <> help "Input file with supertagging results"
  )
  <*> switch
  ( long "with-prob"
    -- <> short 'p'
    <> help "Set on if the input file contains info about probabilities"
  )
  <*> (optional . option auto)
  ( long "max-tags"
    <> short 'm'
    <> help "Maximum number of the most probable supertags to take"
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
  <*> (fmap T.pack . strOption)
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
  <$> strOption
  ( long "input"
    <> short 'i'
    <> help "Input file with supertagging results"
  )
  <*> (optional . option auto)
  ( long "max-tags"
    <> short 'm'
    <> help "Maximum number of the most probable supertags to take"
  )
  <*> (optional . option auto)
  ( long "min-prob"
    <> help "Minimum probability of a supertag to take"
  )
  <*> (optional . option auto)
  ( long "beta"
    <> help "Beta parameter à la Clark & Curran"
  )
  <*> (fmap T.pack . strOption)
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


removeColOptions :: Parser Command
removeColOptions = RemoveCol
  <$> option auto
  ( long "colnum"
    <> short 'c'
    <> help "Column to remove"
  )


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
      let parseSuper =
            if withProb
            then Br.parseSuperProb
            else Br.parseSuper
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
        <$> LIO.readFile inputPath

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
          -- Calculate the position map (mapping from tokens to their
          -- positions)
          posMap = M.fromList [(x, fst x) | x <- input]

          -- Create the compressed grammar representation
          gram
            = DAG.mkGram
            -- . (\xs -> trace (show $ length xs) xs)
            . anchorTags'
            -- . anchorTagsIgnoreProbs
            . zip [0 :: Int ..]
            $ sent

          -- Create the corresponding position map
          depMap = mkDepMap $ zip [0 :: Int ..] sent

        -- Check against the gold file or perform simple recognition
        putStr "# "
        TIO.putStr . T.unwords $ map snd input
        LIO.putStr " => "
        case goldTree of
          Just tree -> do
            parses <- map (fmap rmTokID . O.unTree) <$>
              E.parse gram startSym posMap depMap (E.fromList input)
            print (tree `elem` parses)
            when (checkRepetitions && length parses /= length (nub parses)) $ do
              putStrLn "WARNING: repetitions in the set of parsed trees!"
          Nothing -> do
            -- reco <- E.recognizeFrom gram startSym (E.fromList input)
            begTime <- Time.getCurrentTime
            hype <- E.earley gram posMap depMap (E.fromList input)
            let n = length input
                reco = (not.null) (E.finalFrom startSym n hype)
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
                putStr "\t"
                parses <- E.parse gram startSym posMap depMap (E.fromList input)
                putStr . show $ sum
                  -- We have to evaluate them to alleviate the memory leak
                  [ L.length txtTree `seq` (1 :: Int)
                  | tree <- take k parses
                  , let txtTree = (Br.showTree . fmap rmTokID $ O.unTree tree)
                  ]
            putStrLn ""

        -- Show the parsed trees
        case showParses of
          Nothing -> return ()
          Just k -> do
            parses <- E.parse gram startSym posMap depMap (E.fromList input)
            forM_ (take k parses) $ \tree -> do
              if brackets
                then do
                  LIO.putStrLn . Br.showTree . fmap rmTokID $ O.unTree tree
                else do
                  putStrLn ""
                  putStrLn . R.drawTree . fmap show $ O.unTree tree
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
        . limitTagsBeta betaParam
        . limitTagsNum maxTags
        . parseSuper
        <$> LIO.readFile inputPath

      forM_ super $ \sent -> do

        let
          -- Add token IDs in order to distinguish tokens with identical word
          -- forms (which may have different supertags)
          input = zip [0 :: Int ..] (map Br.tokWord sent)
          inputVect = V.fromList (map Br.tokWord sent)

          -- Create the compressed grammar representation
          gram
            = DAG.mkGram
            . anchorTags
            . zip [0 :: Int ..]
            $ sent
          automat = A.mkAuto memoTerm gram
          memoTerm = Memo.wrap
            (\i -> (i, inputVect V.! i))
            (\(i, _w) -> i)
            Memo.integral

        -- Check against the gold file or perform simple recognition
        putStr "# "
        TIO.putStr . T.unwords $ map snd input
        LIO.putStr " => "

        begTime <- Time.getCurrentTime
        hypeRef <- IORef.newIORef Nothing
        let n = length input
            consume = do
              A.HypeModif{..} <- P.await
              case (modifType, modifItem) of
                (A.NewNode, A.ItemP p) ->
                  if (D.isFinal_ startSym n p) then do
                    semiTime <- P.liftIO Time.getCurrentTime
                    P.liftIO . IORef.writeIORef hypeRef $ Just (modifHype, semiTime)
                    if fullHype
                      then consume
                      else return modifHype
                  else consume
                _ -> consume
        finalHype <- P.runEffect $
          A.earleyAutoP automat (A.fromList input)
          P.>-> consume
        endTime <- Time.getCurrentTime
        (semiHype, semiTime) <- maybe (finalHype, endTime) id
          <$> IORef.readIORef hypeRef
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


    RemoveCol{..} -> do
      file <- LIO.getContents
      forM_ (L.lines file)
        $ LIO.putStrLn
        . L.intercalate "\t"
        . remove (colNum-1)
        . L.splitOn "\t"

  where

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
    limitTagsNum = \case
      Nothing -> id
      Just m -> map . map $ \superTok -> superTok
        {Br.tokTags = take m (Br.tokTags superTok)}


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


-- | Tag anchoring function which:
--
--   (a) Joins identical trees with different terminals
--   (b) Replaces the weights by 0s (stems from (a))
--
anchorTagsIgnoreProbs
  :: [(Int, Br.SuperTok)]
  -> [(O.Tree T.Text (S.Set (Int, T.Text)), DAG.Weight)]
anchorTagsIgnoreProbs xs = do
  (tag, termSet) <- M.toList tagMap
  return (anchorTag termSet tag, 0)
  where
    tagMap = M.fromListWith S.union $ do
      (tokID, Br.SuperTok{..}) <- xs
      (tag, _weight) <- tokTags
      return (tag, S.singleton (tokID, tokWord))


-- | A version of `anchorTagsIgnoreProbs` which preserves probabilities, but
-- does not join identical supertags.  Besides, it replaces each probability
-- `p` by `-log(p)`.
anchorTags
  :: [(Int, Br.SuperTok)]
  -> [(O.Tree T.Text (Int, T.Text), DAG.Weight)]
anchorTags =
  concatMap (uncurry anchor)
  where
    anchor tokID Br.SuperTok{..} = map
      ( Arr.first (anchorTag (tokID, tokWord))
      . Arr.second (\p -> -log(p))
      )
      tokTags


-- | A version of `anchorTags`.
anchorTags'
  :: [(Int, Br.SuperTok)]
  -> [(O.Tree T.Text (S.Set (Int, T.Text)), DAG.Weight)]
anchorTags' =
  concatMap (uncurry anchor)
  where
    anchor tokID Br.SuperTok{..} = map
      ( Arr.first (anchorTag $ S.singleton (tokID, tokWord))
      . Arr.second (\p -> -log(p))
      )
      tokTags


anchorTag :: t -> Br.Tree -> O.Tree T.Text t
anchorTag x = fmap . O.mapTerm $ \case
  Br.Anchor -> x
  Br.Term _ -> error "Cannot process a co-anchor terminal node"


-- | Create the dependency map corresponding to the given list of tokens.  Note
-- that the `Br.deph` values have to be handled carefully -- in the
-- corresponding format, tokens are numbered from 1 and not from 0.
mkDepMap :: [(Int, Br.SuperTok)] -> M.Map Int Int
mkDepMap toks = M.fromList
  [ (pos, tokDeph - 1)
  | (pos, Br.SuperTok{..}) <- toks ]


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | Remove the k-th element in the list.
remove :: Int -> [a] -> [a]
remove k xs = take k xs ++ drop (k+1) xs


-- | Remove info about token IDs.
rmTokID :: O.Node n (Int, t) -> O.Node n t
rmTokID = \case
  O.Term (_, x) -> O.Term x
  O.NonTerm x -> O.NonTerm x
  O.Sister x -> O.Sister x
  O.Foot x -> O.Foot x


-- | Remove the repeating elements from the input list.
nub :: Ord a => [a] -> [a]
nub = S.toList . S.fromList
