{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}


-- import           Prelude hiding (words)
import           Control.Monad (forM_, when)
import           Data.Monoid ((<>))
import           Options.Applicative
import qualified Data.Set as S
import qualified Data.Tree as R
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as LIO

import qualified NLP.Partage.Tree.Other as O
import qualified NLP.Partage.DAG as DAG
import qualified NLP.Partage.AStar as A
import qualified NLP.Partage.Earley as E
import qualified NLP.Partage.Format.Brackets as Br


--------------------------------------------------
-- Global Options
--------------------------------------------------


data Command
    = Earley
      { inputPath :: FilePath
      , goldPath :: Maybe FilePath
      , startSym :: T.Text
      , showParses :: Maybe Int
      , brackets :: Bool
      , checkRepetitions :: Bool
      }
    -- ^ Parse the given sentences using the Earley-style chart parser
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
      (progDesc "Parse the input grammar file")
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
      super <- Br.parseSuper <$> LIO.readFile inputPath

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
          anchorTag tokID tokWord = Br.mapTerm $ \case
            Br.Anchor -> (tokID, tokWord)
            Br.Term _ -> error "Cannot process a co-anchor terminal node"
          anchorTags tokID Br.SuperTok{..} =
            map (anchorTag tokID tokWord) tokTags

          -- Create the compressed grammar representation
          gram
            = DAG.mkGram
            . map (,0)
            . concatMap (uncurry anchorTags)
            . zip [0 :: Int ..]
            $ sent

        -- Check against the gold file or perform simple recognition
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
            reco <- E.recognizeFrom gram startSym (E.fromList input)
            print reco

        -- Show the parsed trees
        case showParses of
          Nothing -> return ()
          Just k -> do
            parses <- E.parse gram startSym (E.fromList input)
            forM_ (take k parses) $ \tree -> do
              if brackets
                then do
                  LIO.putStrLn . Br.showTree . fmap rmTokID $ O.unTree tree
                else do
                  putStrLn ""
                  putStrLn . R.drawTree . fmap show $ O.unTree tree
            putStrLn ""


    RemoveCol{..} -> do
      file <- LIO.getContents
      forM_ (L.lines file)
        $ LIO.putStrLn
        . L.intercalate "\t"
        . remove (colNum-1)
        . L.splitOn "\t"


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
