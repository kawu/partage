{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}


-- import           Prelude hiding (words)
import           Control.Monad (forM_)
import           Data.Monoid ((<>))
import           Options.Applicative
import qualified Data.Tree as R
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
-- import qualified Data.Text.Lazy as L
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
    = Early
      { inputPath :: FilePath
      , startSym  :: T.Text
      , showParses :: Maybe Int
      }
      -- ^ Parse the given sentences using the Early-style chart parser


--------------------------------------------------
-- Early options
--------------------------------------------------


earlyOptions :: Parser Command
earlyOptions = Early
  <$> strOption
  ( long "input"
    <> short 'i'
    <> metavar "FILE"
    <> help "Input file with sentences to parse"
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


--------------------------------------------------
-- Global options
--------------------------------------------------


opts :: Parser Command
opts = subparser
  ( command "early"
    (info (helper <*> earlyOptions)
      (progDesc "Parse the input grammar file")
    )
--     <> command "lexicon"
--     (info (helper <*> lexicOptions)
--       (progDesc "Parse and print the lexicon")
--     )
  )


-- | Run program depending on the cmdline arguments.
run :: Command -> IO ()
run cmd =
  case cmd of
    Early{..} -> do
      file <- LIO.readFile inputPath
      let super = Br.parseSuper file
      forM_ super $ \sent -> do
        let input = map Br.tokWord sent
            anchor Br.SuperTok{..} = map (Br.anchor tokWord) tokTags
            gram = map (,0) $ concatMap anchor sent
            dag = DAG.mkGram gram
        reco <- E.recognizeFrom dag startSym (E.fromList input)
        putStr "# "
        TIO.putStr $ T.unwords input
        LIO.putStr " => "
        print reco
        case showParses of
          Nothing -> return ()
          Just k -> do
            parses <- E.parse dag startSym (E.fromList input)
            forM_ (take k parses) $ \tree -> do
              putStrLn ""
              putStrLn . R.drawTree . fmap show . O.unTree $ tree
            -- putStrLn ""


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
