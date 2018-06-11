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
      { startSym  :: T.Text
      , showParses :: Maybe Int
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
  <$> (fmap T.pack . strOption)
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
      file <- LIO.getContents
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
