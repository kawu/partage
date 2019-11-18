{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}


module NLP.Partage.Format.Brackets
  (

    -- * Types
    Tree
  , NonTerm
  , Term(..)
  , LexTree
  , Super
  , SuperSent
  , SuperTok(..)

    -- * Anchoring
  , anchor

    -- * Parsing
  , parseTree
  , parseTree'
  , parseSuper
  , parseSuperProb

    -- * Rendering
  , showTree
  )
where


import           Control.Applicative ((<|>))
import           Control.Arrow (second)

-- import           Data.List (intersperse)
import           Data.Monoid (mconcat, mappend)
import qualified Data.Char as C
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Attoparsec.Text as Atto
import qualified Data.Tree as R
import qualified Data.Map.Strict as M

import qualified NLP.Partage.Tree.Other as O

-- import Debug.Trace (trace)


-------------------------------------------------------------
-- Core types
-------------------------------------------------------------


-- | Non-terminal
type NonTerm = T.Text


-- | Terminal or anchor
data Term
  = Term (Maybe T.Text)
      -- ^ `Nothing` represent an empty terminal
  | Anchor
  deriving (Show, Eq, Ord)


-- | Non-lexicalized tree (with anchor)
type Tree = O.Tree NonTerm Term


-- | Lexicalized tree (with the anchor lexicalized)
type LexTree = O.Tree NonTerm (Maybe T.Text)


-- | Supertagging token is a pair (word, tags), where:
--
--   * word -- word on the given position in the sentence
--   * tags -- list of possible supertags interpretation of the word +
--             the corresponding probabilities
--   * deph -- the position/probability of the dependency head(s)
--
data SuperTok = SuperTok
  { tokWord :: T.Text
  , tokTags :: [(Tree, Double)]
  , tokDeph :: M.Map Int Double
  } deriving (Show, Eq)


-- | Sentence after supertagging
type SuperSent = [SuperTok]


-- | List of sentences after supertagging
type Super = [SuperSent]


-- | Check if the probabilities in the token are correctly specified.
checkSuperTok :: T.Text -> SuperTok -> SuperTok
checkSuperTok tokTxt tok@SuperTok{..} =
  checkProb "tag" (map snd tokTags) $
  checkProb "dependency" (M.elems tokDeph) $
    tok
  where
    checkProb _   [] = id
    checkProb typ xs =
      assert typ (sum xs >= 0.1) .
      assert typ (all (>=0.0) xs) .
      assert typ (all (<=1.0) xs)
    assert typ cond x
      | cond = x
      | otherwise = error $
          typ ++ " probabilities in the following " ++
          "are incorrect: " ++ T.unpack tokTxt
--     equal x y =
--       x - eps <= y && x + eps >= y
--     eps = 0.1


-------------------------------------------------------------
-- Anchoring
-------------------------------------------------------------


-- | Replace the anchor with the given terminal.
anchor :: T.Text -> Tree -> LexTree
anchor lx =
  fmap onNode
  where
    onNode (O.Term Anchor) = O.Term (Just lx)
    onNode (O.Term (Term x)) = O.Term x
    onNode (O.NonTerm x) = O.NonTerm x
    onNode (O.Sister x) = O.Sister x
    onNode (O.Foot x) = O.Foot x


-------------------------------------------------------------
-- Tree Parsing
-------------------------------------------------------------


-- | Parse a tree in the bracketed format.
parseTree :: T.Text -> Either String Tree
parseTree = Atto.parseOnly (treeP <* Atto.endOfInput)


-- | Version of `parseTree` which fails if the input is incorrectly formatted.
parseTree' :: T.Text -> Tree
parseTree' txt =
  case parseTree txt of
    Left err -> error $ unlines
      [ "Brackets.parseTree': failed to parsed with the following error:"
      , err ]
    Right x -> x


-- | Parse a tree in bracketed format. Only anchors are allowed as terminals.
treeP :: Atto.Parser Tree
treeP = emptyP <|> emptyP' <|> nodeP <|> leafP


forestP :: Atto.Parser [Tree]
forestP = treeP `Atto.sepBy` Atto.skipMany Atto.space


-- | Non-leaf tree.
nodeP :: Atto.Parser Tree
nodeP = between '(' ')' $ do
  (nonTerm, starred) <- nonTermP
  Atto.skipWhile C.isSpace
  subTrees <- forestP
  let nodeLabel =
        if starred && null subTrees
        then O.Foot nonTerm
        else if starred
             then O.Sister nonTerm
             else O.NonTerm nonTerm
  return $ R.Node nodeLabel subTrees


leafP :: Atto.Parser Tree
leafP =
  leaf <$> (anchorP <|> terminalP)
  where
    leaf x = R.Node (O.Term x) []


terminalP :: Atto.Parser Term
terminalP =
  Term . Just <$> Atto.takeWhile1 pr
  where
    pr c = not $ C.isSpace c || elem c [')', '(']


emptyP :: Atto.Parser Tree
emptyP = do
  _ <- Atto.string "-NONE-"
  return $ R.Node (O.Term $ Term Nothing) []


emptyP' :: Atto.Parser Tree
emptyP' = between '(' ')' $ do
  _ <- Atto.string "-NONE-"
  Atto.skipWhile C.isSpace
  return $ R.Node (O.Term $ Term Nothing) []


anchorP :: Atto.Parser Term
anchorP = Anchor <$ Atto.string "<>"


-- | Parses a non-terminal + information if it's marked with a star
-- (sister/foot).
nonTermP :: Atto.Parser (NonTerm, Bool)
nonTermP = do
  nonTerm <- Atto.takeTill $ \c -> C.isSpace c || c == '*' || c == ')'
  starred <- (True <$ Atto.char '*') <|> pure False
  return (nonTerm, starred)


-------------------------------------------------------------
-- Super Parsing
-------------------------------------------------------------


parseSuperTok :: T.Text -> SuperTok
parseSuperTok xs =
  case T.splitOn "\t" xs of
    [] -> error "Brackets.parseSuperTok: empty line"
    [_] -> error "Brackets.parseSuperTok: no supertags"
    [_, _] -> error "Brackets.parseSuperTok: no dependency head"
    word : deph : tags -> SuperTok
      { tokWord = word
      , tokTags = map ((,0) . parseTree') tags
      , tokDeph = M.singleton (read (T.unpack deph)) 0.0
      }


-- | Parse a sentence in a supertagged file.
parseSuperSent :: T.Text -> SuperSent
parseSuperSent = map parseSuperTok . T.lines


-- | Parse a supertagged file.
parseSuper :: L.Text -> Super
parseSuper
  = map (parseSuperSent . L.toStrict)
  . filter realSent
  . L.splitOn "\n\n"
  where
    realSent = not . L.null


-------------------------------------------------------------
-- Super Parsing with Probabilities
-------------------------------------------------------------


-- | Parse the tree in the bracketed format with a probability put on the right
-- after the colon.
parseTreeProb :: T.Text -> (Tree, Double)
parseTreeProb txt =
  case T.breakOn ":" (T.reverse txt) of
    (probTxt, treeTxt) ->
      ( parseTree' (T.reverse $ T.tail treeTxt)
      , case TR.double (T.reverse probTxt) of
          Right (prob, "") -> prob
          _ -> error "Brackets.parseTreeProb: failed to parse probability"
      )


parseSuperTokProb :: T.Text -> SuperTok
parseSuperTokProb xs = checkSuperTok xs $
  case T.splitOn "\t" xs of
    [] -> error "Brackets.parseSuperTok: empty line"
    [_] -> error "Brackets.parseSuperTok: no supertags"
    [_, _] -> error "Brackets.parseSuperTok: no dependency head"
    _id : word : deph : tags -> SuperTok
      { tokWord = word
      , tokTags = map parseTreeProb tags
      , tokDeph = parseDeph $ T.strip deph
      }


-- | Parse a sentence in a supertagged file.
parseSuperSentProb :: T.Text -> SuperSent
parseSuperSentProb = map parseSuperTokProb . T.lines


-- | Parse a supertagged file.
parseSuperProb :: L.Text -> Super
parseSuperProb
  = map (parseSuperSentProb . L.toStrict)
  . filter realSent
  . L.splitOn "\n\n"
  where
    realSent = not . L.null


parseDeph :: T.Text -> M.Map Int Double
parseDeph str
  | T.null str = M.empty
  | otherwise = M.fromList
      [ ( read $ T.unpack depStr
        , case TR.double depProb of
            Right (prob, "") -> prob
            _ -> error $ "Brackets.parseDeph: failed to parse probability " 
              ++ T.unpack depProb
        )
      | one <- T.splitOn "|" str
      , let (depStr, depProb) = 
              second T.tail $ T.breakOn ":" one
      ]


-------------------------------------------------------------
-- Tree Rendering
-------------------------------------------------------------


-- | Render the given lexicalized tree in the bracketed format.
showTree :: LexTree -> L.Text
showTree = B.toLazyText . buildTree


buildTree :: LexTree -> B.Builder
buildTree tree
  | isTerm (R.rootLabel tree) =
      buildLabel (R.rootLabel tree)
  | otherwise = mconcat
      [ "("
      , buildLabel (R.rootLabel tree)
      , buildForest (R.subForest tree)
      , ")"
      ]


buildForest :: [LexTree] -> B.Builder
buildForest =
  mconcat . map (mappend " " . buildTree)
  -- mconcat . intersperse " " . map buildTree


buildLabel :: O.Node NonTerm (Maybe T.Text) -> B.Builder
buildLabel = \case
  O.NonTerm x -> B.fromText x
  O.Term (Just x) -> B.fromText x
  O.Term Nothing -> "-NONE-" -- B.fromText 
  O.Sister x -> B.fromText x `mappend` "*"
  O.Foot x -> B.fromText x `mappend` "*"


isTerm :: O.Node NonTerm (Maybe T.Text) -> Bool
isTerm = \case
  O.Term _ -> True
  _ -> False


-------------------------------------------------------------
-- Utils
-------------------------------------------------------------


between :: Char -> Char -> Atto.Parser a -> Atto.Parser a
between p q par = do
  _ <- Atto.char p
  x <- par
  _ <- Atto.char q
  return x
