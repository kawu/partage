module NLP.Partage.AStar.Base
  ( Pos
  -- * Input
  , Input (..)
  , Tok (..)
  , fromList
  -- * Utils
  , nonTerm
  , nonTerm'
  , labNonTerm
  )
where


import           Data.Function              (on)

import qualified NLP.Partage.DAG             as DAG
import qualified NLP.Partage.Tree.Other      as O
import           NLP.Partage.AStar.Auto      (Auto (..))


-- | A position in the input sentence.
type Pos = Int


--------------------------------------------------
-- Input
--------------------------------------------------


-- | Input of the parser.
newtype Input t = Input {
    -- inputSent :: V.Vector (S.Set t)
      inputSent :: [Tok t]
      -- ^ The input sentence
      -- WARNING: some functions (notably, `Deriv.tokenize`) assume
      -- that the input is a sequence, and not a word-lattice, for
      -- example.
    }


-- | A token is a terminal enriched with information about the position
-- in the input sentence.
data Tok t = Tok
  { position :: Int
    -- ^ Position of the node in the dependency tree
  , terminal :: t
    -- ^ Terminal on the corresponding position
  } deriving (Show)


instance Eq (Tok t) where
  (==) = (==) `on` position
instance Ord (Tok t) where
  compare = compare `on` position


-- -- | Input of the parser.
-- data Input t = Input {
--       inputSent :: V.Vector (S.Set t)
--     -- ^ The input sentence
--     , lexGramI  :: t -> S.Set t
--     -- ^ Lexicon grammar interface: each terminal @t@ in the
--     -- `inputSent` can potentially represent several different
--     -- terminals (anchors) at the level of the grammar.
--     -- If equivalent to `id`, no lexicon-grammar interface is used.
--     -- Otherwise, type @t@ represents both anchors and real terminals
--     -- (words from input sentences).
--     }


-- | Construct `Input` from a list of terminals.
fromList :: [t] -> Input t
fromList = Input . map (uncurry Tok) . zip [0..]
-- fromList = fromSets . map S.singleton


-- -- | Construct `Input` from a list of sets of terminals, each set
-- -- representing all possible interpretations of a given word.
-- fromSets :: [S.Set t] -> Input t
-- -- fromSets xs = Input (V.fromList xs) (\t -> S.singleton t)
-- fromSets xs = Input (V.fromList xs)


-- -- | Set the lexicon-grammar interface to
-- setLexGramI :: Input t ->


--------------------------------------------------
-- Utils
--------------------------------------------------


-- -- | Take the non-terminal of the underlying DAG node.
-- nonTerm :: Either n DID -> Hype n t -> n
-- nonTerm i =
--     check . nonTerm' i . gramDAG . automat
--   where
--     check Nothing  = error "nonTerm: not a non-terminal ID"
--     check (Just x) = x


-- | Take the non-terminal of the underlying DAG node.
nonTerm :: Either n DAG.DID -> Auto n t -> n
nonTerm i =
    check . nonTerm' i . gramDAG
  where
    check Nothing  = error "nonTerm: not a non-terminal ID"
    check (Just x) = x


-- | Take the non-terminal of the underlying DAG node.
nonTerm' :: Either n DAG.DID -> DAG.DAG (O.Node n t) w -> Maybe n
nonTerm' i dag = case i of
    Left rootNT -> Just rootNT
    Right did   -> labNonTerm =<< DAG.label did dag
    -- Right did   -> labNonTerm . DAG.label did -- . gramDAG . automat


-- | Take the non-terminal of the underlying DAG node.
labNonTerm :: O.Node n t -> Maybe n
labNonTerm (O.NonTerm y) = Just y
labNonTerm (O.Foot y) = Just y
labNonTerm _ = Nothing
