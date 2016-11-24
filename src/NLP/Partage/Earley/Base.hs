module NLP.Partage.Earley.Base
( Pos
-- * Input
, Input (..)
, Tok (..)
, fromList
, fromSets
-- * Utils
, nonTerm
, nonTerm'
, labNonTerm
-- * Unification
, Unify (..)
) where


import           Data.Function (on)
import qualified Data.Set as S
import qualified Data.Vector as V

import qualified NLP.Partage.DAG             as DAG
import qualified NLP.Partage.Tree.Other      as O
import           NLP.Partage.Earley.Auto     (Auto (..))


-- | A position in the input sentence.
type Pos = Int


--------------------------------------------------
-- Unificication type
--------------------------------------------------


-- | A class of types over which the unification computation can be performed.
class Unify v where
  -- | Unification function.  It can fail with `Nothing`, which means that the
  -- two given values do not unify.
  unify :: v -> v -> Maybe v

instance Unify () where
  unify _ _ = Just ()



--------------------------------------------------
-- Input
--------------------------------------------------


-- | Input of the parser.
newtype Input t v = Input {
      inputSent :: V.Vector (S.Set (t, v))
    -- ^ The input sentence
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


-- | Construct `Input` from a list of terminals.
fromList :: [(t, v)] -> Input t v
fromList = fromSets . map S.singleton


-- | Construct `Input` from a list of sets of terminals, each set
-- representing all possible interpretations of a given word.
fromSets :: [S.Set (t, v)] -> Input t v
fromSets xs = Input (V.fromList xs)


--------------------------------------------------
-- Utils
--------------------------------------------------


-- -- | Take the non-terminal of the underlying DAG node.
-- nonTerm :: Either n DID -> Hype n t -> n
-- nonTerm i hype =
--     case i of
--         Left rootNT -> rootNT
--         Right did   -> check $
--             DAG.label did (gramDAG $ automat hype)
--   where
--     check Nothing  = error "nonTerm: not a non-terminal ID"
--     check (Just x) = x


-- | Take the non-terminal of the underlying DAG node.
nonTerm :: DAG.DID -> Auto n t a -> n
-- nonTerm :: Either n DAG.DID -> Auto n t a -> n
nonTerm i =
    check . nonTerm' i . gramDAG
  where
    check Nothing  = error "nonTerm: not a non-terminal ID"
    check (Just x) = x


-- | Take the non-terminal of the underlying DAG node.
nonTerm' :: DAG.DID -> DAG.DAG (O.Node n t) a -> Maybe n
-- nonTerm' :: Either n DAG.DID -> DAG.DAG (O.Node n t) a -> Maybe n
nonTerm' did dag = labNonTerm =<< DAG.label did dag
-- nonTerm' i dag = case i of
--     Left rootNT -> Just rootNT
--     Right did   -> labNonTerm =<< DAG.label did dag
--     -- Right did   -> labNonTerm . DAG.label did -- . gramDAG . automat


-- | Take the non-terminal of the underlying DAG node.
labNonTerm :: O.Node n t -> Maybe n
labNonTerm (O.NonTerm y) = Just y
labNonTerm (O.Foot y) = Just y
labNonTerm _ = Nothing
