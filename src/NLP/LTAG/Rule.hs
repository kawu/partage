{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}


module NLP.LTAG.Rule where


import           Control.Applicative ((<$>))
import qualified Control.Monad.RWS.Strict   as RWS

import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)

import qualified NLP.FeatureStructure.Tree as FT
import qualified NLP.FeatureStructure.Graph as FG

import           NLP.LTAG.Core
import qualified NLP.LTAG.Tree2 as G


----------------------
-- Initial Trees
----------------------


-- Each initial tree is factorized into a collection of flat CF
-- rules.  In order to make sure that this collection of rules
-- can be only used to recognize this particular tree, each
-- non-terminal is paired with an additional identifier.
--
-- Within the context of substitution, both the non-terminal and
-- the identifier have to agree.  In case of adjunction, only the
-- non-terminals have to be equal.


-- | Additional symbol identifier.
type SymID = Int


-- | Symbol: a (non-terminal, maybe identifier) pair addorned with
-- a feature structure. 
data Sym n i f a = Sym
    { nonTerm :: n
    , ide     :: Maybe SymID
    , featStr :: FT.FN i f a }
    deriving (Show, Eq, Ord)


-- -- | Show the symbol.
-- viewSym :: View n => Sym n -> String
-- viewSym (x, Just i) = "(" ++ view x ++ ", " ++ show i ++ ")"
-- viewSym (x, Nothing) = "(" ++ view x ++ ", _)"


-- | Label: a symbol, a terminal or a generalized foot node.
-- Generalized in the sense that it can represent not only a foot
-- note of an auxiliary tree, but also a non-terminal on the path
-- from the root to the real foot note of an auxiliary tree.
data Lab n t i f a
    = NonT (Sym n i f a)
    | Term t
    | Foot (Sym n i f a)
    deriving (Show, Eq, Ord)


-- -- | Show the label.
-- viewLab :: (View n, View t) => Lab n t -> String
-- viewLab (NonT s) = "N" ++ viewSym s
-- viewLab (Term t) = "T(" ++ view t ++ ")"
-- viewLab (Foot s) = "F" ++ viewSym s


-- | A rule for an elementary tree.
data Rule n t i f a = Rule {
    -- | The head of the rule
      headR :: Sym n i f a
    -- | The body of the rule
    , bodyR  :: [Lab n t i f a]
    } deriving (Show, Eq, Ord)


--------------------------
-- Rule generation monad
--------------------------


-- | Identifier generation monad.
type RM n t i f a = RWS.RWS () [Rule n t i f a] Int


-- | Pull the next identifier.
nextSymID :: RM n t i f a SymID
nextSymID = RWS.state $ \i -> (i, i + 1)


-- | Save the rule in the writer component of the monad.
keepRule :: Rule n t i f a -> RM n t i f a ()
keepRule = RWS.tell . (:[])


-- | Evaluate the RM monad.
runRM :: RM n t i f a b -> (b, [Rule n t i f a])
runRM rm = RWS.evalRWS rm () 0


-----------------------------------------
-- Tree Factorization
-----------------------------------------


-- | Take an initial tree and factorize it into a list of rules.
treeRules
    :: Bool         -- ^ Is it a top level tree?  `True' for
                    -- an entire initial tree, `False' otherwise.
    -> G.Tree n t i f a     -- ^ The tree itself
    -> RM n t i f a (Lab n t i f a)
treeRules isTop G.INode{..} = case subTrees of
    [] -> return $ NonT $ Sym
        { nonTerm = labelI
        , ide     = Nothing
        , featStr = fsTree }
    _  -> do
        let xSym i = Sym 
              { nonTerm = labelI
              , ide = i
              , featStr = fsTree }
        x <- if isTop
            then return $ xSym Nothing
            else xSym . Just <$> nextSymID
        xs <- mapM (treeRules False) subTrees
        keepRule $ Rule x xs
        return $ NonT x
treeRules _ G.LNode{..} = return $ Term labelL


-----------------------------------------
-- Auxiliary Tree Factorization
-----------------------------------------


-- | Convert an auxiliary tree to a lower-level auxiliary
-- representation and a list of corresponding rules which
-- represent the "substitution" trees on the left and on the
-- right of the spine.
auxRules
    :: Bool
    -> G.AuxTree n t i f a
    -> RM n t i f a (Lab n t i f a)
auxRules b G.AuxTree{..} =
    doit b auxTree auxFoot
  where
    doit _ G.INode{..} [] = return $ Foot $ Sym
        { nonTerm = labelI
        , ide     = Nothing
        , featStr = fsTree }
    doit isTop G.INode{..} (k:ks) = do
        let (ls, bt, rs) = split k subTrees
        let xSym i = Sym 
              { nonTerm = labelI
              , ide = i
              , featStr = fsTree }
        x <- if isTop
            then return $ xSym Nothing
            else xSym . Just <$> nextSymID
        ls' <- mapM (treeRules False) ls
        bt' <- doit False bt ks
        rs' <- mapM (treeRules False) rs
        keepRule $ Rule x $ ls' ++ (bt' : rs')
        return $ Foot x
    doit _ _ _ = error "auxRules: incorrect path"
    split =
        doit []
      where
        doit acc 0 (x:xs) = (reverse acc, x, xs)
        doit acc k (x:xs) = doit (x:acc) (k-1) xs
        doit acc _ [] = error "auxRules.split: index to high"


--------------------------
-- Internal rule
--------------------------


-- | A feature graph identifier, i.e. an identifier used to refer
-- to individual nodes in a FS.
type FID = Int


-- | Symbol: a (non-terminal, maybe identifier) pair addorned with
-- a feature structure. 
data ISym n f a = ISym
    { nonTermI :: n
    , ideI     :: Maybe SymID
    , fgID     :: FID }
    deriving (Show, Eq, Ord)


-- | Label: a symbol, a terminal or a generalized foot node.
-- Generalized in the sense that it can represent not only a foot
-- note of an auxiliary tree, but also a non-terminal on the path
-- from the root to the real foot note of an auxiliary tree.
data ILab n t f a
    = INonT (ISym n f a)
    | ITerm t
    | IFoot (ISym n f a)
    deriving (Show, Eq, Ord)


-- | A rule for an elementary tree.
data IRule n t f a = IRule {
    -- | The head of the rule
      headI :: ISym n f a
    -- | The body of the rule
    , bodyI :: [ILab n t f a]
    -- | The underlying feature graph.
    , graphI :: FG.Graph f a
    } deriving (Show, Eq, Ord)


-- | Compile a regular rule to an internal rule.
compile :: (Ord i, Ord f, Eq a) => Rule n t i f a -> IRule n t f a
compile Rule{..} = unJust $ do
    (is, g) <- FT.compiles $ FNode
        (featStr headR)
        (fromBody bodyR) 
    (rh, rb) <- unCons is
    return $ IRule
        { headI = mkISym headR rh
        , bodyI = mergeBody bodyR rb
        , graphI = g }
  where
    fromBody [] = FNil
    fromBody (x:xs) = ($ fromBody xs) $ case x of
        NonT y -> FNode $ featStr y
        Term _ -> FGap
        Foot y -> FNode $ featStr y
    mergeBody (NonT x : xs) (FNode i is) =
        INonT (mkISym x i) : mergeBody xs is
    mergeBody (Term t : xs) (FGap is) =
        ITerm t : mergeBody xs is
    mergeBody (Foot x : xs) (FNode i is) =
        IFoot (mkISym x i) : mergeBody xs is
    mergeBody _ _ = error "compile.mergeBody: unexpected case"
    mkISym Sym{..} i = ISym
        { nonTermI = nonTerm
        , ideI = ide
        , fgID = i }


--------------------------
-- Utility
--------------------------


-- | Retrieve the Just value.  Error otherwise.
unJust :: Maybe a -> a
unJust (Just x) = x
unJust Nothing = error "unJust: got Nothing!" 


-- | A list with potential gaps.
data FList a
    = FNil
    | FGap (FList a)
    | FNode a (FList a) 
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


-- | Uncons the FList.  Ignore the leading gaps.
unCons :: FList a -> Maybe (a, FList a)
unCons FNil = Nothing
unCons (FGap xs) = unCons xs
unCons (FNode x xs) = Just (x, xs)
