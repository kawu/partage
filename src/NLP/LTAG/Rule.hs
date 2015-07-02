{-# LANGUAGE RecordWildCards #-}


module NLP.LTAG.Rule where


import           Control.Applicative ((<$>))
import qualified Control.Monad.RWS.Strict   as RWS

import qualified NLP.FeatureStructure.Tree as FT

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


-- -- | Symbol: a (non-terminal, maybe identifier) pair addorned with
-- -- a feature structure. 
-- data Sym n i f a = Sym
--     { nonTerm :: n
--     , ide     :: Maybe SymID
--     , featStr :: FT.FN i f a }
--     deriving (Show, Eq, Ord)


-- -- | Show the symbol.
-- viewSym :: View n => Sym n -> String
-- viewSym (x, Just i) = "(" ++ view x ++ ", " ++ show i ++ ")"
-- viewSym (x, Nothing) = "(" ++ view x ++ ", _)"


-- -- | A spot of a node within an elementary tree.
-- data Spot a
--     = Root
--     -- ^ A root
--     | Vert
--     -- ^ A vertebra of a spine
--     | Leaf
--     -- ^ A leaf (or a foot)


-- | Label represent one of the following:
-- * A non-terminal
-- * A terminal
-- * A root of an auxiliary tree
-- * A foot node of an auxiliary tree
-- * A vertebra of the spine of the auxiliary tree
data Lab n t i f a
    = NonT
        { nonTerm   :: n
        , labID     :: Maybe SymID
        , featStr   :: FT.FN i f a }
    | Term t
    | AuxRoot
        { nonTerm   :: n
        , featStr   :: FT.FN i f a
        , footStr   :: FT.FN i f a }
    | AuxFoot
        -- ^ Feature structure of the foot is stored at the level
        -- of a root label. 
        { nonTerm   :: n }
    | AuxVert
        { nonTerm   :: n
        , symID     :: SymID
        , featStr   :: FT.FN i f a }
    deriving (Show, Eq, Ord)


-- -- | Show the label.
-- viewLab :: (View n, View t) => Lab n t -> String
-- viewLab (NonT s) = "N" ++ viewSym s
-- viewLab (Term t) = "T(" ++ view t ++ ")"
-- viewLab (Foot s) = "F" ++ viewSym s


-- | A rule for an elementary tree.
data Rule n t i f a = Rule {
    -- | The head of the rule.  TODO: should not be allowed to be
    -- a terminal or a foot.
      headR :: Lab n t i f a
    -- | The body of the rule
    , bodyR :: [Lab n t i f a]
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
    [] -> return $ NonT
        { nonTerm = labelI
        , labID   = Nothing
        , featStr = fsTree }
    _  -> do
        let xSym i = NonT 
              { nonTerm = labelI
              , labID   = i
              , featStr = fsTree }
        x <- if isTop
            then return $ xSym Nothing
            else xSym . Just <$> nextSymID
        xs <- mapM (treeRules False) subTrees
        keepRule $ Rule x xs
        return x
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
    fst <$> doit b auxTree auxFoot
  where
    doit _ G.INode{..} [] = return $
        ( AuxFoot {nonTerm = labelI}
        , fsTree )
    doit isTop G.INode{..} (k:ks) = do
        let (ls, bt, rs) = split k subTrees
        ls' <- mapM (treeRules False) ls
        (bt', _footStr) <- doit False bt ks
        rs' <- mapM (treeRules False) rs
        x <- if isTop
            then return $ AuxRoot
                { nonTerm = labelI
                , featStr = fsTree
                , footStr = _footStr }
            else nextSymID >>= \i -> return $ AuxVert
                { nonTerm = labelI
                , symID   = i
                , featStr = fsTree }
        keepRule $ Rule x $ ls' ++ (bt' : rs')
        return (x, _footStr)
    doit _ _ _ = error "auxRules: incorrect path"
    split =
        doit []
      where
        doit acc 0 (x:xs) = (reverse acc, x, xs)
        doit acc k (x:xs) = doit (x:acc) (k-1) xs
        doit acc _ [] = error "auxRules.split: index to high"
