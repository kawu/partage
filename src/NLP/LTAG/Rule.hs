{-# LANGUAGE RecordWildCards #-}


module NLP.LTAG.Rule where


import           Control.Applicative ((<$>))
-- import qualified Control.Monad.RWS.Strict   as RWS
import qualified Control.Monad.State.Strict   as E

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import           Data.List (intercalate)

import qualified Pipes as P

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
        , rootTopFS :: FT.FN i f a
        , rootBotFS :: FT.FN i f a }
    | Term t
    | AuxRoot
        { nonTerm   :: n
        , rootTopFS :: FT.FN i f a
        , rootBotFS :: FT.FN i f a
        , footTopFS :: FT.FN i f a
        , footBotFS :: FT.FN i f a }
    | AuxFoot
        -- ^ Feature structure of the foot is stored at the level
        -- of a root label.
        { nonTerm   :: n }
    | AuxVert
        { nonTerm   :: n
        , symID     :: SymID
        , rootTopFS :: FT.FN i f a
        , rootBotFS :: FT.FN i f a }
    deriving (Show)


-- | Show full info about the label.
viewLabFS
    :: (Ord i, View n, View t, View i, View f, View a)
    => Lab n t i f a
    -> String
viewLabFS lab = case lab of
    NonT{..} -> "N(" ++ view nonTerm
        ++ ( case labID of
                Nothing -> ""
                Just i  -> ", " ++ view i ) ++ ")"
        ++ "[t=" ++ showFS rootTopFS
        ++ ",b=" ++ showFS rootBotFS ++ "]"
    Term t -> "T(" ++ view t ++ ")"
    AuxRoot{..} -> "A(" ++ view nonTerm ++ ")"
        ++ "[t=" ++ showFS rootTopFS
        ++ ",b=" ++ showFS rootBotFS
        ++ ",ft=" ++ showFS footTopFS
        ++ ",fb=" ++ showFS footBotFS ++ "]"
    AuxFoot x -> "F(" ++ view x ++ ")"
    AuxVert{..} -> "V(" ++ view nonTerm ++ ", " ++ view symID ++ ")"
        ++ "[t=" ++ showFS rootTopFS
        ++ ",b=" ++ showFS rootBotFS ++ "]"
    where showFS = FT.showFN


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
    } deriving (Show)


-- | Print the state.
printRuleFS
    :: ( Ord i, View n, View t
       , View i, View f, View a )
    => Rule n t i f a -> IO ()
printRuleFS Rule{..} = do
    putStr $ viewLabFS headR
    putStr " -> "
    putStr $ intercalate " " $ map viewLabFS bodyR


--------------------------
-- Rule generation monad
--------------------------


-- | Identifier generation monad.
-- type RM n t i f a = RWS.RWS () [Rule n t i f a] Int
type RM n t i f a m = P.Producer (Rule n t i f a) (E.StateT Int m)


-- | Pull the next identifier.
nextSymID :: Monad m => RM n t i f a m SymID
nextSymID = E.state $ \i -> (i, i + 1)


-- | Save the rule in the writer component of the monad.
keepRule :: Monad m => Rule n t i f a -> RM n t i f a m ()
-- keepRule = RWS.tell . (:[])
keepRule = P.yield


-- | Evaluate the RM monad.
-- runRM :: RM n t i f a b -> (b, [Rule n t i f a])
-- runRM rm = RWS.evalRWS rm () 0
runRM :: Monad m => P.Effect (E.StateT Int m) a -> m a
runRM = flip E.evalStateT 0 . P.runEffect


-----------------------------------------
-- Tree Factorization
-----------------------------------------


-- | A feature is either a regular feature 'f' or a special feature.
type Feat f = Either f (Spec f)


-- A special feature contains a path to the "first" (to be defined
-- precisely) usage of the respective variable within the sub-forest.
data Spec f = Spec {
    -- | A path to the first occurance of the variable.
      path  :: [Int]
    -- | A feature path which leads to the variable.
    , feat  :: [f]
    -- | In top or bottom feature structure.
    , inTop :: Bool }
    deriving (Show, Eq, Ord)


instance View f => View (Spec f) where
    view = show


-- | Add a step to the path.
addStep :: Int -> Spec f -> Spec f
addStep x s = s {path = x : path s}


-- | Add a feature to the feature path.
addFeat :: f -> Spec f -> Spec f
addFeat x s = s {feat = x : feat s}


-- | Take an initial tree and factorize it into a list of rules.
treeRules
    :: (Monad m, Ord i, Ord f)
    => Bool         -- ^ Is it a top level tree?  `True' for
                    -- an entire initial tree, `False' otherwise.
    -> G.Tree n t i f a     -- ^ The tree itself
    -> RM n t i (Feat f) a m
        (Lab n t i (Feat f) a)
treeRules isTop G.INode{..} = case (subTrees, isTop) of
    ([], _) -> return $ NonT
        -- Foot or substitution node:
        { nonTerm = labelI
        , labID   = Nothing
        -- In theory one of the following should be an empty FS, but
        -- we can adopt a more general definition where both are
        -- non-empty.
        , rootTopFS = addNoFeats topFS
        , rootBotFS = addNoFeats botFS }
    (_, True) -> do
        -- Root node:
        let x = NonT 
              { nonTerm = labelI
              , labID   = Nothing
              , rootTopFS = addNoFeats topFS
              , rootBotFS = addNoFeats botFS }
        xs <- mapM (treeRules False) subTrees
        keepRule $ Rule x xs
        return x
    (_, False) -> do
        -- Internal node; top and bottom feature structures
        -- are split between different rules, dummy attributes
        -- have to be added in order to preserve relations between
        -- tree-local variables.
        i <- nextSymID
        -- First compute the set of all identifiers which occur
        -- in the `botFS` and the sub-trees.  These IDs will be
        -- kept as special attribute values in `rootTopFS`.
        --
        -- Compute the map from identifiers (occuring in the `botFS`
        -- and the sub-trees) to their addresses.  These IDs will be
        -- kept as special attribute values in `rootTopFS`.
--         let is = S.unions
--                 $ idsIn botFS
--                 : map idsInTree subTrees
        let is = M.union
                (idsInBot botFS)
                (idsInFor subTrees)
            x0 = NonT 
                { nonTerm = labelI
                , labID   = Just i
                , rootTopFS = FT.empty
                , rootBotFS = FT.empty }
            xb = x0
                { rootTopFS = addIdFeats is FT.empty
                , rootBotFS = addNoFeats botFS }
            xt = x0
                { rootTopFS = addIdFeats is topFS }
        xs <- mapM (treeRules False) subTrees
        keepRule $ Rule xb xs
        return xt
treeRules _ G.LNode{..} = return $ Term labelL


-----------------------------------------
-- Auxiliary Tree Factorization
-----------------------------------------


-- | Convert an auxiliary tree to a lower-level auxiliary
-- representation and a list of corresponding rules which
-- represent the "substitution" trees on the left and on the
-- right of the spine.
auxRules
    :: (Monad m, Ord i, Ord f)
    => Bool
    -> G.AuxTree n t i f a
    -- -> RM n t i f a (Lab n t i f a)
    -> RM n t i (Feat f) a m
        (Lab n t i (Feat f) a)
auxRules b G.AuxTree{..} =
    fst <$> doit b auxTree auxFoot
  where
    doit _ G.INode{..} [] = return $
        ( AuxFoot {nonTerm = labelI}
        -- We thread feature structures corresponding to the foot
        -- along the spine of the auxiliary tree.
        -- We thread the set of utilized identifiers as well.
        -- Foot FSs are only taken into account at the level of
        -- the root.
        , ((topFS, botFS), M.empty) )
    doit isTop G.INode{..} (k:ks) = do
        let (ls, bt, rs) = split k subTrees
        ls' <- mapM (treeRules False) ls
        (bt', (topBotFS, is0)) <- doit False bt ks
        rs' <- mapM (treeRules False) rs
        let is = M.unions
               [ idsInBot botFS
               -- TODO: This (-1) is a bit adhoc and dangeruos...
               -- Is it at least correct?
               , fmap (addStep (-1)) is0
               , idsInFor (ls ++ rs) ]
        -- In case of an internal node `xt` and `xb` are slighly
        -- different; for a root, they are the same:
        (xt, xb) <- if isTop
            then do
                let x = AuxRoot
                        { nonTerm = labelI
                        , rootTopFS = addNoFeats topFS
                        , rootBotFS = addNoFeats botFS
                        , footTopFS = addNoFeats $ fst topBotFS
                        , footBotFS = addNoFeats $ snd topBotFS }
                return (x, x)
            else nextSymID >>= \i -> do
                let x0 = AuxVert
                        { nonTerm = labelI
                        , symID   = i
                        , rootTopFS = FT.empty
                        , rootBotFS = FT.empty }
                    xb = x0
                        { rootTopFS = addIdFeats is FT.empty
                        , rootBotFS = addNoFeats botFS }
                    xt = x0
                        { rootTopFS = addIdFeats is topFS }
                return (xt, xb)
        keepRule $ Rule xb $ ls' ++ (bt' : rs')
        return ( xt,
            ( topBotFS
            -- We need to add the set of IDs from `topFS` here in
            -- order to keep the invariant that the set contains all
            -- IDs from the subtree corresponding to the currently
            -- visited node.
            , M.union (idsInTop topFS) is ) )
    doit _ _ _ = error "auxRules: incorrect path"
    split =
        doit []
      where
        doit acc 0 (x:xs) = (reverse acc, x, xs)
        doit acc k (x:xs) = doit (x:acc) (k-1) xs
        doit acc _ [] = error "auxRules.split: index to high"


-----------------------------------------
-- Dumm identifiers
-----------------------------------------


-- | Retrieve identifiers from an FS.
idsIn :: Ord i => Bool -> FT.FN i f a -> M.Map i (Spec f)
idsIn isTop FT.FN{..} =
    here `M.union` below
  where
    here = case ide of
        Just i -> M.singleton i $ Spec [] [] isTop
        Nothing -> M.empty
    below = case val of
        FT.Subs av -> avIds av
        FT.Atom x  -> M.empty
    avIds av = M.unions
        [ fmap (addFeat f) (idsIn isTop fn)
        | (f, fn) <- M.toList av ]


idsInTop :: Ord i => FT.FN i f a -> M.Map i (Spec f)
idsInTop = idsIn True


idsInBot :: Ord i => FT.FN i f a -> M.Map i (Spec f)
idsInBot = idsIn False


-- | Retrieve identifiers from an elementary tree.
idsInTree :: Ord i => G.Tree n l i f a  -> M.Map i (Spec f)
idsInTree G.INode{..} = M.unions
    [ idsInTop topFS
    , idsInBot botFS
    , idsInFor subTrees ]
idsInTree G.LNode{} = M.empty


-- | Retrieve identifiers in a forest.
idsInFor :: Ord i => [G.Tree n l i f a]  -> M.Map i (Spec f)
idsInFor
    = M.unions
    . map addStep'
    . zip [0..] 
    . map idsInTree
  where
    addStep' (i, ms) = fmap (addStep i) ms


-- | Add specifc ID features to an FS.
addIdFeats
    :: (Ord i, Ord f)
    => M.Map i (Spec f)
    -> FT.FN i f a
    -> FT.FN i (Feat f) a
addIdFeats =
    doFN
  where
    doFN is fn@FT.FN{} = fn {FT.val = doFT is (FT.val fn)}
    doFT is (FT.Subs av) = FT.Subs $ M.fromList $
        [ (Right sp, var i)
        | (i, sp) <- M.toList is ]
            ++
        [ (Left f, doFN M.empty fn)
        | (f, fn) <- M.toList av ]
    doFT _ (FT.Atom x) = FT.Atom x
    var i = FT.FN (Just i) (FT.Subs M.empty)


-- | Add no specific ID features to an FS.
addNoFeats
    :: (Ord i, Ord f)
    => FT.FN i f a
    -> FT.FN i (Feat f) a
addNoFeats = addIdFeats M.empty
