{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}


{- 
 - Early parser for TAGs: Rules.
 -}


module NLP.LTAG.Early3.Rule where


import           Control.Applicative ((<$>))
import           Control.Monad (void)
import qualified Control.Monad.RWS.Strict as S

import qualified Pipes as P

import qualified NLP.LTAG.Tree as G
import           NLP.LTAG.Early3.Core


----------------------
-- Initial Trees
----------------------


-- Each initial tree is factorized into a collection of flat CF
-- rules.  In order to make sure that this collection of rules
-- can be only used to recognize this particular tree, each
-- non-terminal is paired with additional identifier.
--
-- Within the context of substitution, both the non-terminal and
-- the identifier have to agree.  In case of adjunction, only the
-- non-terminals have to be equal.


-- | A rule for initial tree.
data Init n t = Init {
    -- | The head of the rule
      headI :: Sym n
    -- | The body of the rule
    , body  :: [Lab n t]
    } deriving (Show, Eq, Ord)


-- | A rule in general.
type Rule n t = Either (Init n t) (Aux n t)


--------------------------
-- Rule generation monad
--------------------------


-- | Identifier generation monad.
type RM n t a = S.RWS () [Rule n t] Int a


-- | Pull the next identifier.
nextID :: RM n t ID
nextID = S.state $ \i -> (i, i + 1)


-- | Save the rule in the writer component of the monad.
keepInit :: Init n t -> RM n t ()
keepInit = keepRule . Left


-- | Save the rule in the writer component of the monad.
keepAux :: Aux n t -> RM n t ()
keepAux = keepRule . Right


-- | Save the rule in the writer component of the monad.
keepRule :: Rule n t -> RM n t ()
keepRule = S.tell . (:[])


-- | Evaluate the RM monad.
runRM :: RM n t a -> (a, [Rule n t])
runRM rm = S.evalRWS rm () 0


-----------------------------------------
-- Tree Factorization
-----------------------------------------


-- | Take an initial tree and factorize it into a list of rules.
treeRules
    :: Bool         -- ^ Is it a top level tree?  `True' for
                    -- initial trees, `False' otherwise.
    -> G.Tree n t   -- ^ The tree itself
    -> RM n t (Lab n t)
treeRules isTop G.INode{..} = case subTrees of
    [] -> do
        let x = (labelI, Nothing)
        keepInit $ Init x []
        return $ Left x
    _  -> do
        x <- if isTop
            then return (labelI, Nothing)
            else (labelI,) . Just <$> nextID
        xs <- mapM (treeRules False) subTrees
        keepInit $ Init x xs
        return $ Left x
treeRules _ G.FNode{..} = return $ Right labelF


------------------------
-- Auxiliary Tree Rules
------------------------


-- | Auxiliary tree.
data Aux n t = Aux {
    -- | The head of the auxiliary rule. 
      headA :: Sym n
    -- | Labels on the left.
    , left  :: [Lab n t]
    -- | Following the spine of the auxiliary tree.
    -- `Nothing' if foot node.
    , down  :: Maybe (Sym n)
    -- | Labels on the right.
    , right :: [Lab n t]
    } deriving (Show, Eq, Ord)


-----------------------------------------
-- Auxiliary Tree Factorization
-----------------------------------------


-- | Convert an auxiliary tree to a lower-level auxiliary
-- representation and a list of corresponding rules which
-- represent the "substitution" trees on the left and on the
-- right of the spine.
auxRules :: Bool -> G.AuxTree n t -> RM n t (Maybe (Sym n))
auxRules b G.AuxTree{..} =
    doit b auxTree auxFoot
  where
    doit _ G.INode{..} [] = return Nothing
    doit isTop G.INode{..} (k:ks) = do
        let (ls, bt, rs) = split k subTrees
        x <- if isTop
            then return (labelI, Nothing)
            else (labelI,) . Just <$> nextID
        ls' <- mapM (treeRules False) ls
        bt' <- doit False bt ks
        rs' <- mapM (treeRules False) rs
        keepAux $ Aux x ls' bt' rs'
        return $ Just x
    doit _ _ _ = error "auxRules: incorrect path"
    split =
        doit []
      where
        doit acc 0 (x:xs) = (reverse acc, x, xs)
        doit acc k (x:xs) = doit (x:acc) (k-1) xs
        doit acc _ [] = error "auxRules.split: index to high"
