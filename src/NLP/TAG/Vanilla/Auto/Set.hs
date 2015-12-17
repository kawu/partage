{-# LANGUAGE RecordWildCards #-}


-- | A version in which a separate (abstract) automaton is built for
-- each distinct rule head symbol.


module NLP.TAG.Vanilla.Auto.Set where


import           Control.Applicative ((<$>))
import           Control.Monad (forM)
import qualified Control.Monad.State.Strict as E
-- -- import           Control.Monad.Trans.Class (lift)

import           Data.Maybe (maybeToList)
import qualified Data.Set                   as S
import qualified Data.Map.Strict            as M

import           Data.DAWG.Gen.Types (ID)

import           NLP.TAG.Vanilla.Rule
    ( Lab(..), Rule(..) )


import qualified NLP.TAG.Vanilla.Auto.Mini as A
-- import qualified NLP.TAG.Vanilla.Auto.Shell as Sh
import           NLP.TAG.Vanilla.Auto.Edge (Edge(..))


-- import qualified NLP.TAG.Vanilla.Auto.DAWG as A


--------------------------------------------------
-- Interface
--------------------------------------------------


-- -- | DAWG as automat with one parameter.
-- newtype Auto a = Auto { unAuto :: D.DAWG a () }


shell :: (Ord a) => AutoSet a -> A.Auto a
shell AutoSet{..} = A.Auto
    { roots  = rootSet
    , follow = \i x -> do
        (auto, j) <- M.lookup i nodeMap
        A.follow auto j x
    , edges  = \i -> do
        (auto, j) <- maybeToList (M.lookup i nodeMap)
        A.edges auto j
    }


--------------------------------------------------
-- Implementation
--------------------------------------------------


-- | A collection of DFAs.
data AutoSet a = AutoSet
    { rootSet   :: S.Set ID
    -- ^ A set of roots
    , nodeMap   :: M.Map ID (A.Auto a, ID)
    -- ^ For a given external ID, an automaton it corresponds to
    -- and the corresponding internal ID (in this automaton)
    }


-- | Build automata from the given grammar.
buildAuto
    :: (Ord n, Ord t)
    => S.Set (Rule n t)
        -- ^ The grammar to compress
    -> (S.Set (Rule n t) -> A.Auto (Edge (Lab n t)))
        -- ^ The underlying automaton construction method
    -> AutoSet (Edge (Lab n t))
buildAuto gram mkAuto = runM $ do
    (rootSets, nodeMaps) <- unzip <$> mapM reID
        [ ruleSet
        | (_headSym, ruleSet) <- M.toList gramByHead ]
    return AutoSet
        { rootSet   = S.unions rootSets
        , nodeMap   = M.unions nodeMaps }
  where
    -- grammar divided by heads
    gramByHead = M.fromList
        [ (nonTerm (headR r), r)
        | r <- S.toList gram ]
    -- reidentification
    reID ruleSet = do
        auto <- mkAuto ruleSet
        nodeMap <- M.fromList <$>
            forM (S.toList (A.allIDs auto)) $ \i -> do
                e <- newID
                return (e, (auto, i))
        rootSet <- do
            internRoots <- A.roots auto
            S.fromList <$> mapM
                -- NOPE, nodeMap does not map internal to
                -- external but the other way around.
                (snd . (nodeMap M.!))
                (S.toList internRoots)
        return (rootSet, nodeMap)
    runM = flip E.evalState 0
    newID = E.state $ \n -> (n, n + 1)
