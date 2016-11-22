{-# LANGUAGE OverloadedStrings #-}


-- | A monad for defining elementary trees with FS unification.


module NLP.Partage.FSTree
(
) where


-- import qualified Control.Monad.State.Strict as E
import qualified Data.Text as T
import qualified Data.Tree as R

import qualified NLP.Partage.FS as FS
import qualified NLP.Partage.Env as Env
import qualified NLP.Partage.Tree.Comp as C
import qualified NLP.Partage.Tree.Other as O


--------------------------------------------------
-- Types
--------------------------------------------------


-- -- | An elementary tree -- what we want to get.
-- type Tree n t = R.Tree (O.Node n t)
-- -- type Tree n t k v = T.Tree (O.Node n t, FS.FS k v)
--
--
-- -- | A tree forest.
-- type Forest n t = [Tree n t]
--
--
-- -- | Tree defining monad transformer.
-- type TreeT n t m = E.StateT (Forest n t) m


--------------------------------------------------
-- Primitives
--------------------------------------------------


-- -- | Create a node with its children.
-- node
--   :: (Monad m)
--   => n
--   -- ^ Root non-terminal
--   -> TreeT m (Forest n t)
--   -- ^ How to create children
--   -> TreeT m (Tree n t)
-- node x childrenM = do
--   let root = O.NonTerm x
--   children <- childrenM
--   return $ R.Node root children
--
--
--
-- -- | Run the computation and return the resulting value and
-- -- the underlying forest.
-- runTreeT :: (Monad m) => TreeT n t m a -> m (a, Forest n t)
-- runTreeT = undefined
