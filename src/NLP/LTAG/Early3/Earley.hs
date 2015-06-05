{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}


{-
 - The actual Earley-style parser.
 -}


module NLP.LTAG.Early3.Earley where


import           Control.Applicative ((<$>))
import           Control.Monad (guard)
import qualified Control.Monad.State.Strict as St
import           Control.Monad.Trans.Class (lift)

import           Data.Maybe (maybeToList)
import qualified Data.Set as S
import qualified Data.IntMap.Strict as I
import qualified Data.Sequence as Seq
import           Data.Sequence (ViewL(..), (|>))

import qualified Pipes as P

import           NLP.LTAG.Early3.Core
import qualified NLP.LTAG.Early3.Rule as R


--------------------------------------------------
-- CHART STATE
--------------------------------------------------


-- | Parsing state.
data State n t
    -- | Regular context-free rule. 
    = Init {
        -- | The head of the rule represented by the state.
          root  :: Sym n
        -- | Starting position.
        , beg   :: Pos
        -- | The list of elements yet to process. 
        , right :: [Lab n t] }
    -- | Auxiliary rule (processing left part)
    | Aux1 {
        -- | The head of the rule represented by the state.
          root  :: Sym n
        -- | Starting position.
        , beg   :: Pos
        -- | Following the spine of the auxiliary tree.
        -- `Nothing' if foot node.
        , down  :: Maybe (Sym n)
        -- | The list of elements yet to process. 
        , right :: [Lab n t]
        -- | The real right side of the rule, so far not even
        -- touched.
        , rest  :: [Lab n t] }
    -- | Auxiliary rule (processing right part)
    | Aux2 {
        -- | The head of the rule represented by the state.
          root  :: Sym n
        -- | Starting position.
        , beg   :: Pos
        -- | Gap starting position.
        , gapBeg   :: Pos
        -- | Gap ending position.
        , gapEnd   :: Pos
        -- | Following the spine of the auxiliary tree.
        -- `Nothing' if foot node.
        , down  :: Maybe (Sym n)
        -- | The list of elements yet to process. 
        , right :: [Lab n t] }
    -- | Auxiliary rule (only left part)
    | AuxL {
        -- | The head of the rule represented by the state.
          root  :: Sym n
        -- | Starting position.
        , beg   :: Pos
        -- | Following the spine of the auxiliary tree.
        -- `Nothing' if foot node.
        , down  :: Maybe (Sym n)
        -- | The list of elements yet to process. 
        , right :: [Lab n t] }
    deriving (Show, Eq, Ord)


-- -- | Parsing state: processed auxiliary rule elements and the elements
-- -- yet to process.
-- -- TODO: what about rules with left side being empty?
-- -- TODO: what about rules with both sides being empty?
-- data StateL n t = StateL {
--     -- | The head of the rule represented by the state.
--       rootL  :: Sym n
--     -- | Starting position.
--     , begL   :: Pos
-- --     -- | The list of processed elements of the rule.
-- --     -- (Stored in the inverse order?)
-- --     , leftL  :: [Lab n t]
--     -- | The list of elements yet to process. 
--     , rightL :: [Lab n t]
--     -- | The real right side of the rule, so far not even
--     -- touched.
--     , restL  :: [Lab n t]
--     } deriving (Show, Eq, Ord)
-- 
-- 
-- -- | Parsing state: processed auxiliary rule elements and the elements
-- -- yet to process.  Processing the second part of the rule.
-- data StateR n t = StateR {
--     -- | The head of the rule represented by the state.
--       rootR   :: Sym n
--     -- | Starting position (left part)
--     , begR    :: Pos
--     -- | Ending position (left part)
--     , endR    :: Pos
--     -- | Starting position (right part)
--     , newEndR :: Pos
-- --     -- | The list of processed elements of the rule.
-- --     -- (Stored in the inverse order?)
-- --     , leftR   :: [Lab n t]
--     -- | The list of elements yet to process.
--     , rightR  :: [Lab n t]
-- --     -- | The left part of the rule, already processed and
-- --     -- spanning (begR, endR).
-- --     , doneR   :: [Lab n t]
--     } deriving (Show, Eq, Ord)
-- 
-- 
-- -- | Generic state.
-- type State n t = Three (StateI n t) (StateL n t) (StateR n t)
-- 
-- 
-- -- | Generic function which tells what the state still expects on
-- -- the right.
-- right :: State n t -> [Lab n t]
-- right (One StateI{..}) = rightI
-- right (Two StateL{..}) = rightL
-- right (Thr StateR{..}) = rightR
-- 
-- 
-- -- | Consume the given terminal if the rules actually expects it.
-- -- Return the rule after consumption.
-- consume :: Eq t => t -> State n t -> Maybe (State n t)
-- consume t (One st@StateI{..}) = do
--     (x, xs) <- decoList rightI
--     guard $ labEqTerm t x
--     return $ One $ st {rightI = xs}
-- consume t (Two st@StateL{..}) = do
--     (x, xs) <- decoList rightL
--     guard $ labEqTerm t x
--     return $ Two $ st {rightL = xs}
-- consume t (Thr st@StateR{..}) = do
--     (x, xs) <- decoList rightR
--     guard $ labEqTerm t x
--     return $ Thr $ st {rightR = xs}


--------------------------------------------------
-- CHART
--------------------------------------------------


-- | Chart entry -- all states ending on the given
-- position.
type Entry n t = S.Set (State n t)


-- | A chart is a map from indiced to chart entries.                                                     
type Chart n t = I.IntMap (Entry n t)


-- | N-th position of the chart.
(!?) :: Chart n t -> Int -> Entry n t
chart !? k = case I.lookup k chart of
    Just e  -> e
    Nothing -> error $ "!?: no such index in the chart"


-- -- | Complex, "dual" chart entry -- all states ending on the
-- -- given position.
-- type EntryD


--------------------------------------------------
-- CHART MONAD
--------------------------------------------------


-- -- | State for the global Earley-style computations.
-- data EarSt n t = EarSt {
--     -- | The CFG grammar.
--       gram  :: [R.Rule n t]
--     -- | The chart computed so far.
--     , chart :: Chart n t
--     } deriving (Show, Eq, Ord)
-- 
-- 
-- -- | Monad for local computations on a given position of the chart.
-- type Ear n t = St.StateT (EarSt n t) IO
-- 
-- 
-- -- | Run the Earley monad.
-- execEar
--     :: [R.Rule n t] -- ^ The grammar
--     -> Int          -- ^ Length of the input sentence
--     -> Ear n t a    -- ^ The computation to perform
--     -> IO (Chart n t)
-- execEar gr n comp
--     = fmap chart $ St.execStateT comp
--     $ EarSt {gram=gr, chart=ch0}
--   where
--     -- ch0 = I.fromList [(i, S.empty) | i <- [0..n]]
--     ch0 = undefined
--     -- TODO: since we do not implement any prediction yet, we
--     -- have to fill the chart with all rules in the beginning!
-- 
-- 
-- -- | Get the underlying grammar.
-- getGram :: Ear n t [R.Rule n t]
-- getGram = St.gets gram
-- 
-- 
-- -- | Get the underlying chart.
-- getChart :: Ear n t (Chart n t)
-- getChart = St.gets chart
-- 
-- 
-- -- | Get the underlying chart.
-- getEntry :: Pos -> Ear n t (Entry n t)
-- getEntry k = (!? k) <$> getChart
-- 
-- 
-- -- | Check if there is a state in the chart.
-- hasState
--     :: (Ord n, Ord t)
--     => Pos          -- ^ Position of the chart
--     -> State n t    -- ^ State to add at the given position
--     -> Ear n t Bool
-- hasState k p = S.member p <$> getEntry k
-- 
-- 
-- -- | Add state to the chart.
-- addState
--     :: (Ord n, Ord t)
--     => Pos          -- ^ Position of the chart
--     -> State n t    -- ^ State to add at the given position
--     -> Ear n t ()
-- addState k p = St.modify $ \s@EarSt{..} ->
--     let en = case I.lookup k chart of
--             Nothing -> S.singleton p
--             Just en -> S.insert p en
--         chart' = I.insert k en chart
--     in  s {chart=chart'}


--------------------------------------------------
-- SCAN
--------------------------------------------------


-- -- | The scan operation.
-- scan
--     :: (Show n, Ord n, Ord t)
--     => Pos                  -- ^ The current position
--     -> t                    -- ^ Terminal to scan
--     -> Entry n t            -- ^ The entry
--     -> Ear n t ()
-- scan k w entry = P.runListT $ do
--     -- grm <- lift getGram
--     let each = P.Select . P.each
--     -- for each state,
--     q  <- each $ S.toList entry
--     -- ... not yet completed ...
--     q' <- each $ maybeToList $ consume w q
--     -- add a corresponding state.
--     lift $ do
--         addState (k+1) q'
-- --         lift $ do
-- --             putStr "[S]  " >> printState' k q
-- --             putStr "  :  " >> printState' (k+1) q'


--------------------------------------------------
-- COMPLETE
--------------------------------------------------


-- -- | The queue of the <completed> states yet to process.
-- type ComSt n t = Seq.Seq (State n t)
-- 
-- 
-- -- | A monad for complete computations.
-- type Com n t = St.StateT (ComSt n t) (Ear n t)
-- 
-- 
-- -- | Run the Com monad given the initial set of states.
-- runCom :: [State n t] -> Com n t a -> Ear n t a
-- runCom xs com = St.evalStateT com $ Seq.fromList xs
-- 
-- 
-- -- | Pop item from the queue.
-- popQueue :: Com n t (Maybe (State n t))
-- popQueue = St.state $ \seq -> case Seq.viewl seq of
--     EmptyL  -> (Nothing, seq)
--     x :< xs -> (Just x, xs)
-- 
-- 
-- -- | Push item into the queue.
-- pushQueue :: State n t -> Com n t ()
-- pushQueue x = St.modify $ \xs -> xs |> x


-- -- | Update the current entry using `complete' operations.
-- complete
--     :: (Show n, Ord n, Ord t)
--     => Pos              -- ^ Current position
--     -> Entry n t        -- ^ Current entry
--     -> Ear n t ()
-- complete k en0 =
--     runCom (S.toList en0) (loop step)
--   where
--     -- execute the given function as long as the queue is non-empty
--     loop f = do
--         p <- popQueue
--         case p of
--             Nothing -> return ()
--             Just x  -> f x >> loop f
--     -- p is the state poped from the queue
--     step p = P.runListT $ do
--         -- make sure that p is completed
--         guard $ null $ right p
--         -- The chart built so far
--         chart <- lift $ lift getChart
--         -- For each rule ending on the beg position of p ...
--         let each = P.Select . P.each
--         q <- each $ S.toList $ chart !? beg p
--         -- ... which is not yet completed ...
--         (r, rs) <- each $ maybeToList $ decoList $ right q
--         -- ... and expects a root non-terminal of the rule
--         -- which we know has been completed,
--         guard $ r == root p
--         return ()
-- --         -- construct the new state,
-- --         let new = q {left=r:left q, right=rs}
-- --         lift $ do 
-- --             -- check if it is already present in the chart,
-- --             b <- lift $ hasState k new
-- --             -- add it to the chart (for the sake of traces if it is
-- --             -- already there)
-- --             lift $ addState k new $ Comp q p
-- --             when b $ lift . lift $ do
-- --                 -- if present, only notify,
-- --                 putStr "[R]  " >> printState' (beg p) q
-- --                 putStr "  +  " >> printState' k p
-- --                 putStr "  :  " >> printState' k new
-- --             when (not b) $ do
-- --                 lift . lift $ do
-- --                     putStr "[C]  " >> printState' (beg p) q
-- --                     putStr "  +  " >> printState' k p
-- --                     putStr "  :  " >> printState' k new
-- --                 -- if completed, add it to the queue
-- --                 when (null $ right new) $
-- --                     pushQueue new


--------------------------------------------------
-- UTILS
--------------------------------------------------


-- | Extension of `Either a b'.
data Three a b c
    = One a
    | Two b
    | Thr c
    deriving (Show, Eq, Ord)


-- | Deconstruct list.  Utility function.
decoList :: [a] -> Maybe (a, [a])
decoList [] = Nothing
decoList (y:ys) = Just (y, ys)


-- | Label equals terminal?
labEqTerm :: Eq t => t -> Lab n t -> Bool
labEqTerm x (Right y) = x == y
labEqTerm _ _ = False
