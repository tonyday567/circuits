-- | Queue strategies and ends for circuits — pure and STM.
--
-- The 'Queue' type describes buffering semantics (Unbounded, Bounded,
-- Single, Latest, Newest).  Two families of ends:
--
-- * 'endsSTM' — STM mutables, blocking reads.
-- * 'endsPure' — pure @[a]@ state, 'Bool'/'Maybe' for partiality.
--
-- 'endsQueue' creates a dual pair of circuit ends sharing an STM channel.
-- 'push' and 'pop' lift pure ends into 'Circuit's with state threaded
-- through the tensor.  All four are polymorphic in the tensor @t@.
module Circuit.Queue
  ( -- * Queue strategies
    Queue (..),

    -- * Queue ends
    endsSTM,
    endsPure,

    -- * Circuit ends (STM)
    endsQueue,
    closeQueue,

    -- * Ends product
    Ends (..),
    openSTM,

    -- * Type aliases
    WireK,
    Emit,
    Commit,

    -- * State-threading lifters
    push,
    pop,
  )
where

import Circuit.Classes ((>>>))
import Circuit.Layer (run)
import Circuit.Trace (In (..), Out (..), Trace (..), Traced)
import Control.Applicative
import Control.Arrow (Kleisli (..))
import Control.Concurrent.STM
import Control.Monad (void)
import Prelude

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XNondecreasingIndentation
-- >>> import Circuit (Trace(..), run)
-- >>> import Circuit.Ends (openK)
-- >>> import Circuit.Queue
-- >>> import Circuit.Trace (runIn, runOut, close)
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> import Circuit.Classes ((>>>))
-- >>> import Control.Concurrent.STM (STM, TQueue, atomically, newTQueueIO, readTQueue, writeTQueue)

-- ---------------------------------------------------------------------------
-- Type aliases
-- ---------------------------------------------------------------------------

-- | A wire over 'Kleisli' @m@ with the @(,)@ tensor, by convention.
-- 'endsQueue' and 'closeQueue' are polymorphic in the tensor; this alias
-- pins it for readability.
type WireK m = Trace (,) (Kleisli m)

-- | Unit-grounded harvest port (@() → a@).
--
-- Same shape as plugging free 'Out' against unit 'In':
-- @'runIn' outA inU :: Trace t arr () a@.
-- Free ends remain 'In'/'Out'; this alias is only the port shape over
-- 'Kleisli' @m@ (historical name — prefer speaking in In/Out).
--
-- >>> import Circuit (run)
-- >>> import Circuit.Ends (open)
-- >>> import Circuit.Trace (runIn)
-- >>> let (outA, _inA) = open ("emit me" :: String)
-- >>> let (_outU, inU) = open ()
-- >>> run (runIn outA inU) ()
-- "emit me"
type Emit m a = WireK m () a

-- | Unit-grounded feed port (@a → ()@).
--
-- Same shape as plugging free 'In' against unit 'Out':
-- @'runOut' inA outU :: Trace t arr a ()@.
--
-- >>> import Circuit (run)
-- >>> import Circuit.Ends (open)
-- >>> import Circuit.Trace (runOut)
-- >>> let (_outA, inA) = open ("consume me" :: String)
-- >>> let (outU, _inU) = open ()
-- >>> run (runOut inA outU) "payload"
-- ()
type Commit m a = WireK m a ()

-- ---------------------------------------------------------------------------
-- Queue strategies
-- ---------------------------------------------------------------------------

-- | How messages are queued between producer and consumer.
data Queue a
  = -- | Unbounded FIFO queue.
    Unbounded
  | -- | Bounded FIFO with backpressure (write blocks when full).
    Bounded Int
  | -- | Single-slot buffer (write rejects when full — MVar-style A).
    -- Overwrite-on-full (B) is 'SwapQ'.
    Single
  | -- | Single-slot buffer, overwrite-on-full (B semantics — swapTMVar).
    -- Write always succeeds; read empties.
    SwapQ
  | -- | Always holds the latest value (overwrites, never blocks).
    Latest a
  | -- | Like 'Bounded' but drops oldest when full.
    Newest Int
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- STM ends
-- ---------------------------------------------------------------------------

-- | Create STM write/read ends for a queue strategy.
--
-- @
-- endsSTM :: Queue a -> STM (a -> STM (), STM a)
-- @
--
-- The read end blocks until a value is available.  Write behaviour
-- varies by strategy:
--
-- [/Unbounded/] Never blocks on write.
-- [/Bounded n/] Blocks on write when @n@ items are queued.
-- [/Single/] MVar-style: blocks on write when full (A semantics).
-- [/Latest a/] Never blocks; always holds a value (seed @a@ initially).
-- [/Newest n/] Never blocks on write (drops oldest); blocks on empty read.
--
-- === Unbounded
--
-- >>> (w, r) <- atomically (endsSTM Unbounded :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2
-- >>> atomically r
-- 1
-- >>> atomically r
-- 2
--
-- Multi-op compose in one transaction:
--
-- >>> (w, r) <- atomically (endsSTM Unbounded :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2 >> r
-- 1
--
-- === Bounded
--
-- >>> (w, r) <- atomically (endsSTM (Bounded 2) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2
-- >>> atomically r
-- 1
-- >>> atomically r
-- 2
-- >>> atomically (w 3)  -- succeeds: reads drained the queue
-- >>> atomically r
-- 3
--
-- === Single (A: MVar-style — write blocks when full)
--
-- >>> (w, r) <- atomically (endsSTM (Single :: Queue Int) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 42
-- >>> atomically r
-- 42
-- >>> atomically $ w 99 >> r  -- compose: write then read in one transaction
-- 99
--
-- === SwapQ (B: swapTMVar-style — write always succeeds, overwriting)
--
-- >>> (w, r) <- atomically (endsSTM (SwapQ :: Queue Int) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2  -- second write overwrites the first
-- >>> atomically r
-- 2
-- >>> (w2, r2) <- atomically (endsSTM (SwapQ :: Queue Int) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w2 5 >> r2  -- compose: write then read in one transaction
-- 5
--
-- === Latest (always holds a value, never blocks)
--
-- >>> (w, r) <- atomically (endsSTM (Latest 0) :: STM (Int -> STM (), STM Int))
-- >>> atomically r
-- 0
-- >>> atomically $ w 5
-- >>> atomically r
-- 5
-- >>> atomically $ w 7 >> r  -- compose: overwrite then read
-- 7
--
-- === Newest (bounded; drops oldest when full)
--
-- >>> (w, r) <- atomically (endsSTM (Newest 2) :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2 >> w 3  -- 3rd write drops oldest (1)
-- >>> atomically r
-- 2
-- >>> atomically r
-- 3
endsSTM :: Queue a -> STM (a -> STM (), STM a)
endsSTM = \case
  Bounded n -> do
    q <- newTBQueue (fromIntegral n)
    pure (writeTBQueue q, readTBQueue q)
  Unbounded -> do
    q <- newTQueue
    pure (writeTQueue q, readTQueue q)
  Single -> do
    m <- newEmptyTMVar
    pure (putTMVar m, takeTMVar m)
  SwapQ -> do
    v <- newEmptyTMVar
    let write x = tryPutTMVar v x >>= \case True -> pure (); False -> void (swapTMVar v x)
    pure (write, takeTMVar v)
  Latest a -> do
    t <- newTVar a
    pure (writeTVar t, readTVar t)
  Newest n -> do
    q <- newTBQueue (fromIntegral n)
    let write x = writeTBQueue q x <|> (tryReadTBQueue q *> write x)
    pure (write, readTBQueue q)

-- ---------------------------------------------------------------------------
-- Pure ends
-- ---------------------------------------------------------------------------

-- | Create pure write/read ends for a queue strategy.
--
-- All strategies operate on a @[a]@ buffer.  'Bool' signals write
-- acceptance; 'Maybe' signals value availability.
--
-- === Unbounded
--
-- >>> let (w_ub, r_ub) = endsPure (Unbounded :: Queue Int)
-- >>> let (ub1, ow1) = w_ub 1 []
-- >>> ow1
-- True
-- >>> let (ub2, ow2) = w_ub 2 ub1
-- >>> ow2
-- True
-- >>> r_ub ub2
-- ([2],Just 1)
-- >>> r_ub []
-- ([],Nothing)
--
-- === Bounded
--
-- >>> let (w_b, r_b) = endsPure (Bounded 2 :: Queue Int)
-- >>> let (bb1, bw1) = w_b 1 []
-- >>> bw1
-- True
-- >>> let (bb2, bw2) = w_b 2 bb1
-- >>> bw2
-- True
-- >>> let (bb3, bw3) = w_b 3 bb2
-- >>> bw3
-- False
-- >>> r_b bb2
-- ([2],Just 1)
-- >>> r_b []
-- ([],Nothing)
--
-- === Single (A: MVar-style — write rejects when full)
--
-- >>> let (w_s, r_s) = endsPure (Single :: Queue Int)
-- >>> let (sb1, sw1) = w_s 1 []
-- >>> sw1
-- True
-- >>> let (sb2, sw2) = w_s 2 sb1
-- >>> sw2
-- False
-- >>> sb2
-- [1]
-- >>> r_s sb1
-- ([],Just 1)
-- >>> r_s []
-- ([],Nothing)
--
-- === SwapQ (B: swapTMVar-style — write always succeeds, overwriting)
--
-- >>> let (w_sw, r_sw) = endsPure (SwapQ :: Queue Int)
-- >>> let (sw1, swok1) = w_sw 1 []
-- >>> swok1
-- True
-- >>> sw1
-- [1]
-- >>> let (sw2, swok2) = w_sw 2 sw1
-- >>> swok2
-- True
-- >>> sw2
-- [2]
-- >>> r_sw sw1
-- ([],Just 1)
-- >>> r_sw []
-- ([],Nothing)
--
-- === Latest (read never empties; returns seed when empty)
--
-- >>> let (w_l, r_l) = endsPure (Latest 0 :: Queue Int)
-- >>> r_l []
-- ([],Just 0)
-- >>> let (lb1, _) = w_l 5 []
-- >>> r_l lb1
-- ([5],Just 5)
-- >>> let (lb2, _) = w_l 7 lb1
-- >>> r_l lb2
-- ([7],Just 7)
--
-- === Newest (bounded; drops oldest when full)
--
-- >>> let (w_n, r_n) = endsPure (Newest 2 :: Queue Int)
-- >>> let (nb1, _) = w_n 1 []
-- >>> let (nb2, _) = w_n 2 nb1
-- >>> nb2
-- [1,2]
-- >>> let (nb3, _) = w_n 3 nb2
-- >>> nb3
-- [2,3]
-- >>> r_n nb3
-- ([3],Just 2)
endsPure :: Queue a -> (a -> [a] -> ([a], Bool), [a] -> ([a], Maybe a))
endsPure = \case
  Unbounded ->
    ( \x buf -> (buf ++ [x], True),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )
  Bounded n ->
    ( \x buf -> if length buf < n then (buf ++ [x], True) else (buf, False),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )
  -- Single: MVar-style (A).  Write succeeds only when empty;
  -- overwrite-on-full (B) lives in SwapQ.
  Single ->
    ( \x buf -> case buf of [] -> ([x], True); _ -> (buf, False),
      \case [] -> ([], Nothing); x : _ -> ([], Just x)
    )
  -- SwapQ: B semantics — write always succeeds (overwrites); read empties.
  SwapQ ->
    ( \x _ -> ([x], True),
      \case [] -> ([], Nothing); x : _ -> ([], Just x)
    )
  Latest d ->
    ( \x _ -> ([x], True),
      \buf -> (buf, Just (case buf of x : _ -> x; [] -> d))
    )
  Newest n ->
    ( \x buf ->
        let buf' = buf ++ [x]
         in if length buf' <= n then (buf', True) else (drop 1 buf', True),
      \case [] -> ([], Nothing); x : xs -> (xs, Just x)
    )

-- ---------------------------------------------------------------------------
-- State-threading lifters
-- ---------------------------------------------------------------------------

-- | Push to state, returning 'Bool'.
-- 'False' signals rejection (e.g. bounded queue full).
--
-- Bare FIFO via 'endsPure' (note: 'flip' to match state-first order):
--
-- >>> let qpush = push (flip (fst (endsPure Unbounded)))
-- >>> run (qpush :: Trace (,) (->) ([Int], Int) ([Int], Bool)) ([], 1)
-- ([1],True)
push :: (s -> a -> (s, Bool)) -> Trace t (->) (s, a) (s, Bool)
push f = Arr (uncurry f)

-- | Pop from state, returning 'Maybe' a.
-- 'Nothing' signals empty.
--
-- Bare FIFO via 'endsPure':
--
-- >>> let qpop = pop (snd (endsPure Unbounded))
-- >>> run (qpop :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([1,2,3], ())
-- ([2,3],Just 1)
-- >>> run (qpop :: Trace (,) (->) ([Int], ()) ([Int], Maybe Int)) ([], ())
-- ([],Nothing)
pop :: (s -> (s, Maybe a)) -> Trace t (->) (s, ()) (s, Maybe a)
pop f = Arr (\(s, ()) -> f s)

-- ---------------------------------------------------------------------------
-- STM queue ends
-- ---------------------------------------------------------------------------

-- | Create a dual pair: push end and pop end sharing a single STM channel.
--
-- Each operation is wrapped in its own 'atomically'.  You cannot batch
-- multiple writes or a write-plus-read into a single STM transaction.
--
-- For atomic composition use 'endsSTM' directly:
--
-- >>> (w, r) <- atomically (endsSTM Unbounded :: STM (Int -> STM (), STM Int))
-- >>> atomically $ w 1 >> w 2 >> r  -- both writes + read in ONE transaction
-- 1
--
-- 'endsQueue' bakes 'atomically' into each circuit step.  The same work
-- would require three separate 'atomically' calls — visible to concurrent
-- writers.  When you need multi-op atomicity, reach for 'endsSTM' and wrap
-- in 'atomically' yourself.
--
-- Use 'WireK' to pin the tensor for readability:
--
-- >>> (pushA, popA) <- atomically (endsQueue Unbounded :: STM (WireK IO Int (), WireK IO () Int))
-- >>> (pushB, popB) <- atomically (endsQueue Unbounded :: STM (WireK IO Int (), WireK IO () Int))
-- >>> let pipe = Arr (Kleisli $ \() -> pure (7 :: Int)) >>> pushA >>> popA >>> pushB >>> popB
-- >>> runKleisli (run pipe) ()
-- 7
endsQueue :: Queue a -> STM (Trace t (Kleisli IO) a (), Trace t (Kleisli IO) () a)
endsQueue q = do
  (write, read') <- endsSTM q
  pure (Arr (Kleisli (atomically . write)), Arr (Kleisli (\() -> atomically read')))

-- | Plug a push end and a pop end together into a single circuit.
--
-- This is the extrinsic analogue of 'Circuit.Ends.close': two ends
-- that share an STM channel are composed into @Circuit a a@.
--
-- >>> (pushA, popA) <- atomically (endsQueue Unbounded :: STM (WireK IO Int (), WireK IO () Int))
-- >>> runKleisli (run (closeQueue pushA popA)) 42
-- 42
closeQueue ::
  (Traced t (Kleisli IO)) =>
  Trace t (Kleisli IO) a () ->
  Trace t (Kleisli IO) () a ->
  Trace t (Kleisli IO) a a
closeQueue push' pop' = push' >>> pop'

-- ---------------------------------------------------------------------------
-- Ends product — the dual free ends as a named record
-- ---------------------------------------------------------------------------

-- | The product of free channel ends: 'commit' writes, 'emit' reads.
--
-- Named after the collective noun for the commit / emit pair.
-- The type parameters let @a@ and @b@ differ; for queues they are the same.
data Ends t arr a b = Ends
  { commit :: In arr t a  -- ^ Write end (producer).
  , emit   :: Out arr t b  -- ^ Read end  (consumer).
  }

-- | Open a queue strategy as STM 'Ends'.
--
-- Allocates STM primitives and returns the dual ends sharing the same
-- mutable channel.  Both ends live in 'STM', so you can compose
-- operations across channels in a single 'atomically' block.
--
-- @
-- ends <- atomically (openSTM Unbounded)
-- atomically $ do
--   msg <- runKleisli (run (runIn (emit ends) inU)) ()
--   runKleisli (run (runOut (commit ends) outU)) msg
-- @
--
-- === Unbounded
--
-- >>> import Circuit.Ends (openK)
-- >>> let (outU, inU) = openK ()
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (run (runOut (commit ends) outU)) 42
-- >>> atomically $ runKleisli (run (runIn (emit ends) inU)) ()
-- 42
--
-- Multi-op compose in one 'atomically' (both writes + read):
--
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (run (runOut (commit ends) outU)) 1 >> runKleisli (run (runOut (commit ends) outU)) 2 >> runKleisli (run (runIn (emit ends) inU)) ()
-- 1
--
-- 'close' recovers the value through the queue:
--
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (run (close (commit ends) (emit ends))) 7
-- 7
--
-- === SwapQ (overwrite on write)
--
-- >>> ends <- atomically (openSTM SwapQ :: STM (Ends (,) (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (run (runOut (commit ends) outU)) 1 >> runKleisli (run (runOut (commit ends) outU)) 2 >> runKleisli (run (runIn (emit ends) inU)) ()
-- 2
openSTM :: Queue a -> STM (Ends (,) (Kleisli STM) a a)
openSTM = \case
  Unbounded -> do
    q <- newTQueue
    let outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTQueue q)
        inA = In $ \o -> Arr (Kleisli $ \a -> writeTQueue q a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  Bounded n -> do
    q <- newTBQueue (fromIntegral n)
    let outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTBQueue q)
        inA = In $ \o -> Arr (Kleisli $ \a -> writeTBQueue q a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  Single -> do
    v <- newEmptyTMVar
    let outA = Out $ \_ -> Arr (Kleisli $ \_ -> takeTMVar v)
        inA = In $ \o -> Arr (Kleisli $ \a -> putTMVar v a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  SwapQ -> do
    v <- newEmptyTMVar
    let write x = tryPutTMVar v x >>= \case True -> pure (); False -> void (swapTMVar v x)
        outA = Out $ \_ -> Arr (Kleisli $ \_ -> takeTMVar v)
        inA = In $ \o -> Arr (Kleisli $ \a -> write a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  Latest a -> do
    t <- newTVar a
    let outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTVar t)
        inA = In $ \o -> Arr (Kleisli $ \a -> writeTVar t a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
  Newest n -> do
    q <- newTBQueue (fromIntegral n)
    let write x = writeTBQueue q x <|> (tryReadTBQueue q *> write x)
        outA = Out $ \_ -> Arr (Kleisli $ \_ -> readTBQueue q)
        inA = In $ \o -> Arr (Kleisli $ \a -> write a >> runKleisli (run (runIn o inA)) a)
    pure (Ends inA outA)
