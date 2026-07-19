-- | Queue strategies and STM 'Ends' for circuits.
--
-- The 'Queue' type describes buffering semantics (Unbounded, Bounded,
-- Single, Latest, Newest).  The canonical API is 'openSTM' and 'openIO',
-- which return a matched pair of free ends sharing a single STM channel.
-- 'openCollectSTM' and 'openCollectIO' provide a collector view where
-- single elements go in and the collected list is drained on demand.
module Circuit.Queue
  ( -- * Queue strategies
    Queue (..),

    -- * STM 'Ends'
    openSTM,

    -- * IO 'Ends'
    openIO,

    -- * STM collector 'Ends'
    openCollectSTM,

    -- * IO collector 'Ends'
    openCollectIO,

    -- * Type alias
    WireK,
  )
where

import Circuit.Classes ((>>>))
import Circuit.Ends (Ends (..), In (..), Out (..), commit, emit)
import Circuit.Ends.Unit (HasUnit (..))
import Circuit.Trace (Trace (..))
import Control.Applicative
import Control.Arrow (Kleisli (..))
import Control.Concurrent.STM
import Control.Monad (void)
import Prelude

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XNondecreasingIndentation
-- >>> import Circuit
-- >>> import Circuit.Classes ((>>>))
-- >>> import Circuit.Ends (Ends(..), In(..), Out(..), commit, emit, close)
-- >>> import Circuit.Ends.Unit (HasUnit (..))
-- >>> import Circuit.Queue
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> import Control.Concurrent.STM (STM, atomically)
-- >>> import Data.Profunctor (lmap)

-- ---------------------------------------------------------------------------
-- Type aliases
-- ---------------------------------------------------------------------------

-- | A wire over 'Kleisli' @m@ with the @(,)@ tensor, by convention.
-- 'openSTM' and 'openIO' fix the tensor to @(,)@; this alias pins it for
-- readability.
type WireK m = Trace (,) (Kleisli m)

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

-- | Internal STM primitive for a queue strategy.
--
-- Returns the raw write/read actions used by 'openSTM' and 'openIO'.
-- Exported only for advanced multi-op atomicity; the canonical API is
-- 'openSTM'.
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
-- IO 'Ends'
-- ---------------------------------------------------------------------------

-- | Open a queue strategy as STM 'Ends'.
--
-- Allocates STM primitives and returns the dual ends sharing the same
-- mutable channel.  Both ends live in 'STM', so you can compose
-- operations across channels in a single 'atomically' block.
--
-- @
-- ends <- atomically (openSTM Unbounded)
-- atomically $ do
--   msg <- runKleisli (emit (companion ends) (conjoint endsU)) ()
--   runKleisli (commit (conjoint ends) (companion endsU)) msg
-- @
--
-- === Unbounded
--
-- >>> import Circuit.Ends.Unit (HasUnit (..))
-- >>> let endsU = open
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 42
-- >>> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 42
--
-- Multi-op compose in one 'atomically' (both writes + read):
--
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 1 >> runKleisli (commit (conjoint ends) (companion endsU)) 2 >> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 1
--
-- 'close' recovers the value through the queue:
--
-- >>> ends <- atomically (openSTM Unbounded :: STM (Ends (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (close (conjoint ends) (companion ends)) 7
-- 7
--
-- === SwapQ (overwrite on write)
--
-- >>> ends <- atomically (openSTM SwapQ :: STM (Ends (Kleisli STM) Int Int))
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 1 >> runKleisli (commit (conjoint ends) (companion endsU)) 2 >> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 2
openSTM :: Queue a -> STM (Ends (Kleisli STM) a a)
openSTM = \case
  Unbounded -> do
    q <- newTQueue
    let outA = Out $ \_ -> Kleisli $ \_ -> readTQueue q
        inA = In $ \o -> Kleisli $ \a -> writeTQueue q a >> runKleisli (emit o inA) a
    pure (Ends inA outA)
  Bounded n -> do
    q <- newTBQueue (fromIntegral n)
    let outA = Out $ \_ -> Kleisli $ \_ -> readTBQueue q
        inA = In $ \o -> Kleisli $ \a -> writeTBQueue q a >> runKleisli (emit o inA) a
    pure (Ends inA outA)
  Single -> do
    v <- newEmptyTMVar
    let outA = Out $ \_ -> Kleisli $ \_ -> takeTMVar v
        inA = In $ \o -> Kleisli $ \a -> putTMVar v a >> runKleisli (emit o inA) a
    pure (Ends inA outA)
  SwapQ -> do
    v <- newEmptyTMVar
    let write x = tryPutTMVar v x >>= \case True -> pure (); False -> void (swapTMVar v x)
        outA = Out $ \_ -> Kleisli $ \_ -> takeTMVar v
        inA = In $ \o -> Kleisli $ \a -> write a >> runKleisli (emit o inA) a
    pure (Ends inA outA)
  Latest a -> do
    t <- newTVar a
    let outA = Out $ \_ -> Kleisli $ \_ -> readTVar t
        inA = In $ \o -> Kleisli $ \x -> writeTVar t x >> runKleisli (emit o inA) x
    pure (Ends inA outA)
  Newest n -> do
    q <- newTBQueue (fromIntegral n)
    let write x = writeTBQueue q x <|> (tryReadTBQueue q *> write x)
        outA = Out $ \_ -> Kleisli $ \_ -> readTBQueue q
        inA = In $ \o -> Kleisli $ \a -> write a >> runKleisli (emit o inA) a
    pure (Ends inA outA)


-- | Open a queue strategy as IO 'Ends'.
--
-- Like 'openSTM', but each primitive operation is wrapped in its own
-- 'atomically'.  You cannot batch multiple writes or a write-plus-read
-- into a single STM transaction; for that use 'openSTM' and wrap in
-- 'atomically' yourself.
--
-- >>> import Circuit.Ends.Unit (HasUnit (..))
-- >>> let endsU = open
-- >>> ends <- openIO Unbounded :: IO (Ends (Kleisli IO) Int Int)
-- >>> runKleisli (commit (conjoint ends) (companion endsU)) 42
-- >>> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 42
openIO :: Queue a -> IO (Ends (Kleisli IO) a a)
openIO q = do
  (write, read') <- atomically (endsSTM q)
  let outA = Out $ \_ -> Kleisli $ \_ -> atomically read'
      inA = In $ \o -> Kleisli $ \a -> atomically (write a) >> runKleisli (emit o inA) a
  pure (Ends inA outA)

-- ---------------------------------------------------------------------------
-- Collector ends
-- ---------------------------------------------------------------------------

-- | Drain every element currently readable by the given single-value read
-- action.  The read action is assumed to retry when the buffer is empty;
-- 'orElse' catches that retry and terminates the list.
drainRead :: STM a -> STM [a]
drainRead read' = (read' >>= \x -> (x :) <$> drainRead read') `orElse` pure []

-- | Internal STM primitive for a collector strategy.
--
-- Like 'endsSTM', but reads drain the whole buffer as a list.  The write
-- action uses the queue's normal strategy; the read action returns every
-- element currently stored and clears it.
--
-- This assumes the underlying read action retries when empty.  Strategies
-- whose read never retries (e.g. 'Latest') are not suitable for collection.
collectSTM :: Queue a -> STM (a -> STM (), STM [a])
collectSTM q = do
  (write, read') <- endsSTM q
  pure (write, drainRead read')

-- | Open a queue strategy as a collector 'Ends'.
--
-- Single @a@s go in through 'commit'; the accumulated @[a]@ is drained
-- through 'emit'.  The read clears the buffer, so each 'emit' returns only
-- the elements written since the last read.
--
-- >>> import Circuit.Ends.Unit (HasUnit (..))
-- >>> let endsU = open
-- >>> ends <- atomically (openCollectSTM Unbounded :: STM (Ends (Kleisli STM) Int [Int]))
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 1
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 2
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 3
-- >>> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- [1,2,3]
openCollectSTM :: Queue a -> STM (Ends (Kleisli STM) a [a])
openCollectSTM q = do
  (write, drain) <- collectSTM q
  let outA = Out $ \_ -> Kleisli $ \_ -> drain
      inA = In $ \o -> Kleisli $ \a -> write a >> runKleisli (emit o inA) a
  pure (Ends inA outA)

-- | Open a queue strategy as an IO collector 'Ends'.
--
-- Like 'openCollectSTM', but each operation is wrapped in its own
-- 'atomically'.
--
-- >>> import Circuit.Ends.Unit (HasUnit (..))
-- >>> let endsU = open
-- >>> ends <- openCollectIO Unbounded :: IO (Ends (Kleisli IO) Int [Int])
-- >>> runKleisli (commit (conjoint ends) (companion endsU)) 1
-- >>> runKleisli (commit (conjoint ends) (companion endsU)) 2
-- >>> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- [1,2]
openCollectIO :: Queue a -> IO (Ends (Kleisli IO) a [a])
openCollectIO q = do
  (write, drain) <- atomically (collectSTM q)
  let outA = Out $ \_ -> Kleisli $ \_ -> atomically drain
      inA = In $ \o -> Kleisli $ \a -> atomically (write a) >> runKleisli (emit o inA) a
  pure (Ends inA outA)
