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
  )
where

import Circuit.Ends (Ends (..), HasUnit (..), In (..), Out (..), commit, emit, endsK, toActions)
import Control.Applicative
import Control.Arrow (Kleisli (..))
import Control.Concurrent.STM
import Control.Monad (void)
import Prelude

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :set -XNondecreasingIndentation
-- >>> import Circuit
-- >>> import Circuit.Ends (Ends(..), In(..), Out(..), commit, emit, close)
-- >>> import Circuit.Ends (HasUnit(..))
-- >>> import Circuit.Queue
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> import Control.Concurrent.STM (STM, atomically)

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
-- Returns the raw write/read actions used by 'openSTM'.  Not exported;
-- the canonical API is 'openSTM'.
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
-- Allocates STM primitives and returns a matched pair of ends sharing
-- the same mutable channel.  Both ends live in 'STM', so you can compose
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
-- >>> import Circuit.Ends (HasUnit(..))
-- >>> let endsU = open :: Ends (Kleisli STM) () ()
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
openSTM q = do
  (write, read') <- endsSTM q
  pure (endsK write read')


-- | Open a queue strategy as IO 'Ends'.
--
-- Like 'openSTM', but each primitive operation is wrapped in its own
-- 'atomically'.  You cannot batch multiple writes or a write-plus-read
-- into a single STM transaction; for that use 'openSTM' and wrap in
-- 'atomically' yourself.
--
-- >>> import Circuit.Ends (HasUnit(..))
-- >>> let endsU = open :: Ends (Kleisli IO) () ()
-- >>> ends <- openIO Unbounded :: IO (Ends (Kleisli IO) Int Int)
-- >>> runKleisli (commit (conjoint ends) (companion endsU)) 42
-- >>> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 42
openIO :: Queue a -> IO (Ends (Kleisli IO) a a)
openIO q = do
  e <- atomically (openSTM q)
  let (Kleisli write, Kleisli receive) = toActions e
  pure (endsK (atomically . write) (atomically (receive ())))

-- ---------------------------------------------------------------------------
-- Collector ends
-- ---------------------------------------------------------------------------

-- | Drain every element currently readable by a single-value 'Out' end.
--
-- The read action is assumed to retry when the buffer is empty;
-- 'orElse' (via the 'Alternative' instance for 'STM') catches that retry
-- and terminates the list.  Strategies whose read never retries (e.g.
-- 'Latest') are not suitable for collection.
--
-- This is a compositional transformer on 'Out' ends: it turns an
-- @'Out' ('Kleisli' STM) a@ into an @'Out' ('Kleisli' STM) [a]@ without
-- reaching behind the 'Ends' abstraction.
collectOut :: Out (Kleisli STM) a -> Out (Kleisli STM) [a]
collectOut o = Out $ \i -> Kleisli $ \x -> drain (runKleisli (emit o i) x)
  where
    drain r = (r >>= \y -> (y :) <$> drain r) `orElse` pure []

-- | Open a queue strategy as a collector 'Ends'.
--
-- Single @a@s go in through 'commit'; the accumulated @[a]@ is drained
-- through 'emit'.  The read clears the buffer, so each 'emit' returns only
-- the elements written since the last read.
--
-- Built compositionally from 'openSTM' and 'collectOut'.
--
-- >>> import Circuit.Ends (HasUnit(..))
-- >>> let endsU = open :: Ends (Kleisli STM) () ()
-- >>> ends <- atomically (openCollectSTM Unbounded :: STM (Ends (Kleisli STM) Int [Int]))
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 1
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 2
-- >>> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 3
-- >>> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- [1,2,3]
openCollectSTM :: Queue a -> STM (Ends (Kleisli STM) a [a])
openCollectSTM q = (\ends -> Ends (conjoint ends) (collectOut (companion ends))) <$> openSTM q

-- | Open a queue strategy as an IO collector 'Ends'.
--
-- Like 'openCollectSTM', but each operation is wrapped in its own
-- 'atomically'.  The collector drain is still an STM transaction, so this
-- allocates the raw STM actions and wraps them in IO.
--
-- >>> import Circuit.Ends (HasUnit(..))
-- >>> let endsU = open :: Ends (Kleisli IO) () ()
-- >>> ends <- openCollectIO Unbounded :: IO (Ends (Kleisli IO) Int [Int])
-- >>> runKleisli (commit (conjoint ends) (companion endsU)) 1
-- >>> runKleisli (commit (conjoint ends) (companion endsU)) 2
-- >>> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- [1,2]
openCollectIO :: Queue a -> IO (Ends (Kleisli IO) a [a])
openCollectIO q = do
  e <- atomically (openCollectSTM q)
  let (Kleisli write, Kleisli receive) = toActions e
  pure (endsK (atomically . write) (atomically (receive ())))
