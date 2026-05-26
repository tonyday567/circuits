# PureQueue — queue strategies (R&D)

```haskell
-- | Pure queue ends, parameterised by strategy.
--
-- The Queue type from Box.Queue, but with pure (non-STM) implementations.
-- Each strategy determines what "write" and "read" mean under contention.
--
-- This is the pure analogue of Box.Queue.ends:
--   ends :: Queue a -> STM (a -> STM (), STM a)
--
-- Here:
--   ends :: Queue a -> (QueueState, (a -> QueueState -> (QueueState, Bool),
--                                     QueueState -> (QueueState, Maybe a)))
module PureQueue where

-- | How messages are queued between producer and consumer.
data Queue a
  = Unbounded
  | Bounded Int
  | Single
  | Latest a
  | Newest Int
  | New
  deriving (Show, Eq)

-- | FIFO queue: (inbox, outbox). Push to inbox, pop from outbox.
-- When outbox is empty, reverse inbox into it.
type FIFO a = ([a], [a])

snoc :: a -> FIFO a -> FIFO a
snoc x (inbox, outbox) = (x : inbox, outbox)

uncons :: FIFO a -> (Maybe a, FIFO a)
uncons ([], []) = (Nothing, ([], []))
uncons (inbox, x : outbox) = (Just x, (inbox, outbox))
uncons (inbox, []) = uncons ([], reverse inbox)

size :: FIFO a -> Int
size (inbox, outbox) = length inbox + length outbox

-- | Queue state and operations, parametrised by strategy.
data Ends a = forall s. Ends
  { eInit  :: s
  , eWrite :: s -> a -> (s, Bool)   -- Bool: write succeeded?
  , eRead  :: s -> (s, Maybe a)     -- Maybe: value available?
  }

ends :: Queue a -> Ends a
ends = \case
  -- Write always succeeds, read blocks when empty.
  Unbounded -> Ends
    { eInit  = mempty @(FIFO a)
    , eWrite = \q x -> (snoc x q, True)
    , eRead  = \q -> let (ma, q') = uncons q in (q', ma)
    }

  -- Write fails when full (no blocking in pure code), read blocks when empty.
  Bounded n -> Ends
    { eInit  = mempty @(FIFO a)
    , eWrite = \q x -> if size q < n then (snoc x q, True) else (q, False)
    , eRead  = \q -> let (ma, q') = uncons q in (q', ma)
    }

  -- Write only succeeds if slot is empty (STM: putTMVar blocks if full).
  -- Read takes and empties.
  Single -> Ends
    { eInit  = Nothing
    , eWrite = \q x -> case q of Nothing -> (Just x, True); Just _ -> (q, False)
    , eRead  = \q -> (Nothing, q)
    }

  -- Write overwrites, read always returns the current value.
  -- State is always a value (never Nothing).
  Latest a -> Ends
    { eInit  = a
    , eWrite = \_ x -> (x, True)
    , eRead  = \q -> (q, Just q)
    }

  -- Write always succeeds (drops oldest when full), read blocks when empty.
  Newest n -> Ends
    { eInit  = mempty @(FIFO a)
    , eWrite = \q x ->
        let q' = if size q >= n
                 then snd (uncons q)  -- drop oldest
                 else q
        in (snoc x q', True)
    , eRead  = \q -> let (ma, q') = uncons q in (q', ma)
    }

  -- Write: drop any pending value, then fill. Always succeeds.
  -- Read: take and empty.
  New -> Ends
    { eInit  = Nothing
    , eWrite = \_ x -> (Just x, True)
    , eRead  = \q -> (Nothing, q)
    }
```
