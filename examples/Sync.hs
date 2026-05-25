module Sync where

import Circuit

-- | Simple FIFO queue: (inbox, outbox). Push to inbox, pop from outbox.
-- When outbox is empty, reverse inbox into it (amortized O(1)).
type Queue a = ([a], [a])

enqueue :: a -> Queue a -> Queue a
enqueue x (inbox, outbox) = (x : inbox, outbox)

dequeue :: Queue a -> Maybe (a, Queue a)
dequeue ([], []) = Nothing
dequeue (inbox, x : outbox) = Just (x, (inbox, outbox))
dequeue (inbox, []) = dequeue ([], reverse inbox)

type Queues a b = (Queue a, Queue b)

-- | Process one event. If a pair can be formed, return Just (a, b).
-- Queues are visible state, threaded by Compose.
sync :: Circuit (->) (,) (Queues a b, Either a b) (Queues a b, Maybe (a, b))
sync = Lift step
  where
    step ((as, bs), Left a) = case dequeue bs of
      Nothing     -> ((enqueue a as, bs), Nothing)
      Just (b, bs') -> ((as, bs'), Just (a, b))
    step ((as, bs), Right b) = case dequeue as of
      Nothing      -> ((as, enqueue b bs), Nothing)
      Just (a, as') -> ((as', bs), Just (a, b))

-- | Process a list of interleaved events, collecting all pairs.
syncAll :: (Queues a b, [Either a b]) -> (Queues a b, [(a, b)])
syncAll = go
  where
    go (qs, [])     = (qs, [])
    go (qs, e : es) = case reify sync (qs, e) of
      (qs', Nothing) -> go (qs', es)
      (qs', Just p)  -> let (qs'', ps) = go (qs', es) in (qs'', p : ps)

-- $setup
-- >>> import Sync
-- >>> import Circuit

emptyQueues :: Queues a b
emptyQueues = (([], []), ([], []))
