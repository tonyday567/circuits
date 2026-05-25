-- | Queue combinators for traced categories.
--
-- A queue has two ends that share a buffer via the ambient state wire:
--
--   * 'push' — enqueue an element (snoc onto buffer).
--   * 'pop'  — dequeue an element (uncons from buffer).
--   * 'queue' — 'pop . push', a one-step FIFO delay.
--
-- All three operate on pairs @(buf, payload)@ where @buf@ is the buffer
-- and @payload@ is the element or unit.  The buffer is the /ambient/
-- state wire; composition threads it through automatically.
module Circuit.Queue
  ( -- * Stream decomposition
    Uncons (..),
    HasEmpty (..),
    HasLength (..),

    -- * Queue ends
    push,
    pop,
    queue,
  )
where

import Circuit.Circuit (Circuit (..))
import Data.These (These (..))

-- $setup
-- >>> import Circuit.Circuit (reify)
-- >>> import Circuit.Queue

-- ---------------------------------------------------------------------------
-- Stream decomposition (from circuits-parser)
-- ---------------------------------------------------------------------------

-- | Types that have an empty / zero value.
class HasEmpty f where
  emptyF :: f

instance HasEmpty [a] where
  emptyF = []

-- | Types whose length can be measured and prefix-taken.
class HasLength f where
  streamLength :: f -> Int
  streamTake :: Int -> f -> f

instance HasLength [a] where
  streamLength = length
  streamTake = take

-- | Deconstruct a stream into head and tail.
--
-- Returns 'These' to distinguish three cases:
--
--   * 'This'  x    — stream had exactly one element @x@.
--   * 'That'  xs   — stream was empty, returned intact.
--   * 'These' x xs — stream had @x@ as head and @xs@ as tail.
class (HasEmpty f) => Uncons f s where
  uncons :: f -> These s f

-- | List instance.
--
-- >>> uncons ([] :: [Int])
-- That []
--
-- >>> uncons [1,2,3]
-- These 1 [2,3]
instance Uncons [a] a where
  uncons [] = That []
  uncons (x : xs) = These x xs

-- ---------------------------------------------------------------------------
-- Queue ends
-- ---------------------------------------------------------------------------

-- | Enqueue: snoc an element onto the buffer, return @()@.
--
-- The payload @a@ is appended to the end of the buffer.
-- The returned unit signals "acknowledged."
--
-- >>> reify push ([], 1)
-- ([1],())
--
-- >>> reify push ([1,2], 3)
-- ([1,2,3],())
push :: Circuit (->) (,) ([a], a) ([a], ())
push = Lift $ \(buf, a) -> (buf ++ [a], ())

-- | Dequeue: uncons an element from the buffer.
--
-- The head of the buffer becomes the output; the tail becomes the
-- new buffer.  Empty buffer raises an error.
--
-- >>> reify pop ([1,2,3], ())
-- ([2,3],1)
pop :: Circuit (->) (,) ([a], ()) ([a], a)
pop = Lift $ \(buf, ()) -> case uncons buf of
  These x xs -> (xs, x)
  That _ -> (buf, error "Queue.pop: empty buffer")
  This x -> ([], x)

-- | One-step FIFO queue: 'pop . push'.
--
-- Pushes the input element, then immediately pops the oldest element.
-- The net effect is a one-element delay (after the first value primes
-- the buffer).
--
-- >>> reify queue ([], 1)
-- ([1],1)
--
-- >>> reify queue ([1], 2)
-- ([2],1)
--
-- >>> reify queue ([2], 3)
-- ([3],2)
queue :: Circuit (->) (,) ([a], a) ([a], a)
queue = Compose pop push
