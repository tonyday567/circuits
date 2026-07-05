# PureQueue.Circuit — lifting queue ends into circuits (R&D)

```haskell
-- | Pure queue ends lifted into circuits.
--
-- Unlike the existential Ends in PureQueue, this module keeps state types
-- visible so they compose as circuits with push/pop.
--
-- The pure analogue of @makeQueue@ is to use 'PureQueue.ends' to get the
-- write/read functions, then lift them with the combinators below.  The
-- state type (@'FIFO' a@, @'Maybe' a@, or @a@) is determined by the strategy
-- and threaded by the caller via sequential composition '(>>>)'.
--
-- @
--   let (q0, write, read) = ends Unbounded
--       src = Arr (\() -> (q0, 7))
--       pipe = src >>> pushC write >>> popC read
--   in run pipe ()
-- @
module PureQueue.Circuit where

import Circuit (Trace (..), run)
import PureQueue (FIFO, Queue (..), size, snoc, uncons)

-- | Write end as a Trace. Bool = write accepted?
writeC :: (s -> a -> (s, Bool)) -> Trace (,) (->) (s, a) (s, Bool)
writeC f = Arr (uncurry f)

-- | Read end as a Trace. Maybe a = value available?
readC :: (s -> (s, Maybe a)) -> Trace (,) (->) (s, ()) (s, Maybe a)
readC f = Arr (\(s, ()) -> f s)

-- | Write end that errors on rejection (Bounded-full, Single-occupied).
pushC :: (s -> a -> (s, Bool)) -> Trace (,) (->) (s, a) (s, ())
pushC f = Arr $ \(s, a) -> case f s a of
  (s', True)  -> (s', ())
  (_,  False) -> error "pushC: rejected"

-- | Read end that errors on empty.
popC :: (s -> (s, Maybe a)) -> Trace (,) (->) (s, ()) (s, a)
popC f = Arr $ \(s, ()) -> case f s of
  (s', Just a) -> (s', a)
  (_,  Nothing) -> error "popC: empty"

-- | Push that silently drops on rejection (Bounded-full → discard).
pushDrop :: (s -> a -> (s, Bool)) -> Trace (,) (->) (s, a) (s, ())
pushDrop f = Arr $ \(s, a) -> case f s a of
  (s', True)  -> (s', ())
  (s', False) -> (s', ())

-- | Pop that returns Nothing on empty instead of erroring.
popMaybe :: (s -> (s, Maybe a)) -> Trace (,) (->) (s, ()) (s, Maybe a)
popMaybe = readC
```
