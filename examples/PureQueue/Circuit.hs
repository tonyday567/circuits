-- | Pure queue ends lifted into circuits.
--
-- Unlike the existential Ends in PureQueue, this module keeps state types
-- visible so they compose as circuits with push/pop.
--
-- The pure analogue of @makeQueue@ is to use 'PureQueue.ends' to get the
-- write/read functions, then lift them with the combinators below.  The
-- state type (@'FIFO' a@, @'Maybe' a@, or @a@) is determined by the strategy
-- and threaded by the caller via 'Compose'.
--
-- @
--   let (q0, write, read) = ends Unbounded
--       src = Lift (\() -> (q0, 7))
--       pipe = src >>> pushC write >>> popC read
--   in reify pipe ()
-- @
module PureQueue.Circuit where

import Circuit
import PureQueue (FIFO, Queue (..), size, snoc, uncons)

-- | Write end as a Circuit. Bool = write accepted?
--
-- This is push with a success flag instead of ().
writeC :: (s -> a -> (s, Bool)) -> Circuit (->) (,) (s, a) (s, Bool)
writeC f = Lift (uncurry f)

-- | Read end as a Circuit. Maybe a = value available?
--
-- This is pop with an optional result instead of error-on-empty.
readC :: (s -> (s, Maybe a)) -> Circuit (->) (,) (s, ()) (s, Maybe a)
readC f = Lift (\(s, ()) -> f s)

-- | Write end that errors on rejection (Bounded-full, Single-occupied).
-- Collapses Bool into (), matching the push signature.
pushC :: (s -> a -> (s, Bool)) -> Circuit (->) (,) (s, a) (s, ())
pushC f = Lift $ \(s, a) -> case f s a of
  (s', True)  -> (s', ())
  (_,  False) -> error "pushC: rejected"

-- | Read end that errors on empty.
-- Collapses Maybe a into a, matching the pop signature.
popC :: (s -> (s, Maybe a)) -> Circuit (->) (,) (s, ()) (s, a)
popC f = Lift $ \(s, ()) -> case f s of
  (s', Just a) -> (s', a)
  (_,  Nothing) -> error "popC: empty"

-- | Push that silently drops on rejection (Bounded-full → discard).
pushDrop :: (s -> a -> (s, Bool)) -> Circuit (->) (,) (s, a) (s, ())
pushDrop f = Lift $ \(s, a) -> case f s a of
  (s', True)  -> (s', ())
  (s', False) -> (s', ())

-- | Pop that returns Nothing on empty instead of erroring.
-- Same as readC, but with explicit naming.
popMaybe :: (s -> (s, Maybe a)) -> Circuit (->) (,) (s, ()) (s, Maybe a)
popMaybe = readC
