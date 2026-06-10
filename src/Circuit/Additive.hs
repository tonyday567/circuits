{-# LANGUAGE CPP #-}

-- | Additive structure on channel objects — the monoid that cotangents need.
--
-- Reverse-mode automatic differentiation requires cotangent channels to carry
-- a commutative monoid: fan-out on the forward pass becomes fan-in (summation)
-- on the backward pass.  This class captures that structure.
--
-- Two law profiles are supported, distinguished by whether 'plus' is idempotent:
--
--   * __counting__ (@g ⊞ g = 2g@) — gradient accumulation, where multiplicity
--     matters.  This is the standard 'Num'/'Vector' style.
--
--   * __idempotent__ (@x ⊞ x = x@) — CRDT-style merge, where merging an agent
--     with itself yields the same agent.  Join-semilattice / 'Meet' style.
--
-- See "Circuit.AD" for the 'D' arrow that uses 'Additive' to implement
-- reverse-mode differentiation via 'Trace'.
module Circuit.Additive
  ( -- * Additive
    Additive (..),
  )
where

#ifdef __GLASGOW_HASKELL__
#else
import Circuit.Classes
#endif

-- | A commutative monoid on channel objects.
--
-- Laws:
--
-- @
--   -- monoid
--   plus a zero = a              -- unit
--   plus zero a = a              -- unit
--   plus a (plus b c) = plus (plus a b) c   -- associativity
--   plus a b = plus b a          -- commutativity
-- @
--
-- For the idempotent law profile, additionally:
--
-- @
--   plus a a = a                 -- idempotence
-- @
--
-- The bimonoid compatibility laws (interaction with copy/discard) are the
-- responsibility of the instance.  In a cartesian category where every
-- object carries a comonoid (Fox's theorem), these are:
--
-- @
--   copy . plus = (plus × plus) . (id × swap × id) . (copy × copy)
--   copy . zero = zero × zero
--   discard . plus = discard × discard
-- @
class Additive arr a where
  -- | Sum two values of the channel type.
  --
  -- @
  -- plus :: (a, a) -> a
  -- plus (3, 4) = 7  -- for a Num-backed instance
  -- @
  plus :: arr (a, a) a

  -- | The neutral element.
  --
  -- @
  -- zero :: () -> a
  -- zero () = 0  -- for a Num-backed instance
  -- @
  zero :: arr () a
