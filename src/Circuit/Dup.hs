{-# LANGUAGE CPP #-}

-- | Comonoid structure on channel objects — the forward half of the bimonoid.
--
-- A 'Dup' instance equips an object with 'dup' (copy) and 'discard', forming
-- a cocommutative comonoid.  In a cartesian category like @(->)@, every object
-- carries this structure for free (Fox's theorem).  In a differentiable
-- category like 'Circuit.AD.D', it does not — copy's pullback is addition,
-- which is the structural cost of fan-out in reverse-mode AD.
--
-- 'Dup' is the comonoid dual of 'Additive' (the monoid).  Together with
-- the bimonoid compatibility laws, they form the algebraic basis for
-- 'Circuit.Net', the free traced PROP with a bimonoid over a primitive set.
--
-- 'Linear' combines both — the precondition for 'Circuit.Net.transpose'
-- to be total.
module Circuit.Dup
  ( -- * Dup
    Dup (..),

    -- * Linear
    Linear,
  )
where

import Circuit.Additive (Additive)

-- | A cocommutative comonoid on channel objects.
--
-- Laws:
--
-- @
--   -- comonoid
--   fst . dup = id              -- left unit
--   snd . dup = id              -- right unit
--   (dup × id) . dup = (id × dup) . dup  -- coassociativity
--   swap . dup = dup            -- cocommutativity
-- @
--
-- For the bimonoid with 'Additive', the compatibility laws are:
--
-- @
--   dup . plus = (plus × plus) . (id × swap × id) . (dup × dup)
--   dup . zero = zero × zero
--   discard . plus = discard × discard
-- @
class Dup arr a where
  -- | Copy a value into a pair.
  --
  -- @
  -- dup :: a -> (a, a)
  -- dup x = (x, x)
  -- @
  dup :: arr a (a, a)

  -- | Discard a value.
  --
  -- @
  -- discard :: a -> ()
  -- discard _ = ()
  -- @
  discard :: arr a ()

-- | Both the comonoid ('Dup') and monoid ('Additive') on a channel object.
--
-- On a linear base arrow, every type carries both structures.  This is
-- the precondition for 'Circuit.Net.transpose' to be total — when we
-- swap 'Copy' for 'Add', both constraint dictionaries must be available.
class (Dup arr a, Additive arr a) => Linear arr a
