{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free traced PROP with a bimonoid over a primitive set.
--
-- 'Net' extends 'Circuit' with structural rows for the monoidal and
-- bimonoid operations: parallel composition, copy, discard, addition,
-- and zero.  Where 'Circuit' dissolved these into opaque 'Lift' calls,
-- 'Net' keeps them as inspectable constructors — the difference between
-- wiring you can read backwards and wiring that's been melted into the
-- prims.
--
-- = Normal form
--
-- Every 'Net' normalizes to a single outermost 'Knot' wrapped around
-- a knot-free core — combinational logic plus a register bank plus one
-- feedback bus.  Hardware calls this a netlist.  AD calls the bus the
-- tape.  The Mendler pattern match fires exactly once by construction.
--
-- = transposition
--
-- @transpose :: Net arr t a b -> Net arr t b a@ is structural recursion
-- over the syntax: 'Compose' reverses, 'Copy' swaps with 'Add', 'Discard'
-- with 'Zero', 'Knot' with itself.  Only 'Lift' and 'Knot' require the
-- base arrow to be transposable; the spine is always reversible.
--
-- = Relationship to Circuit
--
-- @upgrade :: Circuit arr t a b -> Net arr t a b@ is constructor-to-constructor.
-- @forget :: Net arr t a b -> Circuit arr t a b@ dissolves structural rows
-- into opaque 'Lift' calls — lossy, like 'flatten' for 'Hyper'.
module Circuit.Net
  ( -- * Net
    Net (..),

    -- * Transposition
    transpose,

    -- * Conversion
    upgrade,
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category
import Data.Profunctor
#else
import Circuit.Classes
#endif

import Circuit.Additive (Additive (..))
import Circuit.Circuit qualified as C
import Circuit.Dup (Dup (..), Linear)
import Prelude hiding (id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Circuit (Circuit(..))
-- >>> import Circuit.Net
-- >>> import Prelude hiding (id, (.))

-- | The free traced PROP with a bimonoid.
--
-- Three families of constructor:
--
--   * __Circuit heritage__ — 'Lift', 'Compose', 'Knot' (unchanged).
--   * __Monoidal__ — 'Par', 'Swap', 'Perm' (parallel composition, braiding).
--   * __Bimonoid__ — 'Copy', 'Discard' (comonoid), 'Add', 'Zero' (monoid).
--
-- 'Dup' and 'Additive' constraints ride as dictionary arguments on the
-- constructors that need them — laws in the typeclass holes, evidence on
-- the GADT rows.
data Net arr t a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Net arr t a b

  -- | Sequential composition.
  Compose :: Net arr t b c -> Net arr t a b -> Net arr t a c

  -- | Parallel composition (monoidal product).
  Par :: Net arr t a b -> Net arr t c d -> Net arr t (a, c) (b, d)

  -- | Symmetric braiding.
  Swap :: Net arr t (a, b) (b, a)

  -- | Wire permutation (domain and codomain are the same multiset).
  --
  -- Bundles a permutation with its inverse so that transposition is
  -- well-defined: @transpose (Perm f g) = Perm g f@.  Only sound
  -- when @g . f = id@ and @f . g = id@ — orthogonal / permutation
  -- maps.  The law is the caller's responsibility; document it.
  Perm :: arr a b -> arr b a -> Net arr t a b

  -- | Copy: fan-out.  Requires both comonoid and monoid ('Linear').
  Copy :: Linear arr a => Net arr t a (a, a)

  -- | Discard: erase.  Requires 'Linear'.
  Discard :: Linear arr a => Net arr t a ()

  -- | Add: fan-in.  Requires 'Linear'.
  Add :: Linear arr a => Net arr t (a, a) a

  -- | Zero: the neutral element.  Requires 'Linear'.
  Zero :: Linear arr a => Net arr t () a

  -- | Feedback loop.  The body is a 'Net', not an opaque base arrow —
  -- so 'transpose' can reach inside and swap 'Copy' ↔ 'Add' within
  -- the loop.  Normal form: 'fuse' collects all feedback into a single
  -- outermost 'Knot' around knot-free wiring.
  Knot :: Net arr t (t a b) (t a c) -> Net arr t b c

-- | Transpose a 'Net' — the backward circuit as inspectable syntax.
--
-- The structural rows are self-dual under transposition:
-- 'Compose' reverses, 'Copy' ↔ 'Add', 'Discard' ↔ 'Zero',
-- 'Knot' ↔ 'Knot' (recurring into the body).  'Perm' flips its pair.
--
-- Only 'Lift' requires the base arrow to be transposable — hence the
-- explicit @tr@ argument.  'Knot' bodies are 'Net' wiring, so
-- 'transpose' can reach inside loops.
transpose ::
  (forall x y. arr x y -> arr y x) ->
  Net arr t a b ->
  Net arr t b a
transpose tr = \case
  Lift f -> Lift (tr f)
  Compose f g -> Compose (transpose tr g) (transpose tr f)
  Par f g -> Par (transpose tr f) (transpose tr g)
  Swap -> Swap
  Perm f g -> Perm g f
  Copy -> Add
  Add -> Copy
  Discard -> Zero
  Zero -> Discard
  Knot f -> Knot (transpose tr f)

-- | Upgrade a 'Circuit' to a 'Net' — constructor-to-constructor.
--
-- The structural rows ('Par', 'Copy', 'Add', etc.) are absent from
-- 'Circuit', so upgrading a lifted 'Circuit' produces a 'Net' with
-- only 'Lift', 'Compose', and 'Knot' — the same information, now in
-- a GADT that can hold more.  'Circuit.Knot' lifts to 'Net.Lift' body
-- inside 'Net.Knot'.
upgrade :: C.Circuit arr t a b -> Net arr t a b
upgrade (C.Lift f) = Lift f
upgrade (C.Compose f g) = Compose (upgrade f) (upgrade g)
upgrade (C.Knot f) = Knot (upgrade f)
