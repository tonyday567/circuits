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
-- with 'Zero', 'Knot' with itself (recurring into the body).  Only 'Lift'
-- requires the base arrow to be transposable; the spine is always reversible.
--
-- = Status
--
-- Instances for 'Dup' @(->)@ and 'Additive' @(->)@ exist.
-- Instances for @D@ exist ('Circuit.AD' in @circuits-ad@).
-- 'runNet' and 'forget' (netlist to circuit) are implemented; 'fuse' is
-- conservative and does not achieve a single outermost 'Knot' in general.
module Circuit.Net
  ( -- * Net
    Net (..),

    -- * Transposition
    transpose,

    -- * Conversion
    upgrade,

    -- * Normalization
    fuse,

    -- * Interpretation
    runNet,
    forget,
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category
import Data.Profunctor
#else
import Circuit.Classes
#endif

import Circuit.Circuit qualified as C
import Circuit.Dagger (Additive (..), Dup (..), Duplex (..), Linear)
import Circuit.Monoidal (MonoidalP (..))
import Circuit.Traced (Trace (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Circuit (Circuit(..), reify)
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
-- 'Knot' ↔ 'Knot' (recurring into the body).
--
-- 'Lift' transposes via 'Duplex' field swap.  Only nets over
-- 'Duplex' are transposable — the forward\/backward pairing is
-- structural in the base arrow.
transpose ::
  Net (Duplex arr) t a b ->
  Net (Duplex arr) t b a
transpose = \case
  Lift (Duplex f g) -> Lift (Duplex g f)
  Compose f g -> Compose (transpose g) (transpose f)
  Par f g -> Par (transpose f) (transpose g)
  Swap -> Swap
  Copy -> Add
  Add -> Copy
  Discard -> Zero
  Zero -> Discard
  Knot f -> Knot (transpose f)

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

-- | Interpret a 'Net' to a plain arrow.
--
-- The canonical map out of the free traced PROP with a bimonoid.
-- Structural rows dispatch to their typeclass counterparts:
-- 'Par' to 'parA', 'Copy' to 'dup', 'Add' to 'plus', etc.
-- 'Knot' uses the 'Trace' instance on the base arrow.
--
-- >>> runNet (Circuit.Net.Lift (+1) :: Net (->) (,) Int Int) 5
-- 6
runNet ::
  (Trace arr t, MonoidalP arr) =>
  Net arr t a b ->
  arr a b
runNet = \case
  Lift f -> f
  Compose (Knot f) g -> trace (runNet f . untrace (runNet g))
  Compose g f -> runNet g . runNet f
  Par f g -> parA (runNet f) (runNet g)
  Swap -> swapA
  Copy -> dup
  Discard -> discard
  Add -> plus
  Zero -> zero
  Knot f -> trace (runNet f)

-- | Forget the structural rows of a 'Net', melting them into 'Lift' calls.
--
-- The forgetful map from the free traced PROP with bimonoid to the free
-- traced monoidal category.  Structural rows become opaque base-arrow
-- operations; sub-circuit structure is preserved where possible.
--
-- 'runNet' factors through 'forget': @runNet = reify . forget@.
--
-- >>> reify (forget (Circuit.Net.Lift (+1) :: Net (->) (,) Int Int)) 5
-- 6
--
-- | Collect all feedback into a single outermost 'Knot'.
--
-- Uses the sliding axiom to pull 'Knot' outward through 'Compose'.
-- 'untraceNet' is semantic (structure is lost) — a syntactic
-- untrace would require associators at the 'Net' level.
fuse ::
  (Trace arr t, MonoidalP arr) =>
  Net arr t a b ->
  Net arr t a b
fuse = \case
  Compose (Knot f) g
    | not (isKnot g) -> Knot (Compose (fuse f) (untraceNet (fuse g)))
  Compose f (Knot g)
    | not (isKnot f) -> Knot (Compose (untraceNet (fuse f)) (fuse g))
  Knot (Knot f) -> Knot (Knot (fuse f))
  Knot f -> Knot (fuse f)
  Compose f g -> Compose (fuse f) (fuse g)
  Par f g -> Par (fuse f) (fuse g)
  other -> other
  where
    isKnot (Knot _) = True
    isKnot _ = False
    untraceNet f = Lift (untrace (runNet f))

forget ::
  (Trace arr t, MonoidalP arr) =>
  Net arr t a b ->
  C.Circuit arr t a b
forget = \case
  Lift f -> C.Lift f
  Compose g f -> C.Compose (forget g) (forget f)
  Par f g -> C.Lift (parA (runNet f) (runNet g))
  Swap -> C.Lift swapA
  Copy -> C.Lift dup
  Discard -> C.Lift discard
  Add -> C.Lift plus
  Zero -> C.Lift zero
  Knot f -> C.Knot (forget f)
