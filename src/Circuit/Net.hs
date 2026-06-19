{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
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
-- 'loom' and 'melt' interpret a 'Net' to a plain arrow and a
-- 'Circuit' respectively.  Instances for 'Comonoid' @(->)@ and
-- 'Monoid' @(->)@ exist; @D@ instances live in @circuits-ad@.
module Circuit.Net
  ( -- * Net
    Net (..),

    -- * Transposition
    transpose,

    -- * Conversion
    upgrade,

    -- * Interpretation
    loom,
    melt,
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category
import Data.Profunctor
#else
import Circuit.Classes
#endif

import Circuit.Trace qualified as C
import Circuit.Dagger qualified as Dg
import Circuit.Monoidal (MonoidalP (..))
import Circuit.Traced qualified as Traced
import Prelude hiding (Monoid, id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Circuit (Circuit(..), reify)
-- >>> import Circuit.Net
-- >>> import Prelude hiding (id, (.), Monoid)

-- | The free traced PROP with a bimonoid.
--
-- Three families of constructor:
--
--   * __Circuit heritage__ — 'Lift', 'Compose', 'Knot' (unchanged).
--   * __Monoidal__ — 'Par', 'Swap' (parallel composition, braiding).
--   * __Bimonoid__ — 'Copy', 'Discard' (comonoid), 'Plus', 'Zero' (monoid).
--
-- 'Comonoid' and 'Monoid' constraints ride as dictionary arguments on the
-- constructors that need them — laws in the typeclass holes, evidence on
-- the GADT rows.
data Net t arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Net t arr a b
  -- | Sequential composition.
  Compose :: Net t arr b c -> Net t arr a b -> Net t arr a c
  -- | Parallel composition (monoidal product).
  Par :: Net t arr a b -> Net t arr c d -> Net t arr (a, c) (b, d)
  -- | Symmetric braiding.
  Swap :: Net t arr (a, b) (b, a)
  -- | Copy: fan-out.  Requires both comonoid and monoid ('Bimonoid').
  Copy :: (Dg.Bimonoid arr a) => Net t arr a (a, a)
  -- | Discard: erase.  Requires 'Bimonoid'.
  Discard :: (Dg.Bimonoid arr a) => Net t arr a ()
  -- | Plus: fan-in.  Requires 'Bimonoid'.
  Plus :: (Dg.Bimonoid arr a) => Net t arr (a, a) a
  -- | Zero: the neutral element.  Requires 'Bimonoid'.
  Zero :: (Dg.Bimonoid arr a) => Net t arr () a
  -- | Feedback loop.  The body is a 'Net', not an opaque base arrow —
  -- so 'transpose' can reach inside and swap 'Copy' ↔ 'Plus' within
  -- the loop.
  Knot :: Net t arr (t a b) (t a c) -> Net t arr b c

-- | Transpose a 'Net' — the backward circuit as inspectable syntax.
--
-- The structural rows are self-dual under transposition:
-- 'Compose' reverses, 'Copy' ↔ 'Plus', 'Discard' ↔ 'Zero',
-- 'Knot' ↔ 'Knot' (recurring into the body).
--
-- 'Lift' transposes via 'Dagger' field swap — only nets over
-- 'Dagger' are transposable, since the forward\/backward pairing is
-- structural in the base arrow.
--
-- Law: @transpose . transpose = id@.
--
-- >>> import Circuit.Dagger qualified as Dg
-- >>> let n = Circuit.Net.Lift (Dg.Dagger (+1) (subtract 1)) :: Net (,) (Dg.Dagger (->)) Int Int
-- >>> Dg.front (loom (transpose (transpose n))) 5
-- 6
transpose ::
  Net t (Dg.Dagger arr) a b ->
  Net t (Dg.Dagger arr) b a
#ifdef __GLASGOW_HASKELL__
transpose = \case
  Lift (Dg.Dagger f g) -> Lift (Dg.Dagger g f)
  Compose f g -> Compose (transpose g) (transpose f)
  Par f g -> Par (transpose f) (transpose g)
  Swap -> Swap
  Copy -> Plus
  Plus -> Copy
  Discard -> Zero
  Zero -> Discard
  Knot f -> Knot (transpose f)
#else
transpose = undefined
#endif

-- | Upgrade a 'Circuit' to a 'Net' — constructor-to-constructor.
--
-- The structural rows ('Par', 'Copy', 'Plus', etc.) are absent from
-- 'Circuit', so upgrading a lifted 'Circuit' produces a 'Net' with
-- only 'Lift', 'Compose', and 'Knot' — the same information, now in
-- a GADT that can hold more.  'Circuit.Knot' lifts to 'Net.Knot'.
upgrade :: C.Circuit t arr a b -> Net t arr a b
upgrade (C.Lift f) = Lift f
upgrade (C.Compose f g) = Compose (upgrade f) (upgrade g)
upgrade (C.Knot f) = Knot (upgrade f)

-- | Interpret a 'Net' to a plain arrow.
--
-- The canonical map out of the free traced PROP with a bimonoid.
-- Structural rows dispatch to their typeclass counterparts:
-- 'Par' to 'par', 'Copy' to 'copy', 'Plus' to 'plus', etc.
-- 'Knot' uses the 'Trace' instance on the base arrow.
--
-- @'loom' = 'C.reify' . 'melt'@ — first melt structural rows into
-- 'Circuit', then reify to a plain arrow.  The Mendler sliding case is
-- handled once in 'Circuit.Trace.freeze'.
--
-- >>> loom (Circuit.Net.Lift (+1) :: Net (,) (->) Int Int) 5
-- 6
loom ::
  (Traced.Trace arr t, MonoidalP arr) =>
  Net t arr a b ->
  arr a b
loom = C.reify . melt

-- | Melt the structural rows of a 'Net' into opaque 'Lift' calls.
--
-- The forgetful map from the free traced PROP with bimonoid to the free
-- traced monoidal category.  Structural rows ('Par', 'Copy', 'Plus',
-- etc.) become opaque base-arrow operations; the 'Knot' and 'Compose'
-- structure is preserved.
--
-- 'loom' factors through 'melt': @loom = reify . melt@.
--
-- >>> reify (melt (Circuit.Net.Lift (+1) :: Net (,) (->) Int Int)) 5
-- 6
melt ::
  (Traced.Trace arr t, MonoidalP arr) =>
  Net t arr a b ->
  C.Circuit t arr a b
melt = \case
  Lift f -> C.Lift f
  Compose g f -> C.Compose (melt g) (melt f)
  Par f g -> C.Lift (par (loom f) (loom g))
  Swap -> C.Lift swap
#ifdef __GLASGOW_HASKELL__
  Copy -> C.Lift Dg.copy
  Discard -> C.Lift Dg.discard
  Plus -> C.Lift Dg.plus
  Zero -> C.Lift Dg.zero
#else
  _ -> undefined
#endif
  Knot f -> C.Knot (melt f)
