{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free traced PROP with a bimonoid over a primitive set.
--
-- 'Net' extends 'Trace' with structural rows for the monoidal and
-- bimonoid operations: parallel composition, copy, discard, addition,
-- and zero.  Where 'Trace' keeps only 'Arr' and 'Knot' in normal form,
-- 'Net' keeps the wiring inspectable — the difference between wiring you
-- can read backwards and wiring that has been melted into a single loop.
--
-- 'weave' and 'melt' interpret a 'Net' to a plain arrow and a
-- 'Trace' respectively.  Instances for 'Comonoid' @(->)@ and
-- 'Monoid' @(->)@ exist; @D@ instances live in @circuits-ad@.
module Circuit.Net
  ( -- * Net
    Net (..),

    -- * Transposition
    transpose,

    -- * Conversion
    enrich,

    -- * Interpretation
    weave,
    melt,
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category
import Data.Profunctor
#else
import Circuit.Classes
#endif

import Circuit.Dagger qualified as Dg
import Circuit.Monoidal (MonoidalP (..))
import Circuit.Trace qualified as C
import Circuit.Traced
import Prelude hiding (Monoid, id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Circuit.Trace (Trace(..), run)
-- >>> import Circuit.Net
-- >>> import Prelude hiding (id, (.), Monoid)

-- | The free traced PROP with a bimonoid.
--
-- Three families of constructor:
--
--   * __Sequential__ — 'Lift', 'Compose'.
--   * __Monoidal__ — 'Par', 'Swap' (parallel composition, braiding).
--   * __Bimonoid__ — 'Copy', 'Discard' (comonoid), 'Plus', 'Zero' (monoid).
--   * __Feedback__ — 'Knot', with a 'Net' body so 'transpose' can reach inside.
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
-- >>> Dg.front (weave (transpose (transpose n))) 5
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

-- | Upgrade a 'Trace' to a 'Net' — constructor-to-constructor.
--
-- 'Trace' is the normal form 'Arr' / 'Knot' over a base-arrow body;
-- 'Net' keeps the same information but can hold more structure.
-- 'Circuit.Trace.Arr' lifts to 'Net.Lift'; 'Circuit.Trace.Knot' lifts
-- to 'Net.Knot' around a 'Lift' body.
enrich :: C.Trace t arr a b -> Net t arr a b
enrich (C.Arr f) = Lift f
enrich (C.Knot f) = Knot (Lift f)

-- | Interpret a 'Net' to a plain arrow.
--
-- The canonical map out of the free traced PROP with a bimonoid.
-- Structural rows dispatch to their typeclass counterparts:
-- 'Par' to 'par', 'Copy' to 'copy', 'Plus' to 'plus', etc.
-- 'Knot' uses the 'Traced' instance on the base arrow.
--
-- @'weave' = 'C.run' . 'melt'@ — first melt structural rows into
-- 'Trace', then run to a plain arrow.
--
-- >>> weave (Circuit.Net.Lift (+1) :: Net (,) (->) Int Int) 5
-- 6
weave ::
  (Traced arr t, MonoidalP arr, C.Channelled arr t) =>
  Net t arr a b ->
  arr a b
weave = C.run . melt

-- | Melt the structural rows of a 'Net' into the normal form of 'Trace'.
--
-- The forgetful map from the free traced PROP with bimonoid to the free
-- traced monoidal category.  Structural rows ('Par', 'Copy', 'Plus',
-- etc.) become opaque base-arrow operations wrapped in 'Arr'; 'Compose'
-- and 'Knot' use the 'Category' and 'Traced' instances of 'Trace'.
--
-- @'weave' = 'C.run' . 'melt'@.
--
-- >>> run (melt (Circuit.Net.Lift (+1) :: Net (,) (->) Int Int)) 5
-- 6
melt ::
  (Traced arr t, MonoidalP arr, C.Channelled arr t) =>
  Net t arr a b ->
  C.Trace t arr a b
melt (Lift f) = C.Arr f
melt (Compose g f) = melt g . melt f
melt (Knot f) = trace (melt f)
melt (Par f g) = C.Arr (par (C.run (melt f)) (C.run (melt g)))
melt Swap = C.Arr swap
melt Copy = C.Arr Dg.copy
melt Discard = C.Arr Dg.discard
melt Plus = C.Arr Dg.plus
melt Zero = C.Arr Dg.zero
