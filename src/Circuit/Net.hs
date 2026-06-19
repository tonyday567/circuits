{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free traced PROP with a bimonoid over a primitive set.
--
-- 'Net' extends 'Trace' with structural rows for the monoidal and
-- bimonoid operations: parallel composition, copy, discard, addition,
-- and zero.  Where 'Trace' dissolved these into opaque 'Lift' calls,
-- 'Net' keeps them as inspectable constructors — the difference between
-- wiring you can read backwards and wiring that's been melted into the
-- prims.
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

import Circuit.Trace qualified as C
import Circuit.Dagger qualified as Dg
import Circuit.Monoidal (MonoidalP (..))
import Circuit.Traced
import Prelude hiding (Monoid, id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Circuit.Trace (Trace(..), realise)
-- >>> import Circuit.Net
-- >>> import Prelude hiding (id, (.), Monoid)

-- | The free traced PROP with a bimonoid.
--
-- Three families of constructor:
--
--   * __Circuit heritage__ — 'Lift', 'Compose', 'Trace' (unchanged).
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
  Trace :: Net t arr (t a b) (t a c) -> Net t arr b c

-- | Transpose a 'Net' — the backward circuit as inspectable syntax.
--
-- The structural rows are self-dual under transposition:
-- 'Compose' reverses, 'Copy' ↔ 'Plus', 'Discard' ↔ 'Zero',
-- 'Trace' ↔ 'Trace' (recurring into the body).
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
  Trace f -> Trace (transpose f)
#else
transpose = undefined
#endif

-- | Upgrade a 'Trace' to a 'Net' — constructor-to-constructor.
--
-- The structural rows ('Par', 'Copy', 'Plus', etc.) are absent from
-- 'Trace', so upgrading a lifted 'Trace' produces a 'Net' with
-- only 'Lift', 'Compose', and 'Trace' — the same information, now in
-- a GADT that can hold more.  'Circuit.Trace' lifts to 'Net.Trace'.
enrich :: C.Trace t arr a b -> Net t arr a b
enrich (C.Lift f) = Lift f
enrich (C.Compose f g) = Compose (enrich f) (enrich g)
enrich (C.Trace f) = Trace (enrich f)

-- | Interpret a 'Net' to a plain arrow.
--
-- The canonical map out of the free traced PROP with a bimonoid.
-- Structural rows dispatch to their typeclass counterparts:
-- 'Par' to 'par', 'Copy' to 'copy', 'Plus' to 'plus', etc.
-- 'Trace' uses the 'Trace' instance on the base arrow.
--
-- @'weave' = 'C.realise' . 'melt'@ — first melt structural rows into
-- 'Trace', then realise to a plain arrow.  The Mendler sliding case is
-- handled once in 'Circuit.Trace.freeze'.
--
-- >>> weave (Circuit.Net.Lift (+1) :: Net (,) (->) Int Int) 5
-- 6
weave ::
  (Traced arr t, MonoidalP arr) =>
  Net t arr a b ->
  arr a b
weave = C.realise . melt

-- | Melt the structural rows of a 'Net' into opaque 'Lift' calls.
--
-- The forgetful map from the free traced PROP with bimonoid to the free
-- traced monoidal category.  Structural rows ('Par', 'Copy', 'Plus',
-- etc.) become opaque base-arrow operations; the 'Trace' and 'Compose'
-- structure is preserved.
--
-- 'weave' factors through 'melt': @weave = realise . melt@.
--
-- >>> realise (melt (Circuit.Net.Lift (+1) :: Net (,) (->) Int Int)) 5
-- 6
melt ::
  (Traced arr t, MonoidalP arr) =>
  Net t arr a b ->
  C.Trace t arr a b
melt = \case
  Lift f -> C.Lift f
  Compose g f -> C.Compose (melt g) (melt f)
  Par f g -> C.Lift (par (weave f) (weave g))
  Swap -> C.Lift swap
#ifdef __GLASGOW_HASKELL__
  Copy -> C.Lift Dg.copy
  Discard -> C.Lift Dg.discard
  Plus -> C.Lift Dg.plus
  Zero -> C.Lift Dg.zero
#else
  _ -> undefined
#endif
  Trace f -> C.Trace (melt f)
