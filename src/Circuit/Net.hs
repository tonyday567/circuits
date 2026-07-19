{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free traced PROP with a bimonoid over a primitive set.
--
-- 'Net' extends 'C.Trace' with structural rows for the monoidal and
-- bimonoid operations: parallel composition, copy, discard, addition,
-- and zero.  Where 'C.Trace' keeps only 'C.Arr' and 'C.Knot' in normal
-- form, 'Net' keeps the wiring inspectable — the difference between
-- wiring you can read backwards and wiring that has been melted into a
-- single loop.
--
-- @
-- Free = Lift + Compose
-- Mon  = Free + Par + Swap
-- Net  = Mon + Knot + Copy + Discard + Plus + Zero
-- @
--
-- 'run' @Net@ interprets a 'Net' to a plain arrow.  'melt' interprets the
-- structural rows into the normal form of 'C.Trace'; the overlapping
-- @Action (,) (C.Trace t arr)@ instance is what absorbs parallel 'Knot's.
module Circuit.Net
  ( -- * Net
    Net (..),

    -- * Transposition
    transpose,

    -- * Conversion
    enrich,
    widen,
    sift,

    -- * Interpretation
    melt,
  )
where

import Circuit.Classes (Category (..), Discrete (..), (>>>))
import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.Mon qualified as M
import Circuit.Tensor (Action (..), Tensor (..))
import Circuit.Trace (Traced (..), compD, traceD)
import Circuit.Trace qualified as C
import Data.Kind (Type)
import Prelude hiding (Monoid, id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Circuit.Dagger qualified as Dg
-- >>> import Circuit.Layer (bind, run, unit)
-- >>> import Circuit.Mon qualified as M
-- >>> import Circuit.Net
-- >>> import Circuit.Trace (Trace (..))
-- >>> import Circuit.Trace qualified as C
-- >>> import Prelude hiding (id, (.), Monoid)

-- | The free traced PROP with a bimonoid.
--
-- Four families of constructor:
--
--   * __Sequential__ — 'Lift', 'Compose'.
--   * __Monoidal__ — 'Par', 'Swap' (parallel composition, braiding).
--   * __Bimonoid__ — 'Copy', 'Discard' (comonoid), 'Plus', 'Zero' (monoid).
--   * __Feedback__ — 'Knot', with a 'Net' body so 'transpose' can reach inside.
--
-- 'Dg.Comonoid' and 'Dg.Monoid' constraints ride as dictionary arguments on the
-- constructors that need them — laws in the typeclass holes, evidence on
-- the GADT rows.
data Net (t :: Type -> Type -> Type) arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Net t arr a b
  -- | Sequential composition.
  Compose :: Net t arr b c -> Net t arr a b -> Net t arr a c
  -- | Parallel composition (monoidal product).
  Par :: Net t arr a b -> Net t arr c d -> Net t arr (a, c) (b, d)
  -- | Symmetric braiding.
  Swap :: Net t arr (a, b) (b, a)
  -- | Copy: fan-out.  Requires both comonoid and monoid ('Dg.Bimonoid').
  Copy :: (Dg.Bimonoid arr a) => Net t arr a (a, a)
  -- | Discard: erase.  Requires 'Dg.Bimonoid'.
  Discard :: (Dg.Bimonoid arr a) => Net t arr a ()
  -- | Plus: fan-in.  Requires 'Dg.Bimonoid'.
  Plus :: (Dg.Bimonoid arr a) => Net t arr (a, a) a
  -- | Zero: the neutral element.  Requires 'Dg.Bimonoid'.
  Zero :: (Dg.Bimonoid arr a) => Net t arr () a
  -- | Feedback loop.  The body is a 'Net', not an opaque base arrow —
  -- so 'transpose' can reach inside and swap 'Copy' ↔ 'Plus' within
  -- the loop.
  Knot :: Net t arr (t a b) (t a c) -> Net t arr b c

-- | The 'Category' instance preserves inspectable wiring.
--
-- Composition uses the explicit 'Compose' constructor, so 'Copy',
-- 'Plus', 'Par', and 'Knot' stay visible.  'melt' collapses the
-- structure when the normal form is needed.
--
-- For the @(,)@ feedback tensor, composing two 'Knot's fuses their
-- channels into a pair. This terminates when the structure maps and the
-- user knot bodies match the channel lazily; strict bodies still
-- diverge, as documented in "Circuit.Monoidal".
instance (Category arr) => Category (Net t arr) where
  type Ob (Net t arr) a = Ob arr a
  id = Lift id
  g . f = Compose g f

-- | Transpose a 'Net' — the backward circuit as inspectable syntax.
--
-- The structural rows are self-dual under transposition:
-- 'Compose' reverses, 'Par' transposes componentwise, 'Copy' ↔ 'Plus',
-- 'Discard' ↔ 'Zero', 'Knot' ↔ 'Knot' (recurring into the body).
--
-- 'Lift' transposes via 'Dg.Dagger' field swap — only nets over
-- 'Dg.Dagger' are transposable, since the forward\/backward pairing is
-- structural in the base arrow.
--
-- Law: @transpose . transpose = id@.
--
-- >>> import Circuit.Dagger qualified as Dg
-- >>> let n1 = Lift (Dg.Dagger (+1) (subtract 1)) :: Net (,) (Dg.Dagger (->)) Int Int
-- >>> let n2 = Lift (Dg.Dagger (+1) (subtract 1)) `Compose` Lift (Dg.Dagger (+1) (subtract 1)) :: Net (,) (Dg.Dagger (->)) Int Int
-- >>> Dg.front (run (transpose (transpose n1))) 5
-- 6
-- >>> Dg.front (run (transpose (transpose n2))) 5
-- 7
--
-- Asymmetric factors catch the direction of 'Compose' reversal:
-- forward is @(*2) . (+1)@, backward is @(subtract 1) . (`div` 2)@.
--
-- >>> let n3 = Lift (Dg.Dagger (+1) (subtract 1)) `Compose` Lift (Dg.Dagger (*2) (\x -> x `div` 2)) :: Net (,) (Dg.Dagger (->)) Int Int
-- >>> Dg.front (run (transpose n3)) 10
-- 4
transpose ::
  Net t (Dg.Dagger arr) a b ->
  Net t (Dg.Dagger arr) b a
#ifdef __GLASGOW_HASKELL__
transpose = \case
  Lift (Dg.Dagger f g) -> Lift (Dg.Dagger g f)
  Compose g f -> Compose (transpose f) (transpose g)
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

-- | Upgrade a 'C.Trace' to a 'Net' — constructor-to-constructor.
--
-- 'C.Trace' is the normal form 'C.Arr' / 'C.Knot' over a base-arrow body;
-- 'Net' keeps the same information but can hold more structure.
-- 'C.Arr' lifts to 'Net.Lift'; 'C.Knot' lifts to 'Net.Knot' around a
-- 'Lift' body.
enrich :: C.Trace t arr a b -> Net t arr a b
enrich (C.Arr f) = Lift f
enrich (C.Knot f) = Knot (Lift f)

-- | Include a 'M.Mon' circuit into 'Net' — constructor-to-constructor.
--
-- 'Net' duplicates the four rows of 'M.Mon' ('Arr', 'Compose', 'Par',
-- 'Swap') so that structural wiring stays inspectable.  This is the
-- injection of the 'Mon' layer into the 'Net' layer.
--
-- >>> let m = M.Arr (+1) `M.Compose` M.Arr (*2) :: M.Mon (->) Int Int
-- >>> run (widen m :: Net (,) (->) Int Int) 5
-- 11
--
-- Coherence: 'sift' projects 'widen' back to the original 'Mon'.
--
-- >>> run (sift (widen m :: Net (,) (->) Int Int)) 5
-- 11
-- >>> run m 5
-- 11
--
-- Coherence: 'melt' and 'bind unit' agree on 'Mon' circuits.
--
-- >>> run (melt (widen m :: Net (,) (->) Int Int)) 5
-- 11
-- >>> run (bind unit m :: Trace (,) (->) Int Int) 5
-- 11
--
-- Coherence: 'Net' folds through 'widen' match 'Mon' folds.
--
-- >>> let h :: forall x y. (x -> y) -> Trace (,) (->) x y; h f = C.Arr f
-- >>> run (bind h (widen m :: Net (,) (->) Int Int)) 5
-- 11
-- >>> run (bind h m) 5
-- 11
--
-- Coherence: transposition commutes with 'widen'.
--
-- >>> let dm = M.Arr (Dg.Dagger (+1) (subtract 1)) `M.Compose` M.Arr (Dg.Dagger (*2) (\x -> x `div` 2)) :: M.Mon (Dg.Dagger (->)) Int Int
-- >>> Dg.front (run (transpose (widen dm :: Net (,) (Dg.Dagger (->)) Int Int))) 10
-- 4
-- >>> Dg.front (run (widen (M.monTranspose dm) :: Net (,) (Dg.Dagger (->)) Int Int)) 10
-- 4
widen :: M.Mon arr a b -> Net t arr a b
widen (M.Arr f) = Lift f
widen (M.Compose g f) = Compose (widen g) (widen f)
widen (M.Par f g) = Par (widen f) (widen g)
widen M.Swap = Swap

-- | Forget the feedback and bimonoid rows of a 'Net', keeping only the
-- 'M.Mon' wiring.
--
-- 'sift' is 'bind unit', so it collapses 'Knot' and the bimonoid rows
-- into 'M.Arr' while leaving 'Compose', 'Par', and 'Swap' inspectable.
-- Together with 'widen' it gives the layer inclusion @Mon ↪ Net@.
-- Note the converse does not hold: @widen . sift ≠ id@ because 'sift'
-- forgets knots and bimonoid structure.
sift ::
  (Traced t (->), Action (,) (->)) =>
  Net t (->) a b ->
  M.Mon (->) a b
sift = bind unit

-- | Melt the structural rows of a 'Net' into the normal form of 'C.Trace'.
--
-- The interpretation from the free traced PROP with bimonoid to the free
-- traced monoidal category.  Structural rows ('Par', 'Copy', 'Plus',
-- etc.) become opaque base-arrow operations wrapped in 'C.Arr'; 'Compose'
-- and 'C.Knot' use the 'Category' and 'Traced' instances of 'C.Trace'.
-- Parallel 'Knot's are absorbed by the overlapping
-- @Action (,) (C.Trace t arr)@ instance, not by 'melt' alone.
--
-- @'run' @Net = 'C.run' . 'melt'@.
--
-- >>> run (melt (Lift (+1) :: Net (,) (->) Int Int)) 5
-- 6
melt ::
  (Traced t (->), Action (,) (->), Action (,) (C.Trace t (->))) =>
  Net t (->) a b ->
  C.Trace t (->) a b
melt (Lift f) = C.Arr f
melt (Compose g f) = melt g . melt f
melt (Par f g) = par (melt f) (melt g)
melt Swap = C.Arr swap
melt Copy = C.Arr Dg.copy
melt Discard = C.Arr Dg.discard
melt Plus = C.Arr Dg.plus
melt Zero = C.Arr Dg.zero
melt (Knot f) = trace (melt f)

-- | Free traced PROP with a bimonoid.
--
-- Structural rows are interpreted in the target category: parallel
-- composition uses 'par', braiding uses 'swap', and the bimonoid
-- generators are the images under @h@ of the source dictionaries carried
-- by the 'Copy', 'Discard', 'Plus', and 'Zero' constructors.
--
-- [Conditional] 'bind' @h@ interprets bimonoid generators as images under
-- @h@ of the source arrow's dictionaries.  This is the free-PROP fold
-- only when @h@ is a bimonoid homomorphism (automatic for 'unit' and
-- 'hmap', but must be verified for custom @h@).
-- | 'Traced' + 'Action' + 'Discrete' — free 'Net' fold needs trivial 'Ob'.
class (Traced t arr, Action (,) arr, Discrete arr) => FreeNet t arr

instance (Traced t arr, Action (,) arr, Discrete arr) => FreeNet t arr

instance Layer (Net t) where
  type Law (Net t) arr' = FreeNet t arr'
  unit = Lift
  bind :: forall arr' arr. (Law (Net t) arr') => (arr :~> arr') -> (Net t arr :~> arr')
  bind h (Lift f) = h f
  bind h (Compose g f) = bind h g `compD` bind h f
  bind h (Par f g) = par (bind h f) (bind h g)
  bind _ Swap = swap
  bind h Copy = h Dg.copy
  bind h Discard = h Dg.discard
  bind h Plus = h Dg.plus
  bind h Zero = h Dg.zero
  bind h (Knot f) = traceD (bind h f)
