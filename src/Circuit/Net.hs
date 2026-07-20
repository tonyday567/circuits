{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free traced PROP with a bimonoid over a primitive set.
--
-- 'Net' extends 'C.Loop' with structural rows for the monoidal and
-- bimonoid operations: parallel composition, copy, discard, addition,
-- and zero.  Where 'C.Loop' keeps only 'C.Lift' and 'C.Knot' in normal
-- form, 'Net' keeps the wiring inspectable — the difference between
-- wiring you can read backwards and wiring that has been melted into a
-- single loop.
--
-- @
-- Free = Lift + Compose
-- Sym  = Free + Par + Swap
-- Net  = Sym + Knot + Copy + Discard + Plus + Zero
-- @
--
-- 'run' @Net@ interprets a 'Net' to a plain arrow.  'melt' interprets the
-- structural rows into the normal form of 'C.Loop'.
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

    -- * Free Net constraint
    FreeNet,
  )
where

import Circuit.Category (Category (..), Discrete (..), (>>>))
import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer (..), (:~>))
import Circuit.Layer qualified as Layer
import Circuit.Sym qualified as M
import Circuit.Tensor (Action (..), Tensor (..))
import Circuit.Loop (Traced (..))
import Circuit.Loop qualified as C
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger qualified as Dg
-- >>> import Circuit.Layer (bind, run, unit)
-- >>> import Circuit.Sym qualified as M
-- >>> import Circuit.Net
-- >>> import Circuit.Loop (Loop (Knot))
-- >>> import Circuit.Loop qualified as C
-- >>> import Prelude hiding (id, (.))

-- | The free traced PROP with a bimonoid.
--
-- Four families of constructor:
--
--   * __Sequential__ — 'Lift', 'Compose'.
--   * __Monoidal__ — 'Par', 'Swap' (parallel composition, braiding).
--   * __Bimonoid__ — 'Copy', 'Discard' (comonoid), 'Plus', 'Zero' (monoid).
--   * __Feedback__ — 'Knot', with a 'Net' body so 'transpose' can reach inside.
--
-- 'Dg.Comonoid' and 'Dg.WireMonoid' (via 'Dg.Bimonoid') constraints ride as dictionary arguments on the
-- constructors that need them — laws in the typeclass holes, evidence on
-- the GADT rows.
--
-- The wiring monoidal structure ('Par' / 'Swap') is cartesian: it always
-- uses @(,)@. Only the feedback tensor carried by 'Knot' is polymorphic
-- in @t@. This is why 'Net' is a PROP over the cartesian wiring category
-- with feedback supplied by the traced tensor.
--
-- 'Net' extends 'C.Loop' inspectably. 'enrich' embeds a 'Loop' into
-- 'Net', and 'melt' collapses it back; 'melt' . 'enrich' = 'id'.
data Net (t :: Type -> Type -> Type) arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Net t arr a b
  -- | Sequential composition.
  --
  -- The 'Ob' constraint on the intermediate object @b@ is carried in the
  -- constructor so folding does not need a 'Discrete' base.
  Compose :: Ob arr b => Net t arr b c -> Net t arr a b -> Net t arr a c
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
  --
  -- The constructor carries the 'Ob' evidence for the feedback channel in
  -- the /source/ category.
  Knot :: Ob arr s => Net t arr (t s a) (t s b) -> Net t arr a b

-- | The 'Category' instance preserves inspectable wiring.
--
-- Composition uses the explicit 'Compose' constructor, so 'Copy',
-- 'Plus', 'Par', and 'Knot' stay visible.  'melt' collapses the
-- structure when the normal form is needed.
--
-- Composition uses the explicit 'Compose' constructor so structural
-- rows remain inspectable.  'melt' collapses them to the normal form of
-- 'C.Loop' when needed.
instance (Category arr) => Category (Net t arr) where
  type Ob (Net t arr) a = Ob arr a
  id = Lift id
  g . f = Compose g f

-- | A discrete base yields a discrete free traced PROP.
instance (Category arr, Discrete arr) => Discrete (Net t arr) where
  withOb @a x = withOb @arr @a x

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

-- | Upgrade a 'C.Loop' to a 'Net' — constructor-to-constructor.
--
-- 'C.Loop' is the normal form 'C.Lift' / 'C.Knot' over a base-arrow body;
-- 'Net' keeps the same information but can hold more structure.
-- 'C.Lift' lifts to 'Net.Lift'; 'C.Knot' lifts to 'Net.Knot' around a
-- 'Lift' body.
enrich :: C.Loop t arr a b -> Net t arr a b
enrich (C.Lift f) = Lift f
enrich (C.Knot f) = Knot (Lift f)

-- | Include a 'M.Sym' circuit into 'Net' — constructor-to-constructor.
--
-- 'Net' duplicates the four rows of 'M.Sym' ('Lift', 'Compose', 'Par',
-- 'Swap') so that structural wiring stays inspectable.  This is the
-- injection of the 'Sym' layer into the 'Net' layer.
--
-- >>> let m = M.Lift (+1) `M.Compose` M.Lift (*2) :: M.Sym (->) Int Int
-- >>> run (widen m :: Net (,) (->) Int Int) 5
-- 11
--
-- Coherence: 'sift' projects 'widen' back to the original 'Sym'.
--
-- >>> run (sift (widen m :: Net (,) (->) Int Int)) 5
-- 11
-- >>> run m 5
-- 11
--
-- Coherence: 'melt' agrees with the function fold on 'Sym' circuits.
--
-- >>> run (melt (widen m :: Net (,) (->) Int Int)) 5
-- 11
-- >>> let h f = f
-- >>> (bind h m :: Int -> Int) 5
-- 11
--
-- Coherence: 'Net' folds through 'widen' match 'Sym' folds.
--
-- >>> let h f = f
-- >>> (bind h (widen m :: Net (,) (->) Int Int) :: Int -> Int) 5
-- 11
-- >>> (bind h m :: Int -> Int) 5
-- 11
--
-- Coherence: transposition commutes with 'widen'.
--
-- >>> let dm = M.Lift (Dg.Dagger (+1) (subtract 1)) `M.Compose` M.Lift (Dg.Dagger (*2) (\x -> x `div` 2)) :: M.Sym (Dg.Dagger (->)) Int Int
-- >>> Dg.front (run (transpose (widen dm :: Net (,) (Dg.Dagger (->)) Int Int))) 10
-- 4
-- >>> Dg.front (run (widen (M.monTranspose dm) :: Net (,) (Dg.Dagger (->)) Int Int)) 10
-- 4
widen :: M.Sym arr a b -> Net t arr a b
widen (M.Lift f) = Lift f
widen (M.Compose g f) = Compose (widen g) (widen f)
widen (M.Par f g) = Par (widen f) (widen g)
widen M.Swap = Swap

-- | Forget the feedback and bimonoid rows of a 'Net', keeping only the
-- 'M.Sym' wiring.
--
-- 'sift' collapses 'Knot' and the bimonoid rows into 'M.Lift' while
-- leaving 'Compose', 'Par', and 'Swap' inspectable. Together with 'widen'
-- it gives the adjunction between 'M.Sym' and 'Net'.
-- Note the converse does not hold: @widen . sift ≠ id@ because 'sift'
-- forgets knots and bimonoid structure.
sift ::
  forall t arr a b.
  (Traced t arr, Action (,) arr, Discrete arr) =>
  Net t arr a b ->
  M.Sym arr a b
sift (Lift f) = M.Lift f
sift (Compose g f) = M.Compose (sift g) (sift f)
sift (Par f g) = M.Par (sift f) (sift g)
sift Swap = M.Swap
sift Copy = M.Lift Dg.copy
sift Discard = M.Lift Dg.discard
sift Plus = M.Lift Dg.plus
sift Zero = M.Lift Dg.zero
sift n@(Knot @_ @s @_ @_ @_ _) =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @(t s a) $
        withOb @arr @(t s b) $
          M.Lift (Layer.run (melt n))

-- | Melt the structural rows of a 'Net' into the normal form of 'C.Loop'.
--
-- The interpretation from the free traced PROP with bimonoid to the free
-- traced monoidal category.  Structural rows ('Par', 'Copy', 'Plus',
-- etc.) become opaque base-arrow operations wrapped in 'C.Lift'; 'Compose'
-- and 'C.Knot' use the 'Category' and 'Traced' instances of 'C.Loop'.
--
-- @'run' @Net = 'run' . 'melt'@.
--
-- >>> run (melt (Lift (+1) :: Net (,) (->) Int Int)) 5
-- 6
melt ::
  forall t arr a b.
  (Traced t arr, Action (,) arr, Discrete arr) =>
  Net t arr a b ->
  C.Loop t arr a b
melt (Lift f) = C.Lift f
melt (Compose @_ @b1 @_ @_ @_ g f) =
  withOb @arr @a $
    withOb @arr @b1 $
      withOb @arr @b $
        (melt g . melt f)
melt (Par f g) = par (melt f) (melt g)
melt Swap = C.Lift swap
melt Copy = C.Lift Dg.copy
melt Discard = C.Lift Dg.discard
melt Plus = C.Lift Dg.plus
melt Zero = C.Lift Dg.zero
melt (Knot @_ @s @_ @_ @_ f) =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @(t s a) $
        withOb @arr @(t s b) $
          trace (melt f)

-- | 'Traced' + 'Action' + 'Discrete' — free 'Net' fold needs trivial 'Ob'.
class (Traced t arr, Action (,) arr, Discrete arr) => FreeNet t arr

instance (Traced t arr, Action (,) arr, Discrete arr) => FreeNet t arr

-- | Free traced PROP with a bimonoid.
--
-- Structural rows are interpreted in the target category: parallel
-- composition uses 'par', braiding uses 'swap', and the bimonoid
-- generators are the images under @h@ of the source dictionaries carried
-- by the 'Copy', 'Discard', 'Plus', and 'Zero' constructors.
--
-- [Conditional] 'bind' @h@ interprets bimonoid generators as images under
-- @h@ of the source arrow's dictionaries.  This is the free-PROP fold
-- only when @h@ is a bimonoid homomorphism (automatic for the generator
-- embedding, but must be verified for custom @h@).
instance Layer (Net t) where
  type Law (Net t) arr' = FreeNet t arr'
  type Run (Net t) arr = (Traced t arr, Action (,) arr, Discrete arr)
  type Bind (Net t) arr = Discrete arr
  unit = Lift
  run = Layer.run . melt
  bind :: forall arr' arr a b. (Law (Net t) arr', Bind (Net t) arr, Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) => (arr :~> arr') -> Net t arr a b -> arr' a b
  bind h (Lift f) = h f
  bind h (Compose @_ @b1 @_ @_ @_ g f) =
    withOb @arr @b1 $
      withOb @arr' @b1 $
        (bind h g . bind h f)
  bind h (Par @_ @_ @a1 @b1 @c @d f g) =
    withOb @arr @a1 $
      withOb @arr @b1 $
        withOb @arr @c $
          withOb @arr @d $
            withOb @arr' @a1 $
              withOb @arr' @b1 $
                withOb @arr' @c $
                  withOb @arr' @d $
                    par (bind h f) (bind h g)
  bind _ Swap = swap
  bind h Copy = h Dg.copy
  bind h Discard = h Dg.discard
  bind h Plus = h Dg.plus
  bind h Zero = h Dg.zero
  bind h (Knot @_ @s @_ @_ @_ f) =
    withOb @arr @s $
      withOb @arr @(t s a) $
        withOb @arr @(t s b) $
          withOb @arr' @s $
            withOb @arr' @(t s a) $
              withOb @arr' @(t s b) $
                trace (bind h f)
