{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
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

    -- * Sym
    Sym (..),
    FreeSym,

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

import Circuit.Category (Category (..), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger qualified as Dg
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.Layer qualified as Layer
import Circuit.Loop qualified as C
import Circuit.Tensor (Action (..), Tensor (..), Unit)
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger qualified as Dg
-- >>> import Circuit.Layer (bind, run, unit)
-- >>> import Circuit.Net
-- >>> import Circuit.Loop (Loop (Knot))
-- >>> import Circuit.Loop qualified as C
-- >>> import Prelude hiding (id, (.))

-- | The free traced PROP with a bimonoid.
--
-- Four families of constructor:
--
--   * __Sequential__ — @Lift@, @Compose@.
--   * __Monoidal__ — 'Par', 'Swap' (parallel composition, braiding).
--   * __Copy/Discard__ — the comonoid on channel objects.
--   * __Plus/Zero__ — the monoid on channel objects.
--   * __Feedback__ — 'Knot', with a 'Net' body so 'transpose' can reach inside.
--
-- 'Dg.CopyT' / 'Dg.DiscardT' and 'Dg.MergeT' / 'Dg.ZeroT' constraints ride
-- as dictionary arguments on the constructors that need them — laws in the
-- typeclass holes, evidence on the GADT rows.
--
-- The wiring monoidal structure ('Par' / 'Swap') is over a generic tensor
-- @w@. The feedback tensor @t@ carried by 'Knot' remains polymorphic and
-- independent of @w@. This is why 'Net' is a PROP over a symmetric monoidal
-- wiring category with feedback supplied by the traced tensor.
--
-- 'Net' extends 'C.Loop' inspectably. 'enrich' embeds a 'Loop' into
-- 'Net', and 'melt' collapses it back; 'melt' . 'enrich' = 'id'.
data Net (w :: Type -> Type -> Type) (t :: Type -> Type -> Type) arr a b where
  -- | Embed a base arrow.
  Lift :: arr a b -> Net w t arr a b
  -- | Sequential composition.
  Compose :: Net w t arr b c -> Net w t arr a b -> Net w t arr a c
  -- | Parallel composition (monoidal product over @w@).
  Par ::
    Net w t arr a b ->
    Net w t arr c d ->
    Net w t arr (w a c) (w b d)
  -- | Symmetric braiding over @w@.
  Swap :: Net w t arr (w a b) (w b a)
  -- | Copy: fan-out.  Requires 'Dg.CopyT' on the wiring tensor @w@.
  Copy ::
    (Dg.CopyT w arr a) =>
    Net w t arr a (w a a)
  -- | Discard: erase.  Requires 'Dg.DiscardT' on the wiring tensor @w@.
  Discard ::
    (Dg.DiscardT w arr a) =>
    Net w t arr a (Unit w)
  -- | Plus: fan-in.  Requires 'Dg.MergeT' on the wiring tensor @w@.
  Plus ::
    (Dg.MergeT w arr a) =>
    Net w t arr (w a a) a
  -- | Zero: the neutral element.  Requires 'Dg.ZeroT' on the wiring tensor @w@.
  Zero ::
    (Dg.ZeroT w arr a) =>
    Net w t arr (Unit w) a
  -- | Feedback loop.  The body is a 'Net', not an opaque base arrow.
  Knot ::
    Net w t arr (t s a) (t s b) ->
    Net w t arr a b

-- | The 'Category' instance preserves inspectable wiring.
--
-- Composition uses the explicit @Compose@ constructor, so 'Copy',
-- 'Plus', 'Par', and 'Knot' stay visible.  'melt' collapses the
-- structure when the normal form is needed.
--
-- Composition uses the explicit @Compose@ constructor so structural
-- rows remain inspectable.  'melt' collapses them to the normal form of
-- 'C.Loop' when needed.
instance (Category arr) => Category (Net w t arr) where
  id = Lift id
  g . f = Compose g f

-- | Upgrade a 'C.Loop' to a 'Net' — constructor-to-constructor.
--
-- 'C.Loop' is the normal form 'C.Lift' / 'C.Knot' over a base-arrow body;
-- 'Net' keeps the same information but can hold more structure.
-- 'C.Lift' lifts to 'Net.Lift'; 'C.Knot' lifts to 'Net.Knot' around a
-- @Lift@ body.
enrich :: C.Loop t arr a b -> Net w t arr a b
enrich (C.Lift f) = Lift f
enrich (C.Knot f) = Knot (Lift f)

-- | Include a 'Sym' circuit into 'Net' — constructor-to-constructor.
--
-- 'Net' duplicates the four rows of 'Sym' (@SymLift@, @SymCompose@, 'SymPar',
-- 'SymSwap') so that structural wiring stays inspectable.  This is the
-- injection of the 'Sym' layer into the 'Net' layer.
--
-- >>> let m = SymLift (+1) `SymCompose` SymLift (*2) :: Sym (,) (->) Int Int
-- >>> run (widen m :: Net (,) (,) (->) Int Int) 5
-- 11
--
-- Coherence: 'sift' projects 'widen' back to the original 'Sym'.
--
-- >>> run (sift (widen m :: Net (,) (,) (->) Int Int)) 5
-- 11
-- >>> run m 5
-- 11
--
-- Coherence: 'melt' agrees with the function fold on 'Sym' circuits.
--
-- >>> run (melt (widen m :: Net (,) (,) (->) Int Int)) 5
-- 11
-- >>> let h f = f
-- >>> (bind h m :: Int -> Int) 5
-- 11
--
-- Coherence: 'Net' folds through 'widen' match 'Sym' folds.
--
-- >>> let h f = f
-- >>> (bind h (widen m :: Net (,) (,) (->) Int Int) :: Int -> Int) 5
-- 11
-- >>> (bind h m :: Int -> Int) 5
-- 11
--
-- Coherence: transposition commutes with 'widen'.
--
-- >>> let dm = SymLift (Dg.Dagger (+1) (subtract 1)) `SymCompose` SymLift (Dg.Dagger (*2) (\x -> x `div` 2)) :: Sym (,) (Dg.Dagger (->)) Int Int
-- >>> Dg.front (Dg.transpose (run dm)) 10
-- 4
-- >>> Dg.front (Dg.transpose (run (widen dm :: Net (,) (,) (Dg.Dagger (->)) Int Int))) 10
-- 4
widen :: Sym w arr a b -> Net w t arr a b
widen (SymLift f) = Lift f
widen (SymCompose g f) = Compose (widen g) (widen f)
widen (SymPar f g) = Par (widen f) (widen g)
widen SymSwap = Swap

-- | Forget the feedback and bimonoid rows of a 'Net', keeping only the
-- 'Sym' wiring.
--
-- 'sift' collapses 'Knot' and the bimonoid rows into 'SymLift' while
-- leaving @Compose@, 'Par', and 'Swap' inspectable. Together with 'widen'
-- it gives the adjunction between 'Sym' and 'Net'.
-- Note the converse does not hold: @widen . sift ≠ id@ because 'sift'
-- forgets knots and bimonoid structure.
sift ::
  forall w t arr a b.
  (Traced t arr, Action w arr) =>
  Net w t arr a b ->
  Sym w arr a b
sift (Lift f) = SymLift f
sift (Compose g f) = SymCompose (sift g) (sift f)
sift (Par f g) = SymPar (sift f) (sift g)
sift Swap = SymSwap
sift Copy = SymLift (Dg.copyT @w)
sift Discard = SymLift (Dg.discardT @w)
sift Plus = SymLift (Dg.plusT @w)
sift Zero = SymLift (Dg.zeroT @w)
sift n@(Knot @_ @_ @_ @_ @_ _) = SymLift (Layer.run (melt n))

-- | Melt the structural rows of a 'Net' into the normal form of 'C.Loop'.
--
-- The interpretation from the free traced PROP with bimonoid to the free
-- traced monoidal category.  Structural rows ('Par', 'Copy', 'Plus',
-- etc.) become opaque base-arrow operations wrapped in 'C.Lift'; @Compose@
-- and 'C.Knot' use the 'Category' and 'Traced' instances of 'C.Loop'.
--
-- @'run' @Net = 'run' . 'melt'@.
--
-- >>> run (melt (Lift (+1) :: Net (,) (,) (->) Int Int)) 5
-- 6
melt ::
  forall w t arr a b.
  (Traced t arr, Action w arr) =>
  Net w t arr a b ->
  C.Loop t arr a b
melt (Lift f) = C.Lift f
melt (Compose g f) = melt g . melt f
melt (Par f g) = par (melt f) (melt g)
melt Swap = C.Lift swap
melt Copy = C.Lift (Dg.copyT @w)
melt Discard = C.Lift (Dg.discardT @w)
melt Plus = C.Lift (Dg.plusT @w)
melt Zero = C.Lift (Dg.zeroT @w)
melt (Knot f) = trace (melt f)

-- | 'Traced' + 'Action' — free 'Net' fold carries its own structure.
class (Traced t arr, Action w arr) => FreeNet w t arr

instance (Traced t arr, Action w arr) => FreeNet w t arr

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
instance Layer (Net w t) where
  type Law (Net w t) arr' = FreeNet w t arr'
  type Run (Net w t) arr = (Traced t arr, Action w arr)
  type Bind (Net w t) arr = ()
  unit = Lift
  bind ::
    forall arr' arr a b.
    (Law (Net w t) arr') =>
    (arr :~> arr') ->
    Net w t arr a b ->
    arr' a b
  bind h (Lift f) = h f
  bind h (Compose (g :: Net w t arr b1 c) (f :: Net w t arr a b1)) =
    bind h g . bind h f
  bind h (Par (f :: Net w t arr a1 b1) (g :: Net w t arr c d)) =
    par (bind h f) (bind h g)
  bind _h Swap = swap
  bind h Copy = h (Dg.copyT @w)
  bind h Discard = h (Dg.discardT @w)
  bind h Plus = h (Dg.plusT @w)
  bind h Zero = h (Dg.zeroT @w)
  bind h (Knot (f :: Net w t arr (t s a) (t s b))) =
    trace (bind h f)

-- ===========================================================================
-- Sym
-- ===========================================================================

-- | The free symmetric monoidal category over a base arrow.
--
-- 'Sym' extends the free category ('Free') with explicit
-- monoidal product ('SymPar') and symmetry ('SymSwap') syntax.  It is the
-- intermediate layer between 'Free' and 'Net':
--
-- @
-- Free = Lift + Compose
-- Sym  = Free + Par + Swap
-- Net  = Sym + Knot + Copy + Discard + Plus + Zero
-- @
--
-- The tensor is the wiring tensor @w@, matching 'Circuit.Tensor.Action'.
--
-- Four constructors:
--
--   * 'SymLift' — embed a base arrow.
--   * 'SymCompose' — sequential composition.
--   * 'SymPar' — tensor product of morphisms (parallel composition).
--   * 'SymSwap' — symmetry / braiding.
data Sym (w :: Type -> Type -> Type) arr a b where
  -- | Embed a base arrow.
  SymLift :: arr a b -> Sym w arr a b
  -- | Sequential composition.
  SymCompose :: Sym w arr b c -> Sym w arr a b -> Sym w arr a c
  -- | Tensor product of morphisms (parallel composition on disjoint wires).
  SymPar ::
    Sym w arr a b ->
    Sym w arr c d ->
    Sym w arr (w a c) (w b d)
  -- | Symmetric braiding.
  SymSwap :: Sym w arr (w a b) (w b a)

-- | 'Sym' is a category.
instance (Category arr) => Category (Sym w arr) where
  id = SymLift id
  (.) = SymCompose

-- | 'Sym' has a tensor structure over @w@.
--
-- This is the syntactic instance: 'SymPar' is its own interpretation.
-- The unitors require the base arrow to have its own @w@-tensor unitors.
instance (Tensor w arr) => Tensor w (Sym w arr) where
  par = SymPar
  unitl = SymLift unitl
  unitl' = SymLift unitl'
  unitr = SymLift unitr
  unitr' = SymLift unitr'

-- | 'Sym' has a symmetric braiding over @w@.
--
-- This is the syntactic instance: 'SymSwap' is its own interpretation.
instance (Action w arr) => Action w (Sym w arr) where
  swap = SymSwap

-- | Lift the 'Channel' structure through 'Sym'.
instance (Category arr, Channel t arr) => Channel t (Sym w arr) where
  assoc = SymLift assoc
  assoc' = SymLift assoc'
  slide = SymLift slide

-- | 'Action' — free 'Sym' fold carries its own structure.
--
-- Sequential structure is folded with the target's category composition.
class (Action w arr) => FreeSym w arr

instance (Action w arr) => FreeSym w arr

instance Layer (Sym w) where
  type Law (Sym w) arr' = FreeSym w arr'
  type Run (Sym w) arr = Action w arr
  type Bind (Sym w) arr = ()
  unit = SymLift
  bind ::
    forall arr' arr a b.
    (Law (Sym w) arr') =>
    (arr :~> arr') ->
    Sym w arr a b ->
    arr' a b
  bind h (SymLift f) = h f
  bind h (SymCompose (g :: Sym w arr b1 c) (f :: Sym w arr a b1)) =
    bind h g . bind h f
  bind h (SymPar (f :: Sym w arr a1 b1) (g :: Sym w arr c d)) =
    par (bind h f) (bind h g)
  bind _h SymSwap = swap

-- | Lift the 'Strength' structure through 'Sym'.
instance (Strength t arr, Action w arr) => Strength t (Sym w arr) where
  strength = SymLift . strength . run

-- | Lift the 'Traced' structure through 'Sym'.
--
-- Loop bodies are 'run' into the base arrow before tracing, just as for
-- 'Free'.
instance (Traced t arr, Action w arr) => Traced t (Sym w arr) where
  trace = SymLift . trace . run
