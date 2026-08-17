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

import Circuit.Category (Category (..), Discrete (..), ObDict (..), withObDict, (.>))
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
  --
  -- The 'Ob' constraint on the intermediate object @b@ is carried in the
  -- constructor so folding does not need a 'Discrete' base.
  Compose :: (Ob arr b) => Net w t arr b c -> Net w t arr a b -> Net w t arr a c
  -- | Parallel composition (monoidal product over @w@).
  Par :: Net w t arr a b -> Net w t arr c d -> Net w t arr (w a c) (w b d)
  -- | Symmetric braiding over @w@.
  Swap :: Net w t arr (w a b) (w b a)
  -- | Copy: fan-out.  Requires 'Dg.CopyT' on the wiring tensor @w@.
  Copy :: (Dg.CopyT w arr a) => Net w t arr a (w a a)
  -- | Discard: erase.  Requires 'Dg.DiscardT' on the wiring tensor @w@.
  Discard :: (Dg.DiscardT w arr a) => Net w t arr a (Unit w)
  -- | Plus: fan-in.  Requires 'Dg.MergeT' on the wiring tensor @w@.
  Plus :: (Dg.MergeT w arr a) => Net w t arr (w a a) a
  -- | Zero: the neutral element.  Requires 'Dg.ZeroT' on the wiring tensor @w@.
  Zero :: (Dg.ZeroT w arr a) => Net w t arr (Unit w) a
  -- | Feedback loop.  The body is a 'Net', not an opaque base arrow.
  --
  -- The constructor carries the 'Ob' evidence for the feedback channel in
  -- the /source/ category.
  Knot :: (Ob arr s) => Net w t arr (t s a) (t s b) -> Net w t arr a b

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
  type Ob (Net w t arr) a = Ob arr a
  id = Lift id
  g . f = Compose g f

-- | A discrete base yields a discrete free traced PROP.
instance (Category arr, Discrete arr) => Discrete (Net w t arr) where
  withOb @a x = withOb @arr @a x

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
-- >>> let m = SymLift (+1) `SymCompose` SymLift (*2) :: Sym (->) Int Int
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
-- >>> let phi d = d
-- >>> (bind phi h m :: Int -> Int) 5
-- 11
--
-- Coherence: 'Net' folds through 'widen' match 'Sym' folds.
--
-- >>> let h f = f
-- >>> let phi d = d
-- >>> (bind phi h (widen m :: Net (,) (,) (->) Int Int) :: Int -> Int) 5
-- 11
-- >>> (bind phi h m :: Int -> Int) 5
-- 11
--
-- Coherence: transposition commutes with 'widen'.
--
-- >>> let dm = SymLift (Dg.Dagger (+1) (subtract 1)) `SymCompose` SymLift (Dg.Dagger (*2) (\x -> x `div` 2)) :: Sym (Dg.Dagger (->)) Int Int
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
  (Traced t arr, Action w arr, Discrete arr) =>
  Net w t arr a b ->
  Sym w arr a b
sift (Lift f) = SymLift f
sift (Compose g f) = SymCompose (sift g) (sift f)
sift (Par f g) = SymPar (sift f) (sift g)
sift Swap = SymSwap
sift Copy =
  withOb @arr @a $
    withOb @arr @(w a a) $
      SymLift (Dg.copyT @w)
sift Discard =
  withOb @arr @a $
    withOb @arr @(Unit w) $
      SymLift (Dg.discardT @w)
sift Plus =
  withOb @arr @(w a a) $
    withOb @arr @a $
      SymLift (Dg.plusT @w)
sift Zero =
  withOb @arr @(Unit w) $
    withOb @arr @b $
      SymLift (Dg.zeroT @w)
sift n@(Knot @_ @s @_ @_ @_ _) =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @(t s a) $
        withOb @arr @(t s b) $
          SymLift (Layer.run (melt n))

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
  (Traced t arr, Action w arr, Discrete arr) =>
  Net w t arr a b ->
  C.Loop t arr a b
melt (Lift f) = C.Lift f
melt (Compose @_ @b1 @_ @_ @_ g f) =
  withOb @arr @a $
    withOb @arr @b1 $
      withOb @arr @b $
        (melt g . melt f)
melt (Par f g) = go f g
  where
    go ::
      forall a1 b1 c d.
      Net w t arr a1 b1 ->
      Net w t arr c d ->
      C.Loop t arr (w a1 c) (w b1 d)
    go f' g' =
      withOb @arr @a1 $
        withOb @arr @b1 $
          withOb @arr @c $
            withOb @arr @d $
              par (melt f') (melt g')
melt Swap =
  case () of
    () ->
      let swap' :: forall a1 b1. (a ~ w a1 b1) => C.Loop t arr a b
          swap' =
            withOb @arr @a1 $
              withOb @arr @b1 $
                C.Lift swap
       in swap'
melt Copy =
  withOb @arr @a $
    withOb @arr @(w a a) $
      C.Lift (Dg.copyT @w)
melt Discard =
  withOb @arr @a $
    withOb @arr @(Unit w) $
      C.Lift (Dg.discardT @w)
melt Plus =
  withOb @arr @(w a a) $
    withOb @arr @a $
      C.Lift (Dg.plusT @w)
melt Zero =
  withOb @arr @(Unit w) $
    withOb @arr @b $
      C.Lift (Dg.zeroT @w)
melt (Knot @_ @s @_ @_ @_ f) =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @(t s a) $
        withOb @arr @(t s b) $
          trace (melt f)

-- | 'Traced' + 'Action' + 'Discrete' — free 'Net' fold needs trivial 'Ob'.
class (Traced t arr, Action w arr, Discrete arr) => FreeNet w t arr

instance (Traced t arr, Action w arr, Discrete arr) => FreeNet w t arr

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
  type Run (Net w t) arr = (Traced t arr, Action w arr, Discrete arr)
  type Bind (Net w t) arr = Discrete arr
  unit = Lift
  bind ::
    forall arr' arr a b.
    (Law (Net w t) arr', Bind (Net w t) arr, Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) =>
    (forall s. ObDict arr s -> ObDict arr' s) ->
    (arr :~> arr') ->
    Net w t arr a b ->
    arr' a b
  bind _phi h (Lift f) = h f
  bind phi h (Compose @_ @b1 @_ @_ @_ g f) =
    withObDict (obDict :: ObDict arr b1) $
      withObDict (phi (obDict :: ObDict arr b1)) (bind phi h g . bind phi h f)
  bind phi h (Par @_ @_ @_ @a1 @b1 @c @d f g) =
    withObDict (obDict :: ObDict arr a1) $
      withObDict (obDict :: ObDict arr b1) $
        withObDict (obDict :: ObDict arr c) $
          withObDict (obDict :: ObDict arr d) $
            withObDict (phi (obDict :: ObDict arr a1)) $
              withObDict (phi (obDict :: ObDict arr b1)) $
                withObDict (phi (obDict :: ObDict arr c)) $
                  withObDict (phi (obDict :: ObDict arr d)) $
                    withOb @arr' @(w a1 c) $
                      withOb @arr' @(w b1 d) $
                        par (bind phi h f) (bind phi h g)
  bind _phi _ Swap =
    case () of
      () ->
        let swap' :: forall a1 b1. (a ~ w a1 b1) => arr' a b
            swap' =
              withOb @arr' @a1 $
                withOb @arr' @b1 $
                  swap
         in swap'
  bind _phi h Copy =
    withOb @arr @a $
      withOb @arr @(w a a) $
        withOb @arr' @a $
          withOb @arr' @(w a a) $
            h (Dg.copyT @w)
  bind _phi h Discard =
    withOb @arr @a $
      withOb @arr @(Unit w) $
        withOb @arr' @a $
          withOb @arr' @(Unit w) $
            h (Dg.discardT @w)
  bind _phi h Plus =
    withOb @arr @(w a a) $
      withOb @arr @a $
        withOb @arr' @(w a a) $
          withOb @arr' @a $
            h (Dg.plusT @w)
  bind _phi h Zero =
    withOb @arr @(Unit w) $
      withOb @arr @b $
        withOb @arr' @(Unit w) $
          withOb @arr' @b $
            h (Dg.zeroT @w)
  bind phi h (Knot @_ @s @_ @_ @_ f) =
    withOb @arr @s $
      withOb @arr @(t s a) $
        withOb @arr @(t s b) $
          withObDict (phi (obDict :: ObDict arr s)) $
            withOb @arr' @(t s a) $
              withOb @arr' @(t s b) $
                trace (bind phi h f)

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
  --
  -- The 'Ob' constraint on the intermediate object @b@ is carried in the
  -- constructor so folding does not need a 'Discrete' base.
  SymCompose :: (Ob arr b) => Sym w arr b c -> Sym w arr a b -> Sym w arr a c
  -- | Tensor product of morphisms (parallel composition on disjoint wires).
  SymPar :: Sym w arr a b -> Sym w arr c d -> Sym w arr (w a c) (w b d)
  -- | Symmetric braiding.
  SymSwap :: Sym w arr (w a b) (w b a)

-- | 'Sym' is a category.
instance (Category arr) => Category (Sym w arr) where
  type Ob (Sym w arr) a = Ob arr a
  id = SymLift id
  (.) = SymCompose

-- | A discrete base yields a discrete free monoidal category.
instance (Category arr, Discrete arr) => Discrete (Sym w arr) where
  withOb @a x = withOb @arr @a x

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
  withTensorOb ::
    forall a b r.
    ObDict (Sym w arr) a ->
    ObDict (Sym w arr) b ->
    ((Ob (Sym w arr) (t a b)) => r) ->
    r
  withTensorOb (dA :: ObDict (Sym w arr) a) (dB :: ObDict (Sym w arr) b) k =
    withObDict dA $
      withObDict dB $
        withTensorOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) k

-- | 'Action' plus 'Discrete' so free 'Sym' can fold intermediate objects.
--
-- Sequential structure is folded with the target's category composition.
class (Action w arr, Discrete arr) => FreeSym w arr

instance (Action w arr, Discrete arr) => FreeSym w arr

instance Layer (Sym w) where
  type Law (Sym w) arr' = FreeSym w arr'
  type Run (Sym w) arr = (Action w arr, Discrete arr)
  type Bind (Sym w) arr = Discrete arr
  unit = SymLift
  bind ::
    forall arr' arr a b.
    (Law (Sym w) arr', Bind (Sym w) arr, Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) =>
    (forall s. ObDict arr s -> ObDict arr' s) ->
    (arr :~> arr') ->
    Sym w arr a b ->
    arr' a b
  bind _phi h (SymLift f) = h f
  bind phi h (SymCompose @_ @b1 g f) = withObDict (phi (ObDict :: ObDict arr b1)) (bind phi h g . bind phi h f)
  bind phi h (SymPar (f :: Sym w arr a1 b1) (g :: Sym w arr c d)) =
    let dA1 = obDict :: ObDict arr a1
        dB1 = obDict :: ObDict arr b1
        dC = obDict :: ObDict arr c
        dD = obDict :: ObDict arr d
     in withObDict dA1 $
          withObDict dB1 $
            withObDict dC $
              withObDict dD $
                withObDict (phi dA1) $
                  withObDict (phi dB1) $
                    withObDict (phi dC) $
                      withObDict (phi dD) $
                        withOb @arr' @(w a1 c) $
                          withOb @arr' @(w b1 d) $
                            par (bind phi h f) (bind phi h g)
  bind _phi _ (SymSwap @_ @_ @a1 @b1) =
    withOb @arr' @a1 $
      withOb @arr' @b1 $
        swap

-- | Lift the 'Strength' structure through 'Sym'.
instance (Strength t arr, Action w arr, Discrete arr) => Strength t (Sym w arr) where
  strength = SymLift . strength . run
  withStrengthOb ::
    forall a b c r.
    ObDict (Sym w arr) a ->
    ObDict (Sym w arr) b ->
    ObDict (Sym w arr) c ->
    ((Ob (Sym w arr) (t a b), Ob (Sym w arr) (t a c)) => r) ->
    r
  withStrengthOb (dA :: ObDict (Sym w arr) a) (dB :: ObDict (Sym w arr) b) (dC :: ObDict (Sym w arr) c) k =
    withObDict dA $
      withObDict dB $
        withObDict dC $
          withStrengthOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) (ObDict :: ObDict arr c) k

-- | Lift the 'Traced' structure through 'Sym'.
--
-- Loop bodies are 'run' into the base arrow before tracing, just as for
-- 'Free'.
instance (Traced t arr, Action w arr, Discrete arr) => Traced t (Sym w arr) where
  trace = SymLift . trace . run
