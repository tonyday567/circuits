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
import Circuit.Tensor (Action (..), Tensor (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

type family Fst (p :: Type) :: Type where
  Fst (a, b) = a

type family Snd (p :: Type) :: Type where
  Snd (a, b) = b

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
-- 'Dg.CopyDiscard' and 'Dg.MergeZero' constraints ride as dictionary
-- arguments on the constructors that need them — laws in the typeclass
-- holes, evidence on the GADT rows.
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
  Compose :: (Ob arr b) => Net t arr b c -> Net t arr a b -> Net t arr a c
  -- | Parallel composition (monoidal product).
  Par :: Net t arr a b -> Net t arr c d -> Net t arr (a, c) (b, d)
  -- | Symmetric braiding.
  Swap :: Net t arr (a, b) (b, a)
  -- | Copy: fan-out.  Requires 'Dg.Copy'.
  Copy :: (Dg.Copy arr a) => Net t arr a (a, a)
  -- | Discard: erase.  Requires 'Dg.Discard'.
  Discard :: (Dg.Discard arr a) => Net t arr a ()
  -- | Plus: fan-in.  Requires 'Dg.Merge'.
  Plus :: (Dg.Merge arr a) => Net t arr (a, a) a
  -- | Zero: the neutral element.  Requires 'Dg.Zero'.
  Zero :: (Dg.Zero arr a) => Net t arr () a
  -- | Feedback loop.  The body is a 'Net', not an opaque base arrow.
  --
  -- The constructor carries the 'Ob' evidence for the feedback channel in
  -- the /source/ category.
  Knot :: (Ob arr s) => Net t arr (t s a) (t s b) -> Net t arr a b

-- | The 'Category' instance preserves inspectable wiring.
--
-- Composition uses the explicit @Compose@ constructor, so 'Copy',
-- 'Plus', 'Par', and 'Knot' stay visible.  'melt' collapses the
-- structure when the normal form is needed.
--
-- Composition uses the explicit @Compose@ constructor so structural
-- rows remain inspectable.  'melt' collapses them to the normal form of
-- 'C.Loop' when needed.
instance (Category arr) => Category (Net t arr) where
  type Ob (Net t arr) a = Ob arr a
  id = Lift id
  g . f = Compose g f

-- | A discrete base yields a discrete free traced PROP.
instance (Category arr, Discrete arr) => Discrete (Net t arr) where
  withOb @a x = withOb @arr @a x

-- | Upgrade a 'C.Loop' to a 'Net' — constructor-to-constructor.
--
-- 'C.Loop' is the normal form 'C.Lift' / 'C.Knot' over a base-arrow body;
-- 'Net' keeps the same information but can hold more structure.
-- 'C.Lift' lifts to 'Net.Lift'; 'C.Knot' lifts to 'Net.Knot' around a
-- @Lift@ body.
enrich :: C.Loop t arr a b -> Net t arr a b
enrich (C.Lift f) = Lift f
enrich (C.Knot f) = Knot (Lift f)

-- | Include a 'Sym' circuit into 'Net' — constructor-to-constructor.
--
-- 'Net' duplicates the four rows of 'Sym' (@SymLift@, @SymCompose@, 'SymPar',
-- 'SymSwap') so that structural wiring stays inspectable.  This is the
-- injection of the 'Sym' layer into the 'Net' layer.
--
-- >>> let m = SymLift (+1) `SymCompose` SymLift (*2) :: Sym (->) Int Int
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
-- >>> let phi d = d
-- >>> (bind phi h m :: Int -> Int) 5
-- 11
--
-- Coherence: 'Net' folds through 'widen' match 'Sym' folds.
--
-- >>> let h f = f
-- >>> let phi d = d
-- >>> (bind phi h (widen m :: Net (,) (->) Int Int) :: Int -> Int) 5
-- 11
-- >>> (bind phi h m :: Int -> Int) 5
-- 11
--
-- Coherence: transposition commutes with 'widen'.
--
-- >>> let dm = SymLift (Dg.Dagger (+1) (subtract 1)) `SymCompose` SymLift (Dg.Dagger (*2) (\x -> x `div` 2)) :: Sym (Dg.Dagger (->)) Int Int
-- >>> Dg.front (Dg.transpose (run dm)) 10
-- 4
-- >>> Dg.front (Dg.transpose (run (widen dm :: Net (,) (Dg.Dagger (->)) Int Int))) 10
-- 4
widen :: Sym arr a b -> Net t arr a b
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
  forall t arr a b.
  (Traced t arr, Action (,) arr, Discrete arr) =>
  Net t arr a b ->
  Sym arr a b
sift (Lift f) = SymLift f
sift (Compose g f) = SymCompose (sift g) (sift f)
sift (Par f g) = SymPar (sift f) (sift g)
sift Swap = SymSwap
sift Copy = SymLift Dg.copy
sift Discard = SymLift Dg.discard
sift Plus = SymLift Dg.plus
sift Zero = SymLift Dg.zero
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
melt Swap =
  withOb @arr @(Fst a) $
    withOb @arr @(Snd a) $
      C.Lift swap
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
  bind ::
    forall arr' arr a b.
    (Law (Net t) arr', Bind (Net t) arr, Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) =>
    (forall s. ObDict arr s -> ObDict arr' s) ->
    (arr :~> arr') ->
    Net t arr a b ->
    arr' a b
  bind _phi h (Lift f) = h f
  bind phi h (Compose @_ @b1 @_ @_ @_ g f) =
    withObDict (obDict :: ObDict arr b1) $
      withObDict (phi (obDict :: ObDict arr b1)) (bind phi h g . bind phi h f)
  bind phi h (Par @_ @_ @a1 @b1 @c @d f g) =
    withObDict (obDict :: ObDict arr a1) $
      withObDict (obDict :: ObDict arr b1) $
        withObDict (obDict :: ObDict arr c) $
          withObDict (obDict :: ObDict arr d) $
            withObDict (phi (obDict :: ObDict arr a1)) $
              withObDict (phi (obDict :: ObDict arr b1)) $
                withObDict (phi (obDict :: ObDict arr c)) $
                  withObDict (phi (obDict :: ObDict arr d)) $
                    withOb @arr' @(a1, c) $
                      withOb @arr' @(b1, d) $
                        par (bind phi h f) (bind phi h g)
  bind _phi _ Swap =
    withOb @arr' @(Fst a) $
      withOb @arr' @(Snd a) $
        swap
  bind _phi h (Copy @_ @c) =
    withOb @arr' @c $
      withOb @arr' @(c, c) $
        h Dg.copy
  bind _phi h (Discard @_ @c) =
    withOb @arr' @c $
      withOb @arr' @() $
        h Dg.discard
  bind _phi h (Plus @_ @c) =
    withOb @arr' @(c, c) $
      withOb @arr' @c $
        h Dg.plus
  bind _phi h (Zero @_ @c) =
    withOb @arr' @() $
      withOb @arr' @c $
        h Dg.zero
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
-- monoidal product ('Par') and symmetry ('Swap') syntax.  It is the
-- intermediate layer between 'Free' and 'Net':
--
-- @
-- Free = Lift + Compose
-- Sym  = Free + Par + Swap
-- Net  = Sym + Knot + Copy + Discard + Plus + Zero
-- @
--
-- The tensor is fixed to @(,)@, matching 'Circuit.Tensor.Action'.
--
-- Four constructors:
--
--   * 'SymLift' — embed a base arrow.
--   * 'SymCompose' — sequential composition.
--   * 'SymPar' — tensor product of morphisms (parallel composition).
--   * 'SymSwap' — symmetry / braiding.
data Sym arr a b where
  -- | Embed a base arrow.
  SymLift :: arr a b -> Sym arr a b
  -- | Sequential composition.
  --
  -- The 'Ob' constraint on the intermediate object @b@ is carried in the
  -- constructor so folding does not need a 'Discrete' base.
  SymCompose :: (Ob arr b) => Sym arr b c -> Sym arr a b -> Sym arr a c
  -- | Tensor product of morphisms (parallel composition on disjoint wires).
  SymPar :: Sym arr a b -> Sym arr c d -> Sym arr (a, c) (b, d)
  -- | Symmetric braiding.
  SymSwap :: Sym arr (a, b) (b, a)

-- | 'Sym' is a category.
instance (Category arr) => Category (Sym arr) where
  type Ob (Sym arr) a = Ob arr a
  id = SymLift id
  (.) = SymCompose

-- | A discrete base yields a discrete free monoidal category.
instance (Category arr, Discrete arr) => Discrete (Sym arr) where
  withOb @a x = withOb @arr @a x

-- | 'Sym' has a tensor structure whose tensor is @(,)@.
--
-- This is the syntactic instance: 'SymPar' is its own interpretation.
-- The unitors require the base arrow to have its own cartesian unitors.
instance (Tensor (,) arr) => Tensor (,) (Sym arr) where
  par = SymPar
  unitl = SymLift unitl
  unitl' = SymLift unitl'
  unitr = SymLift unitr
  unitr' = SymLift unitr'

-- | 'Sym' has a symmetric braiding.
--
-- This is the syntactic instance: 'SymSwap' is its own interpretation.
instance (Tensor (,) arr) => Action (,) (Sym arr) where
  swap = SymSwap

-- | Lift the 'Channel' structure through 'Sym'.
instance (Category arr, Channel t arr) => Channel t (Sym arr) where
  assoc = SymLift assoc
  assoc' = SymLift assoc'
  slide = SymLift slide
  withTensorOb ::
    forall a b r.
    ObDict (Sym arr) a ->
    ObDict (Sym arr) b ->
    ((Ob (Sym arr) (t a b)) => r) ->
    r
  withTensorOb (dA :: ObDict (Sym arr) a) (dB :: ObDict (Sym arr) b) k =
    withObDict dA $
      withObDict dB $
        withTensorOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) k

-- | 'Action' plus 'Discrete' so free 'Sym' can fold intermediate objects.
--
-- Sequential structure is folded with the target's category composition.
class (Action (,) arr, Discrete arr) => FreeSym arr

instance (Action (,) arr, Discrete arr) => FreeSym arr

instance Layer Sym where
  type Law Sym arr' = FreeSym arr'
  type Run Sym arr = (Action (,) arr, Discrete arr)
  type Bind Sym arr = Discrete arr
  unit = SymLift
  bind ::
    forall arr' arr a b.
    (Law Sym arr', Bind Sym arr, Ob arr a, Ob arr b, Ob arr' a, Ob arr' b) =>
    (forall s. ObDict arr s -> ObDict arr' s) ->
    (arr :~> arr') ->
    Sym arr a b ->
    arr' a b
  bind _phi h (SymLift f) = h f
  bind phi h (SymCompose @_ @b1 g f) = withObDict (phi (ObDict :: ObDict arr b1)) (bind phi h g . bind phi h f)
  bind phi h (SymPar (f :: Sym arr a1 b1) (g :: Sym arr c d)) =
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
                        withOb @arr' @(a1, c) $
                          withOb @arr' @(b1, d) $
                            par (bind phi h f) (bind phi h g)
  bind _phi _ SymSwap =
    withOb @arr' @(Fst a) $
      withOb @arr' @(Snd a) $
        swap

-- | Lift the 'Strength' structure through 'Sym'.
instance (Strength t arr, Action (,) arr, Discrete arr) => Strength t (Sym arr) where
  strength = SymLift . strength . run
  withStrengthOb ::
    forall a b c r.
    ObDict (Sym arr) a ->
    ObDict (Sym arr) b ->
    ObDict (Sym arr) c ->
    ((Ob (Sym arr) (t a b), Ob (Sym arr) (t a c)) => r) ->
    r
  withStrengthOb (dA :: ObDict (Sym arr) a) (dB :: ObDict (Sym arr) b) (dC :: ObDict (Sym arr) c) k =
    withObDict dA $
      withObDict dB $
        withObDict dC $
          withStrengthOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) (ObDict :: ObDict arr c) k

-- | Lift the 'Traced' structure through 'Sym'.
--
-- Loop bodies are 'run' into the base arrow before tracing, just as for
-- 'Free'.
instance (Traced t arr, Action (,) arr, Discrete arr) => Traced t (Sym arr) where
  trace = SymLift . trace . run
