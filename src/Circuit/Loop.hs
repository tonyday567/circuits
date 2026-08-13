{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free traced monoidal category, in existential normal form.
--
-- @Loop t arr a b@ is the free traced monoidal category over a /monoidal/
-- base morphism @arr@ with tensor @t@. The two constructors encode:
--
--   * 'Lift' — a plain base arrow.
--   * 'Knot' — a feedback loop with a hidden feedback channel.
--
-- The laws of traced monoidal categories are performed by the 'Category'
-- and 'Traced' instances, so every value is already in normal form: at most
-- one 'Knot' at the top, over a base-arrow body.
--
-- Over a premonoidal base the normal form is sound only when the 'Channel'
-- structural maps ('assoc', 'slide', etc.) are central. This is the
-- Benton–Hyland Central Sliding side-condition; see 'Circuit.Channel.Traced'
-- and the @circuits-axioma@ oracle "Loop trace requires centrality over
-- Kleisli IO".
--
-- For example, a @Loop (,) (->)@ is the initial traced monoidal cartesian
-- category over Haskell functions.
--
-- = Introduce / resolve
--
-- The vocabulary in this module follows the introduce/resolve pattern:
--
--   * 'Knot' introduces feedback; 'trace' resolves it. This is the gold
--     type-changing pair; composition fuses 'Knot's.
--
-- The polar channel ends (@Out@, @In@), their counit (@close@), and
-- their unit (@open@) all live in "Circuit.Ends".
--
-- == Interpreting a 'Loop'
--
-- Use 'run' or 'bind' to interpret a 'Loop' into a target category.  The
-- 'Category' and 'Traced' instances of the target discharge the knot; for
-- @(->)@ this is lazy knot-tying, and for 'Either' it is iteration.
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor that pairs a feedback value with a payload.
--   The two tensors provided are @(,)@ (simultaneous / lazy sharing) and
--   'Either' (sequential / iteration).
--
-- * __Feedback value__: The component that travels around the loop (the first
--   parameter of the tensor inside a 'Knot' body).
--
-- * __Payload__: The component that is transformed and emitted (the second
--   parameter of the tensor inside a 'Knot' body).
--
-- * __Feedback channel__: The hidden type @s@ in a 'Knot'. It is the value
--   the abstraction hides.
module Circuit.Loop
  ( -- * Loop
    Loop (..),

    -- * Layer witness
    FreeLoop,
  )
where

import Circuit.Category (Category (..), Discrete (..), ObDict (..), withObDict, (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Layer (Layer (..), run, (:~>))
import Control.Arrow (Kleisli (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.Profunctor
import Prelude hiding (id, (.))

-- | Helpers for building explicit object dictionaries from tensor/strength
-- closure.  These replace the old @withOb@ ladder when the base category is
-- not necessarily 'Discrete'.
obPair ::
  forall t arr a b.
  (Channel t arr) =>
  ObDict arr a ->
  ObDict arr b ->
  ObDict arr (t a b)
obPair da db = withTensorOb @t @arr da db ObDict

obStrength ::
  forall t arr a b c.
  (Strength t arr) =>
  ObDict arr a ->
  ObDict arr b ->
  ObDict arr c ->
  (ObDict arr (t a b), ObDict arr (t a c))
obStrength da db dc = withStrengthOb @t @arr da db dc (ObDict, ObDict)

-- $setup
-- >>> import Circuit.Layer (run)

-- | The free traced monoidal category over base morphism @arr@ and tensor @t@,
-- in existential normal form.
--
-- Two constructors:
--
--   * 'Lift' — a plain base arrow.
--   * 'Knot' — a feedback loop with hidden channel @s@.
data Loop (t :: Type -> Type -> Type) arr a b where
  -- | A plain base arrow.
  Lift :: arr a b -> Loop t arr a b
  -- | Tie a feedback loop. The tensor @t@ carries the hidden channel type @s@.
  --
  -- The argument is the base arrow itself, /not/ a 'Lift'-wrapped stage.
  -- The constructor carries the 'Ob' evidence for the feedback channel in
  -- the /source/ category.  'Layer.bind' transports this evidence to the
  -- target using a dictionary transformer and the target's 'Channel'
  -- closure, so the target need not be 'Discrete'.
  Knot ::
    ( Ob arr s,
      Ob arr (t s a),
      Ob arr (t s b)
    ) =>
    arr (t s a) (t s b) ->
    Loop t arr a b

-- $examples
--
-- >>> run (Lift (+1) :: Loop (,) (->) Int Int) 5
-- 6
--
-- >>> run (Knot (\(acc, x) -> (x, acc)) :: Loop (,) (->) Int Int) 42
-- 42
--
-- For the @(,)@ tensor the channel value is self-referential, so the body
-- must use an irrefutable pattern or otherwise avoid forcing the channel
-- before producing its constructor:
--
-- >>> run (Knot (\ ~(ns, ()) -> (0 : ns, take 3 ns)) :: Loop (,) (->) () [Int]) ()
-- [0,0,0]

instance (Strength t arr) => Category (Loop t arr) where
  type Ob (Loop t arr) a = Ob arr a
  id :: forall a. (Ob arr a) => Loop t arr a a
  id = Lift id
  (.) :: forall a b c. (Ob arr a, Ob arr b, Ob arr c) => Loop t arr b c -> Loop t arr a b -> Loop t arr a c
  Lift f . Lift g = Lift (f . g)
  Knot @_ @s @_ @_ @_ f . Lift g =
    let dS = ObDict :: ObDict arr s
        dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        dSA = obPair @t dS dA
        (dSB, dSC) = obStrength @t dS dB dC
     in withObDict dSA $
          withObDict dSB $
            withObDict dSC $
              Knot (f . strength g)
  Lift f . Knot @_ @s @_ @_ @_ g =
    let dS = ObDict :: ObDict arr s
        dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        (dSA, dSB) = obStrength @t dS dA dB
        dSC = obPair @t dS dC
     in withObDict dSA $
          withObDict dSB $
            withObDict dSC $
              Knot (strength f . g)
  Knot @_ @s2 @_ @_ @_ f . Knot @_ @s1 @_ @_ @_ g =
    let dS2 = ObDict :: ObDict arr s2
        dS1 = ObDict :: ObDict arr s1
        dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        dS1A = obPair @t dS1 dA
        dS1B = obPair @t dS1 dB
        dS1C = obPair @t dS1 dC
        dS2B = obPair @t dS2 dB
        dS2C = obPair @t dS2 dC
        dS12 = obPair @t dS2 dS1
        dS12A = obPair @t dS12 dA
        dS12C = obPair @t dS12 dC
        dS2S1A = obPair @t dS2 dS1A
        dS2S1B = obPair @t dS2 dS1B
        dS2S1C = obPair @t dS2 dS1C
        (_, dS2_S1B) = obStrength @t dS2 dS1A dS1B
        (dS1_S2B, dS1_S2C) = obStrength @t dS1 dS2B dS2C
     in withObDict dS12 $
          withObDict dS12A $
            withObDict dS2S1A $
              withObDict dS1A $
                withObDict dS1B $
                  withObDict dS1C $
                    withObDict dS2S1B $
                      withObDict dS2_S1B $
                        withObDict dS1_S2B $
                          withObDict dS2B $
                            withObDict dS2C $
                              withObDict dS2S1C $
                                withObDict dS1_S2C $
                                  withObDict dS12C $
                                    Knot (assoc .> strength g .> slide .> strength f .> slide .> assoc')

-- | A discrete base yields a discrete free traced category.
instance (Strength t arr, Discrete arr) => Discrete (Loop t arr) where
  withOb @a x = withOb @arr @a x

instance (Profunctor arr, Bifunctor t, Discrete arr, Channel t arr) => Profunctor (Loop t arr) where
  dimap :: forall a b c d. (a -> b) -> (c -> d) -> Loop t arr b c -> Loop t arr a d
  dimap f g (Lift h) = Lift (dimap f g h)
  dimap f g (Knot @_ @s @_ @_ @_ h) =
    withOb @arr @s $
      let dS = ObDict :: ObDict arr s
          dA = obDict :: ObDict arr a
          dD = obDict :: ObDict arr d
          dSA = obPair @t dS dA
          dSD = obPair @t dS dD
       in withObDict dSA $
            withObDict dSD $
              Knot (dimap (second f) (second g) h)
  lmap :: forall a b c. (a -> b) -> Loop t arr b c -> Loop t arr a c
  lmap f (Lift h) = Lift (lmap f h)
  lmap f (Knot @_ @s @_ @_ @_ h) =
    withOb @arr @s $
      let dS = ObDict :: ObDict arr s
          dA = obDict :: ObDict arr a
          dSA = obPair @t dS dA
       in withObDict dSA $
            Knot (lmap (second f) h)
  rmap :: forall a b c. (b -> c) -> Loop t arr a b -> Loop t arr a c
  rmap g (Lift h) = Lift (rmap g h)
  rmap g (Knot @_ @s @_ @_ @_ h) =
    withOb @arr @s $
      let dS = ObDict :: ObDict arr s
          dC = obDict :: ObDict arr c
          dSC = obPair @t dS dC
       in withObDict dSC $
            Knot (rmap (second g) h)

instance (Bifunctor t) => Functor (Loop t (->) a) where
  fmap f (Lift g) = Lift (f . g)
  fmap f (Knot g) = Knot (second f . g)

-- | Lift the 'Channel' structure of the base arrow into 'Loop t arr'.
instance (Strength t arr) => Channel t (Loop t arr) where
  assoc ::
    forall a b c.
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t b c),
      Ob arr (t (t a b) c),
      Ob arr (t a (t b c))
    ) =>
    Loop t arr (t (t a b) c) (t a (t b c))
  assoc =
    let dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        dAB = obPair @t dA dB
        dBC = obPair @t dB dC
        dAB_C = obPair @t dAB dC
        dA_BC = obPair @t dA dBC
     in Lift $
          withObDict dA $
            withObDict dB $
              withObDict dC $
                withObDict dAB $
                  withObDict dBC $
                    withObDict dAB_C $
                      withObDict dA_BC assoc
  assoc' ::
    forall a b c.
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t b c),
      Ob arr (t (t a b) c),
      Ob arr (t a (t b c))
    ) =>
    Loop t arr (t a (t b c)) (t (t a b) c)
  assoc' =
    let dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        dAB = obPair @t dA dB
        dBC = obPair @t dB dC
        dA_BC = obPair @t dA dBC
        dAB_C = obPair @t dAB dC
     in Lift $
          withObDict dA $
            withObDict dB $
              withObDict dC $
                withObDict dAB $
                  withObDict dBC $
                    withObDict dA_BC $
                      withObDict dAB_C assoc'
  slide ::
    forall a b c.
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t b c),
      Ob arr (t a c),
      Ob arr (t a (t b c)),
      Ob arr (t b (t a c))
    ) =>
    Loop t arr (t a (t b c)) (t b (t a c))
  slide =
    let dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        dBC = obPair @t dB dC
        dAC = obPair @t dA dC
        dA_BC = obPair @t dA dBC
        dB_AC = obPair @t dB dAC
     in Lift $
          withObDict dA $
            withObDict dB $
              withObDict dC $
                withObDict dBC $
                  withObDict dAC $
                    withObDict dA_BC $
                      withObDict dB_AC slide
  withTensorOb ::
    forall a b r.
    ObDict (Loop t arr) a ->
    ObDict (Loop t arr) b ->
    ((Ob (Loop t arr) (t a b)) => r) ->
    r
  withTensorOb (dA :: ObDict (Loop t arr) a) (dB :: ObDict (Loop t arr) b) k =
    withObDict dA $
      withObDict dB $
        withTensorOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) k

-- | Lift the 'Strength' class through 'Loop t'.
instance (Strength t arr) => Strength t (Loop t arr) where
  strength :: forall a b c. (Ob arr a, Ob arr b, Ob arr c, Ob arr (t a b), Ob arr (t a c)) => Loop t arr b c -> Loop t arr (t a b) (t a c)
  strength (Lift f) =
    let dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        (dAB, dAC) = obStrength @t dA dB dC
     in Lift $
          withObDict dA $
            withObDict dB $
              withObDict dC $
                withObDict dAB $
                  withObDict dAC $
                    strength f
  strength (Knot @_ @s @_ @_ @_ f) =
    let dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        dS = ObDict :: ObDict arr s
        dSB = obPair @t dS dB
        dSC = obPair @t dS dC
        dSAB = obPair @t dS (obPair @t dA dB)
        dSAC = obPair @t dS (obPair @t dA dC)
        dASB = obPair @t dA (obPair @t dS dB)
        dASC = obPair @t dA (obPair @t dS dC)
     in withObDict dSAB $
          withObDict dASB $
            withObDict dASC $
              withObDict dSB $
                withObDict dSC $
                  withObDict dSAC $
                    Knot (slide .> strength f .> slide)
  withStrengthOb ::
    forall a b c r.
    ObDict (Loop t arr) a ->
    ObDict (Loop t arr) b ->
    ObDict (Loop t arr) c ->
    ((Ob (Loop t arr) (t a b), Ob (Loop t arr) (t a c)) => r) ->
    r
  withStrengthOb (dA :: ObDict (Loop t arr) a) (dB :: ObDict (Loop t arr) b) (dC :: ObDict (Loop t arr) c) k =
    withObDict dA $
      withObDict dB $
        withObDict dC $
          withStrengthOb @t @arr (ObDict :: ObDict arr a) (ObDict :: ObDict arr b) (ObDict :: ObDict arr c) k

-- | Lift the 'Traced' class through 'Loop t'.
--
-- 'trace' hides a wire as a 'Knot'.
instance (Traced t arr) => Traced t (Loop t arr) where
  trace ::
    forall a b c.
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t a c)
    ) =>
    Loop t arr (t a b) (t a c) ->
    Loop t arr b c
  trace (Lift f) =
    let dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        dAB = obPair @t dA dB
        dAC = obPair @t dA dC
     in withObDict dA $
          withObDict dB $
            withObDict dC $
              withObDict dAB $
                withObDict dAC $
                  Knot f
  trace (Knot @_ @s @_ @_ @_ f) =
    let dA = ObDict :: ObDict arr a
        dB = ObDict :: ObDict arr b
        dC = ObDict :: ObDict arr c
        dS = ObDict :: ObDict arr s
        dSA = obPair @t dS dA
        dSAB = obPair @t dSA dB
        dSAC = obPair @t dSA dC
        dSAC' = obPair @t dS (obPair @t dA dC)
     in withObDict dSAB $
          withObDict dSAC $
            withObDict dSAC' $
              withObDict dSA $
                Knot (assoc .> f .> assoc')

-- | 'Traced' plus 'Channel' — required to fold free 'Loop' over a base
-- category whose object constraint is closed under the tensor.
class (Traced t arr, Channel t arr) => FreeLoop t arr

instance (Traced t arr, Channel t arr) => FreeLoop t arr

-- | Free traced monoidal category.
instance Layer (Loop t) where
  type Law (Loop t) arr' = FreeLoop t arr'
  type Run (Loop t) arr = (Traced t arr, Channel t arr)
  type Bind (Loop t) arr = ()
  unit = Lift
  bind ::
    forall arr arr' a b.
    (Law (Loop t) arr', Ob arr' a, Ob arr' b) =>
    (forall s. ObDict arr s -> ObDict arr' s) ->
    (arr :~> arr') ->
    Loop t arr a b ->
    arr' a b
  bind _phi h (Lift f) = h f
  bind phi h (Knot @_ @s @_ @_ @_ f) =
    withObDict (phi (ObDict :: ObDict arr s)) $
      withTensorOb @t @arr' @s @a (ObDict :: ObDict arr' s) (ObDict :: ObDict arr' a) $
        withTensorOb @t @arr' @s @b (ObDict :: ObDict arr' s) (ObDict :: ObDict arr' b) $
          trace (h f)
