{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Parameterised hyperfunctions: the final encoding over an arbitrary
-- base category.
--
-- The existing "Circuit.Hyper" is the specialisation to the function
-- category @(->)@.  This module generalises the construction to any
-- category @arr@ that carries the small amount of structure captured by
-- 'HyperBase': an underlying "runner" @Run arr@, a way to build and read
-- arrows as functions into that runner, and a fixed-point operator for
-- tying the feedback knot.
--
-- The two named targets from the card are recovered as instances:
--
-- * @(->)@ — 'Run' is 'Data.Functor.Identity.Identity', 'fixRun' is 'fix'.
-- * @'Control.Arrow.Kleisli' m@ — 'Run' is @m@, 'fixRun' is 'mfix'.
--
-- === doctests
--
-- >>> import Circuit.HyperArr
-- >>> import Circuit.Channel (trace)
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Data.Functor.Identity (Identity (..))
--
-- >>> let body = liftH (Kleisli (\(xs, ()) -> Identity (0 : xs, take 3 xs)) :: Kleisli Identity ([Int], ()) ([Int], [Int]))
-- >>> runIdentity (observeH (trace body) ())
-- [0,0,0]
module Circuit.HyperArr
  ( -- * Hyperfunctions over a base category
    HyperArr (..),

    -- * Base-category structure
    HyperBase (..),

    -- * Generic constructors and eliminators
    liftH,
    observeH,
    baseH,
    pushH,
    runHyperH,

    -- * Function-category bridge
    toHyper,
    fromHyper,
    liftF,
    observeF,
    baseF,
    pushF,
    runHyperF,

    -- * Kleisli aliases
    liftArr,
    observeArr,
    baseArr,
    pushArr,
    runHyperArr,
  )
where

import Circuit.Category (Category (..), ObDict (..), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Hyper qualified as H
import Control.Arrow (Kleisli (..))
import Control.Monad.Fix (MonadFix, mfix)
import Data.Bifunctor (second)
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.HyperArr
-- >>> import Circuit.Channel (trace)
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Data.Functor.Identity (Identity (..))

-- | A hyperfunction from @a@ to @b@ over the base category @arr@.
--
-- To produce a @b@ in @arr@ you must supply a continuation that can
-- produce an @a@.
newtype HyperArr arr a b = HyperArr
  { -- | Feed a continuation into the hyperfunction.
    invoke :: arr (HyperArr arr b a) b
  }

-- ---------------------------------------------------------------------------
-- Base-category structure
-- ---------------------------------------------------------------------------

-- | Enough structure on a base category @arr@ to give 'HyperArr arr' a
-- traced monoidal category structure.
--
-- * 'Run' is the underlying functor in which arrows are evaluated.
-- * 'runArr' / 'mkArr' witness that @arr@ is concretely represented by
--   functions into 'Run'.
-- * 'fixRun' ties the recursive knot used by the trace.
class (Category arr, Monad (Run arr)) => HyperBase arr where
  -- | Underlying effect functor for evaluating arrows.
  type Run arr :: Type -> Type

  -- | Evaluate an arrow at a value.
  runArr :: arr a b -> a -> Run arr b

  -- | Build an arrow from a function into 'Run'.
  mkArr :: (a -> Run arr b) -> arr a b

  -- | Fixed-point operator for 'Run'.
  fixRun :: (a -> Run arr a) -> Run arr a

-- | Function category: arrows run in the identity monad and knots tie
-- by Haskell laziness.
instance HyperBase (->) where
  type Run (->) = Identity
  runArr f a = Identity (f a)
  mkArr f = runIdentity . f
  fixRun f = let x = f (runIdentity x) in x

-- | Kleisli arrows: arrows run in the monad and knots tie with 'mfix'.
instance (MonadFix m) => HyperBase (Kleisli m) where
  type Run (Kleisli m) = m
  runArr = runKleisli
  mkArr = Kleisli
  fixRun = mfix

-- ---------------------------------------------------------------------------
-- Generic constructors and eliminators
-- ---------------------------------------------------------------------------

-- | Push a base morphism onto a hyperfunction.
pushH ::
  (HyperBase arr) =>
  arr a b ->
  HyperArr arr a b ->
  HyperArr arr a b
pushH f h = HyperArr $ mkArr $ \k -> do
  a_val <- runArr (invoke k) h
  runArr f a_val

-- | Embed a base morphism into a hyperfunction.
--
-- This is the coinductive character of the construction: the morphism is
-- pushed onto every future continuation.
liftH :: (HyperBase arr) => arr a b -> HyperArr arr a b
liftH f = pushH f (liftH f)

-- | A constant hyperfunction.
baseH :: (HyperBase arr) => b -> HyperArr arr a b
baseH b = HyperArr $ mkArr $ \_ -> pure b

-- | Extract the underlying arrow as a function into 'Run'.
observeH :: (HyperBase arr) => HyperArr arr a b -> a -> Run arr b
observeH h a = runArr (invoke h) (baseH a)

-- | Close the self-referential loop.
runHyperH ::
  forall arr a.
  (HyperBase arr) =>
  HyperArr arr a a ->
  Run arr a
runHyperH h = fixRun @arr $ \a -> runArr (invoke h) (baseH a)

-- ---------------------------------------------------------------------------
-- Generic instances
-- ---------------------------------------------------------------------------

instance (HyperBase arr) => Category (HyperArr arr) where
  type Ob (HyperArr arr) a = Ob arr a
  id = liftH id
  f . g = HyperArr $ mkArr $ \k -> runArr (invoke f) (g . k)

instance (HyperBase arr, Channel (,) arr) => Channel (,) (HyperArr arr) where
  assoc = liftH assoc
  assoc' = liftH assoc'
  slide = liftH slide
  withTensorOb ::
    forall a b r.
    ObDict (HyperArr arr) a ->
    ObDict (HyperArr arr) b ->
    ((Ob (HyperArr arr) (a, b)) => r) ->
    r
  withTensorOb ObDict ObDict =
    withTensorOb @(,) @arr @a @b @r
      (ObDict :: ObDict arr a)
      (ObDict :: ObDict arr b)

instance (HyperBase arr, Strength (,) arr) => Strength (,) (HyperArr arr) where
  strength h = liftH $ mkArr $ \(a, b) -> (a,) <$> observeH h b
  withStrengthOb ::
    forall a b c r.
    ObDict (HyperArr arr) a ->
    ObDict (HyperArr arr) b ->
    ObDict (HyperArr arr) c ->
    ((Ob (HyperArr arr) (a, b), Ob (HyperArr arr) (a, c)) => r) ->
    r
  withStrengthOb ObDict ObDict ObDict =
    withStrengthOb @(,) @arr @a @b @c @r
      (ObDict :: ObDict arr a)
      (ObDict :: ObDict arr b)
      (ObDict :: ObDict arr c)

instance
  ( HyperBase arr,
    Strength (,) arr
  ) =>
  Traced (,) (HyperArr arr)
  where
  trace = traceHyper
    where
      traceHyper ::
        forall a b c.
        HyperArr arr (a, b) (a, c) ->
        HyperArr arr b c
      traceHyper body =
        HyperArr $
          mkArr $ \k ->
            snd
              <$> fixRun @arr
                ( \pair -> do
                    let cont =
                          HyperArr $
                            mkArr $ \_ -> do
                              a_val <- observeH k (snd pair)
                              pure (fst pair, a_val)
                    runArr (invoke body) cont
                )

-- ---------------------------------------------------------------------------
-- Function-category specialisation
-- ---------------------------------------------------------------------------

-- | Convert the function-category hyperfunction to the existing
-- "Circuit.Hyper" type.
toHyper :: HyperArr (->) a b -> H.Hyper a b
toHyper (HyperArr f) = H.Hyper (f . fromHyper)

-- | Convert the existing "Circuit.Hyper" type to the function-category
-- parameterised hyperfunction.
fromHyper :: H.Hyper a b -> HyperArr (->) a b
fromHyper (H.Hyper f) = HyperArr (f . toHyper)

-- | Push a plain function onto a function-category hyperfunction.
pushF :: (a -> b) -> HyperArr (->) a b -> HyperArr (->) a b
pushF = pushH

-- | Embed a plain function into a function-category hyperfunction.
liftF :: (a -> b) -> HyperArr (->) a b
liftF = liftH

-- | A constant function-category hyperfunction.
baseF :: b -> HyperArr (->) a b
baseF = baseH

-- | Extract a plain function from a function-category hyperfunction.
observeF :: HyperArr (->) a b -> a -> b
observeF h = runIdentity . observeH h

-- | Close the self-referential loop in a function-category hyperfunction.
runHyperF :: HyperArr (->) a a -> a
runHyperF = runIdentity . runHyperH

-- ---------------------------------------------------------------------------
-- Kleisli aliases
-- ---------------------------------------------------------------------------

-- | Alias for 'pushH' on @Kleisli m@.
pushArr ::
  (MonadFix m) =>
  Kleisli m a b ->
  HyperArr (Kleisli m) a b ->
  HyperArr (Kleisli m) a b
pushArr = pushH

-- | Alias for 'liftH' on @Kleisli m@.
liftArr :: (MonadFix m) => Kleisli m a b -> HyperArr (Kleisli m) a b
liftArr = liftH

-- | Alias for 'baseH' on @Kleisli m@.
baseArr :: (MonadFix m) => b -> HyperArr (Kleisli m) a b
baseArr = baseH

-- | Alias for 'observeH' on @Kleisli m@.
observeArr ::
  (MonadFix m) =>
  HyperArr (Kleisli m) a b ->
  a ->
  m b
observeArr = observeH

-- | Alias for 'runHyperH' on @Kleisli m@.
runHyperArr ::
  (MonadFix m) =>
  HyperArr (Kleisli m) a a ->
  m a
runHyperArr = runHyperH
