{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Parameterised hyperfunctions: the final encoding over an arbitrary
-- base category.
--
-- The existing "Circuit.Hyper" is the specialisation to the function
-- category @(->)@.  This module generalises the construction to any
-- category @arr@, with the monadic base @Control.Arrow.Kleisli m@ as the
-- second named target (Kidney & Wu's monadic hyperfunction @HypM@).
--
-- The design question is: what structure on @arr@ is needed for a
-- 'Category'/'Channel'/'Traced' instance on @HyperArr arr@?  For now we
-- give the two concrete specialisations the card names; the common
-- abstraction can be extracted once the pattern is visible.
--
-- === doctests
--
-- >>> import Circuit.HyperArr
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Data.Functor.Identity (Identity (..))
--
-- >>> let body = liftArr (Kleisli (\(xs, ()) -> Identity (0 : xs, take 3 xs)) :: Kleisli Identity ([Int], ()) ([Int], [Int]))
-- >>> runIdentity (observeArr (trace body) ())
-- [0,0,0]
module Circuit.HyperArr
  ( -- * Hyperfunctions over a base category
    HyperArr (..),

    -- * Function-category bridge
    toHyper,
    fromHyper,

    -- * Kleisli constructors and eliminators
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
pushF f h = HyperArr (\k -> f (invoke k h))

-- | Embed a plain function into a function-category hyperfunction.
liftF :: (a -> b) -> HyperArr (->) a b
liftF f = pushF f (liftF f)

-- | A constant function-category hyperfunction.
baseF :: b -> HyperArr (->) a b
baseF b = HyperArr (const b)

-- | Extract a plain function from a function-category hyperfunction.
observeF :: HyperArr (->) a b -> a -> b
observeF h a = invoke h (baseF a)

instance Category (HyperArr (->)) where
  type Ob (HyperArr (->)) a = ()
  id = liftF id
  f . g = HyperArr (\k -> invoke f (g . k))

instance Channel (,) (HyperArr (->)) where
  assoc = liftF (\(~(~(a, b), c)) -> (a, (b, c)))
  assoc' = liftF (\ ~(a, ~(b, c)) -> ((a, b), c))
  slide = liftF (\ ~(a, ~(b, c)) -> (b, (a, c)))
  withTensorOb ObDict ObDict k = k

instance Strength (,) (HyperArr (->)) where
  strength h = liftF (second (observeF h))
  withStrengthOb ObDict ObDict ObDict k = k

instance Traced (,) (HyperArr (->)) where
  trace body =
    HyperArr $ \k ->
      let pair = invoke body cont
          cont = HyperArr $ \_ ->
            let a_val = invoke k (baseF (snd pair))
             in (fst pair, a_val)
       in snd pair

-- ---------------------------------------------------------------------------
-- Kleisli specialisation (monadic hyperfunctions)
-- ---------------------------------------------------------------------------

-- | Push a base morphism onto a 'HyperArr' over @Kleisli m@.
pushArr ::
  (Monad m) =>
  Kleisli m a b ->
  HyperArr (Kleisli m) a b ->
  HyperArr (Kleisli m) a b
pushArr f h = HyperArr $ Kleisli $ \k -> runKleisli f =<< runKleisli (invoke k) h

-- | Embed a base morphism into a 'HyperArr' over @Kleisli m@.
--
-- This is the coinductive character of the construction: the morphism is
-- pushed onto every future continuation.
liftArr ::
  (Monad m) =>
  Kleisli m a b ->
  HyperArr (Kleisli m) a b
liftArr f = pushArr f (liftArr f)

-- | A constant 'HyperArr' over @Kleisli m@.
baseArr :: (Monad m) => b -> HyperArr (Kleisli m) a b
baseArr b = HyperArr $ Kleisli $ \_ -> pure b

-- | Extract the underlying Kleisli morphism from a 'HyperArr'.
observeArr ::
  (Monad m) =>
  HyperArr (Kleisli m) a b ->
  a ->
  m b
observeArr h a = runKleisli (invoke h) (baseArr a)

-- | Close the self-referential loop in a monadic hyperfunction.
runHyperArr ::
  (MonadFix m) =>
  HyperArr (Kleisli m) a a ->
  m a
runHyperArr h = mfix $ \a -> runKleisli (invoke h) (baseArr a)

instance (Monad m) => Category (HyperArr (Kleisli m)) where
  type Ob (HyperArr (Kleisli m)) a = ()
  id = liftArr (Kleisli pure)
  f . g = HyperArr $ Kleisli $ \k -> runKleisli (invoke f) (g . k)

instance (Monad m) => Channel (,) (HyperArr (Kleisli m)) where
  assoc =
    liftArr $
      Kleisli $
        \(~(~(a, b), c)) -> pure (a, (b, c))
  assoc' =
    liftArr $
      Kleisli $
        \ ~(a, ~(b, c)) -> pure ((a, b), c)
  slide =
    liftArr $
      Kleisli $
        \ ~(a, ~(b, c)) -> pure (b, (a, c))
  withTensorOb ObDict ObDict k = k

instance (Monad m) => Strength (,) (HyperArr (Kleisli m)) where
  strength h = liftArr $ Kleisli $ \(a, b) -> (a,) <$> observeArr h b
  withStrengthOb ObDict ObDict ObDict k = k

instance (MonadFix m) => Traced (,) (HyperArr (Kleisli m)) where
  trace body =
    HyperArr $
      Kleisli $ \k ->
        snd
          <$> mfix
            ( \pair -> do
                let cont =
                      HyperArr $
                        Kleisli $ \_ -> do
                          a_val <- observeArr k (snd pair)
                          pure (fst pair, a_val)
                runKleisli (invoke body) cont
            )
