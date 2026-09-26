{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

module Circuit.Hyper
  ( HyperA (..),
    Hyper,
    pattern Hyper,
    lift,
    observe,
    baseHyper,
    push,
    runHyper,
    liftK,
    observeK,
    baseK,
    pushK,
    runHyperK,
    encodeEither,
    runEither,
    encode,
    encodeK,
  )
where

import Circuit.Category (Category (..), K (..))
import Circuit.Syntax (SigCompose (..), (:+:) (..))
import Circuit.Syntax qualified as Syn
import Circuit.Trace (SigYank (..), Trace)
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Control.Monad.Fix (MonadFix, mfix)
import Data.Bifunctor (second)
import Prelude hiding (id, (.))

newtype HyperA arr a b = HyperA
  { invoke :: arr (HyperA arr b a) b
  }

type Hyper = HyperA (->)

pattern Hyper :: (HyperA (->) b a -> b) -> Hyper a b
pattern Hyper f = HyperA f

{-# COMPLETE Hyper :: Hyper #-}

lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

observe :: Hyper a b -> (a -> b)
observe h a = invoke h (baseHyper a)

baseHyper :: a -> Hyper b a
baseHyper b = HyperA $ const b

push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = HyperA $ \k -> f (invoke k h)

runHyper :: Hyper a a -> a
runHyper h = let a = invoke h (baseHyper a) in a

liftK :: (Monad m) => K m a b -> HyperA (K m) a b
liftK f = pushK f (liftK f)

observeK :: (Monad m) => HyperA (K m) a b -> a -> m b
observeK h a = runK (invoke h) (baseK a)

baseK :: (Monad m) => b -> HyperA (K m) a b
baseK b = HyperA $ K $ \_ -> pure b

pushK :: (Monad m) => K m a b -> HyperA (K m) a b -> HyperA (K m) a b
pushK f h = HyperA $ K $ \k -> do
  a_val <- runK (invoke k) h
  runK f a_val

runHyperK :: (MonadFix m) => HyperA (K m) a a -> m a
runHyperK h = mfix $ \a -> runK (invoke h) (baseK a)

instance Category Hyper where
  id = lift id
  f . g = HyperA $ \k -> invoke f (g . k)

instance Assoc (,) Hyper where
  assoc = lift assoc
  assoc' = lift assoc'

instance Slide (,) Hyper where
  slide = lift slide

instance Strength (,) Hyper where
  strength h = lift $ second (observe h)

instance Yank (,) Hyper where
  yank body = HyperA $ \k ->
    let pair = invoke body cont
        cont = HyperA $ const (second (observe k) pair)
     in snd pair

instance (Monad m) => Category (HyperA (K m)) where
  id = liftK id
  f . g = HyperA $ K $ \k -> runK (invoke f) (g . k)

instance (Monad m) => Assoc (,) (HyperA (K m)) where
  assoc = liftK assoc
  assoc' = liftK assoc'

instance (Monad m) => Slide (,) (HyperA (K m)) where
  slide = liftK slide

instance (Monad m) => Strength (,) (HyperA (K m)) where
  strength h = liftK $ K $ \(a, b) -> (a,) <$> observeK h b

instance (MonadFix m) => Yank (,) (HyperA (K m)) where
  yank body = HyperA $ K $ \k -> do
    pair <- mfix $ \pair -> do
      let cont =
            HyperA $ K $ \_ -> do
              b <- observeK k (snd pair)
              pure (fst pair, b)
      runK (invoke body) cont
    pure (snd pair)

encodeEither ::
  (Either a b -> Either a c) ->
  Hyper (Either a b -> c) (Either a b -> c)
encodeEither f = h
  where
    h =
      Hyper
        ( \k s ->
            case f s of
              Right c -> c
              Left a -> invoke k h (Left a)
        )

runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = runHyper (encodeEither f) (Right b)

encode ::
  Trace (,) (->) a b ->
  Hyper a b
encode (Syn.Lift f) = lift f
encode (Syn.Oper (L (SigCompose g f))) = encode g . encode f
encode (Syn.Oper (R (YankBody body))) = yank (encode body)

encodeK ::
  (MonadFix m) =>
  Trace (,) (K m) a b ->
  HyperA (K m) a b
encodeK (Syn.Lift f) = liftK f
encodeK (Syn.Oper (L (SigCompose g f))) = encodeK g . encodeK f
encodeK (Syn.Oper (R (YankBody body))) = yank (encodeK body)
