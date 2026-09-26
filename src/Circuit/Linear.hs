{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Circuit.Linear
  ( Bot,
    Par (..),
    distL,
    distR,
    mix,
    Lolli (..),
    Exponential (..),
    BangCopy (..),
    BangWeaken (..),
    WhyNotIntro (..),
    WhyNotMonoid (..),
    LinearBang,
    AffineBang,
    RelevantBang,
  )
where

import Circuit.Category (Category (..), K (..))
import Circuit.Tensor (Tensor, Unit)
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

type family Bot (p :: k -> k -> k) :: k

class (Category arr) => Par p arr where
  parP :: arr a b -> arr c d -> arr (p a c) (p b d)

  unitlP :: arr (p (Bot p) a) a

  unitlP' :: arr a (p (Bot p) a)

  unitrP :: arr (p a (Bot p)) a

  unitrP' :: arr a (p a (Bot p))

type instance Bot Either = Void

instance Par Either (->) where
  parP = bimap
  {-# INLINE parP #-}
  unitlP = either absurd id
  {-# INLINE unitlP #-}
  unitlP' = Right
  {-# INLINE unitlP' #-}
  unitrP = either id absurd
  {-# INLINE unitrP #-}
  unitrP' = Left
  {-# INLINE unitrP' #-}

instance (Monad m) => Par Either (K m) where
  parP (K f) (K g) =
    K $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE parP #-}
  unitlP = K $ either absurd pure
  {-# INLINE unitlP #-}
  unitlP' = K $ pure . Right
  {-# INLINE unitlP' #-}
  unitrP = K $ either pure absurd
  {-# INLINE unitrP #-}
  unitrP' = K $ pure . Left
  {-# INLINE unitrP' #-}

distL :: (a, Either b c) -> Either (a, b) c
distL (a, Left b) = Left (a, b)
distL (_, Right c) = Right c
{-# INLINE distL #-}

distR :: (Either b c, a) -> Either b (c, a)
distR (Left b, _) = Left b
distR (Right c, a) = Right (c, a)
{-# INLINE distR #-}

mix :: Void -> ()
mix = absurd
{-# INLINE mix #-}

class (Category arr) => Lolli (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) where
  type LolliT t arr a b :: Type

  lolli ::
    arr a b ->
    arr (LolliT t arr a b) (LolliT t arr a b)

  evalLinear ::
    arr (t a (LolliT t arr a b)) b

  curryL ::
    arr (t a b) c ->
    arr a (LolliT t arr b c)

  uncurryL ::
    arr a (LolliT t arr b c) ->
    arr (t a b) c

instance Lolli (,) (->) where
  type LolliT (,) (->) a b = a -> b
  lolli _ = id
  {-# INLINE lolli #-}
  evalLinear (a, f) = f a
  {-# INLINE evalLinear #-}
  curryL f a b = f (a, b)
  {-# INLINE curryL #-}
  uncurryL g (a, b) = g a b
  {-# INLINE uncurryL #-}

class (Tensor t arr) => Exponential t arr where
  type Bang t arr a :: Type
  type WhyNot t arr a = result | result -> a

class (Exponential t arr) => BangCopy t arr where
  copyE ::
    arr (Bang t arr a) (t (Bang t arr a) (Bang t arr a))

class (Exponential t arr) => BangWeaken t arr where
  discardE ::
    arr (Bang t arr a) (Unit t)

  derelict ::
    arr (Bang t arr a) a

class (Exponential t arr) => WhyNotIntro t arr where
  introduce ::
    arr a (WhyNot t arr a)

class (Exponential t arr, Par p arr) => WhyNotMonoid t p arr where
  mergeE ::
    arr (p (WhyNot t arr a) (WhyNot t arr a)) (WhyNot t arr a)

  zeroE ::
    arr (Bot p) (WhyNot t arr a)

type LinearBang t arr = (Exponential t arr, BangCopy t arr, BangWeaken t arr)

type AffineBang t arr = (Exponential t arr, BangWeaken t arr)

type RelevantBang t arr = (Exponential t arr, BangCopy t arr)

instance Exponential (,) (->) where
  type Bang (,) (->) a = a
  type WhyNot (,) (->) a = [a]

instance BangCopy (,) (->) where
  copyE x = (x, x)
  {-# INLINE copyE #-}

instance BangWeaken (,) (->) where
  discardE _ = ()
  {-# INLINE discardE #-}
  derelict = id
  {-# INLINE derelict #-}

instance WhyNotIntro (,) (->) where
  introduce x = [x]
  {-# INLINE introduce #-}

instance WhyNotMonoid (,) Either (->) where
  mergeE = either id id
  {-# INLINE mergeE #-}
  zeroE = absurd
  {-# INLINE zeroE #-}
