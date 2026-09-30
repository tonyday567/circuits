{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Circuit.Category
  ( Category (..),
    (.>),
    (<.),
    (|>),
    (<|),
    K (..),
    Comonad (..),
    CoK (..),
    Dist (..),
    BiK (..),
    Op (..),
    FunctionLike (..),
    Pointed (..),
  )
where

import Control.Monad ((<=<))
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

class Category (arr :: k -> k -> Type) where
  id :: arr a a

  (.) :: arr b c -> arr a b -> arr a c

(.>) :: (Category arr) => arr a b -> arr b c -> arr a c
f .> g = g . f
{-# INLINE (.>) #-}

infixr 9 .>

(<.) :: (Category arr) => arr b c -> arr a b -> arr a c
(<.) = (.)
{-# INLINE (<.) #-}

infixr 9 <.

(|>) :: a -> (a -> b) -> b
x |> f = f x
{-# INLINE (|>) #-}

infixl 1 |>

(<|) :: (a -> b) -> a -> b
f <| x = f x
{-# INLINE (<|) #-}

infixr 0 <|

instance Category (->) where
  id x = x
  (f . g) x = f (g x)

newtype K m a b = K {runK :: a -> m b}

instance (Monad m) => Category (K m) where
  id = K pure
  K f . K g = K (f <=< g)

class (Functor w) => Comonad w where
  extract :: w a -> a

  duplicate :: w a -> w (w a)

  extend :: (w a -> b) -> w a -> w b
  extend f wa = fmap f (duplicate wa)

instance Comonad Identity where
  extract = runIdentity
  duplicate = Identity

instance Comonad ((,) s) where
  extract = snd
  duplicate (s, a) = (s, (s, a))

newtype CoK c a b = CoK {runCoK :: c a -> b}

instance (Comonad c) => Category (CoK c) where
  id = CoK extract
  CoK g . CoK f = CoK (\ca -> g (extend f ca))

class (Comonad w, Monad m) => Dist w m where
  dist :: w (m a) -> m (w a)

instance (Monad m) => Dist ((,) s) m where
  dist (s, mb) = (s,) <$> mb

newtype BiK w m a b = BiK {runBiK :: w a -> m b}

instance (Dist w m) => Category (BiK w m) where
  id = BiK (pure . extract)
  BiK g . BiK f = BiK (\wa -> dist (extend f wa) >>= g)

newtype Op arr a b = Op {runOp :: arr b a}

instance (Category arr) => Category (Op arr) where
  id :: forall a. Op arr a a
  id = Op id
  {-# INLINE id #-}

  (.) :: forall a b c. Op arr b c -> Op arr a b -> Op arr a c
  Op g . Op f = Op (f . g)
  {-# INLINE (.) #-}

class (Category arr) => FunctionLike arr where
  function :: (a -> b) -> arr a b

instance FunctionLike (->) where
  function = id
  {-# INLINE function #-}

instance (Monad m) => FunctionLike (K m) where
  function f = K (pure . f)

class Pointed a where
  point :: a

instance Pointed () where
  point = ()
  {-# INLINE point #-}

instance Pointed (Maybe a) where
  point = Nothing
  {-# INLINE point #-}

instance Pointed [a] where
  point = []
  {-# INLINE point #-}
