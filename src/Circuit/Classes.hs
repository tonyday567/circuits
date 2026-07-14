{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Local category hierarchy with object constraints.
--
-- On GHC, 'Bifunctor' and 'Profunctor' still come from packages.
-- 'Category' is always local so morphisms can carry an associated 'Ob'
-- constraint (e.g. 'Finite' for matrices, 'KnownNat' for harpie mats).
--
-- 'Discrete' marks categories whose 'Ob' is trivial for every object
-- (@Ob = ()@). Free constructions that fuse existential channels
-- (notably 'Trace') require 'Discrete' on the base.
module Circuit.Classes
  ( Category (..),
    Discrete (..),
    (>>>),
    (<<<),
#ifdef __GLASGOW_HASKELL__
    Bifunctor (..),
    Profunctor (..),
#else
    Bifunctor (..),
    Profunctor (..),
#endif
  )
where

import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

#ifdef __GLASGOW_HASKELL__
import Control.Arrow (Kleisli (..))
import Control.Monad ((<=<))
import Data.Bifunctor (Bifunctor (..))
import Data.Profunctor (Profunctor (..))
#endif

-- | A category whose objects may carry a constraint.
--
-- @Ob arr a@ is the evidence required to mention object @a@ in @arr@.
-- Unconstrained categories use the default @()@. Constrained ones
-- specialise it (e.g. @Ob (Mat s) a = Finite a@).
class Category (arr :: k -> k -> Type) where
  -- | Object constraint for this category.
  type Ob arr (a :: k) :: Constraint

  type Ob arr a = ()

  -- | Identity morphism.
  id :: (Ob arr a) => arr a a

  -- | Composition (right-to-left).
  (.) :: (Ob arr a, Ob arr b, Ob arr c) => arr b c -> arr a b -> arr a c

-- | Categories with a trivial object constraint for every type.
--
-- 'withOb' discharges @Ob arr a@ at an arbitrary @a@. Free constructions
-- that hide existential channels use this instead of
-- @forall x. Ob arr x@ (illegal on associated types).
class (Category arr) => Discrete arr where
  withOb :: forall a r. (Ob arr a => r) -> r

-- | Left-to-right composition.
(>>>) :: (Category arr, Ob arr a, Ob arr b, Ob arr c) => arr a b -> arr b c -> arr a c
f >>> g = g . f
{-# INLINE (>>>) #-}

-- | Right-to-left composition (synonym for '(.)').
(<<<) :: (Category arr, Ob arr a, Ob arr b, Ob arr c) => arr b c -> arr a b -> arr a c
(<<<) = (.)
{-# INLINE (<<<) #-}

-- | Unconstrained function category.
instance Category (->) where
  type Ob (->) a = ()
  id x = x
  (f . g) x = f (g x)

instance Discrete (->) where
  withOb x = x

#ifdef __GLASGOW_HASKELL__
-- | Kleisli arrows of a monad (unconstrained objects).
instance (Monad m) => Category (Kleisli m) where
  type Ob (Kleisli m) a = ()
  id = Kleisli pure
  Kleisli f . Kleisli g = Kleisli (f <=< g)

instance (Monad m) => Discrete (Kleisli m) where
  withOb x = x
#else

class Bifunctor p where
  bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
  first :: (a -> b) -> p a c -> p b c
  second :: (b -> c) -> p a b -> p a c
  bimap f g = first f . second g
  first f = bimap f id
  second = bimap id

instance Bifunctor (,) where
  bimap f g (a, b) = (f a, g b)

instance Bifunctor Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right b) = Right (g b)

class Profunctor p where
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d
  lmap :: (a -> b) -> p b c -> p a c
  rmap :: (b -> c) -> p a b -> p a c
  dimap f g = lmap f . rmap g
  lmap f = dimap f id
  rmap = dimap id

#endif
