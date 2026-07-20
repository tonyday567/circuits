{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Local category hierarchy with object constraints.
--
-- 'Category' is local so morphisms can carry an associated 'Ob'
-- constraint.
--
-- 'Discrete' marks categories whose 'Ob' is trivial for every object
-- (@Ob = ()@). Constrained bases can implement 'Circuit.Loop.Traced'
-- directly, but /hosting/ the free constructions (@Free@, @Sym@, @Loop@,
-- @Net@, and the syntax in "Circuit.Algebra") additionally requires
-- 'Discrete', because compound tensor objects (e.g. @t s a@ inside a
-- 'Loop.Knot') carry no 'Ob' evidence and must be manufactured on demand.
--
-- == Operator convention
--
-- The tip of the operator points in the direction of data flow.
--
-- * @|@ means /apply/ to a value: @('|>')@ feeds a value into a function
--   (forward application, like @&@), and @('<|')@ applies a function
--   to a value (backward application, like @('$')@).
-- * @.@ means /compose/ morphisms: @('.>')@ is forward composition and
--   @('.')@ is backward composition as usual.
module Circuit.Category
  ( Category (..),
    Discrete (..),
    (.>),
    (|>),
    (<|),
  )
where

import Control.Arrow (Kleisli (..))
import Control.Monad ((<=<))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

-- | A category whose objects may carry a constraint.
--
-- @Ob arr a@ is the evidence required to mention object @a@ in @arr@.
-- Unconstrained categories use the default @()@. Constrained categories
-- specialise the associated type to whatever their objects require.
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
-- that bind an existential object (notably @Loop@ in "Circuit.Loop")
-- use it where a polymorphic @Ob@ constraint cannot be written.
class (Category arr) => Discrete arr where
  withOb :: forall a r. ((Ob arr a) => r) -> r

-- | Forward composition. @f .> g = g . f@
(.>) :: (Category arr, Ob arr a, Ob arr b, Ob arr c) => arr a b -> arr b c -> arr a c
f .> g = g . f
{-# INLINE (.>) #-}

-- | Forward application. @x |> f = f x@
(|>) :: a -> (a -> b) -> b
x |> f = f x
{-# INLINE (|>) #-}

infixl 1 |>

-- | Backward application. @f <| x = f x@
(<|) :: (a -> b) -> a -> b
f <| x = f x
{-# INLINE (<|) #-}

infixr 0 <|

-- | Unconstrained function category.
instance Category (->) where
  type Ob (->) a = ()
  id x = x
  (f . g) x = f (g x)

instance Discrete (->) where
  withOb x = x

-- | Kleisli arrows of a monad (unconstrained objects).
instance (Monad m) => Category (Kleisli m) where
  type Ob (Kleisli m) a = ()
  id = Kleisli pure
  Kleisli f . Kleisli g = Kleisli (f <=< g)

instance (Monad m) => Discrete (Kleisli m) where
  withOb x = x
