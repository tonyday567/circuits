{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

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
-- 'ObC' is a thin class wrapper around the 'Ob' constraint family. It
-- exists so that 'Circuit.Channel.Channel' can state tensor closure as a
-- quantified superclass: GHC requires the head of a quantified constraint
-- to be a class or type variable, not a type-family application.
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
    Ob,
    ObC,
    ObDict (..),
    withObDict,
    (.>),
    (|>),
    (<|),
  )
where

import Control.Arrow (Kleisli (..))
import Control.Monad ((<=<))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

-- | Explicit object-constraint dictionary for a category @arr@ and object @a@.
--
-- Carrying @a@ as a type parameter avoids the non-injectivity of the
-- associated 'Ob' constraint family when threading dictionaries through folds.
data ObDict arr a where
  ObDict :: (Ob arr a) => ObDict arr a

-- | Bring an object constraint into scope from an explicit dictionary.
withObDict :: forall arr a r. ObDict arr a -> ((Ob arr a) => r) -> r
withObDict ObDict x = x

-- | A class wrapper around 'Ob' so it can appear as the head of a
-- quantified constraint. The default instance makes 'ObC' available
-- whenever 'Ob' is.
class (Ob arr a) => ObC arr a

instance (Ob arr a) => ObC arr a

-- | A category whose objects may carry a constraint.
--
-- @Ob arr a@ is the evidence required to mention object @a@ in @arr@.
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
  obDict :: forall a. ObDict arr a
  obDict = withOb @arr @a ObDict

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
