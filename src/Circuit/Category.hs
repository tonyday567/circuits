{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Local category hierarchy without object constraints.
--
-- 'Category' is local so morphisms can carry an associated object
-- constraint.  This version removes the constraint-family apparatus:
-- objects are unconstrained at the type level and legitimacy is an
-- audit concern rather than a discharge concern.
--
-- == Operator convention
--
-- The tip of the operator points in the direction of data flow.
--
-- * @|@ means /apply/ to a value: @('|>')@ feeds a value into a function
--   (forward application, like @&@), and @('<|')@ applies a function
--   to a value (backward application, like @'$'@).
-- * @.@ means /compose/ morphisms: @('.>')@ is forward composition and
--   @('.')@ is backward composition as usual.
module Circuit.Category
  ( Category (..),
    (.>),
    (|>),
    (<|),
  )
where

import Control.Arrow (Kleisli (..))
import Control.Monad ((<=<))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- | A category without object constraints.
--
-- @Ob arr a@ is gone; every object is mentionable.  Lawfulness is
-- checked by the axioma oracles rather than by type-level discharge.
class Category (arr :: k -> k -> Type) where
  -- | Identity morphism.
  id :: arr a a

  -- | Composition (right-to-left).
  (.) :: arr b c -> arr a b -> arr a c

-- | Forward composition. @f .> g = g . f@
(.>) :: (Category arr) => arr a b -> arr b c -> arr a c
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
  id x = x
  (f . g) x = f (g x)

-- | Kleisli arrows of a monad (unconstrained objects).
instance (Monad m) => Category (Kleisli m) where
  id = Kleisli pure
  Kleisli f . Kleisli g = Kleisli (f <=< g)
