{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
-- * @.@ means /compose/ morphisms: @('.>')@ is forward composition,
--   @('.')@ is backward composition as usual, and @('<.')@ is the same
--   backward composition under a non-Prelude name.
module Circuit.Category
  ( Category (..),
    (.>),
    (<.),
    (|>),
    (<|),
    K (..),
    Comonad (..),
    CoK (..),
    Op (..),
    FunctionLike (..),
    Pointed (..),
  )
where

import Control.Monad ((<=<))
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Data.Functor.Identity (Identity (..))

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

infixr 9 .>

-- | Backward composition (non-Prelude name for '(.)').
--
-- @f <. g = f . g@, so data flows from @g@ to @f@.
(<.) :: (Category arr) => arr b c -> arr a b -> arr a c
(<.) = (.)
{-# INLINE (<.) #-}

infixr 9 <.

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

-- | Kleisli arrows of a monad, named locally.
newtype K m a b = K {runK :: a -> m b}

instance (Monad m) => Category (K m) where
  id = K pure
  K f . K g = K (f <=< g)

-- | A comonad, named locally.
--
-- As with 'Category', the laws are an audit concern rather than a discharge
-- concern: 'extract' and 'duplicate' should satisfy the comonad laws, and
-- the oracles for that live in the axioma suite, not here.
class (Functor w) => Comonad w where
  -- | Extract the value at the current position.
  extract :: w a -> a

  -- | Present the space of contexts: each position expands to a position of
  -- positions.
  duplicate :: w a -> w (w a)

  -- | Extend a context-dependent computation over a comonadic value.
  extend :: (w a -> b) -> w a -> w b
  extend f wa = fmap f (duplicate wa)

-- | The identity comonad.
instance Comonad Identity where
  extract = runIdentity
  duplicate = Identity

-- | Co-Kleisli arrows of a comonad, named locally.
--
-- The dual seat of 'K'.  Note that @Op (K m)@ is a Kleisli arrow reversed
-- (@b -> m a@), not a co-Kleisli arrow (@c a -> b@): the flip reverses the
-- arrow but not the modality, so @CoK@ is genuinely new furniture.
--
-- >>> let f = CoK (\(Identity a) -> a + 1) :: CoK Identity Int Int
-- >>> runCoK f (Identity 4)
-- 5
newtype CoK c a b = CoK {runCoK :: c a -> b}

instance (Comonad c) => Category (CoK c) where
  id = CoK extract
  CoK g . CoK f = CoK (\ca -> g (extend f ca))

-- | The opposite category: morphisms are reversed.
--
-- @Op arr a b@ is the same hom-set as @arr b a@.  This is the arrow used to
-- make the @Set^op@ rung of the polynomial equipment explicit inside
-- 'Circuit.Body' and 'Circuit.Moore'.
newtype Op arr a b = Op {runOp :: arr b a}

instance (Category arr) => Category (Op arr) where
  id :: forall a. Op arr a a
  id = Op id
  {-# INLINE id #-}

  (.) :: forall a b c. Op arr b c -> Op arr a b -> Op arr a c
  Op g . Op f = Op (f . g)
  {-# INLINE (.) #-}

-- | Categories that can embed pure functions as morphisms.
--
-- This is the canonical functor from the function category @(->)@ into
-- @arr@. It is useful for lifting decision procedures (e.g. bias in a
-- race) into arrows such as Kleisli categories.
class (Category arr) => FunctionLike arr where
  -- | Lift a pure function into the arrow.
  function :: (a -> b) -> arr a b

-- | Functions embed as themselves.
instance FunctionLike (->) where
  function = id
  {-# INLINE function #-}

-- | Kleisli arrows embed pure functions by returning the result in the
-- monad.
instance (Monad m) => FunctionLike (K m) where
  function f = K (pure . f)

-- | A pointed object: an object with a distinguished element.
--
-- This class has no laws by construction — it merely names a chosen
-- element.  It is the structural requirement for the coproduct-unit poles
-- of 'Body Either': on a payload input the companion must produce a carrier
-- value, and there is no ambient state to use.  'Monoid' is over-strong for
-- this purpose, since only the identity element is needed.
--
-- This is the EM side of pointing — an algebra of the @Maybe@ monad,
-- structure on the object. The runner-facing presentation of the same
-- pointing is the unit cell in "Circuit.Equip".
class Pointed a where
  point :: a

-- | The singleton type is canonically pointed.
instance Pointed () where
  point = ()
  {-# INLINE point #-}

-- | 'Maybe' is canonically pointed at 'Nothing'.
instance Pointed (Maybe a) where
  point = Nothing
  {-# INLINE point #-}

-- | Lists are canonically pointed at the empty list.
instance Pointed [a] where
  point = []
  {-# INLINE point #-}
