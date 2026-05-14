{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The free traced monoidal category.
--
-- `Circuit arr t a b` is the initial encoding of a traced monoidal category
-- over a base morphism `arr` with a supplied tensor `t` for the category. The three constructors encode:
--
--   - `Lift`: embedding of a base arrow (strict monoidal functor)
--   - `Compose`: sequential composition (category structure)
--   - `Knot`: feedback channel (trace structure)
--
-- For example, a `Circuit (->) (,)` is the initial traced monoidal cartesian category over Haskell functions.
--
-- The `lower` function interprets any `Circuit` to a plain function via
-- the `Trace` instance on `t`. For encoding into 'Circuit.Hyper', see
-- 'Circuit.Hyper.encode' and 'Circuit.Hyper.encodeEither'.
module Circuit.Circuit
  ( -- * Circuit
    Circuit (..),
    (↑),
    (⊙),
    (↮),

    -- * Operators
    reify,
    lower,
    (↓),
    push,
    (⊲),
  )
where

import Circuit.Traced ( Trace (..))
import Control.Category
import Prelude hiding (id, (.))

-- $setup
--
-- >>> :set -XBlockArguments -XLambdaCase

-- | Circuit arr t a b is the free traced monoidal category.
-- 🟣 need something special here. clear, tight, simple, complete.
data Circuit arr t a b where
  -- | Lift embeds a base arrow (strict monoidal functor).
  Lift :: arr a b -> Circuit arr t a b
  -- | Compose performs sequential composition (category structure).
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  -- | Knot ties a feedback loop. The tensor t carries the channel type.
  Knot :: arr (t a b) (t a c) -> Circuit arr t b c

-- | Synonym for 'Lift'.
infixr 9 ↑

(↑) :: arr a b -> Circuit arr t a b
(↑) = Lift

-- | Synonym for 'Knot'.
infixr 9 ↮

(↮) :: arr (t a b) (t a c) -> Circuit arr t b c
(↮) = Knot

-- | Synonym for 'Compose'.
(⊙) :: (Category arr) => Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
(⊙) = Compose

instance (Category arr) => Category (Circuit arr t) where
  id = Lift id
  (.) = Compose

instance Functor (Circuit (->) t a) where
  fmap f = Compose (Lift f)

instance (Trace (->) t) => Applicative (Circuit (->) t x) where
  pure a = Lift (const a)
  f <*> v = Lift $ \x -> reify f x (reify v x)

instance (Trace (->) t) => Monad (Circuit (->) t x) where
  m >>= k = Lift $ \x -> reify (k (reify m x)) x

-- | Push a plain function onto a Circuit.
--
-- >>> reify (push (+1) (Lift (*2) :: Circuit (->) (,) Int Int)) 5
-- 11
push :: arr b c -> Circuit arr t a b -> Circuit arr t a c
push f = Compose (Lift f)

-- | Push / prepend a plain function to a Circuit. Operator form of 'push'.
infixr 8 ⊲

(⊲) :: arr b c -> Circuit arr t a b -> Circuit arr t a c
(⊲) = push

-- | Interpret a Circuit to a plain function.
--
-- This is the unique traced functor from the initial object (Circuit)
-- to the target category. The Mendler case (when a Loop appears on the
-- left of Compose) enforces the sliding axiom of traced monoidal categories.
--
-- >>> lower (Lift (+1) :: Circuit (->) (,) Int Int) 5
-- 6
lower :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
lower (Lift f) = f
lower (Compose (Knot f) g) = trace (f . untrace (lower g))
lower (Compose f g) = lower f . lower g
lower (Knot k) = trace k

-- | Synonym for 'lower'.
--
-- Because 'lower' returns a plain function, the postfix form
-- chains naturally via function application.
infixl 9 ↓

(↓) :: (Category arr, Trace arr t) => Circuit arr t a b -> arr a b
(↓) = lower

-- | Alias for 'lower': interpret a Circuit as a plain function. Useful to distinguish Circuit.lower from the other adjunctions.
reify :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
reify = lower
