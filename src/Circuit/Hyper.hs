{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hyperfunctions: the final encoding of traced monoidal categories.
--
-- A Hyper is a Church encoding of a Circuit. The feedback channel is
-- structural in the type rather than explicit, so the sliding axiom
-- is inherent to composition rather than enforced by pattern matching.
--
-- Symbolic vocabulary:
--
--   * Type: @a ↬ b@ is a hyperfunction from @a@ to @b@.
--   * Invoke: @h ⇸ k@ applies hyperfunction @h@ to continuation @k@.
--   * Push: @f ⊲ h@ pushes a plain function @f@ onto hyperfunction @h@.
--   * Run: @(⥁) h@ closes the self-referential loop.
module Circuit.Hyper
  ( -- * Type
    Hyper (..),
    type (↬),

    -- * Construction and elimination
    base,
    push,
    lift,
    lower,
    run,

    -- * Symbolic operators
    (⇸),
    (⊲),
    (⥁),
    (○),
    (↑),
    (↓),
  )
where

import Control.Category (Category (..), id)
import Data.Profunctor (Profunctor (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category

-- | Hyper a b is a hyperfunction from a to b.
--
-- A hyperfunction invokes its own dual to produce a value. The
-- self-referential duality unifies forward and backward directions
-- through a single continuation argument.
--
-- Symbol: @a ↬ b@.
newtype Hyper a b = Hyper {invoke :: Hyper b a -> b}

-- | Infix type synonym for 'Hyper'.
--
-- >>> :type (undefined :: Int ↬ Int)
-- (undefined :: Int ↬ Int) :: Int ↬ Int
type (↬) = Hyper

-- ---------------------------------------------------------------------------
-- Construction and elimination
-- ---------------------------------------------------------------------------

-- | The constant continuation: a hyperfunction that ignores its
-- continuation and always returns the same value.
--
-- >>> lower (base 42) 0
-- 42
base :: a -> Hyper b a
base a = Hyper (const a)

-- | Push a plain function onto a hyperfunction.
--
-- The function @f@ is applied to the result produced by invoking the
-- continuation on @h@. This threads the continuation through @f@,
-- allowing feedback-aware composition.
--
-- >>> lower ((+1) ⊲ lift (*2)) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = Hyper (\k -> f (invoke k h))

-- | Embed a plain function into a hyperfunction.
--
-- @lift f@ prepends @f@ to itself recursively, so the function can be
-- applied arbitrarily many times as the continuation chain unwinds.
-- Together with 'lower', this forms the adjunction between plain
-- functions and hyperfunctions: @lower . lift = id@.
--
-- >>> lower (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- | Extract a plain function from a hyperfunction.
--
-- Supplies the hyperfunction with a constant continuation
-- (@invoke h (Hyper (const a))@), asking: \"what output do you produce
-- when the feedback channel feeds back the input @a@?\"
--
-- >>> lower (lift reverse) "hello"
-- "olleh"
lower :: Hyper a b -> (a -> b)
lower h a = invoke h (Hyper (const a))

-- | Close the self-referential loop. Applies a hyperfunction to its
-- own dual: @run h = invoke h (Hyper run)@.
--
-- For a hyperfunction @h :: a ↬ a@, @run h@ resolves the fixed point
-- by feeding the hyperfunction's dual back into itself. The recursive
-- knot ties the forward and backward directions into a single value.
--
-- >>> run (Hyper $ \_ -> 42 :: Int)
-- 42
--
-- >>> run (Hyper $ \h -> invoke h (Hyper $ \_ -> 0) + 1) :: Int
-- 1
run :: Hyper a a -> a
run h = invoke h (Hyper run)

-- ---------------------------------------------------------------------------
-- Instances
-- ---------------------------------------------------------------------------

instance Category Hyper where
  id = lift id
  f . g = Hyper $ \h -> invoke f (g . h)

instance Profunctor Hyper where
  dimap f g h = Hyper $ g . invoke h . dimap g f
  lmap f h = Hyper $ invoke h . rmap f
  rmap f h = Hyper $ f . invoke h . lmap f

instance Functor (Hyper a) where
  fmap = rmap

instance Applicative (Hyper a) where
  pure = base
  hf <*> ha = lift $ \a -> lower hf a (lower ha a)

instance Monad (Hyper a) where
  m >>= k = lift $ \a -> lower (k (lower m a)) a

-- ---------------------------------------------------------------------------
-- Symbolic operators
-- ---------------------------------------------------------------------------

-- | Invoke a hyperfunction with a continuation.
--
-- >>> ((+1) ↑) ⇸ (0 ○)
-- 1
infixr 0 ⇸

(⇸) :: Hyper a b -> Hyper b a -> b
(⇸) = invoke

-- | Push a function onto a hyperfunction. Operator form of 'push'.
--
-- >>> ((*2) ⊲ ((+1) ↑)) ↓ 5
-- 10
infixr 8 ⊲

(⊲) :: (a -> b) -> Hyper a b -> Hyper a b
(⊲) = push

-- | Close the loop. Operator form of 'run'.
(⥁) :: Hyper a a -> a
(⥁) = run

-- | Postfix constant. Operator form of 'base'.
--
-- >>> (42 ○) ↓ 0
-- 42
infixl 9 ○

(○) :: a -> Hyper b a
(○) = base

-- | Postfix lift. Operator form of 'lift'.
--
-- >>> ((+1) ↑) ↓ 5
-- 6
infixr 9 ↑

(↑) :: (a -> b) -> Hyper a b
(↑) = lift

-- | Postfix lower. Operator form of 'lower'.
--
-- Because 'lower' returns a plain function, the postfix form
-- chains naturally via function application:
--
-- >>> ((+1) ↑) ↓ 5
-- 6
--
-- >>> ((*2) ↑) ↓ 5 + 10
-- 20
infixl 9 ↓

(↓) :: Hyper a b -> (a -> b)
(↓) = lower
