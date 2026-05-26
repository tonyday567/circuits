{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free traced monoidal category.
--
-- @Circuit arr t a b@ is the initial encoding of a traced monoidal category
-- over a base morphism @arr@ with a supplied tensor @t@ for the category. The three constructors encode:
--
--   - `Lift`: embedding of a base arrow (strict monoidal functor)
--   - `Compose`: sequential composition (category structure)
--   - `Knot`: introduces a feedback channel (trace structure)
--
-- For example, a `Circuit (->) (,)` is the initial traced monoidal cartesian category over Haskell functions.
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor that pairs a feedback value with a payload
--   inside a 'Knot'. The two tensors provided are @(,)@ (simultaneous / lazy
--   sharing) and 'Either' (sequential / iteration).
--
-- * __Feedback value__: The component that travels around the loop (the first
--   parameter of the tensor inside a 'Knot').
--
-- * __Payload__: The component that is transformed and emitted by the circuit
--   (the second parameter of the tensor).
--
-- * __Feedback channel__: The path the feedback value takes when it is routed
--   back into the next step of the computation. In a 'Knot' the channel type
--   is carried by the tensor @t@.
--
-- These concepts are independent of any particular base arrow @arr@. They
-- describe the structure of feedback itself.
--
-- The `reify` function interprets any `Circuit` to a plain arrow via
-- the `Trace` instance on @t@. For encoding into 'Circuit.Hyper', see
-- 'Circuit.Hyper.encode' and 'Circuit.Hyper.encodeEither'.
module Circuit.Circuit
  ( -- * Circuit
    Circuit (..),

    -- * Type aliases
    Wire,
    Step,

    -- * Operators
    reify,
  )
where

import Circuit.Traced (Trace (..))
import Prelude hiding (id, (.))

#ifdef __GLASGOW_HASKELL__
import Control.Category
import Data.Bifunctor
import Data.Profunctor
#else
import Circuit.Classes
#endif

-- $setup
-- >>> import Control.Category ((>>>))
-- >>> import Data.Profunctor (dimap)
-- >>> import Prelude hiding (id, (.))

-- | The free traced monoidal category over base morphism @arr@ and tensor @t@.
--
-- Three constructors:
--
--   * 'Lift' — embed a base arrow.
--   * 'Compose' — sequential composition.
--   * 'Knot' — feedback loop via the tensor.
data Circuit arr t a b where
  -- | Lift embeds a base arrow (strict monoidal functor).
  --
  -- >>> reify (Lift (+1) :: Circuit (->) (,) Int Int) 5
  -- 6
  Lift :: arr a b -> Circuit arr t a b
  -- | Compose performs sequential composition (category structure).
  --
  -- >>> reify (Lift (+1) >>> Lift (*2) :: Circuit (->) (,) Int Int) 5
  -- 12
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  -- | Knot ties a feedback loop. The tensor @t@ carries the channel type.
  --
  -- >>> reify (Knot (\(acc, x) -> (x, acc)) :: Circuit (->) (,) Int Int) 42
  -- 42
  Knot :: arr (t a b) (t a c) -> Circuit arr t b c

-- | A traced circuit over plain functions with the cartesian tensor.
--
-- @Wire a b = Circuit (->) (,) a b@
--
-- The @(,)@ tensor ties a lazy knot: output and feedback are produced
-- simultaneously.
type Wire = Circuit (->) (,)

-- | A traced circuit over plain functions with the cocartesian tensor.
--
-- @Step a b = Circuit (->) Either a b@
--
-- The @Either@ tensor iterates: @Left@ feeds back (continue),
-- @Right@ terminates (exit).
type Step = Circuit (->) Either

instance (Category arr) => Category (Circuit arr t) where
  id = Lift id
  (.) = Compose

instance Functor (Circuit (->) t a) where
  fmap f = Compose (Lift f)

-- | Profunctor instance for Circuit.
--
-- Maps over both ends of the arrow. For @Compose@, the map is applied
-- to the input of the left sub-circuit and the output of the right
-- sub-circuit, leaving the intermediate type aligned.
--
-- >>> reify (dimap (+ 1) (+ 1) (Lift (* 2) :: Circuit (->) (,) Int Int)) 5
-- 13
instance (Profunctor arr, Bifunctor t) => Profunctor (Circuit arr t) where
  dimap f g (Lift h) = Lift (dimap f g h)
  dimap f g (Compose h k) = Compose (dimap id g h) (dimap f id k)
  dimap f g (Knot k) = Knot (dimap (second f) (second g) k)
  lmap f (Lift h) = Lift (lmap f h)
  lmap f (Compose h k) = Compose (lmap id h) (lmap f k)
  lmap f (Knot k) = Knot (lmap (second f) k)
  rmap g (Lift h) = Lift (rmap g h)
  rmap g (Compose h k) = Compose (rmap g h) (rmap id k)
  rmap g (Knot k) = Knot (rmap (second g) k)

-- | Interpret a Circuit to a plain arrow.
--
-- This is the canonical map out of the free (initial) traced monoidal
-- category.  The interesting case is when a @Knot@ appears on the left
-- of a @Compose@: this is exactly where the sliding axiom of traced
-- monoidal categories is enforced (the Mendler case).
--
-- >>> reify (Lift (+1) :: Circuit (->) (,) Int Int) 5
-- 6
reify :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
reify (Lift f) = f
reify (Compose (Knot f) g) = trace (f . untrace (reify g))
reify (Compose f g) = reify f . reify g
reify (Knot k) = trace k
