{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free traced monoidal category.
--
-- @Circuit t arr a b@ is the initial encoding of a traced monoidal category
-- over a base morphism @arr@ with a supplied tensor @t@ for the category. The three constructors encode:
--
--   - `Lift`: embedding of a base arrow (strict monoidal functor)
--   - `Compose`: sequential composition (category structure)
--   - `Knot`: introduces a feedback channel (trace structure)
--
-- For example, a `Circuit (,) (->)` is the initial traced monoidal cartesian category over Haskell functions.
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor that pairs a feedback value with a payload
--   inside a 'Circuit'. The two tensors provided are @(,)@ (simultaneous / lazy
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
-- The 'reify' function interprets any 'Circuit' to a plain arrow via
-- the 'Trace' class instance on @t@. For encoding into 'Circuit.Hyper', see
-- 'Circuit.Hyper.encode' and 'Circuit.Hyper.encodeEither'.
module Circuit.Trace
  ( -- * Circuit
    Circuit (..),

    -- * Type aliases
    Wire,
    Step,

    -- * Interpreters
    reify,
    freeze,

    -- * Channel ends
    Co (..),
    Contra (..),
    close,
  )
where

import Circuit.Free qualified as F
import Circuit.Traced qualified as Traced
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
data Circuit t arr a b where
  -- | Lift embeds a base arrow (strict monoidal functor).
  --
  -- >>> reify (Lift (+1) :: Circuit (,) (->) Int Int) 5
  -- 6
  Lift :: arr a b -> Circuit t arr a b
  -- | Compose performs sequential composition (category structure).
  --
  -- >>> reify (Lift (+1) >>> Lift (*2) :: Circuit (,) (->) Int Int) 5
  -- 12
  Compose :: Circuit t arr b c -> Circuit t arr a b -> Circuit t arr a c
  -- | Knot ties a feedback loop. The tensor @t@ carries the channel type.
  -- The body is a 'Circuit' so the loop wiring is inspectable before
  -- 'reify' closes it.
  --
  -- >>> reify (Knot (Lift (\(acc, x) -> (x, acc))) :: Circuit (,) (->) Int Int) 42
  -- 42
  Knot :: Circuit t arr (t a b) (t a c) -> Circuit t arr b c

-- | A traced circuit over plain functions with the cartesian tensor.
--
-- @Wire a b = Circuit (,) (->) a b@
--
-- The @(,)@ tensor ties a lazy knot: output and feedback are produced
-- simultaneously.
type Wire = Circuit (,) (->)

-- | A traced circuit over plain functions with the cocartesian tensor.
--
-- @Step a b = Circuit Either (->) a b@
--
-- The @Either@ tensor iterates: @Left@ feeds back (continue),
-- @Right@ terminates (exit).
type Step = Circuit Either (->)

instance (Category arr) => Category (Circuit t arr) where
  id = Lift id
  (.) = Compose

instance Functor (Circuit t (->) a) where
  fmap f = Compose (Lift f)

-- | Profunctor instance for Circuit.
--
-- Maps over both ends of the arrow. For @Compose@, the map is applied
-- to the input of the left sub-circuit and the output of the right
-- sub-circuit, leaving the intermediate type aligned.
--
-- >>> reify (dimap (+ 1) (+ 1) (Lift (* 2) :: Circuit (,) (->) Int Int)) 5
-- 13
instance (Profunctor arr, Bifunctor t) => Profunctor (Circuit t arr) where
  dimap f g (Lift h) = Lift (dimap f g h)
  dimap f g (Compose h k) = Compose (dimap id g h) (dimap f id k)
  dimap f g (Knot k) = Knot (dimap (second f) (second g) k)
  lmap f (Lift h) = Lift (lmap f h)
  lmap f (Compose h k) = Compose (lmap id h) (lmap f k)
  lmap f (Knot k) = Knot (lmap (second f) k)
  rmap g (Lift h) = Lift (rmap g h)
  rmap g (Compose h k) = Compose (rmap g h) (rmap id k)
  rmap g (Knot k) = Knot (rmap (second g) k)

-- | Dissolve 'Circuit' into 'Lift' by calling 'trace' on the base arrow.
--
-- This is the first-stage interpreter: 'Circuit' → 'Free'.  The Mendler
-- case (@'Compose' ('Knot' f) g@) slides @g@ inside the trace, enforcing
-- the sliding axiom of traced monoidal categories.
--
-- 'reify' factors through 'freeze': @'reify' = 'F.runFree' . 'freeze'@.
--
-- >>> F.runFree (freeze (Lift (+1) :: Circuit (,) (->) Int Int)) 5
-- 6
--
-- >>> F.runFree (freeze (Knot (Lift (\(acc, x) -> (x, acc))) :: Circuit (,) (->) Int Int)) 42
-- 42
freeze :: (Category arr, Traced.Trace arr t) => Circuit t arr a b -> F.Free arr a b
freeze = \case
  Lift f -> F.Lift f
  Compose (Knot f) g ->
    F.Lift (Traced.trace (F.runFree (freeze f) . Traced.untrace (F.runFree (freeze g))))
  Compose f g -> F.Compose (freeze f) (freeze g)
  Knot k -> F.Lift (Traced.trace (F.runFree (freeze k)))

-- | Interpret a Circuit to a plain arrow.
--
-- This is the canonical map out of the free (initial) traced monoidal
-- category.  The interesting case is when a @Knot@ appears on the left
-- of a @Compose@: this is exactly where the sliding axiom of traced
-- monoidal categories is enforced (the Mendler case).
--
-- @'reify' = 'F.runFree' . 'freeze'@ — first dissolve 'Circuit' into 'Free',
-- then fold to a plain arrow.
--
-- >>> reify (Lift (+1) :: Circuit (,) (->) Int Int) 5
-- 6
reify :: (Category arr, Traced.Trace arr t) => Circuit t arr x y -> arr x y
reify = F.runFree . freeze

-- | Lift the 'Trace' class through 'Circuit t'.
--
-- A loop body in @Circuit t arr@ is reified before calling the base 'trace'.
instance (Category arr, Traced.Trace arr t) => Traced.Trace (Circuit t arr) t where
  trace body = Lift (Traced.trace (reify body))
  untrace f  = Lift (Traced.untrace (reify f))

-- ---------------------------------------------------------------------------
-- Channel ends — the companion and conjoint of the identity functor.

-- | 'Co' is the companion of the identity functor in the proarrow equipment
-- over 'Circuit'.  Covariant in @a@ (sits in the output position).
--
-- Given a 'Contra' (the other end), produce a circuit from any @x@ to @a@.
-- The @x@ is universally quantified — 'Co' must either return a constant
-- or call the other end.
newtype Co arr t a = Co
  { -- | Run the companion, supplying the other end.
    runContra :: forall x. Contra arr t x -> Circuit t arr x a
  }

-- | 'Contra' is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
--
-- Given a 'Co' (the other end), produce a circuit from @a@ to any @x@.
-- The @x@ is universally quantified — 'Contra' must call the other end
-- to determine what to return.
newtype Contra arr t a = Contra
  { -- | Run the conjoint, supplying the other end.
    runCo :: forall x. Co arr t x -> Circuit t arr a x
  }

-- | @ε@ — the counit of the companion/conjoint adjunction.
--
-- Plug two channel ends together, producing a circuit from @a@ to @a@.
-- This is the yanking identity: eliminating the ends recovers the
-- underlying profunctor on the diagonal.
close :: Contra arr t a -> Co arr t a -> Circuit t arr a a
{- HLINT ignore close "Eta reduce" -}
close contra = runCo contra
