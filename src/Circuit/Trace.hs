{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free traced monoidal category.
--
-- @Trace t arr a b@ is the initial encoding of a traced monoidal category
-- over a base morphism @arr@ with a supplied tensor @t@ for the category. The three constructors encode:
--
--   - `Lift`: embedding of a base arrow (strict monoidal functor)
--   - `Compose`: sequential composition (category structure)
--   - `Trace`: introduces a feedback channel (trace structure)
--
-- For example, a `Trace (,) (->)` is the initial traced monoidal cartesian category over Haskell functions.
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor that pairs a feedback value with a payload
--   inside a 'Trace'. The two tensors provided are @(,)@ (simultaneous / lazy
--   sharing) and 'Either' (sequential / iteration).
--
-- * __Feedback value__: The component that travels around the loop (the first
--   parameter of the tensor inside a 'Trace').
--
-- * __Payload__: The component that is transformed and emitted by the circuit
--   (the second parameter of the tensor).
--
-- * __Feedback channel__: The path the feedback value takes when it is routed
--   back into the next step of the computation. In a 'Trace' the channel type
--   is carried by the tensor @t@.
--
-- These concepts are independent of any particular base arrow @arr@. They
-- describe the structure of feedback itself.
--
-- The 'realise' function interprets any 'Trace' to a plain arrow via
-- the 'Trace' class instance on @t@. For encoding into 'Circuit.Hyper', see
-- 'Circuit.Hyper.encode' and 'Circuit.Hyper.encodeEither'.
module Circuit.Trace
  ( -- * Trace
    Trace (..),

    -- * Type aliases
    Wire,
    Step,

    -- * Interpreters
    realise,
    freeze,

    -- * Channel ends
    Co (..),
    Contra (..),
    close,
  )
where

import Circuit.Free qualified as F
import Circuit.Traced
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
--   * 'Trace' — feedback loop via the tensor.
data Trace t arr a b where
  -- | Lift embeds a base arrow (strict monoidal functor).
  --
  -- >>> realise (Lift (+1) :: Trace (,) (->) Int Int) 5
  -- 6
  Lift :: arr a b -> Trace t arr a b
  -- | Compose performs sequential composition (category structure).
  --
  -- >>> realise (Lift (+1) >>> Lift (*2) :: Trace (,) (->) Int Int) 5
  -- 12
  Compose :: Trace t arr b c -> Trace t arr a b -> Trace t arr a c
  -- | Trace ties a feedback loop. The tensor @t@ carries the channel type.
  -- The body is a 'Trace' so the loop wiring is inspectable before
  -- 'realise' closes it.
  --
  -- >>> realise (Trace (Lift (\(acc, x) -> (x, acc))) :: Trace (,) (->) Int Int) 42
  -- 42
  Trace :: Trace t arr (t a b) (t a c) -> Trace t arr b c

-- | A traced circuit over plain functions with the cartesian tensor.
--
-- @Wire a b = Trace (,) (->) a b@
--
-- The @(,)@ tensor ties a lazy knot: output and feedback are produced
-- simultaneously.
type Wire = Trace (,) (->)

-- | A traced circuit over plain functions with the cocartesian tensor.
--
-- @Step a b = Trace Either (->) a b@
--
-- The @Either@ tensor iterates: @Left@ feeds back (continue),
-- @Right@ terminates (exit).
type Step = Trace Either (->)

instance (Category arr) => Category (Trace t arr) where
  id = Lift id
  (.) = Compose

instance Functor (Trace t (->) a) where
  fmap f = Compose (Lift f)

-- | Profunctor instance for Circuit.
--
-- Maps over both ends of the arrow. For @Compose@, the map is applied
-- to the input of the left sub-circuit and the output of the right
-- sub-circuit, leaving the intermediate type aligned.
--
-- >>> realise (dimap (+ 1) (+ 1) (Lift (* 2) :: Trace (,) (->) Int Int)) 5
-- 13
instance (Profunctor arr, Bifunctor t) => Profunctor (Trace t arr) where
  dimap f g (Lift h) = Lift (dimap f g h)
  dimap f g (Compose h k) = Compose (dimap id g h) (dimap f id k)
  dimap f g (Trace k) = Trace (dimap (second f) (second g) k)
  lmap f (Lift h) = Lift (lmap f h)
  lmap f (Compose h k) = Compose (lmap id h) (lmap f k)
  lmap f (Trace k) = Trace (lmap (second f) k)
  rmap g (Lift h) = Lift (rmap g h)
  rmap g (Compose h k) = Compose (rmap g h) (rmap id k)
  rmap g (Trace k) = Trace (rmap (second g) k)

-- | Dissolve 'Trace' into 'Lift' by calling 'trace' on the base arrow.
--
-- This is the first-stage interpreter: 'Trace' → 'Free'.  The Mendler
-- case (@'Compose' ('Trace' f) g@) slides @g@ inside the trace, enforcing
-- the sliding axiom of traced monoidal categories.
--
-- 'realise' factors through 'freeze': @'realise' = 'F.runFree' . 'freeze'@.
--
-- >>> F.runFree (freeze (Lift (+1) :: Trace (,) (->) Int Int)) 5
-- 6
--
-- >>> F.runFree (freeze (Trace (Lift (\(acc, x) -> (x, acc))) :: Trace (,) (->) Int Int)) 42
-- 42
freeze :: (Category arr, Traced arr t) => Trace t arr a b -> F.Free arr a b
freeze = \case
  Lift f -> F.Lift f
  Compose (Trace f) g ->
    F.Lift (trace (F.runFree (freeze f) . untrace (F.runFree (freeze g))))
  Compose f g -> F.Compose (freeze f) (freeze g)
  Trace k -> F.Lift (trace (F.runFree (freeze k)))

-- | Interpret a Trace to a plain arrow.
--
-- This is the canonical map out of the free (initial) traced monoidal
-- category.  The interesting case is when a @Trace@ appears on the left
-- of a @Compose@: this is exactly where the sliding axiom of traced
-- monoidal categories is enforced (the Mendler case).
--
-- @'realise' = 'F.runFree' . 'freeze'@ — first dissolve 'Trace' into 'Free',
-- then fold to a plain arrow.
--
-- >>> realise (Lift (+1) :: Trace (,) (->) Int Int) 5
-- 6
realise :: (Category arr, Traced arr t) => Trace t arr x y -> arr x y
realise = F.runFree . freeze

-- | Lift the 'Trace' class through 'Trace t'.
--
-- A loop body in @Trace t arr@ is reified before calling the base 'trace'.
instance (Category arr, Traced arr t) => Traced (Trace t arr) t where
  trace body = Lift (trace (realise body))
  untrace f  = Lift (untrace (realise f))

-- ---------------------------------------------------------------------------
-- Channel ends — the companion and conjoint of the identity functor.

-- | 'Co' is the companion of the identity functor in the proarrow equipment
-- over 'Trace'.  Covariant in @a@ (sits in the output position).
--
-- Given a 'Contra' (the other end), produce a circuit from any @x@ to @a@.
-- The @x@ is universally quantified — 'Co' must either return a constant
-- or call the other end.
newtype Co arr t a = Co
  { -- | Run the companion, supplying the other end.
    runContra :: forall x. Contra arr t x -> Trace t arr x a
  }

-- | 'Contra' is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
--
-- Given a 'Co' (the other end), produce a circuit from @a@ to any @x@.
-- The @x@ is universally quantified — 'Contra' must call the other end
-- to determine what to return.
newtype Contra arr t a = Contra
  { -- | Run the conjoint, supplying the other end.
    runCo :: forall x. Co arr t x -> Trace t arr a x
  }

-- | @ε@ — the counit of the companion/conjoint adjunction.
--
-- Plug two channel ends together, producing a circuit from @a@ to @a@.
-- This is the yanking identity: eliminating the ends recovers the
-- underlying profunctor on the diagonal.
close :: Contra arr t a -> Co arr t a -> Trace t arr a a
{- HLINT ignore close "Eta reduce" -}
close contra = runCo contra
