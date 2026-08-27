{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A span-shaped Mealy machine: a morphism across a tensored channel.
--
-- @
--   Body t ch arr a b  =  arr (t ch a) (t ch b)
-- @
--
-- Both the channel and the payload enter together, and both exit together.
-- 'Circuit.System.System' specializes this shape to a Moore machine over a
-- polynomial interface; 'Circuit.Process.Process' is the pointed monomial
-- special case of that.
--
-- == Anatomy
--
-- * __@t@ — tensor__: the bifunctor that pairs a channel with a payload.
--   Common choices are @(,)@ for simultaneous sharing, 'Either' for sequential
--   iteration, and 'Data.These.These' for scheduled interleaving.
--
-- * __@ch@ — channel__: the value threaded alongside the payload.  It may be
--   state, residual, a stream, or a feedback wire.
--
-- * __@arr@ — arrow / morphism__: the base category.  Usually @(->)@ or a
--   Kleisli arrow @K m@.
--
-- This arrangement is the common shape underlying loops, processes, systems,
-- and channel ends: a morphism whose input and output both carry an ambient
-- channel.  'Body' makes that shape explicit before any tracing, scheduling,
-- or pole-splitting is added.
module Circuit.Body
  ( -- * Knot-body category
    Body (..),
    SomeBody (..),
    runSomeBody,
    runFlowchart,

    -- * Carrier-tensoring composition
    cascadeBody,
    cascadeSome,
  )
where

import Circuit.Category (Category (..), K (..), Pointed (..), (.>))
import Circuit.Channel (Channel (..), Strength (..))
import Circuit.Poles (HasDual (..), In (..), Out (..), Poles (..))
import Circuit.Tensor (Tensor (..), TensorSeed (..), Unit)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- | A morphism across a tensored channel.
--
-- @Body t ch arr a b@ is a morphism @arr (t ch a) (t ch b)@.  The channel
-- @ch@ is threaded alongside the payload by the tensor @t@; it may be state,
-- residual, a stream, or any other value the base arrow @arr@ carries along
-- with the input and output.  Composition threads the same channel through
-- both morphisms.
newtype Body t ch arr a b = Body {morphism :: arr (t ch a) (t ch b)}

instance (Category arr) => Category (Body t ch arr) where
  id :: forall a. Body t ch arr a a
  id = Body id
  {-# INLINE id #-}

  (.) :: forall a b c. Body t ch arr b c -> Body t ch arr a b -> Body t ch arr a c
  Body g . Body f = Body (g . f)
  {-# INLINE (.) #-}

-- | A 'Body' with its channel type hidden.
data SomeBody t arr a b where
  SomeBody :: ch -> Body t ch arr a b -> SomeBody t arr a b

-- | Run an existentially-packed cartesian body over a list of inputs.
--
-- This is the @(,)@ / list specialisation of 'SomeBody'.
runSomeBody :: SomeBody (,) (->) a b -> [a] -> [b]
runSomeBody (SomeBody ch0 (Body f)) xs =
  let (_, bs) = foldl (\(ch, acc) a -> let (ch', b) = f (ch, a) in (ch', b : acc)) (ch0, []) xs
   in reverse bs

-- | Run an 'Either' body as a partial function @a -> b@ with a fuel bound.
-- Execution starts with the external input @a@; if the body emits a label
-- @ch@ the runner feeds @Left ch@ back in, decrementing the fuel.
--
-- Returns the result (if any) and the number of steps taken.  A flowchart has
-- no stored state — the input is the entire initial configuration — so there
-- is no seed parameter.  This is the coproduct analogue of 'runSomeBody':
-- where @(,)@ bodies run as stream functions, 'Either' bodies run as halting
-- computations.
runFlowchart :: Body Either ch (->) a b -> Int -> a -> (Maybe b, Int)
runFlowchart (Body f) fuel0 a0 = go fuel0 0 (Right a0)
  where
    go 0 steps _ = (Nothing, steps)
    go n steps (Left ch) =
      case f (Left ch) of
        Left ch' -> go (n - 1) (steps + 1) (Left ch')
        Right b -> (Just b, steps + 1)
    go n steps (Right a) =
      case f (Right a) of
        Left ch' -> go (n - 1) (steps + 1) (Left ch')
        Right b -> (Just b, steps + 1)

-- * HasDual instances for Body

-- | Unit poles for @Body (,) s (->)@ at the unit object @()@.
--
-- The companion discards its input and returns @()@; the conjoint delegates
-- to the companion. Yanking recovers the identity on @()@.
instance HasDual () (Body (,) s (->)) where
  open =
    let outU = Out $ \_ -> Body $ \(s, _) -> (s, ())
        inU = In $ \o -> emit o inU
     in Poles inU outU

-- | Unit poles for @Body (,) s (K m)@.
--
-- Same shape as the @(->)@ instance, but the companion returns @()@ in the
-- monad and threads the ambient state through unchanged.
instance (Monad m) => HasDual () (Body (,) s (K m)) where
  open =
    let outU = Out $ \_ -> Body $ K $ \(s, _) -> pure (s, ())
        inU = In $ \o -> emit o inU
     in Poles inU outU

-- | Unit poles for @Body Either s (->)@ at the unit object @Void@.
--
-- The coproduct case needs a distinguished element of the carrier @s@: on a
-- @Right x@ input the companion must return @Left s@ for some @s@, and there
-- is no ambient state to use.  'Pointed' captures exactly that, which is
-- weaker than 'Monoid'.  This is the structural pointedness requirement that
-- makes @Either@ differ from @(,)@.
instance (Pointed s) => HasDual Void (Body Either s (->)) where
  open =
    let outU = Out $ \_ -> Body $ \case
          Left s -> Left s
          Right _ -> Left point
        inU = In $ \_ -> Body $ \case
          Left s -> Left s
          Right v -> absurd v
     in Poles inU outU

-- | Unit poles for @Body Either s (K m)@ at @Void@.
instance (Monad m, Pointed s) => HasDual Void (Body Either s (K m)) where
  open =
    let outU = Out $ \_ -> Body $ K $ \case
          Left s -> pure (Left s)
          Right _ -> pure (Left point)
        inU = In $ \_ -> Body $ K $ \case
          Left s -> pure (Left s)
          Right v -> absurd v
     in Poles inU outU

-- * Carrier-tensoring composition

-- | Compose two bodies at carriers @ch@ and @ch'@ into a body at carrier
-- @t ch ch'@.  This is the body-level building block of horizontal 2-cell
-- algebra and of the 'Category' instance for 'SomeBody'.
--
-- The composite is
--
-- @
--   assoc .> slide .> strength f .> slide .> strength g .> assoc'
-- @
cascadeBody ::
  (Strength t arr) =>
  Body t ch' arr b c ->
  Body t ch arr a b ->
  Body t (t ch ch') arr a c
cascadeBody g f =
  Body
    ( assoc
        .> slide
        .> strength (morphism f)
        .> slide
        .> strength (morphism g)
        .> assoc'
    )

-- | Pointed carrier-tensoring composition for @t = (,)@ and @arr = (->)@.
--
-- Seeds pair under the tensor, and the composite can be run with
-- 'runSomeBody'.  This is the pointed counterpart to the unpointed
-- 'cascadeBody'.
cascadeSome ::
  SomeBody (,) (->) b c ->
  SomeBody (,) (->) a b ->
  SomeBody (,) (->) a c
cascadeSome (SomeBody s2 g) (SomeBody s1 f) =
  SomeBody (s1, s2) (cascadeBody g f)

-- | 'Category' instance for 'SomeBody'.
--
-- The carrier of the composite is the tensor of the two carriers, and the
-- stored seed is combined with 'seedPair'.  Identity needs a seed at the
-- tensor unit, hence the 'Pointed (Unit t)' requirement.  Tensors whose unit
-- is uninhabited (e.g. 'Either' with @Unit Either = Void@) therefore do not
-- admit an identity; tensors without a canonical value-level pairing (also
-- 'Either', 'Data.These.These') do not admit composition.
instance
  (Strength t arr, Pointed (Unit t), TensorSeed t) =>
  Category (SomeBody t arr)
  where
  id :: forall a. SomeBody t arr a a
  id = SomeBody (point :: Unit t) (Body id)
  {-# INLINE id #-}

  (.) :: forall a b c. SomeBody t arr b c -> SomeBody t arr a b -> SomeBody t arr a c
  SomeBody s2 g . SomeBody s1 f = SomeBody (seedPair s1 s2) (cascadeBody g f)
  {-# INLINE (.) #-}
