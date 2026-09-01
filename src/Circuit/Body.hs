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
-- 'Circuit.Moore.Moore' specializes this shape to a Moore machine over a
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
--   state, residual, a stream, or any other value the base arrow @arr@ carries
--   along with the input and output.
--
-- * __@arr@ — arrow / morphism__: the base category.  Usually @(->)@ or a
--   Kleisli arrow @K m@.  The opposite arrow @Circuit.Category.Op arr@ is also
--   available, so @Body t ch (Op (->)) a b@ is a first-class codata body:
--   the channel carries the residual and the internal morphism runs backward.
--   This makes the @Set^op@ rung of the polynomial equipment explicit.
--
-- This arrangement is the common shape underlying loops, processes, systems,
-- and channel ends: a morphism whose input and output both carry an ambient
-- channel.  'Body' makes that shape explicit before any tracing, scheduling,
-- or pole-splitting is added.
module Circuit.Body
  ( -- * Knot-body category
    Body (..),
    runFlowchart,

    -- * Carrier-tensoring composition
    mergeChannel,
  )
where

import Circuit.Category (Category (..), K (..), Pointed (..), (.>))
import Circuit.Poles (HasDual (..), In (..), Out (..), Poles (..))
import Circuit.Tensor (Tensor (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Category (Op (..))

-- | A morphism across a tensored channel.
--
-- The opposite arrow reverses the internal morphism while keeping the channel
-- threading intact:
--
-- >>> let b = Body (Op (\(s, a) -> (s, a + 1))) :: Body (,) Int (Op (->)) Int Int
-- >>> runOp (morphism b) (5, 3)
-- (5,4)
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

-- | Run an 'Either' body as a partial function @a -> b@ with a fuel bound.
-- Execution starts with the external input @a@; if the body emits a label
-- @ch@ the runner feeds @Left ch@ back in, decrementing the fuel.
--
-- Returns the result (if any) and the number of steps taken.  A flowchart has
-- no stored state — the input is the entire initial configuration — so there
-- is no seed parameter.  This is the coproduct analogue of the cartesian
-- runner: where @(,)@ bodies run as stream functions, 'Either' bodies run as
-- halting computations.
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
-- algebra (for example in "Circuit.Cell").
--
-- The composite is
--
-- @
--   assoc .> slide .> strength f .> slide .> strength g .> assoc'
-- @
mergeChannel ::
  (Strength t arr) =>
  Body t ch' arr b c ->
  Body t ch arr a b ->
  Body t (t ch ch') arr a c
mergeChannel g f =
  Body
    ( assoc
        .> slide
        .> strength (morphism f)
        .> slide
        .> strength (morphism g)
        .> assoc'
    )
