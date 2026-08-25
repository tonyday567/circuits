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
  )
where

import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Poles (HasDual (..), In (..), Out (..), Poles (..))
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

-- | Run an existentially-packed 'Either' body as a partial function @a -> b@
-- with a fuel bound.  Execution starts with the external input @a@; if the
-- body emits a label @ch@ the runner feeds @Left ch@ back in, decrementing
-- the fuel.  Returns 'Nothing' if the fuel is exhausted before a @Right b@
-- output is produced.
--
-- This is the coproduct analogue of 'runSomeBody': where @(,)@ bodies run
-- as stream functions, 'Either' bodies run as halting computations.
runFlowchart :: SomeBody Either (->) a b -> Int -> a -> Maybe b
runFlowchart (SomeBody _ch0 (Body f)) fuel0 a0 = go fuel0 (Right a0)
  where
    go 0 _ = Nothing
    go n (Left ch) =
      case f (Left ch) of
        Left ch' -> go (n - 1) (Left ch')
        Right b -> Just b
    go n (Right a) =
      case f (Right a) of
        Left ch' -> go (n - 1) (Left ch')
        Right b -> Just b

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
-- is no ambient state to use.  Hence the @Monoid s@ constraint.  This is the
-- structural pointedness requirement that makes @Either@ differ from @(,)@.
instance (Monoid s) => HasDual Void (Body Either s (->)) where
  open =
    let outU = Out $ \_ -> Body $ \case
          Left s -> Left s
          Right _ -> Left mempty
        inU = In $ \_ -> Body $ \case
          Left s -> Left s
          Right v -> absurd v
     in Poles inU outU

-- | Unit poles for @Body Either s (K m)@ at @Void@.
instance (Monad m, Monoid s) => HasDual Void (Body Either s (K m)) where
  open =
    let outU = Out $ \_ -> Body $ K $ \case
          Left s -> pure (Left s)
          Right _ -> pure (Left mempty)
        inU = In $ \_ -> Body $ K $ \case
          Left s -> pure (Left s)
          Right v -> absurd v
     in Poles inU outU
