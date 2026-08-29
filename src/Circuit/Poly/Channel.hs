{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Poly-indexed channel type.
--
-- A channel is indexed by a polynomial interface @p :: Poly@. The polynomial
-- describes both the observable position (output) and the direction space
-- (input). The channel carries no residual field; any residual policy is
-- supplied by a 'Circuit.Process.Process' at composition time.
--
-- This module starts with function-category @(->)@ evaluation. The type
-- @Channel arr p@ keeps @arr@ as a parameter so that future slices can add
-- @Kleisli@ evaluation helpers without changing the type.
module Circuit.Poly.Channel
  ( -- * Poly-indexed channel
    Channel (..),

    -- * Observation and interaction
    emitChannel,
    commitChannel,

    -- * Constructing channels
    idChannel,
    constChannel,
    mapChannel,
  )
where

import Circuit.Moore
  ( Moore,
    MooreEval (..),
    evalToMoore,
    fromEvalMoore,
    lensAsMoore,
    moore,
    toEvalMoore,
  )
import Circuit.Poly
  ( Dir,
    Eval (..),
    Mono,
    Morphism (..),
    Poly (..),
    applyLens,
    lens,
    runMorphism,
  )
import Control.Category (id, (.))
import Data.Functor (void)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Poly (Mono, Morphism, lens, applyLens)
-- >>> import Circuit.Moore (Moore)

-- | A channel whose interface is the polynomial @p@.
--
-- Internally it is a Moore machine with hidden state @s@. The state is
-- existentially quantified so that different channel constructors can use
-- different state types.
data Channel arr (p :: Poly) where
  Ch ::
    (MooreEval p) =>
    -- | Current state of the Moore machine.
    s ->
    -- | The machine governing the channel interface.
    Moore (,) arr s p ->
    Channel arr p

-- | Observe the current output of a @(->)@ channel.
--
-- The observation is an @Eval p ()@: a position together with a trivial
-- direction consumer. The position is the channel's current output; the
-- direction consumer is how a future input will advance the channel.
emitChannel :: Channel (->) p -> Eval p ()
emitChannel (Ch s sys) = void (toEvalMoore sys s)

-- | Commit an input direction to a @(->)@ channel, advancing its state.
commitChannel :: Channel (->) p -> Dir p -> Channel (->) p
commitChannel (Ch s sys) d =
  let (_pos, next) = evalToMoore (toEvalMoore sys s)
   in Ch (next d) sys

-- | Identity channel on a monomial interface @Mono a a@.
--
-- Output is the current state; next state is the input direction.  An
-- initial state must be supplied because a Moore machine has no input
-- before the first commit.
idChannel :: a -> Channel (->) (Mono a a)
idChannel s0 = Ch s0 (lensAsMoore (lens id (\_ d -> d)))

-- | Constant-output channel on a monomial interface @Mono a b@.
--
-- Output is always @b@; the state is the constant value and is preserved
-- across commits (the input direction is ignored).
constChannel :: b -> Channel (->) (Mono a b)
constChannel b = Ch b (lensAsMoore (lens (const b) const))

-- | Map a polynomial morphism over a @(->)@ channel.
--
-- The forward map transforms positions; the backward map transforms
-- directions. This is the functorial action of 'Circuit.Poly.Morphism' on
-- channels.
mapChannel ::
  (MooreEval p, MooreEval q) =>
  Morphism p q ->
  Channel (->) p ->
  Channel (->) q
mapChannel m (Ch s sys) =
  Ch s (moore step)
  where
    step (s', d') =
      let tgtEval = runMorphism m (toEvalMoore sys s')
          (pos, next) = evalToMoore tgtEval
       in (next d', pos)
