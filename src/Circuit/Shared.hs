{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Shared-medium fusion: two bodies interleaved on one feedback channel.
--
-- The connective here is the multiplicative disjunction @⅋@ in operational
-- form: two sub-loops share a single feedback channel, and a 'Schedule'
-- resolves the interleaving.  This is the mixed-mode counterpart to
-- 'Circuit.Tensor.superpose', which keeps feedback channels independent
-- (the @⊗@ product).
--
-- 'Bias' is re-exported from "Circuit.Tensor" because it is also used for
-- additive disjunction in "Circuit.Ends".
module Circuit.Shared
  ( -- * Schedule bias
    Bias (..),

    -- * Firing decision
    Fire (..),

    -- * Schedule driver
    Schedule (..),

    -- * Shared fusion class
    Shared (..),

    -- * Shared fusion as a Knot
    sharedKnotBy,
  )
where

import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Loop (Loop (..))
import Circuit.Tensor (Bias (..), Tensor (..))
import Control.Monad (Monad)
import Data.These (These (..))
import Prelude hiding (id, (.))

-- | A schedule decision, now shaped by the inclusive tensor.
--
-- * @L@ — advance the left body only; the right input is not consumed
--   (corresponds to 'This').
-- * @R@ — advance the right body only; the left input is not consumed
--   (corresponds to 'That').
-- * @Both b@ — advance both bodies, with the bias choosing the order
--   (corresponds to 'These').
data Fire = L | R | Both Bias
  deriving (Eq, Show)

-- | A schedule drives shared-feedback fusion.
--
-- The state @s@ is the shared feedback channel.  At each step the schedule
-- looks at the state and chooses which poles advance, returning the updated
-- schedule state.
newtype Schedule s = Schedule
  { -- | Given the current shared state, return the updated state and a 'Fire'
    -- value describing which poles advance and in what order.
    chooseS :: s -> (s, Fire)
  }

-- | Tensors that support shared-feedback fusion of two knot bodies.
--
-- This is the operational content of the multiplicative disjunction: two
-- sub-loops share one feedback channel, and a 'Schedule' resolves the
-- interleaving.  Contrast 'Circuit.Tensor.superpose', which keeps the feedback
-- channels independent (⊗).
class (Tensor t arr) => Shared t arr where
  -- | Fuse two feedback bodies over a shared channel.
  --
  -- The combined body has type @arr (t s (t a c)) (t s (These b d))@: one
  -- shared state @s@, paired inputs @a@ and @c@, and a partial output.  At
  -- each step the schedule chooses which body advances; the gated body's
  -- input is discarded and no output is produced for that side.
  sharedBy ::
    Schedule s ->
    arr (t s a) (t s b) ->
    arr (t s c) (t s d) ->
    arr (t s (t a c)) (t s (These b d))

-- | Shared fusion wrapped as a 'Knot'.
--
-- This takes explicit knot bodies that already share the feedback type @s@.
-- 'Loop' hides its feedback type existentially, so a generic 'Loop'-level
-- combinator cannot constrain two arbitrary knots to share the same channel;
-- this helper makes the shared state explicit at the call site.
sharedKnotBy ::
  forall t arr a b c d s.
  (Shared t arr) =>
  Schedule s ->
  arr (t s a) (t s b) ->
  arr (t s c) (t s d) ->
  Loop t arr (t a c) (These b d)
sharedKnotBy sched f g = Knot (sharedBy sched f g)

-- | Cartesian shared fusion on functions.
--
-- The schedule chooses which bodies advance and in what order.  @L@/@R@
-- run only the chosen body and emit a partial 'This'/'That' product; the
-- other body's input is discarded.  @Both LeftFirst@ / @Both RightFirst@ run
-- both bodies, threading the shared state in the chosen order, and emit a
-- total 'These' product.  When both bodies read and write @s@, the two orders
-- are observationally different — this is the ⅋-vs-⊗ distinction.
instance Shared (,) (->) where
  sharedBy sched f g (s, (a, c)) =
    let (s', fire) = chooseS sched s
     in case fire of
          L ->
            let (s'', b) = f (s', a)
             in (s'', This b)
          R ->
            let (s'', d) = g (s', c)
             in (s'', That d)
          Both LeftFirst ->
            let (s'', b) = f (s', a)
                (s''', d) = g (s'', c)
             in (s''', These b d)
          Both RightFirst ->
            let (s'', d) = g (s', c)
                (s''', b) = f (s'', a)
             in (s''', These b d)
  {-# INLINE sharedBy #-}

-- | Cartesian shared fusion on @K@ arrows.
instance (Monad m) => Shared (,) (K m) where
  sharedBy sched (K f) (K g) =
    K $ \(s, (a, c)) -> do
      let (s', fire) = chooseS sched s
      case fire of
        L -> do
          (s'', b) <- f (s', a)
          pure (s'', This b)
        R -> do
          (s'', d) <- g (s', c)
          pure (s'', That d)
        Both LeftFirst -> do
          (s'', b) <- f (s', a)
          (s''', d) <- g (s'', c)
          pure (s''', These b d)
        Both RightFirst -> do
          (s'', d) <- g (s', c)
          (s''', b) <- f (s'', a)
          pure (s''', These b d)
  {-# INLINE sharedBy #-}
