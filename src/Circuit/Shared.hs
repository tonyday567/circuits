{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Shared-medium fusion: two bodies interleaved on one shared channel.
--
-- The connective here is the multiplicative disjunction @⅋@ in operational
-- form: two sub-loops share a single channel, and a 'Schedule' resolves the
-- interleaving.  This is the mixed-mode counterpart to
-- 'Circuit.Tensor.superpose', which keeps channels independent
-- (the @⊗@ product).
--
-- 'Bias' is re-exported from "Circuit.Tensor" because it is also used for
-- additive disjunction in "Circuit.Poles".
module Circuit.Shared
  ( -- * Schedule bias
    Bias (..),

    -- * Schedule decision
    Pick (..),

    -- * Schedule driver
    Schedule (..),

    -- * Shared fusion class
    Shared (..),

    -- * Shared-medium fusion signature
    SigShared (..),

    -- * Free traced category with shared-medium fusion
    AlgShared,
  )
where

import Circuit.Category (Category (..), K (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..))
import Circuit.Syntax
  ( Algebra (..),
    SigCompose,
    Syntax,
    (:+:),
  )
import Circuit.Tensor (Bias (..), Tensor (..))
import Circuit.Trace (SigYank)
import Control.Monad (Monad)
import Data.Kind (Type)
import Data.These (These (..))
import Prelude hiding (id, (.))

-- | A schedule decision: which poles advance on a shared channel.
--
-- * @PickL@ — advance the left body only; the right input is not consumed
--   (corresponds to 'This').
-- * @PickR@ — advance the right body only; the left input is not consumed
--   (corresponds to 'That').
-- * @Both b@ — advance both bodies, with the bias choosing the order
--   (corresponds to 'These').
data Pick = PickL | PickR | Both Bias
  deriving (Eq, Show)

-- | A schedule drives shared-medium fusion.
--
-- The state @s@ is threaded through the fusion; in typical use it is the
-- shared channel.  At each step the schedule looks at the state and chooses
-- which poles advance, returning the updated schedule state.
newtype Schedule s = Schedule
  { -- | Given the current shared state, return the updated state and a 'Pick'
    -- value describing which poles advance and in what order.
    chooseS :: s -> (s, Pick)
  }

-- | Tensors that support shared-medium fusion of two knot bodies.
--
-- This is the operational content of the multiplicative disjunction: two
-- sub-loops share one channel, and a 'Schedule' resolves the interleaving.
-- Contrast 'Circuit.Tensor.superpose', which keeps the channels independent (⊗).
class (Tensor t arr) => Shared t arr where
  -- | Fuse two knot bodies over a shared channel.
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

-- | Cartesian shared fusion on functions.
--
-- The schedule chooses which bodies advance and in what order.  @PickL@/@PickR@
-- run only the chosen body and emit a partial 'This'/'That' product; the
-- other body's input is discarded.  @Both LeftFirst@ / @Both RightFirst@ run
-- both bodies, threading the shared state in the chosen order, and emit a
-- total 'These' product.  When both bodies read and write @s@, the two orders
-- are observationally different — this is the ⅋-vs-⊗ distinction.
instance Shared (,) (->) where
  sharedBy sched f g (s, (a, c)) =
    let (s', pick) = chooseS sched s
     in case pick of
          PickL ->
            let (s'', b) = f (s', a)
             in (s'', This b)
          PickR ->
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
      let (s', pick) = chooseS sched s
      case pick of
        PickL -> do
          (s'', b) <- f (s', a)
          pure (s'', This b)
        PickR -> do
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

-- Shared-medium fusion signature

-- | Shared-medium fusion (the tensor product ⅋), parameterised by a schedule.
--
-- The constructor takes two bodies that already share a feedback type @s@ and
-- produces the untraced shared body.  The surrounding 'SigYank' closes the
-- feedback loop over @s@, yielding a morphism @t a c -> These b d@.
data SigShared (t :: Type -> Type -> Type) arr rec i o where
  SigShared ::
    Schedule s ->
    rec (t s a) (t s b) ->
    rec (t s c) (t s d) ->
    SigShared t arr rec (t s (t a c)) (t s (These b d))

instance (Shared t arr') => Algebra (SigShared t) arr arr' where
  type Ctx (SigShared t) arr arr' = Shared t arr'
  alg _ rec (SigShared sched f g) = sharedBy sched (rec f) (rec g)

-- | Free traced category with shared-medium fusion (the ⅋ connective).
type AlgShared t arr = Syntax (SigCompose :+: SigShared t :+: SigYank t) arr
