{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A neutral two-lane morphism, with semantics supplied by its packagings
-- and runners.
--
-- Start with:
--
-- @
-- arr (t x y) (t' x' y')
-- @
--
-- At the pair/function corner this is one morphism @(x, y) -> (x', y')@,
-- not independent arrows @x -> x'@ and @y -> y'@. Either result may depend
-- on either source. Currying and braiding give two State readings,
-- @y -> StateX x x' y'@ and @x -> StateX y y' x'@. The bare arrow chooses
-- neither; 'StateX' is a view, not Step's intrinsic semantics.
--
-- The library parameters @ch ch'@ and @i o@ preserve the channel and
-- interface conventions used by machine composition. They do not remove
-- the underlying symmetry. A body or runner decides which lane is seeded,
-- threaded, observed, hidden, or eliminated.
--
-- The two lanes package the same morphism differently:
--
-- * "Circuit.Body" — 'Circuit.Body.Body' factors a transition into commit
--   and emit ('Circuit.Machine.MooreT' seals the channel), and
--   'Circuit.Body.fuse' lands the transition fragment back here. 'Cell'
--   pairs the same unfactored transition with a unit seed.
-- * "Circuit.Trace" — 'Circuit.Trace.Knot' hides the channel
--   existentially, and its one run is 'Circuit.Traced.trace'.
--
-- 'Circuit.Traced.trace' ties the channel as a fixpoint — lazily at @(,)@,
-- by closed iteration at 'Either' — while the machine runners
-- ('Circuit.Machine.scan', 'Circuit.Machine.fold', and the
-- 'Circuit.Traced.Unfold' family) iterate over a tape or from a closed
-- seed. The runner is the semantics. Which steps fit which runs:
--
-- * Every step can be paired with a seed; that asks nothing of the
--   underlying morphism.
-- * A step fuses from a 'Circuit.Body.Body' iff it is
--   Moore-disciplined: the output reads the fresh channel only, so the
--   step factors as @f x = (k x, e (k x))@. The shift register
--   @\\(s, i) -> (i, s)@ fails here — its output reads the stale
--   channel.
-- * A step traces at @(,)@ iff it is productive: the fresh channel's
--   constructor is produced before the stale channel is demanded. The
--   accumulator @\\(n, i) -> (n + i, n + i)@ fails here — the knot is
--   circular. At 'Either' the trace iterates strictly and productivity is
--   free.
--
-- == A worked example
--
-- The recent-window step is both Moore-disciplined (the window reads the
-- fresh channel) and productive (the channel's constructor is immediate):
--
-- >>> :{
-- let win :: ([Int], Int) -> ([Int], [Int])
--     win (ns, i) = (i : ns, take 3 (i : ns))
-- :}
--
-- As a 'Circuit.Machine.MooreT' over a tape, run by
-- 'Circuit.Machine.scan':
--
-- >>> let m = MooreT (Moore (\i -> [i]) (\(ns, i) -> i : ns) (take 3))
-- >>> scan m [1,2,3,4]
-- [[1],[2,1],[3,2,1],[4,3,2]]
--
-- As a knot, run by 'Circuit.Traced.trace' (the 'Circuit.Trace.Knot'
-- packaging folds to exactly this): the channel ties to a constant
-- stream and the window is constant — no tape exists in a knot:
--
-- >>> trace win 7
-- [7,7,7]
--
-- Same step, two runs, different answers: the runner is the semantics.
module Circuit.Step
  ( Step (..),
    Cell (..),
  )
where

import Circuit.Category (Category (..), StateX)
import Circuit.Tensor (Unit)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Machine (Moore (..), MooreT (..), scan)
-- >>> import Circuit.Traced (trace)

-- | Package one two-lane morphism. The channel and interface names follow
-- the library convention; the underlying arrow remains runnerless and
-- unsealed. Category composition uses the diagonal channel and tensor, so
-- consecutive Steps compose through the same interface @arr i o@.
newtype Step t t' ch ch' arr i o = Step {step :: arr (t ch i) (t' ch' o)}

-- | A unit-sourced seed and an unfactored two-lane transition. The seed is
-- outside the transition; 'Circuit.Machine.Mealy' is the diagonal reading.
data Cell t t' ch ch' arr i o = Cell
  { seed :: arr (Unit t) ch,
    step :: Step t t' ch ch' arr i o
  }

instance (Category arr) => Category (Step t t ch ch arr) where
  id :: forall a. Step t t ch ch arr a a
  id = Step id
  {-# INLINE id #-}

  (.) :: forall a b c. Step t t ch ch arr b c -> Step t t ch ch arr a b -> Step t t ch ch arr a c
  Step g . Step f = Step (g . f)
  {-# INLINE (.) #-}
