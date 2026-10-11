{-# LANGUAGE ScopedTypeVariables #-}

-- | The machine tick: one step of a machine, and the shared currency of
-- the machine lane and the traced lane.
--
-- A 'Step' is an arrow from the grammared source @t ch i@ to the
-- grammared target @t' ch' o@: the channel in, the channel out, around a
-- payload. It is runnerless and unsealed — nothing about a 'Step' says
-- how it will be run — and the two lanes package it differently:
--
-- * "Circuit.Machine" — 'Circuit.Machine.Cell' pairs a 'Step' with a
--   seed leg ('Circuit.Machine.MealyT' seals the channel);
--   'Circuit.Machine.Body' factors the tick into commit and emit
--   ('Circuit.Machine.MooreT' seals it), and 'Circuit.Machine.fuse'
--   lands a body back here.
-- * "Circuit.Trace" — 'Circuit.Trace.Knot' hides the channel
--   existentially, and its one run is 'Circuit.Traced.yank'.
--
-- The tick means the same thing in every packaging; the runners are what
-- differ. 'Circuit.Traced.yank' ties the channel as a fixpoint — lazily
-- at @(,)@, by closed iteration at 'Either' — while the machine runners
-- ('Circuit.Machine.scan', 'Circuit.Machine.fold', and the
-- 'Circuit.Traced.Unfold' family) iterate the tick over a tape or from a
-- closed seed. So which steps fit which runs:
--
-- * Every step is a 'Circuit.Machine.Cell' step — the fused packaging
--   asks nothing.
-- * A step fuses from a 'Circuit.Machine.Body' iff it is
--   Moore-disciplined: the output reads the fresh channel only, so the
--   step factors as @f x = (k x, e (k x))@. The shift register
--   @\\(s, i) -> (i, s)@ fails here — its output reads the stale
--   channel.
-- * A step yanks at @(,)@ iff it is productive: the fresh channel's
--   constructor is produced before the stale channel is demanded. The
--   accumulator @\\(n, i) -> (n + i, n + i)@ fails here — the knot is
--   circular. At 'Either' the yank iterates strictly and productivity is
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
-- >>> let m = MooreT (Body (\i -> [i]) (\(ns, i) -> i : ns) (\ns -> Const (take 3 ns)))
-- >>> scan m [1,2,3,4]
-- [[1],[2,1],[3,2,1],[4,3,2]]
--
-- As a knot, run by 'Circuit.Traced.yank' (the 'Circuit.Trace.Knot'
-- packaging folds to exactly this): the channel ties to a constant
-- stream and the window is constant — no tape exists in a knot:
--
-- >>> yank win 7
-- [7,7,7]
--
-- Same step, two runs, different answers: the runner is the semantics.
module Circuit.Step
  ( Step (..),
  )
where

import Circuit.Category (Category (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Machine (Body (..), MooreT (..), scan)
-- >>> import Circuit.Tensor (Const (..))
-- >>> import Circuit.Traced (yank)

-- | One tick of a machine: the arrow from the grammared source
-- @t ch i@ to the grammared target @t' ch' o@. Composition needs the
-- diagonal — the channel and grammar the tick writes must be the ones
-- the next tick reads.
newtype Step t t' ch ch' arr i o = Step {run :: arr (t ch i) (t' ch' o)}

instance (Category arr) => Category (Step t t ch ch arr) where
  id :: forall a. Step t t ch ch arr a a
  id = Step id
  {-# INLINE id #-}

  (.) :: forall a b c. Step t t ch ch arr b c -> Step t t ch ch arr a b -> Step t t ch ch arr a c
  Step g . Step f = Step (g . f)
  {-# INLINE (.) #-}
