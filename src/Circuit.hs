-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- == Usage
--
-- This module re-exports the whole public API. Because it brings its own
-- 'id', '(.)', 'curry' and 'uncurry', importing it unqualified alongside
-- 'Prelude' requires hiding the duplicates:
--
-- @
-- import Prelude hiding (curry, id, uncurry, (.))
-- import Circuit
-- @
--
-- === Lazy feedback (knot-tying)
--
-- Use the @(,)@ tensor to tie a lazy knot. The feedback value and output
-- are produced simultaneously.
--
-- >>> let powers (ns, ()) = (1 : map (*2) ns, take 5 ns)
-- >>> yank powers () :: [Integer]
-- [1,2,4,8,16]
--
-- === Iteration
--
-- Use the 'Either' tensor for loops that terminate.
--
-- >>> let step n = if n < 5 then Left (n + 1) else Right n
-- >>> yank (either step step) (0 :: Int)
-- 5
--
-- === Switching between representations
--
-- @Trace@ is the inspectable free-syntax form. @Hyper@ is the final,
-- coinductive encoding. Convert a @Trace@ to a @Hyper@ with `encode`, and
-- observe it with `observe` (or eliminate it with `runHyper`).
--
-- >>> observe (encode (base (+1) :: Trace (,) (->) Int Int)) 41
-- 42
--
-- == Overview
--
-- This library provides three views on feedback:
--
-- * @Trace@ (in "Circuit.Trace") — the initial, inspectable free-syntax.
-- * @Hyper@ (in "Circuit.Hyper") — the final, coinductive encoding.
-- * `Body` (in "Circuit.Body") — the knot-body category
--   @arr (t ch a) (t ch b)@, the stateful substrate that @Trace@ hides before
--   tracing. The cartesian instance is `Body (,) ch (->)`.
--
-- The `Yank` class (in "Circuit.Traced") abstracts the choice of tensor,
-- supporting lazy knots with @(,), iteration with `Either`, and scheduling
-- with `Data.These.These`.
--
-- All braided, cartesian, and cocartesian structure, plus the fused
-- parallel composition `superpose`, lives in "Circuit.Tensor".
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor pairing a feedback value with a payload
--   inside a @Trace@ (currently @(,), `Either`, or `Data.These.These` for scheduling).
--
-- * __Feedback value__: The component that travels around the loop (the first
--   parameter of the tensor inside a @Trace@).
--
-- * __Payload__: The value being transformed and emitted (the second
--   parameter of the tensor inside a @Trace@).
--
-- * __Feedback channel__: The path the feedback value takes when routed back
--   into the next step.
--
-- == Verb glossary
--
-- * __Folds__ eliminate a free construction:
--   `run` (any `Layer`), `freeze` (`Free` to its base arrow),
--   `melt` (`Net` to @Trace@), `bind` (fold into a target category),
--   `lower` (restrict a fold to the generators).
--
-- * __Injections__ embed one construction into another without eliminating:
--   `unit` (base arrow into a `Layer`), `base` (base arrow into @Trace@),
--   `yank` (close a feedback loop in @Trace@).
--
-- * __Representation changes__: `encode` (@Trace@ to @Hyper@),
--   `observe` / `runHyper` (@Hyper@ to function / fixed point).
module Circuit
  ( module Circuit.Bimonoid,
    module Circuit.Body,
    module Circuit.Category,
    module Circuit.Channel,
    module Circuit.Circ,
    module Circuit.Dagger,
    module Circuit.FinRel,
    module Circuit.Hyper,
    module Circuit.Layer,
    module Circuit.Linear,
    module Circuit.Moore,
    module Circuit.Net,
    module Circuit.Optic,
    module Circuit.Par,
    module Circuit.Poles,
    module Circuit.Poly,
    module Circuit.Process,
    module Circuit.Pullback,
    module Circuit.SMC,
    module Circuit.Shared,
    module Circuit.Span,
    module Circuit.Stamped,
    module Circuit.Stream,
    module Circuit.Syntax,
    module Circuit.Tensor,
    module Circuit.Trace,
    module Circuit.Traced,
  )
where

import Circuit.Bimonoid
import Circuit.Body
import Circuit.Category
import Circuit.Channel
import Circuit.Circ
import Circuit.Dagger
import Circuit.FinRel
import Circuit.Hyper
import Circuit.Layer
import Circuit.Linear
import Circuit.Moore
import Circuit.Net
import Circuit.Optic
import Circuit.Par
import Circuit.Poles
import Circuit.Poly
import Circuit.Process
import Circuit.Pullback
import Circuit.SMC
import Circuit.Shared hiding (Bias)
import Circuit.Span
import Circuit.Stamped
import Circuit.Stream
import Circuit.Syntax
import Circuit.Tensor
import Circuit.Trace hiding (yank)
import Circuit.Traced
import Prelude hiding (curry, id, uncurry, (.))
