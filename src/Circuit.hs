-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- == Tutorial
--
-- This module re-exports the whole public API, grouped into five sections.
-- One counter runs through most of them — @n + i@ accumulating, observed at
-- @n@ — built up from a bare function to a stateful device on a polynomial
-- interface.
--
-- === Arrows: what circuits are made of
--
-- "Circuit.Category" is the local category hierarchy: composition, poles
-- for products and coproducts, no object constraints. "Circuit.Tensor" is
-- the tensor action and braiding. "Circuit.Traced" chooses the feedback
-- discipline: lazy knots over @(,)@, terminating iteration over `Either`,
-- scheduling over `Data.These.These`. "Circuit.Bimonoid" is the bimonoid
-- layer of circuit wiring, copy and discard. Finite relations — the
-- reference semantics in two grades — live in the sibling package
-- @circuits-rel@ as "Circuit.Rel".
--
-- The counter at this level is a bare function, an update paired with an
-- observation:
--
-- >>> let counter (n, i) = (n + i, n)
-- >>> counter (0, 1)
-- (1,0)
--
-- Over the @(,)@ tensor the feedback value and the output are produced
-- simultaneously, which ties a lazy knot:
--
-- >>> let powers (ns, ()) = (1 : map (*2) ns, take 5 ns)
-- >>> yank powers () :: [Integer]
-- [1,2,4,8,16]
--
-- Over `Either` the loop ends when the body answers `Right`:
--
-- >>> let step n = if n < 5 then Left (n + 1) else Right n
-- >>> yank (either step step) (0 :: Int)
-- 5
--
-- === Syntax: free constructions
--
-- "Circuit.Syntax" is the generic substrate: signatures, free layers,
-- folds (@run@, @eval@, @bind@) and injections (@unit@, `Lift`).
-- "Circuit.Trace" adds feedback to the free syntax, making it traced.
-- "Circuit.Net" packages the free symmetric monoidal category with a
-- bimonoid over a primitive set. 'Stratum' — from "Circuit.GMachine" — is
-- the knot-body category @arr (t ch a) (t ch b)@, the stateful shape
-- that tracing hides. "Circuit.Hyper" is the final, coinductive encoding.
-- "Circuit.Span" is finite spans, the residual-remembering rung of the
-- equipment ladder.
--
-- As a stratum, the counter is one morphism @arr (Int, Int) (Int, Int)@,
-- run through its own arrow:
--
-- >>> let counterStratum = Stratum (\(n, i) -> (n + i, n)) :: Stratum (,) Int (->) Int Int
-- >>> morphism counterStratum (0, 1)
-- (1,0)
--
-- The same wiring can be written in free syntax and run. `widen` embeds
-- the primitive layer into the net; `run` folds the net back down:
--
-- >>> let m = Lift (*2) .> Lift (+1) :: SMC (,) (->) Int Int
-- >>> run (widen m :: Net (,) (->) Int Int) 5
-- 11
--
-- @Trace@ is the inspectable free-syntax form; @Hyper@ is the final
-- encoding. Convert with `encode`, observe with `observe`:
--
-- >>> observe (encode (Lift (+1) :: Trace (,) (->) Int Int)) 41
-- 42
--
-- === Machines: stateful observations
--
-- "Circuit.GMachine" is the machine layer. A 'Cell' is a stateful device
-- with two legs over a hidden channel: 'absorb' folds the input into the
-- channel, and the observation leg reads an output back out. 'Body' keeps
-- both legs at the tensor, and 'Stratum' — met in the syntax section — is
-- the category they compose in. 'moore' repackages the legs as a triple —
-- init, step, extract — pointed at an initial channel, and 'scan' runs
-- the machine down an input list.
--
-- The counter as a cell — absorb adds the input to the channel, the
-- observation leg reads the channel. Pointed at seed 0, the init leg
-- absorbs the seed with the first input, so every observation is
-- post-step:
--
-- >>> let counter = Cell (\(n, i) -> n + i) id
-- >>> scan (moore (+ 0) (\n i -> n + i) id) [1,1,1]
-- [1,2,3]
--
-- A one-shot post-step observation is one 'absorb' followed by the
-- observation leg. The leg's selector is hidden in this umbrella — the
-- unqualified `observe` belongs to `Hyper` — so the match is direct:
--
-- >>> case counter of Cell k o -> o (k (0, 1))
-- 1
--
-- 'GMoore' names the pointed carrier, and 'GMooreT' — the channel
-- existentially hidden, the 'Moore' pattern — is the 'Category' the
-- library proved, with 'TensorSchedule' pricing the tensor's constructor
-- grammar and 'scanT' running an input list through it:
--
-- >>> let g = GMooreT (GMoore id (Cell (uncurry (+)) id)) :: GMooreT (,) (->) Int Int
-- >>> scanT g [1,2,3]
-- [1,3,6]
--
-- A bare 'Machine' hangs the cell on a polynomial interface — here the
-- monomial @Mono Int Int@, directions in, positions out:
--
-- >>> let mac = Machine (Cell (\(n, d) -> n + monoDir d) (\n -> (n, ()))) :: Machine (,) Int (->) (Mono Int Int)
-- >>> case machineCell mac of Cell k o -> o (k (0, monoIn 1))
-- (1,())
--
-- === Streams: the neutral interface
--
-- "Circuit.Stream" is the neutral stream interface: `Uncons` destructs a
-- stream of tokens, `Cons` and `Snoc` construct one. It knows nothing
-- about state — only about streams.
--
-- === Helpers
--
-- "Circuit.Poly" is the category @Poly@ of polynomials.
-- "Circuit.Container" is the container view —
-- @Eval p x@ as a position with the pins of that position assigned.
-- "Circuit.Linear" is linear-logic connectives over a base category.
-- "Circuit.Shared" fuses two bodies on one shared channel.
-- "Circuit.Pullback" is linear cotangent maps, the base arrow for
-- reverse-mode gradients. From "Circuit.GMachine", 'Poles' is the
-- equipment surface — a write/read pair of legs over a channel — and
-- 'Point' names a channel value explicitly, at the tensor unit.
--
-- A 'Poles' pair over the unit carrier closes with 'close' to a plain
-- morphism, and a closed morphism lifts straight into a stratum:
--
-- >>> let p = Poles (const ()) (const 42) :: Poles () (->) () Int
-- >>> close p ()
-- 42
-- >>> let s = Stratum (\((), ()) -> ((), close p ())) :: Stratum (,) () (->) () Int
-- >>> morphism s ((), ())
-- ((),42)
--
-- Cells and lenses interconvert; the round trip is the identity on runs:
--
-- >>> let acc = Cell (\(s, i) -> s + i) (* 2)
-- >>> scan (GMooreT (GMoore (+ 0) (lensAsCell (cellAsLens acc)))) [1,2,3]
-- [2,6,12]
--
-- A 'Point' plugs straight into the write leg of a 'Poles' pair:
--
-- >>> let pt = Point (const 7) :: Point (,) (->) Int
-- >>> close (Poles (runPoint pt) (id :: Int -> Int)) ()
-- 7
--
-- Pullback nets compose as cotangent chains — the circuits-diff name for
-- this is reverse mode:
--
-- >>> evalPullback (Lift (Pullback (* 2)) .> Lift (Pullback (* 3)) :: Net (,) Pullback Int Int) 1
-- 6
--
-- At the container grade the monomial's fibre is flat: the direction at a
-- boundary branch equals the direction itself, witnessed on the nose:
--
-- >>> case monoFibreFlat of Refl -> "fibre is flat"
-- "fibre is flat"
--
-- == Usage
--
-- The library brings its own 'id' and '(.)'. Importing it unqualified
-- alongside 'Prelude' requires hiding the duplicates:
--
-- @
-- import Prelude hiding (id, (.))
-- import Circuit
-- @
--
-- == What is not covered
--
-- This tutorial stops at the API surface. It does not argue the gap
-- between the free syntax and its reference semantics — that check lives
-- in the circuits-axioma suite — and it does not render anything: no
-- string diagrams, no pictures.
module Circuit
  ( -- * Arrows
    module Circuit.Category,
    module Circuit.Traced,
    module Circuit.Tensor,
    module Circuit.Bimonoid,

    -- * Syntax
    module Circuit.Syntax,
    module Circuit.Trace,
    module Circuit.Net,
    module Circuit.Hyper,
    module Circuit.Span,

    -- * Machines
    module Circuit.GMachine,

    -- * Streams
    module Circuit.Stream,

    -- * Helpers
    module Circuit.Poly,
    module Circuit.Container,
    module Circuit.Linear,
    module Circuit.Shared,
    module Circuit.Pullback,
  )
where

import Circuit.Bimonoid
import Circuit.Category
import Circuit.Container
import Circuit.GMachine hiding (observe)
import Circuit.Hyper
import Circuit.Linear
import Circuit.Net
import Circuit.Poly hiding (Point)
import Circuit.Pullback
import Circuit.Shared
import Circuit.Span
import Circuit.Stream
import Circuit.Syntax
import Circuit.Tensor
import Circuit.Trace
import Circuit.Traced
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XDataKinds -XLambdaCase
-- >>> import Prelude hiding (id, (.))
-- >>> import Circuit
-- >>> import Data.Type.Equality ((:~:) (Refl))
