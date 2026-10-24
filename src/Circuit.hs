{-# LANGUAGE DuplicateRecordFields #-}

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
-- >>> trace powers () :: [Integer]
-- [1,2,4,8,16]
--
-- Over `Either` the loop ends when the body answers `Right`:
--
-- >>> let step n = if n < 5 then Left (n + 1) else Right n
-- >>> trace (either step step) (0 :: Int)
-- 5
--
-- === Syntax: free constructions
--
-- "Circuit.Syntax" is the generic substrate: signatures, free layers,
-- folds (@run@, @eval@, @bind@) and injections (@unit@, `Lift`).
-- "Circuit.Trace" adds feedback to the free syntax, making it traced.
-- "Circuit.Net" packages the free symmetric monoidal category with a
-- bimonoid over a primitive set. 'Step' — from "Circuit.Step" — is
-- the knot-body arrow @arr (t ch a) (t' ch' b)@, the stateful tick the
-- machine and traced lanes share. "Circuit.Hyper" is the final,
-- coinductive encoding.
-- "Circuit.Span" is finite spans, the residual-remembering rung of the
-- equipment ladder.
--
-- As a single step, the counter is one morphism @(Int, Int) -> (Int, Int)@,
-- run through its own arrow:
--
-- >>> let counterStep = Step (\(n, i) -> (n + i, n)) :: Step (,) (,) Int Int (->) Int Int
-- >>> case counterStep of Step f -> f (0, 1)
-- (1,0)
--
-- The same wiring can be written in free syntax and run. `widen` embeds
-- the primitive layer into the net; `run` folds the net back down:
--
-- >>> let m = Lift (*2) .> Lift (+1) :: SMC (,) (->) Int Int
-- >>> run (widen m :: Net (,) (->) Int Int) 5
-- 11
--
-- @FreeTrace@ is the inspectable free-syntax form; @Hyper@ is the final
-- encoding. Convert with `encode`, observe with `observe`:
--
-- >>> observe (encode (Lift (+1) :: FreeTrace (,) (->) Int Int)) 41
-- 42
--
-- === Machines: stateful observations
--
-- "Circuit.Machine" is the machine layer. A 'Body' is a stateful device
-- with three legs over a channel: 'init' seeds the channel from the
-- first input, 'commit' folds each tick's input into the channel, and
-- 'emit' reads the freshly written channel out. 'Moore' is the corner
-- with the output grammar sealed to 'Const'; 'MooreT' hides the channel
-- existentially, and 'scan' runs a sealed machine down an input list.
--
-- The counter as a body — commit adds the input to the channel, emit
-- reads it; init absorbs the first input with the seed, so every
-- observation is post-step:
--
-- >>> let counter = Body (+ 0) (\(n, i) -> n + i) Const :: Moore (,) Int (->) Int Int
-- >>> scan (MooreT counter) [1,1,1]
-- [1,2,3]
--
-- A one-shot post-step observation is one 'commit' followed by 'emit',
-- the 'Const' wrapper peeled by 'unConst':
--
-- >>> case counter of Body _ k o -> unConst (o (k (0, 1)))
-- 1
--
-- 'MooreT' is the 'Category' the library proved, with 'MergeNat'
-- pricing the tensor's constructor grammar and 'scanT' running an
-- input list through a machine at any tensor:
--
-- >>> let g = MooreT (Body id (uncurry (+)) Const) :: MooreT (,) (->) Int Int
-- >>> scanT g [1,2,3]
-- [1,3,6]
--
-- A body can be hung on a polynomial interface — 'MooreP' types the
-- interface by a polynomial, here the monomial @Mono Int Int@,
-- directions in, positions out:
--
-- >>> let mac = Body ((+ 0) . monoDir) (\(n, d) -> n + monoDir d) (Const . (\n -> (n, ()))) :: MooreP (,) Int (->) (Mono Int Int)
-- >>> case mac of Body _ k o -> unConst (o (k (0, monoIn 1)))
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
-- reverse-mode gradients. From "Circuit.Machine", 'Poles' is the
-- memoryless corner — 'init' and 'commit' the write legs over a
-- channel, 'emit' reading it back.
--
-- A 'Poles' triple over the unit carrier closes with 'close' to a plain
-- morphism, and a closed morphism lifts straight into a step:
--
-- >>> let p = Poles (const ()) (const ()) (const 42) :: Poles () (->) () Int
-- >>> close p ()
-- 42
-- >>> let s = Step (\((), ()) -> ((), close p ())) :: Step (,) (,) () () (->) () Int
-- >>> case s of Step f -> f ((), ())
-- ((),42)
--
-- A body's commit/emit legs are a lens ('bodyAsLens'), and a lens plus
-- a seeding is a body ('lensAsBody'); the round trip is the identity on
-- runs:
--
-- >>> let acc = Body (+ 0) (\(s, i) -> s + i) (Const . (* 2)) :: Moore (,) Int (->) Int Int
-- >>> scan (MooreT (lensAsBody (+ 0) (bodyAsLens acc))) [1,2,3]
-- [2,6,12]
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
-- alongside Prelude requires hiding the duplicates:
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
    module Circuit.Step,
    module Circuit.Machine,

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
import Circuit.Hyper
import Circuit.Linear
import Circuit.Machine
import Circuit.Net
import Circuit.Poly hiding (dagger)
import Circuit.Pullback
import Circuit.Shared
import Circuit.Span
import Circuit.Step
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
