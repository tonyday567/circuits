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
-- "Circuit.Body" holds independent commit and emit legs: 'Channel' names all
-- four channel positions, 'Body' is its diagonal open-transition corner, and
-- 'InitCell' packages a one-shot initial channel with a recurrent body.
-- "Circuit.Machine" holds their runners and the traditional Moore and Mealy
-- readings: 'Moore' retains its input-seeded lifecycle, 'MooreT' hides the
-- channel existentially, and 'scan' runs a sealed machine down an input list.
--
-- The counter as a Moore machine — commit adds the input to the channel,
-- emit reads it; init absorbs the first input with the seed, so every
-- observation is post-step:
--
-- >>> let counter = Moore (+ 0) (\(n, i) -> n + i) id :: Moore (,) Int (->) Int Int
-- >>> scan (MooreT counter) [1,1,1]
-- [1,2,3]
--
-- A one-shot post-step observation is one 'commit' followed by 'emit':
--
-- >>> case counter of Moore _ c e -> e (c (0, 1))
-- 1
--
-- 'MooreT' is the 'Category' the library proved, with 'MergeNat'
-- pricing the tensor's constructor grammar and 'scanT' running an
-- input list through a machine at any tensor:
--
-- >>> let g = MooreT (Moore id (uncurry (+)) id) :: MooreT (,) (->) Int Int
-- >>> scanT g [1,2,3]
-- [1,3,6]
--
-- A Moore machine can be hung on a polynomial interface — 'MooreP' types
-- the interface by a polynomial, here the monomial @Mono Int Int@,
-- directions in, positions out:
--
-- >>> let mac = Moore ((+ 0) . monoDir) (\(n, d) -> n + monoDir d) (\n -> (n, ())) :: MooreP (,) Int (->) (Mono Int Int)
-- >>> case mac of Moore _ c e -> e (c (0, monoIn 1))
-- (1,())
--
-- === Representations and conversion loss
--
-- Start with the channel boundary. A 'Channel' has independent 'commit' and
-- 'emit' legs; it does not impose an order between them. A 'Body' identifies
-- the post-input and pre-output positions, so 'fuse' can compose those legs.
-- An 'InitCell' adds a separate initial channel, whose commit consumes the
-- first input and whose emit supplies the first observation under
-- 'runInitCell'. Later inputs drive the recurrent body. 'Step' itself carries
-- neither initialisation nor a runner.
--
-- Two kinds of loss then stay distinct:
--
-- * 'MooreT' and 'Knot' /hide/ a channel existentially. The value and its
--   runtime role remain, but its type is no longer nameable at the sealed
--   interface.
-- * 'melt' makes wiring /opaque/: structural rows become base arrows wrapped
--   in 'Lift'. Their interpretation remains, but the rows cannot be inspected
--   as rows in the result.
-- * @run@ and @bind@ on 'Knot' /compute feedback away/ with 'trace'. This
--   closes the hidden channel; it does not iterate a machine over an input
--   tape. The runners in "Circuit.Machine" supply different semantics.
--
-- The representations in "Circuit.Net", "Circuit.Trace", "Circuit.Hyper",
-- "Circuit.Step", and "Circuit.Machine" make different trade-offs:
--
-- * 'Net' keeps symmetric-monoidal and bimonoid wiring inspectable: parallel,
--   swap, copy, discard, merge, and zero rows are syntax. It has no feedback
--   constructor.
-- * 'FreeTrace' keeps 'Lift', sequential composition, and 'SigTrace' as an
--   inspectable free-syntax tree. It is not the one-loop normal form.
-- * 'Knot' is either 'Arr' or one 'Knot' over a base-arrow body, with an
--   existential feedback channel. Use it for the one-knot normal form; its
--   elimination calls 'trace' and supplies neither a tape nor a seed.
-- * 'Hyper' and 'HyperA' are final continuation encodings. They support
--   composition and observation through the dual rather than inspection of
--   the original syntax or a named feedback channel.
-- * 'Step' is one fused tick @arr (t ch i) (t' ch' o)@, with visible channel
--   types. Use it when the tick is the whole artifact.
-- * 'MooreT' seals the channel existentially. 'Body', 'Moore', and 'Step'
--   keep their different leg and tick boundaries visible. 'MooreT' alone
--   does not choose a runner.
--
-- The existing conversions preserve and discard different information:
--
-- * 'widen' in "Circuit.Net" embeds @SMC w arr a b@ as @Net w arr a b@. It
--   preserves every SMC constructor, base arrow, tensor, and interface, and
--   discards nothing.
-- * 'melt' in "Circuit.Net" maps @Net w arr a b@ to @FreeTrace w arr a b@. It
--   preserves the interface, tensor, base arrow, sequential syntax, and
--   denotation; the owning module states @run \@Net = eval . melt@. It
--   discards inspectable 'SigPar', 'SigSwap', 'SigCopy', 'SigDiscard',
--   'SigMerge', and 'SigZero' rows, including access to their wiring and
--   generator dictionaries, by interpreting them as opaque 'Lift' arrows.
-- * 'encode' and 'encodeK' in "Circuit.Hyper" preserve composition, trace,
--   interface, and observation. The owning module documents
--   @observe . encode = eval@. They discard the 'Lift', 'SigCompose', and
--   'SigTrace' syntax tree: the result is final continuation structure, not
--   inspectable initial syntax.
-- * 'observe' and 'observeK' in "Circuit.Hyper" preserve external function or
--   Kleisli behaviour. They discard the continuation representation and its
--   intensional account of feedback.
-- * 'fuse' in "Circuit.Body" composes @emit . commit@ to produce a 'Step'.
--   It preserves the exact fused one-tick arrow, channel types, and
--   post-commit output discipline. It discards the separate commit and emit
--   leg boundaries; initialisation belongs to 'InitCell', not to this fusion.
-- * @run@ and @bind@ on 'Knot' return an 'Arr' body or map a 'Knot' body and
--   apply 'trace'. They preserve the denotation in the receiving traced
--   arrow, discard the one-knot normal form, and compute the explicit
--   hidden-channel boundary away.
--
-- Two boundaries prevent over-reading this map. "Circuit.Trace" has no named
-- @FreeTrace -> Knot@ conversion, and the machine runners are not identified
-- with free-syntax denotation. The denotation laws claimed here are the ones
-- stated by the owning modules: @run \@Net = eval . melt@ and
-- @observe . encode = eval@. Q and the cross-lane trace conversions are
-- demonstrated in the @circuits-examples@ Body zoo.
--
-- === Streams: the neutral interface
--
-- "Circuit.Stream" is the neutral stream interface: `Uncons` destructs
-- a stream of tokens, `Cons` and `Snoc` construct one. It knows nothing
-- about state — only about streams. "Circuit.Post" adds addressed posts,
-- causal ancestry, and stream-generic logs and inboxes.
--
-- === Helpers
--
-- "Circuit.Poly" is the category @Poly@ of polynomials.
-- "Circuit.Container" is the container view —
-- @Eval p x@ as a position with the pins of that position assigned.
-- "Circuit.Linear" is linear-logic connectives over a base category.
-- "Circuit.Shared" fuses two bodies on one shared channel.
-- "Circuit.Pullback" is linear cotangent maps, the base arrow for
-- reverse-mode gradients. From "Circuit.Body", 'Poles' is the memoryless
-- corner — 'init' and 'commit' the write legs over a channel, 'emit'
-- reading it back.
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
-- The counter as a 'MooreT' remains input-seeded under 'before'; the Body zoo
-- demonstrates the optic and ecosystem conversions outside this core API:
--
-- >>> scan (before g (* 2)) [1,2,3]
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
    module Circuit.Body,
    module Circuit.Machine,

    -- * Streams and posts
    module Circuit.Stream,
    module Circuit.Post,

    -- * Helpers
    module Circuit.Poly,
    module Circuit.Container,
    module Circuit.Linear,
    module Circuit.Shared,
    module Circuit.Pullback,
  )
where

import Circuit.Bimonoid
import Circuit.Body
import Circuit.Category
import Circuit.Container
import Circuit.Hyper
import Circuit.Linear
import Circuit.Machine
import Circuit.Net
import Circuit.Poly hiding (dagger)
import Circuit.Post
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
