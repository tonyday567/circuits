-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- == Usage
--
-- @
-- import Circuit
-- @
--
-- === Lazy feedback (knot-tying)
--
-- Use the @(,@) tensor to tie a lazy knot. The feedback value and output
-- are produced simultaneously.
--
-- >>> let powers (ns, ()) = (1 : map (*2) ns, take 5 ns)
-- >>> trace powers () :: [Integer]
-- [1,2,4,8,16]
--
-- === Iteration
--
-- Use the `Either` tensor for loops that terminate.
--
-- >>> let step n = if n < 5 then Left (n + 1) else Right n
-- >>> trace (either step step) (0 :: Int)
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
-- The `Traced` class (in "Circuit.Channel") abstracts the choice of tensor,
-- supporting lazy knots with @(,@), iteration with `Either`, and scheduling
-- with `These`.
--
-- All braided, cartesian, and cocartesian structure, plus the general
-- `ambientBy` state-threading combinator, lives in "Circuit.Tensor".
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor pairing a feedback value with a payload
--   inside a @Trace@ (currently @(,), `Either`, or `These` for scheduling).
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
--   `melt` (`Net` to @Trace@), @sift@ (`Net` to `SMC`),
--   @eval@ / @evalInto@ (@Syntax@ via a fragment algebra).
--
-- * __Injections__ embed one construction into another without eliminating:
--   `unit` (base arrow into a `Layer`), @widen@ (`SMC` into `Net`),
--   @base@ / @yank@ (base arrow or body into @Trace@).
--
-- * __Representation changes__: `encode` (@Trace@ to @Hyper@),
--   `observe` / `runHyper` (@Hyper@ to function / fixed point).
module Circuit
  ( -- * Trace (free traced category syntax)
    Trace,
    base,
    yank,
    Traced,
    Strength,
    -- | Close a feedback loop. See "Circuit.Channel".
    trace,
    -- | Open a feedback loop. See "Circuit.Channel".
    strength,

    -- * Polynomial channels (successor to pure '(->)' Ends)
    Channel (..),
    emitChannel,
    commitChannel,
    idChannel,
    constChannel,
    mapChannel,

    -- * Body (knot-body category)
    Body (..),
    SomeBody (..),
    runSomeBody,

    -- * Polynomial interfaces
    System,
    system,
    runSystem,
    mooreSystem,
    Mono,
    Morphism (..),
    lens,
    applyLens,
    prism,
    Pos,
    Dir,

    -- * Stream transformer (first-input-seeded processes)
    Process (..),
    scan,
    fold,
    systemToProcess,
    markSystem,
    delay,
    register,
    mealy,
    runMealy,

    -- * Channel poles (bi-polar effectful/process API; still the right tool for

    -- Kleisli IO/STM plumbing until Channel gains Kleisli evaluation)
    Out (..),
    In (..),
    Poles (..),
    close,
    prefixIn,
    suffixOut,
    poles,
    polesK,
    splay,
    (>:>),
    HasDual (..),

    -- * Copycat / multiplicative excluded middle
    copycat,

    -- * Boxes
    box,
    boxAsymmetric,

    -- * Free
    Free,
    freeze,

    -- * Layer tower
    Layer (..),
    Cat2,
    (:~>),
    lower,

    -- * Operators
    (.>),
    (|>),
    (<|),

    -- * Bimonoid (structural rules)
    Copy (..),
    Discard (..),
    Merge (..),
    Zero (..),
    CopyDiscard,
    MergeZero,
    Bimonoid,

    -- * Dagger (free dagger category)
    Dagger (..),
    transpose,

    -- * SMC
    SMC,

    -- * Net
    Net,
    melt,

    -- * Pullback (linear cotangent maps)
    Pullback (..),
    evalPullback,

    -- * Hyper
    Hyper,
    HyperA (..),
    lift,
    observe,
    push,
    runHyper,
    liftK,
    observeK,
    pushK,
    runHyperK,
    encode,
    encodeK,
    encodeEither,
    runEither,

    -- * Tensor
    superpose,

    -- * Stamped values
    Stamped (..),

    -- * Additive poles
    Bias (..),

    -- * Par (multiplicative disjunction)
    Bot,
    Par (..),
    distL,
    distR,
    mix,

    -- * Linear implication (internal hom)
    Lolli (..),

    -- * Exponentials
    Exponential (..),
    BangCopy (..),
    BangWeaken (..),
    WhyNotIntro (..),
    WhyNotMonoid (..),
    LinearBang,
    AffineBang,

    -- * Channel product
    Tensor (..),
    Action (..),

    -- * Shared-medium fusion (the ⅋ connective)
    Pick (..),
    Schedule (..),
    Shared (..),
  )
where

import Circuit.Bimonoid
  ( Bimonoid,
    Copy (..),
    CopyDiscard,
    Discard (..),
    Merge (..),
    MergeZero,
    Zero (..),
  )
import Circuit.Body
  ( Body (..),
    SomeBody (..),
    runSomeBody,
  )
import Circuit.Category ((.>), (<|), (|>))
import Circuit.Channel
  ( Strength,
    Traced,
    strength,
    trace,
  )
import Circuit.Channel qualified as Channel
import Circuit.Dagger
  ( Dagger (..),
    transpose,
  )
import Circuit.Hyper
  ( Hyper,
    HyperA (..),
    encode,
    encodeEither,
    encodeK,
    lift,
    liftK,
    observe,
    observeK,
    push,
    pushK,
    runEither,
    runHyper,
    runHyperK,
  )
import Circuit.Layer
  ( Cat2,
    Free (..),
    Layer (..),
    freeze,
    lower,
    run,
    (:~>),
  )
import Circuit.Linear
  ( AffineBang,
    BangCopy (..),
    BangWeaken (..),
    Exponential (..),
    LinearBang,
    Lolli (..),
    RelevantBang,
    WhyNotIntro (..),
    WhyNotMonoid (..),
  )
import Circuit.Net
  ( Net,
    melt,
  )
import Circuit.Par
  ( Bot,
    Par (..),
    distL,
    distR,
    mix,
  )
import Circuit.Poles
  ( Bias (..),
    HasDual (..),
    In (..),
    Out (..),
    Poles (..),
    box,
    boxAsymmetric,
    close,
    copycat,
    poles,
    polesK,
    prefixIn,
    splay,
    suffixOut,
    (>:>),
  )
import Circuit.Poly
  ( Dir,
    Mono,
    Morphism (..),
    Pos,
    System,
    applyLens,
    lens,
    mooreSystem,
    prism,
    runSystem,
    system,
  )
import Circuit.Poly.Channel
  ( Channel (..),
    commitChannel,
    constChannel,
    emitChannel,
    idChannel,
    mapChannel,
  )
import Circuit.Process
  ( Process (..),
    delay,
    fold,
    markSystem,
    mealy,
    register,
    runMealy,
    scan,
    systemToProcess,
  )
import Circuit.Pullback
  ( Pullback (..),
    evalPullback,
  )
import Circuit.SMC
  ( SMC,
  )
import Circuit.Shared
  ( Pick (..),
    Schedule (..),
    Shared (..),
  )
import Circuit.Stamped (Stamped (..))
import Circuit.Tensor
  ( Action (..),
    Tensor (..),
    superpose,
  )
import Circuit.Trace (Trace, base, yank)
import Circuit.Trace qualified as Trace
import Prelude hiding (curry, uncurry)
