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
-- `Loop` is the inspectable GADT form. @Hyper@ is the final, coinductive
-- encoding. Convert a `Loop` to a @Hyper@ with `encode`, and observe it
-- with `observe` (or eliminate it with `runHyper`).
--
-- >>> observe (encode (Circuit.Loop.Lift (+1) :: Loop (,) (->) Int Int)) 41
-- 42
--
-- == Overview
--
-- This library provides three views on feedback:
--
-- * `Loop` (in "Circuit.Loop") — the initial, inspectable GADT encoding.
-- * @Hyper@ (in "Circuit.Hyper") — the final, coinductive encoding.
-- * `Thread` (in "Circuit.Thread") — the knot-body category
--   @arr (t s a) (t s b)@, the stateful substrate that `Loop` hides before
--   tracing. `SArr` is its cartesian instance.
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
--   inside a `Loop` (currently @(,@), `Either`, or `These` for scheduling).
--
-- * __Feedback value__: The component that travels around the loop (first
--   parameter of the tensor in a `Loop`).
--
-- * __Payload__: The value being transformed and emitted (second parameter
--   of the tensor).
--
-- * __Feedback channel__: The path the feedback value takes when routed back
--   into the next step.
--
-- == Verb glossary
--
-- * __Folds__ eliminate a free construction:
--   `run` (any `Layer`), `freeze` (`Free` to its base arrow),
--   `melt` (`Net` to `Loop`), @sift@ (`Net` to `Sym`),
--   @eval@ / @evalInto@ (@Syntax@ via an algebra).
--
-- * __Injections__ embed one construction into another without eliminating:
--   `unit` (base arrow into a `Layer`), `enrich` (`Loop` into `Net`),
--   @widen@ (`Sym` into `Net`), @algLoop@ / @algNet@ (direct GADT into @Syntax@).
--
-- * __Representation changes__: `encode` (`Loop` to @Hyper@),
--   `observe` / `runHyper` (@Hyper@ to function / fixed point).
module Circuit
  ( -- * Loop
    Loop (..),
    Traced,
    Strength,
    -- | Close a feedback loop. See "Circuit.Loop".
    trace,
    -- | Open a feedback loop. See "Circuit.Loop".
    strength,

    -- * Polynomial channels (successor to pure '(->)' Ends)
    Channel (..),
    emitChannel,
    commitChannel,
    idChannel,
    constChannel,
    mapChannel,

    -- * Thread (knot-body category)
    Thread (..),
    SomeThread (..),
    SArr (..),
    SomeSArr (..),
    threadToLoop,
    runSomeSArr,

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

    -- * Channel ends (bi-polar effectful/process API; still the right tool for
    -- Kleisli IO/STM plumbing until Channel gains Kleisli evaluation)
    Out (..),
    In (..),
    Ends (..),
    close,
    prefixIn,
    suffixOut,
    ends,
    endsK,
    splay,
    composeEnds,
    (>:>),
    parEnds,
    dimapEnds,
    lmapEnds,
    rmapEnds,
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

    -- * Discrete discharge kit
    compD,
    assocD,
    assocD',
    braidD,
    strengthD,
    traceD,

    -- * Operators
    (.>),
    (|>),
    (<|),

    -- * Chu
    ChuObj (..),
    ChuMorphism (..),
    ChuSemiring (..),
    chuLaw,
    chuLawAt,
    composeChu,
    deliveryMatrix,
    deliversToSemiring,
    endsAsChu,
    lawfulDimapEnds,
    idChu,
    negateChu,

    -- * Dagger (bimonoid + dagger)
    Copy (..),
    Discard (..),
    Merge (..),
    Zero (..),
    CopyDiscard,
    MergeZero,
    Dagger (..),
    Bimonoid,
    transpose,

    -- * Sym
    Sym,

    -- * Net
    Net,
    enrich,
    melt,

    -- * Hyper
    Hyper,
    HyperF (..),
    lift,
    observe,
    base,
    push,
    runHyper,
    encode,
    encodeEither,
    encodeFree,
    runEither,
    flatten,

    -- * Channel
    Braided (..),
    ambient,
    ambientBy,
    superpose,

    -- * Boundary (K + payload)
    Boundary (..),
    isMark,
    isPayload,

    -- * Linearity marks
    Linear (..),
    IsLinear,
    NotLinear,

    -- * Additive ends
    Bias (..),
    IsSilent (..),
    HasSilent (..),
    pairEnds,
    raceEnds,
    raceMediator,

    -- * Par (multiplicative disjunction)
    Bot,
    Par (..),
    distL,
    distR,
    mix,

    -- * Channel product
    Tensor (..),
    Action (..),

    -- * Shared-medium fusion (the ⅋ connective)
    Fire (..),
    Schedule (..),
    Shared (..),
    sharedKnotBy,

    -- * Mediator (Track B residual)
    Mediator (..),
    PS (..),
    LinearResidual (..),
    FlushableResidual (..),
    LinearityViolation (..),
    closeCertified,
    closeCertifiedWith,
    count,
    linear,
    pairSum,
    runMediator,
  )
where

import Circuit.Boundary (Boundary (..), IsLinear, Linear (..), NotLinear, Stamped (..), isMark, isPayload)
import Circuit.Category (Ob, (.>), (<|), (|>))
import Circuit.Channel
  ( Strength,
    Traced,
    assocD,
    assocD',
    braidD,
    compD,
    strengthD,
    traceD,
  )
import Circuit.Channel qualified as Channel
import Circuit.ChannelPoly
  ( Channel (..),
    commitChannel,
    constChannel,
    emitChannel,
    idChannel,
    mapChannel,
  )
import Circuit.Dagger
  ( Bimonoid,
    Copy (..),
    CopyDiscard,
    Discard (..),
    Dagger (..),
    Merge (..),
    MergeZero,
    Zero (..),
    transpose,
  )
import Circuit.Chu
  ( ChuMorphism (..),
    ChuObj (..),
    ChuSemiring (..),
    chuLaw,
    chuLawAt,
    composeChu,
    deliversToSemiring,
    deliveryMatrix,
    idChu,
    negateChu,
  )
import Circuit.Ends
  ( Bias (..),
    Ends (..),
    HasDual (..),
    HasSilent (..),
    In (..),
    IsSilent (..),
    Out (..),
    box,
    boxAsymmetric,
    close,
    composeEnds,
    copycat,
    dimapEnds,
    ends,
    endsAsChu,
    endsK,
    lawfulDimapEnds,
    lmapEnds,
    pairEnds,
    parEnds,
    prefixIn,
    raceEnds,
    raceMediator,
    rmapEnds,
    splay,
    suffixOut,
    (>:>),
  )
import Circuit.Hyper
  ( Hyper,
    HyperF (..),
    base,
    encode,
    encodeEither,
    encodeFree,
    flatten,
    lift,
    observe,
    push,
    runEither,
    runHyper,
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
import Circuit.Loop (Loop (..))
import Circuit.Loop qualified as Loop
import Circuit.Mediate
  ( FlushableResidual (..),
    LinearityViolation (..),
    LinearResidual (..),
    Mediator (..),
    PS (..),
    closeCertified,
    closeCertifiedWith,
    count,
    linear,
    mediateLoop,
    pairSum,
    runMediator,
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
import Circuit.Process
  ( Process (..),
    delay,
    fold,
    markSystem,
    register,
    scan,
    systemToProcess,
  )
import Circuit.Thread
  ( SArr (..),
    SomeSArr (..),
    SomeThread (..),
    Thread (..),
    runSomeSArr,
    threadToLoop,
  )
import Circuit.Net
  ( Net,
    Sym,
    enrich,
    melt,
  )
import Circuit.Tensor
  ( Action (..),
    Bot,
    Braided (..),
    Fire (..),
    Par (..),
    Schedule (..),
    Shared (..),
    Tensor (..),
    ambient,
    ambientBy,
    distL,
    distR,
    mix,
    sharedKnotBy,
    superpose,
  )
import Prelude

-- | Close a feedback loop. See "Circuit.Channel".
trace ::
  (Traced t arr, Ob arr a, Ob arr b, Ob arr c, Ob arr (t a b), Ob arr (t a c)) =>
  arr (t a b) (t a c) ->
  arr b c
trace = Channel.trace

-- | Open a feedback loop. See "Circuit.Channel".
strength ::
  (Strength t arr, Ob arr a, Ob arr b, Ob arr c, Ob arr (t a b), Ob arr (t a c)) =>
  arr b c ->
  arr (t a b) (t a c)
strength = Channel.strength
