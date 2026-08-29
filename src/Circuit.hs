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
-- Use the @(,@) tensor to tie a lazy knot. The feedback value and output
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
-- supporting lazy knots with @(,@), iteration with `Either`, and scheduling
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
  ( -- * Category (local arrow hierarchy)
    Category (..),
    K (..),
    Op (..),
    FunctionLike (..),
    Pointed (..),

    -- * Trace (free traced category syntax)
    Trace,
    base,
    yank,
    SigYank (..),

    -- * Structural channel moves
    Assoc,
    assoc,
    assoc',
    Slide,
    slide,
    Strength,
    strength,
    Yank,
    TraceC,

    -- * Tensor action and braiding
    Tensor (..),
    Action (..),
    Unital (..),
    TensorSeed (..),
    Unit,
    Distributive (..),
    Bias (..),
    superpose,
    assocL,
    assocR,
    coassoc,
    coassoc',
    coseed,
    coabsorbL,
    coabsorbR,
    coreleaseL,
    coreleaseR,

    -- * Polynomial channels
    Channel (..),
    emitChannel,
    commitChannel,
    idChannel,
    constChannel,
    mapChannel,

    -- * Polynomial functors
    Poly,
    Eval (..),
    Pos,
    Dir,
    Mono,
    Morphism (..),
    runMorphism,
    lens,
    dagger,
    applyLens,
    prism,
    prismMatch,
    Netlist (..),
    netRoundTrip,
    tensorUnitorL,
    tensorUnitorL',
    tensorUnitorR,
    tensorUnitorR',
    morphAt,
    parT,
    nestedToComp,
    compToNested,
    compUnitorL,
    compUnitorL',
    compUnitorR,
    compUnitorR',
    compAssocL,
    compAssocR,
    tensorEval,

    -- * Body (knot-body category)
    Body (..),
    SomeBody (..),
    cascadeBody,
    cascadeSome,
    runFlowchart,
    runSomeBody,

    -- * Circ (loose bicategory of bodies)
    Circ (..),
    idCirc,
    Sq (..),
    idSq,
    vcomp,
    Intertwiner (..),
    withIntertwiner,
    downThenAcross,
    acrossThenDown,
    cascade,
    unitorLeft,
    unitorRight,
    unitorLeftSq,
    unitorRightSq,
    associator,
    associatorSq,
    rightWhisker,
    leftWhisker,
    hcompose,
    whiskerSq,
    feedback,
    elgotBody,
    elgotDagger,
    elgotFeedbackBody,
    bisimilarStates,
    isBisimulation,
    maxBisimulation,

    -- * Moore machines
    Moore (..),
    moore,
    mooreMorphism,
    mooreMachine,
    MooreEval (..),
    fromEvalMoore,
    toEvalMoore,
    step,
    monoIn,
    monoDir,
    runMooreMono,
    parWiring,
    SomePoles (..),
    runSomePoles,
    mooreToPolesWithProbe,
    mooreWithSeedToPoles,
    mooreAsLens,
    lensAsMoore,
    duplicateMoore,
    branchMoore,
    runMooreSum,
    branchMooreHet,
    runMooreSumHet,
    SumStep (..),
    Coalgebra (..),
    coalgebraToMoore,
    composeCoalgebra,
    mooreToCoalgebraMono,

    -- * Stream transformer (first-input-seeded processes)
    Process (..),
    Boundary (..),
    isMark,
    isPayload,
    mooreToProcess,
    mooreAsProcess,
    markMoore,
    iterateMoore,
    after,
    scan,
    scanStream,
    fold,
    foldStream,
    encodeList,
    encodeStream,
    mealy,
    runMealy,
    runMealyStream,
    delay,
    register,
    processToBody,
    processToSomeBody,

    -- * Channel poles (bi-polar effectful/process API)
    Out (..),
    In (..),
    Poles (..),
    close,
    plug,
    prefixIn,
    suffixOut,
    companionTight,
    conjointTight,
    HasDual (..),
    copycat,
    poles,
    poles0,
    polesK,
    splay,
    splay0,
    compose,
    compose0,
    (>:>),
    polesTensor,
    iomap,
    imap,
    omap,
    box,
    boxAsymmetric,
    pair,
    race,

    -- * Dagger (free dagger category)
    Dagger (..),
    transpose,

    -- * Free category
    Free,
    freeze,

    -- * Layer tower
    Layer (..),
    Cat2,
    (:~>),
    lower,

    -- * Syntax substrate
    Sig,
    (:+:),
    Syntax (Lift),
    Algebra (..),
    eval,
    evalInto,
    SigCompose (..),
    AlgCat,

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
    SigCopy (..),
    SigDiscard (..),
    SigCopyDiscard,
    SigPlus (..),
    SigZero (..),
    SigMergeZero,
    Affine,
    Relevant,
    Cartesian,
    CoAffine,
    CoRelevant,
    CopyT (..),
    DiscardT (..),
    MergeT (..),
    ZeroT (..),
    BimonoidT,

    -- * SMC
    SMC,
    mirrorSMC,
    FreeSMC,
    SigPar (..),
    SigSwap (..),

    -- * Net
    Net,
    widen,
    sift,
    melt,
    mirrorNet,
    AlgRelevant,
    AlgAffine,
    AlgCartesian,
    AlgCoRelevant,
    AlgCoAffine,
    AlgCocartesian,
    AlgBimonoidal,
    AlgNet,

    -- * Pullback (linear cotangent maps)
    Pullback (..),
    evalPullback,

    -- * Hyper
    Hyper,
    HyperA (..),
    lift,
    observe,
    baseHyper,
    push,
    runHyper,
    liftK,
    observeK,
    baseK,
    pushK,
    runHyperK,
    encode,
    encodeK,
    encodeEither,
    runEither,

    -- * Linear implication and exponentials
    Lolli (..),
    Exponential (..),
    BangCopy (..),
    BangWeaken (..),
    WhyNotIntro (..),
    WhyNotMonoid (..),
    LinearBang,
    AffineBang,
    RelevantBang,

    -- * Par (multiplicative disjunction)
    Bot,
    Par (..),
    distL,
    distR,
    mix,

    -- * Shared-medium fusion (the ⅋ connective)
    Pick (..),
    Schedule (..),
    Shared (..),
    SigShared (..),
    AlgShared,

    -- * Finite spans
    Span (..),
    pairs,
    companionSpan,
    conjointSpan,
    composeS,
    identityS,
    presentS,
    refinesS,
    bodyFromSpan,
    spanFromBody,
    someBodyFromSpan,
    spanDistance,

    -- * Mixed optics
    Optic (..),
    SomeOptic (..),
    withSomeOptic,
    identityOptic,
    composeOptic,
    identitySomeOptic,
    composeSomeOptic,
    opticUpdate,
    someOpticUpdate,
    opticPoles,
    opticAsLens,
    lensAsOptic,

    -- * Finite relations over GF(2)
    FinObj (..),
    KnownDim (..),
    FinRel (..),
    finId,
    compFinRel,
    parFinRel,
    unitlFinRel,
    unitl'FinRel,
    unitrFinRel,
    unitr'FinRel,
    swapFinRel,
    assocFinRel,
    assoc'FinRel,
    slideFinRel,
    strengthFinRel,
    traceFinRel,
    finCopy,
    finDiscard,
    finPlus,
    finZero,
    finScalar,
    wiring,

    -- * Stream algebra
    These (..),
    Uncons (..),
    Cons (..),
    Snoc (..),

    -- * Stamped values
    Stamped (..),
  )
where

import Circuit.Bimonoid
  ( Affine,
    Bimonoid,
    BimonoidT,
    CoAffine,
    CoRelevant,
    Cartesian,
    Copy (..),
    CopyDiscard,
    CopyT (..),
    Discard (..),
    DiscardT (..),
    Merge (..),
    MergeZero,
    MergeT (..),
    Relevant,
    SigCopy (..),
    SigCopyDiscard,
    SigDiscard (..),
    SigMergeZero,
    SigPlus (..),
    SigZero (..),
    Zero (..),
    ZeroT (..),
  )
import Circuit.Body
  ( Body (..),
    SomeBody (..),
    cascadeBody,
    cascadeSome,
    runFlowchart,
    runSomeBody,
  )
import Circuit.Category
  ( Category (..),
    FunctionLike (..),
    K (..),
    Op (..),
    Pointed (..),
    (.>),
    (<|),
    (|>),
  )
import Circuit.Channel
  ( Channel (..),
    commitChannel,
    constChannel,
    emitChannel,
    idChannel,
    mapChannel,
  )
import Circuit.Circ
  ( Circ (..),
    Intertwiner (..),
    Sq (..),
    acrossThenDown,
    associator,
    associatorSq,
    bisimilarStates,
    cascade,
    downThenAcross,
    elgotBody,
    elgotDagger,
    elgotFeedbackBody,
    feedback,
    hcompose,
    idCirc,
    idSq,
    isBisimulation,
    leftWhisker,
    maxBisimulation,
    rightWhisker,
    unitorLeft,
    unitorLeftSq,
    unitorRight,
    unitorRightSq,
    vcomp,
    whiskerSq,
    withIntertwiner,
  )
import Circuit.Dagger
  ( Dagger (..),
    transpose,
  )
import Circuit.FinRel
  ( FinObj (..),
    FinRel (..),
    KnownDim (..),
    assocFinRel,
    assoc'FinRel,
    compFinRel,
    finCopy,
    finDiscard,
    finId,
    finPlus,
    finScalar,
    finZero,
    parFinRel,
    slideFinRel,
    strengthFinRel,
    swapFinRel,
    traceFinRel,
    unitlFinRel,
    unitl'FinRel,
    unitrFinRel,
    unitr'FinRel,
    wiring,
  )
import Circuit.Hyper
  ( Hyper,
    HyperA (..),
    baseHyper,
    baseK,
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
    Free,
    Layer (..),
    freeze,
    lower,
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
    curry,
    evalLinear,
    lolli,
    uncurry,
  )
import Circuit.Moore
  ( Coalgebra (..),
    Moore (..),
    MooreEval (..),
    SomePoles (..),
    SumStep (..),
    branchMoore,
    branchMooreHet,
    coalgebraToMoore,
    composeCoalgebra,
    duplicateMoore,
    fromEvalMoore,
    lensAsMoore,
    moore,
    mooreAsLens,
    mooreMachine,
    mooreMorphism,
    mooreToCoalgebraMono,
    mooreToPolesWithProbe,
    mooreWithSeedToPoles,
    monoDir,
    monoIn,
    parWiring,
    runMooreMono,
    runMooreSum,
    runMooreSumHet,
    runSomePoles,
    step,
    toEvalMoore,
  )
import Circuit.Net
  ( AlgAffine,
    AlgBimonoidal,
    AlgCartesian,
    AlgCoAffine,
    AlgCoRelevant,
    AlgCocartesian,
    AlgNet,
    AlgRelevant,
    Net,
    melt,
    mirrorNet,
    sift,
    widen,
  )
import Circuit.Optic
  ( Optic (..),
    SomeOptic (..),
    composeOptic,
    composeSomeOptic,
    identityOptic,
    identitySomeOptic,
    lensAsOptic,
    opticAsLens,
    opticPoles,
    opticUpdate,
    someOpticUpdate,
    withSomeOptic,
  )
import Circuit.Par
  ( Bot,
    Par (..),
    distL,
    distR,
    mix,
  )
import Circuit.Poles
  ( HasDual (..),
    In (..),
    Out (..),
    Poles (..),
    box,
    boxAsymmetric,
    close,
    companionTight,
    compose,
    compose0,
    conjointTight,
    copycat,
    imap,
    iomap,
    omap,
    pair,
    plug,
    poles,
    poles0,
    polesK,
    polesTensor,
    prefixIn,
    race,
    splay,
    splay0,
    suffixOut,
    (>:>),
  )
import Circuit.Poly
  ( Dir,
    Eval (..),
    Mono,
    Morphism (..),
    Netlist (..),
    Poly,
    Pos,
    applyLens,
    compAssocL,
    compAssocR,
    compToNested,
    compUnitorL,
    compUnitorL',
    compUnitorR,
    compUnitorR',
    dagger,
    lens,
    morphAt,
    nestedToComp,
    netRoundTrip,
    parT,
    prism,
    prismMatch,
    runMorphism,
    tensorEval,
    tensorUnitorL,
    tensorUnitorL',
    tensorUnitorR,
    tensorUnitorR',
  )
import Circuit.Process
  ( Boundary (..),
    Process (..),
    after,
    delay,
    encodeList,
    encodeStream,
    fold,
    foldStream,
    isMark,
    isPayload,
    iterateMoore,
    markMoore,
    mealy,
    mooreAsProcess,
    mooreToProcess,
    processToBody,
    processToSomeBody,
    register,
    runMealy,
    runMealyStream,
    scan,
    scanStream,
  )
import Circuit.Pullback
  ( Pullback (..),
    evalPullback,
  )
import Circuit.SMC
  ( FreeSMC,
    SMC,
    SigPar (..),
    SigSwap (..),
    mirrorSMC,
  )
import Circuit.Shared
  ( AlgShared,
    Pick (..),
    Schedule (..),
    Shared (..),
    SigShared (..),
  )
import Circuit.Span
  ( Span (..),
    bodyFromSpan,
    companionSpan,
    composeS,
    conjointSpan,
    identityS,
    pairs,
    presentS,
    refinesS,
    someBodyFromSpan,
    spanDistance,
    spanFromBody,
  )
import Circuit.Stamped (Stamped (..))
import Circuit.Stream
  ( Cons (..),
    Snoc (..),
    These (..),
    Uncons (..),
  )
import Circuit.Syntax
  ( Algebra (..),
    AlgCat,
    Sig,
    SigCompose (..),
    Syntax (Lift),
    eval,
    evalInto,
    (:+:),
  )
import Circuit.Tensor
  ( Action (..),
    Bias (..),
    Distributive (..),
    Tensor (..),
    TensorSeed (..),
    Unital (..),
    Unit,
    assocL,
    assocR,
    coabsorbL,
    coabsorbR,
    coassoc,
    coassoc',
    coseed,
    coreleaseL,
    coreleaseR,
    superpose,
  )
import Circuit.Trace (Trace, base, yank, SigYank (..))
import Circuit.Traced
  ( Assoc,
    Slide,
    Strength,
    TraceC,
    Yank,
    assoc,
    assoc',
    slide,
    strength,
  )
import Prelude hiding (curry, id, uncurry, (.))
