-- | Circ / bicategory of bodies oracles.
module Axioma.Circ
  ( circTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Body (Body (..), SomeBody (..), runFlowchart, runSomeBody)
import Circuit.Category ((.>))
import Circuit.Channel (Channel (..), Strength (..))
import Circuit.Circ
  ( Sq (..),
    acrossThenDown,
    associatorSq,
    bisimilarStates,
    cascadeBody,
    cascadeSome,
    downThenAcross,
    elgotFeedbackBody,
    hcompose,
    isBisimulation,
    leftWhisker,
    maxBisimulation,
    rightWhisker,
    unitorLeftSq,
    unitorRightSq,
    vcomp,
    whiskerSq,
  )
import Circuit.Poles (Poles (..), box, iomap, poles0)
import Circuit.Tensor (Tensor (..))
import Control.Monad (when)
import Data.Bifunctor (first)
import Data.List (sort)
import Data.Maybe (isNothing)
import Data.Void (Void, absurd)

-- | Exact-oracle range for the intertwiner checks.
carrierRange :: [Int]
carrierRange = [-16 .. 16]

-- | Smaller range for associator and strength-coherence oracles, where the
-- state space is a product.
smallRange :: [Int]
smallRange = [-2 .. 2]

-- | Counter with reset: state is an 'Int', payload is a reset flag.
--
-- Output is a 'Char' marking the parity of the /new/ state.
counterBody :: Body (,) Int (->) Bool Char
counterBody = Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')

-- | Boolean flip with reset: state is a 'Bool', payload is a reset flag.
--
-- Output is a 'Char' marking the new state.
parityBody :: Body (,) Bool (->) Bool Char
parityBody = Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')

-- | Carrier map: counter parity agrees with boolean state.
counterToParitySq :: Sq (,) (->) Int Bool Bool Char
counterToParitySq = Sq odd counterBody parityBody

-- | One-token mutation: observe even-ness instead of odd-ness.
brokenBody :: Body (,) Int (->) Bool Char
brokenBody = Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if even n' then 'x' else 'y')

brokenSq :: Sq (,) (->) Int Bool Bool Char
brokenSq = Sq odd brokenBody parityBody

-- | One-token mutation: reset lands on 1 instead of 0.  The observation is
-- internally consistent; only the state transport through @odd@ breaks.
resetDriftBody :: Body (,) Int (->) Bool Char
resetDriftBody = Body $ \(n, r) -> let n' = if r then 1 else n + 1 in (n', if odd n' then 'x' else 'y')

resetDriftSq :: Sq (,) (->) Int Bool Bool Char
resetDriftSq = Sq odd resetDriftBody parityBody

-- | Reference implementation of pointed cascade, kept as an independent
-- specification against which 'cascadeSome' (which uses 'cascadeBody') is
-- checked.  This inverts the previous arrangement where the reference lived in
-- the library and the test used it.
cascadeSomeReference ::
  SomeBody (,) (->) b c ->
  SomeBody (,) (->) a b ->
  SomeBody (,) (->) a c
cascadeSomeReference (SomeBody s2 (Body g)) (SomeBody s1 (Body f)) =
  SomeBody (s1, s2) $ Body $ \((s1', s2'), a) ->
    let (s1'', b) = f (s1', a)
        (s2'', c) = g (s2', b)
     in ((s1'', s2''), c)

-- | Bodies for the observational cascade tests.  They are intentionally
-- non-commuting and time-varying so that composition order is observable.
sumBody :: Body (,) Int (->) Int Int
sumBody = Body $ \(s, a) -> (s + a, s + a)

maxBody :: Body (,) Int (->) Int Int
maxBody = Body $ \(s, a) -> let s' = max s a in (s', s')

delayBody :: Body (,) Int (->) Int Int
delayBody = Body $ \(s, a) -> (a, s)

-- | Stream-composition oracle: pointed cascade agrees with running the two
-- bodies in sequence on the input list.  @sumBody@ and @maxBody@ do not
-- commute, so a reversed composition order is caught.
--
-- Distinct seeds (0 and -5) ensure a wrongly-paired seed tuple is visible.
cascadeStreamOk :: [Int] -> Bool
cascadeStreamOk xs =
  let f = SomeBody 0 sumBody
      g = SomeBody (-5) maxBody
   in runSomeBody (cascadeSome g f) xs == runSomeBody g (runSomeBody f xs)

-- | Associativity oracle: pointed cascade is associative on input lists.  All
-- three bodies are input- and state-sensitive; @doublerBody@ was removed
-- because it discarded its input and made the test vacuous.
--
-- Distinct seeds (7, 0, -5) catch seed mis-pairing.
cascadeAssocOk :: [Int] -> Bool
cascadeAssocOk xs =
  let f = SomeBody 7 delayBody
      g = SomeBody 0 sumBody
      h = SomeBody (-5) maxBody
   in runSomeBody (cascadeSome h (cascadeSome g f)) xs
        == runSomeBody (cascadeSome (cascadeSome h g) f) xs

-- | 'cascadeSome' agrees with the independent reference implementation.
-- Distinct seeds catch seed mis-pairing.
cascadeAgreesWithReferenceOk :: [Int] -> Bool
cascadeAgreesWithReferenceOk xs =
  let f = SomeBody 2 sumBody
      g = SomeBody (-3) maxBody
   in runSomeBody (cascadeSome g f) xs == runSomeBody (cascadeSomeReference g f) xs

-- | Moore-split 'Poles' for the counter body.  The write pole updates state
-- and discards the payload; the read pole observes state and emits a 'Char'.
counterPoles :: Poles (Body (,) Int (->)) Bool Char
counterPoles = poles0 write readBody
  where
    write = Body $ \(n, r) -> (if r then 0 else n + 1, ())
    readBody = Body $ \(n, ()) -> (n, if odd n then 'x' else 'y')

-- | Moore-split 'Poles' for the parity body.
parityPoles :: Poles (Body (,) Bool (->)) Bool Char
parityPoles = poles0 write readBody
  where
    write = Body $ \(b, r) -> (not r && not b, ())
    readBody = Body $ \(b, ()) -> (b, if b then 'x' else 'y')

-- | Plain boundary maps for the interchange test.  They are type-changing so
-- that swapping them is a type error and applying them twice is not an
-- involution.
boundaryF :: Int -> Bool
boundaryF = odd

boundaryG :: Char -> String
boundaryG c = [c, c]

-- | 'boundaryF' lifted to a 'Body' morphism.  State is threaded through
-- unchanged; only the payload is mapped.
bodyF :: Body (,) s (->) Int Bool
bodyF = Body $ \(s, a) -> (s, boundaryF a)

-- | 'boundaryG' lifted to a 'Body' morphism.
bodyG :: Body (,) s (->) Char String
bodyG = Body $ \(s, c) -> (s, boundaryG c)

-- | The Moore-split 'Poles' representations agree with the original Mealy
-- bodies over the full bounded state space.
polesMatchBodyOk :: Bool
polesMatchBodyOk =
  all
    (\(n, r) -> morphism (box @() counterPoles) (n, r) == morphism counterBody (n, r))
    [(n, r) | n <- carrierRange, r <- [False, True]]
    && all
      (\(b, r) -> morphism (box @() parityPoles) (b, r) == morphism parityBody (b, r))
      [(b, r) | b <- [False, True], r <- [False, True]]

-- | Interchange law, source side: boundary whisker on 'Sq' equals 'iomap' on
-- the 'Poles' representation.
interchangeSourceOk :: (Int, Int) -> Bool
interchangeSourceOk (n, r) =
  let polesSide = box @() (iomap bodyF bodyG counterPoles)
      bodySide = sqSrc (whiskerSq boundaryF boundaryG counterToParitySq)
   in morphism polesSide (n, r) == morphism bodySide (n, r)

-- | Interchange law, target side.
interchangeTargetOk :: (Bool, Int) -> Bool
interchangeTargetOk (b, r) =
  let polesSide = box @() (iomap bodyF bodyG parityPoles)
      bodySide = sqTgt (whiskerSq boundaryF boundaryG counterToParitySq)
   in morphism polesSide (b, r) == morphism bodySide (b, r)

-- | Bodies for the horizontal 2-cell tests.  Each machine's output depends on
-- its carrier, so dropped state threads are visible.
echoBody :: Body (,) Int (->) Char Char
echoBody = Body $ \(n, x) -> (n + 1, if odd n then x else 'z')

echoParityBody :: Body (,) Bool (->) Char Char
echoParityBody = Body $ \(b, x) -> (not b, if b then x else 'z')

echoSq :: Sq (,) (->) Int Bool Char Char
echoSq = Sq odd echoBody echoParityBody

rightWhiskerBody :: Body (,) Int (->) Char Int
rightWhiskerBody = Body $ \(s, x) -> (s + 1, if x == 'x' then s else negate s)

leftWhiskerBody :: Body (,) Int (->) Int Bool
leftWhiskerBody = Body $ \(s, a) -> (s + a, odd s)

-- | Observational right-whisker oracle: running the whiskered source/target
-- bodies must equal running the corresponding square bodies followed by the
-- whisker body.  Distinct seeds catch seed mis-pairing.
rightWhiskerObservationalOk :: [Bool] -> Bool
rightWhiskerObservationalOk rs =
  let sq = rightWhisker counterToParitySq rightWhiskerBody
      counterOuts = runSomeBody (SomeBody 3 counterBody) rs
      hOutsSrc = runSomeBody (SomeBody (-2) rightWhiskerBody) counterOuts
      sqOutsSrc = runSomeBody (SomeBody (3, -2) (sqSrc sq)) rs
      parityOuts = runSomeBody (SomeBody False parityBody) rs
      hOutsTgt = runSomeBody (SomeBody (-2) rightWhiskerBody) parityOuts
      sqOutsTgt = runSomeBody (SomeBody (False, -2) (sqTgt sq)) rs
   in sqOutsSrc == hOutsSrc && sqOutsTgt == hOutsTgt

-- | Square-preservation check: right whisker yields a commuting square.
rightWhiskerSquareOk :: Bool
rightWhiskerSquareOk =
  let sq = rightWhisker counterToParitySq rightWhiskerBody
   in all
        (\((n, s), r) -> downThenAcross sq ((n, s), r) == acrossThenDown sq ((n, s), r))
        [((n, s), r) | n <- carrierRange, s <- carrierRange, r <- [False, True]]

-- | Observational left-whisker oracle.
leftWhiskerObservationalOk :: [Int] -> Bool
leftWhiskerObservationalOk xs =
  let sq = leftWhisker leftWhiskerBody counterToParitySq
      lOutsSrc = runSomeBody (SomeBody 1 leftWhiskerBody) xs
      counterOuts = runSomeBody (SomeBody 4 counterBody) lOutsSrc
      sqOutsSrc = runSomeBody (SomeBody (1, 4) (sqSrc sq)) xs
      lOutsTgt = runSomeBody (SomeBody 1 leftWhiskerBody) xs
      parityOuts = runSomeBody (SomeBody True parityBody) lOutsTgt
      sqOutsTgt = runSomeBody (SomeBody (1, True) (sqTgt sq)) xs
   in sqOutsSrc == counterOuts && sqOutsTgt == parityOuts

-- | Square-preservation check: left whisker yields a commuting square.
leftWhiskerSquareOk :: Bool
leftWhiskerSquareOk =
  let sq = leftWhisker leftWhiskerBody counterToParitySq
   in all
        (\((s, n), x) -> downThenAcross sq ((s, n), x) == acrossThenDown sq ((s, n), x))
        [((s, n), x) | s <- carrierRange, n <- carrierRange, x <- [0, 1]]

-- | Observational horizontal-composition oracle, source and target sides.
hcomposeObservationalOk :: [Bool] -> Bool
hcomposeObservationalOk rs =
  let sq = hcompose echoSq counterToParitySq
      counterOuts = runSomeBody (SomeBody 2 counterBody) rs
      echoOutsSrc = runSomeBody (SomeBody (-3) echoBody) counterOuts
      sqOutsSrc = runSomeBody (SomeBody (2, -3) (sqSrc sq)) rs
      parityOuts = runSomeBody (SomeBody False parityBody) rs
      echoOutsTgt = runSomeBody (SomeBody True echoParityBody) parityOuts
      sqOutsTgt = runSomeBody (SomeBody (False, True) (sqTgt sq)) rs
   in sqOutsSrc == echoOutsSrc && sqOutsTgt == echoOutsTgt

-- | Square-preservation check: horizontal composition yields a commuting square.
hcomposeSquareOk :: Bool
hcomposeSquareOk =
  let sq = hcompose echoSq counterToParitySq
   in all
        (\((n, s), r) -> downThenAcross sq ((n, s), r) == acrossThenDown sq ((n, s), r))
        [((n, s), r) | n <- carrierRange, s <- carrierRange, r <- [False, True]]

-- | Independently implemented middle body for the vertical-composition chain.
-- It is extensionally equal to 'mod4Body' but written differently, so the side
-- condition assertion compares two implementations rather than a binding to
-- itself.
mod4BodyB :: Body (,) Int (->) Bool Char
mod4BodyB = Body $ \(n, r) ->
  let n' = if r then 0 else cycleNext n
      cycleNext m = case m `mod` 4 of
        0 -> 1
        1 -> 2
        2 -> 3
        _ -> 0
   in (n', if odd n' then 'x' else 'y')

-- | Chain of two genuine quotients, Int -> Z4 -> Bool, for vertical
-- composition.  @mod4Body@ keeps the carrier in @[0..3]@.
mod4Body :: Body (,) Int (->) Bool Char
mod4Body = Body $ \(n, r) -> let n' = (if r then 0 else n + 1) `mod` 4 in (n', if odd n' then 'x' else 'y')

sqA :: Sq (,) (->) Int Int Bool Char
sqA = Sq (`mod` 4) counterBody mod4Body

sqB :: Sq (,) (->) Int Bool Bool Char
sqB = Sq odd mod4BodyB parityBody

-- | The middle body of the vertical composite matches on both sides of the
-- shared carrier.  This turns the silent 'vcomp' precondition into a checked
-- one at the call site.
vcompSideConditionOk :: Bool
vcompSideConditionOk =
  all
    (\(n, r) -> morphism (sqTgt sqA) (n, r) == morphism (sqSrc sqB) (n, r))
    [(n, r) | n <- carrierRange, r <- [False, True]]

-- | Vertical composition preserves commutation.
vcompOk :: Bool
vcompOk =
  let sq = vcomp sqB sqA
   in all
        (\(n, r) -> downThenAcross sq (n, r) == acrossThenDown sq (n, r))
        [(n, r) | n <- carrierRange, r <- [False, True]]

-- | Left unitor proof witness: composing @counterBody@ with the identity at
-- the unit carrier is isomorphic to @counterBody@ itself.
unitorLeftOk :: Bool
unitorLeftOk =
  let sq = unitorLeftSq counterBody
   in all
        (\(n, r) -> downThenAcross sq (((), n), r) == acrossThenDown sq (((), n), r))
        [(n, r) | n <- carrierRange, r <- [False, True]]

-- | Right unitor proof witness.
unitorRightOk :: Bool
unitorRightOk =
  let sq = unitorRightSq counterBody
   in all
        (\(n, r) -> downThenAcross sq ((n, ()), r) == acrossThenDown sq ((n, ()), r))
        [(n, r) | n <- carrierRange, r <- [False, True]]

-- | Associator proof witness: carrier bracketing of three composed bodies is
-- isomorphic.  This also stress-tests 'cascadeBody' asymmetrically.
associatorOk :: Bool
associatorOk =
  let sq = associatorSq maxBody sumBody delayBody
   in all
        (\input -> downThenAcross sq input == acrossThenDown sq input)
        [(((s1, s2), s3), a) | s1 <- smallRange, s2 <- smallRange, s3 <- smallRange, a <- smallRange]

-- | Cross-class coherence: for @(,)@ and @(->)@, 'strength' must agree with
-- @tensor id@.  If this fails for an instance, the two halves of the module
-- disagree about what whiskering means.
strengthCoherenceOk :: Bool
strengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
   in and
        [ strength f (s, x) == tensor id f (s, x)
        | s <- smallRange,
          x <- smallRange
        ]

-- | Boundary whisker preserves the square.
whiskerSqSquareOk :: Bool
whiskerSqSquareOk =
  let sq = whiskerSq boundaryF boundaryG counterToParitySq
   in all
        (\(n, r) -> downThenAcross sq (n, r) == acrossThenDown sq (n, r))
        [(n, r) | n <- carrierRange, r <- [0, 1, 2, 3]]

-- * Feedback-category law oracles

--
-- These check the guarded feedback operator from "Circuit.Circ" against the
-- feedback-category axioms of Di Lavore et al., "Span(Graph): a Canonical
-- Feedback Algebra of Open Transition Systems" (arXiv:2010.10069), §3.1:
-- A1 tightening, A2 vanishing, A3 joining, A4 strength/superposing, A5 sliding
-- (isomorphisms only).  Yanking is /not/ an axiom; we assert that it fails.

-- | The body-level action of 'feedback': reassociate so the feedback wire
-- becomes part of the hidden carrier.
feedbackBody :: Body (,) ch (->) (s, a) (s, b) -> Body (,) (ch, s) (->) a b
feedbackBody (Body f) =
  Body $ \((ch, s), a) ->
    let (ch', (s', b)) = f (ch, (s, a))
     in ((ch', s'), b)

-- | Parallel (tensor) composition of two bodies at the body level.  This is
-- the pointed counterpart to the tensor of loose 1-cells used in the
-- superposing and tightening laws.
tensorBody ::
  Body (,) ch1 (->) a b ->
  Body (,) ch2 (->) c d ->
  Body (,) (ch1, ch2) (->) (a, c) (b, d)
tensorBody (Body f) (Body g) =
  Body $ \((ch1, ch2), (a, c)) ->
    let (ch1', b) = f (ch1, a)
        (ch2', d) = g (ch2, c)
     in ((ch1', ch2'), (b, d))

-- | Identity body at the unit carrier.
idBody :: Body (,) () (->) a a
idBody = Body $ \((), a) -> ((), a)

-- | Running-sum body before feedback: state accumulates the input and the
-- output is the new state.
runningSumFB :: Body (,) () (->) (Int, Int) (Int, Int)
runningSumFB = Body $ \((), (s, a)) -> let s' = s + a in ((), (s', s'))

-- | Behaviour oracle: a running-sum feedback circuit produces the cumulative
-- sums [1,3,6] on input [1,2,3].
runningSumFeedbackOk :: Bool
runningSumFeedbackOk =
  runSomeBody (SomeBody ((), 0) (feedbackBody runningSumFB)) [1, 2, 3] == [1, 3, 6]

-- | Body used in the vanishing law: increment the payload while carrying the
-- unit feedback wire.
vanishingFBody :: Body (,) () (->) ((), Int) ((), Int)
vanishingFBody = Body $ \((), ((), a)) -> ((), ((), a + 1))

-- | Direct implementation of the same map without feedback.
vanishingDirectBody :: Body (,) () (->) Int Int
vanishingDirectBody = Body $ \((), a) -> ((), a + 1)

-- | A2 Vanishing: feedback over the unit object @()@ is the identity.
vanishingOk :: Bool
vanishingOk =
  runSomeBody (SomeBody ((), ()) (feedbackBody vanishingFBody)) [1, 2, 3]
    == runSomeBody (SomeBody () vanishingDirectBody) [1, 2, 3]

-- | Post-feedback map used in the tightening law: add ten to the output.
tighteningHBody :: Body (,) () (->) Int Int
tighteningHBody = Body $ \((), x) -> ((), x + 10)

-- | A1 Tightening: @feedback ((id_s \\otimes h) \\circ f) = h \\circ feedback f@.
tighteningOk :: Bool
tighteningOk =
  let idS = idBody :: Body (,) () (->) Int Int
      lhs = feedbackBody ((idS `tensorBody` tighteningHBody) `cascadeBody` runningSumFB)
      rhs = tighteningHBody `cascadeBody` feedbackBody runningSumFB
   in runSomeBody (SomeBody (((), ((), ())), 0) lhs) [1, 2, 3]
        == runSomeBody (SomeBody (((), 0), ()) rhs) [1, 2, 3]

-- | Body used in the joining law: two accumulators @(s,t)@ with output @t'@.
joiningFBody :: Body (,) () (->) ((Int, Int), Int) ((Int, Int), Int)
joiningFBody = Body $ \((), ((s, t), a)) ->
  let s' = s + a; t' = t + s' in ((), ((s', t'), t'))

-- | Reassociate @((s, t), a)@ to @(s, (t, a))@ so that feedback can be applied
-- over @s@ first, leaving @(t, a)@ as the payload for a second feedback.
joiningReassocBody :: Body (,) () (->) (Int, (Int, Int)) (Int, (Int, Int))
joiningReassocBody =
  Body $ \((), (s, (t, a))) ->
    let ((), ((s', t'), b)) = morphism joiningFBody ((), ((s, t), a))
     in ((), (s', (t', b)))

-- | A3 Joining: nested feedback over @(s, t)@ equals single feedback over the
-- pair.  The two sides have carriers @((ch, s), t)@ and @(ch, (s, t))@, so the
-- oracle compares observational outputs.
joiningOk :: Bool
joiningOk =
  let joiningFBOnce :: Body (,) ((), Int) (->) (Int, Int) (Int, Int)
      joiningFBOnce = feedbackBody joiningReassocBody
      joiningFBTwice :: Body (,) (((), Int), Int) (->) Int Int
      joiningFBTwice = feedbackBody joiningFBOnce
   in runSomeBody (SomeBody (((), 0), 0) joiningFBTwice) [1, 2, 3]
        == runSomeBody (SomeBody ((), (0, 0)) (feedbackBody joiningFBody)) [1, 2, 3]

-- | Body used in the superposing law: add 100 to the parallel stream.
superposingGBody :: Body (,) () (->) Int Int
superposingGBody = Body $ \((), x) -> ((), x + 100)

-- | Reassociate @((s, a), c)@ to @(s, (a, c))@ so that feedback over @s@ can
-- be applied to the tensor @f \\otimes g@.
superposingLhsBody :: Body (,) ((), ()) (->) (Int, (Int, Int)) (Int, (Int, Int))
superposingLhsBody =
  Body $ \(((), ()), (s, (a, c))) ->
    let (((), ()), ((s', b), d)) = morphism (runningSumFB `tensorBody` superposingGBody) (((), ()), ((s, a), c))
     in (((), ()), (s', (b, d)))

-- | A4 Strength / superposing: @feedback f \\otimes g = feedback (f \\otimes g)@.
superposingOk :: Bool
superposingOk =
  let lhs = feedbackBody superposingLhsBody
      rhs = feedbackBody runningSumFB `tensorBody` superposingGBody
   in runSomeBody (SomeBody (((), ()), 0) lhs) [(1, 10), (2, 20), (3, 30)]
        == runSomeBody (SomeBody (((), 0), ()) rhs) [(1, 10), (2, 20), (3, 30)]

-- | Isomorphism used in the sliding law: shift state by one.
slidingHBody :: Body (,) () (->) Int Int
slidingHBody = Body $ \((), s) -> ((), s + 1)

-- | Body used in the sliding law: input state is @t@, output state is @t+a@.
slidingFBody :: Body (,) () (->) (Int, Int) (Int, Int)
slidingFBody = Body $ \((), (t, a)) -> let s' = t + a in ((), (s', s'))

-- | A5 Sliding: for an isomorphism @h : s -> t@,
-- @feedback_s (f \\circ (h \\otimes id)) = feedback_t ((h \\otimes id) \\circ f)@.
slidingOk :: Bool
slidingOk =
  let hTensorId = slidingHBody `tensorBody` idBody
      lhs = feedbackBody (slidingFBody `cascadeBody` hTensorId)
      rhs = feedbackBody (hTensorId `cascadeBody` slidingFBody)
   in runSomeBody (SomeBody ((((), ()), ()), 0) lhs) [1, 2, 3]
        == runSomeBody (SomeBody (((), ((), ())), 1) rhs) [1, 2, 3]

-- | Braid on @(s, s)@ used to show yanking fails.
feedbackBraidBody :: Body (,) () (->) (Int, Int) (Int, Int)
feedbackBraidBody = Body $ \((), (x, y)) -> ((), (y, x))

-- | Yanking is /not/ required in a feedback category.  Feedback of the braid
-- on @(s, s)@ yields a one-step delay, not the identity.
yankingFailsOk :: Bool
yankingFailsOk =
  let fbBraid = feedbackBody feedbackBraidBody
   in runSomeBody (SomeBody ((), 0) fbBraid) [1, 2, 3] /= [1, 2, 3]
        && runSomeBody (SomeBody ((), 0) fbBraid) [1, 2, 3] == [0, 1, 2]

-- * Either carrier oracles

-- | A simple 'Either' body: a loop that counts down from @n@ to @0@ and
-- returns @0@.  The carrier is 'Int': the current count.
countdownBody :: Body Either Int (->) Int Int
countdownBody = Body $ \case
  Right n -> Left n
  Left 0 -> Right 0
  Left m -> Left (m - 1)

-- | Behaviour oracle: the countdown flowchart halts with the expected value.
eitherBehaviourOk :: Bool
eitherBehaviourOk =
  runFlowchart (SomeBody 0 countdownBody) 20 5 == Just 0
    && runFlowchart (SomeBody 0 countdownBody) 20 0 == Just 0
    && isNothing (runFlowchart (SomeBody 0 countdownBody) 2 5)

-- | 'strength' for 'Either' is functorial action, which must agree with
-- @tensor id@.
eitherStrengthCoherenceOk :: Bool
eitherStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space = [Left 'a', Right 0, Right 1, Left 'b']
   in all (\x -> strength f x == tensor id f x) space

-- | Left-unitor witness for 'Either': composing with the identity at the
-- unit carrier ('Void') is isomorphic to the original body.
eitherUnitorLeftOk :: Bool
eitherUnitorLeftOk =
  let b = Body $ \case Right n -> Right (n + 1 :: Int); Left v -> absurd v
      sq = unitorLeftSq b
   in all
        (\x -> downThenAcross sq x == acrossThenDown sq x)
        [Right 0, Right 1, Right 2]

-- | Right-unitor witness for 'Either'.
eitherUnitorRightOk :: Bool
eitherUnitorRightOk =
  let b = Body $ \case Right n -> Right (n + 1 :: Int); Left v -> absurd v
      sq = unitorRightSq b
   in all
        (\x -> downThenAcross sq x == acrossThenDown sq x)
        [Right 0, Right 1, Right 2]

-- | Bodies for the 'Either' associativity oracle.  @eitherFBody@ can loop;
-- @eitherGBody@ and @eitherHBody@ always halt.  The oracle checks that the
-- two carrier bracketings agree on inputs that exercise all three paths
-- (straight through, f-loop, g-loop).
eitherFBody :: Body Either Bool (->) Int Int
eitherFBody = Body $ \case
  Right 0 -> Left True
  Right n -> Right n
  Left True -> Right 0
  Left False -> Right 0

eitherGBody :: Body Either () (->) Int Int
eitherGBody = Body $ \case
  Right n | n < 0 -> Left ()
  Right n -> Right (n + 10)
  Left () -> Right 99

eitherHBody :: Body Either () (->) Int Int
eitherHBody = Body $ \case
  Right n -> Right (n * 2)
  Left () -> Right 999

-- | Associativity oracle for 'Either' cascade, using observational halting
-- equality.  The two sides have carriers @((ch1 + ch2) + ch3)@ and
-- @(ch1 + (ch2 + ch3))@, so the check is up to carrier isomorphism.
eitherCascadeAssocOk :: Bool
eitherCascadeAssocOk =
  let lhs = cascadeBody eitherHBody (cascadeBody eitherGBody eitherFBody)
      rhs = cascadeBody (cascadeBody eitherHBody eitherGBody) eitherFBody
   in all
        ( \n ->
            runFlowchart (SomeBody (Right () :: Either (Either Bool ()) ()) lhs) 30 n
              == runFlowchart (SomeBody (Right (Right ()) :: Either Bool (Either () ())) rhs) 30 n
        )
        [5, 0, -1]

-- * Elgot dagger / feedback-at-Either oracles

-- | Helper: run the Elgot dagger of @f :: a -> Either a b@ with a fuel bound.
runElgot :: (a -> Either a b) -> Int -> a -> Maybe b
runElgot f fuel a0 = runFlowchart (SomeBody (Right a0) (elgotFeedbackBody f)) fuel a0

-- | Reference implementation of the Elgot dagger for comparison.
elgotReference :: (a -> Either a b) -> Int -> a -> Maybe b
elgotReference _ 0 _ = Nothing
elgotReference f n a = case f a of
  Left s -> elgotReference f (n - 1) s
  Right b -> Just b

-- | A1 Fixed point: @f^\\dagger(a) = [id, f^\\dagger](f(a))@.
elgotFixedPointOk :: Bool
elgotFixedPointOk =
  let f :: Int -> Either Int Int
      f n = if n <= 0 then Right (n * 10) else Left (n - 1)
   in all (\n -> runElgot f 20 n == elgotReference f 20 n) [0, 1, 2, 3, 4, 5]

-- | A2 Naturality: for @g :: b -> c@, @((id + g) \\circ f)^\\dagger = g \\circ f^\\dagger@.
elgotNaturalityOk :: Bool
elgotNaturalityOk =
  let f :: Int -> Either Int Int
      f n = if n <= 0 then Right (n * 10) else Left (n - 1)
      g = (+ 100)
      f' n = case f n of
        Left s -> Left s
        Right b -> Right (g b)
   in all (\n -> runElgot f' 20 n == (g <$> runElgot f 20 n)) [0, 1, 2, 3, 4, 5]

-- | Yanking at 'Either': feedback of the swap on @s + s@.  Unlike the
-- product case, this halts with the input unchanged, so yanking holds for
-- the coproduct symmetry.
eitherYankOk :: Bool
eitherYankOk =
  let swapBody :: Body Either Void (->) (Either Int Int) (Either Int Int)
      swapBody =
        Body $ \case
          Right (Left s) -> Right (Right s)
          Right (Right s) -> Right (Left s)
          Left v -> absurd v
      yankBody = Body $ assoc .> morphism swapBody .> assoc'
   in runFlowchart (SomeBody (Right 0) yankBody) 10 5 == Just 5
        && runFlowchart (SomeBody (Right 0) yankBody) 10 7 == Just 7

-- * Bisimulation oracles

-- | Three-state body for the bisimulation witness.  States @1@ and @2@ are
-- behaviourally equivalent.
bisim3Body :: Body (,) Int (->) Bool Char
bisim3Body = Body $ \(s, r) ->
  case (s, r) of
    (0, False) -> (1, 'y')
    (0, True) -> (0, 'x')
    (1, False) -> (2, 'x')
    (1, True) -> (0, 'x')
    (2, False) -> (2, 'x')
    (2, True) -> (0, 'x')
    _ -> (0, 'x')

-- | Two-state body: the minimisation of 'bisim3Body'.  State @1@ corresponds
-- to both states @1@ and @2@ of the three-state machine.
bisim2Body :: Body (,) Int (->) Bool Char
bisim2Body = Body $ \(s, r) ->
  case (s, r) of
    (0, False) -> (1, 'y')
    (0, True) -> (0, 'x')
    (1, False) -> (1, 'x')
    (1, True) -> (0, 'x')
    _ -> (0, 'x')

-- | Bounded input alphabet for the finite-state bisimulation checks.
bisimInputs :: [Bool]
bisimInputs = [False, True]

-- | The maximal bisimulation between the three-state and two-state machines.
-- States @1@ and @2@ of the larger machine both collapse to state @1@ of the
-- smaller one.
bisimMaxOk :: Bool
bisimMaxOk =
  sort (maxBisimulation bisimInputs [0, 1, 2] [0, 1] bisim3Body bisim2Body)
    == sort [(0, 0), (1, 1), (2, 1)]

-- | The expected relation is itself a bisimulation.
bisimRelationOk :: Bool
bisimRelationOk =
  isBisimulation bisimInputs bisim3Body bisim2Body [(0, 0), (1, 1), (2, 1)]

-- | Initial states @0@ of the two machines are bisimilar.
bisimInitialStatesOk :: Bool
bisimInitialStatesOk =
  bisimilarStates bisimInputs [0, 1, 2] [0, 1] bisim3Body bisim2Body 0 0

-- | State @1@ of the three-state machine is not bisimilar to state @0@ of the
-- two-state machine (their outputs disagree on a non-reset step).
bisimNonEquivalentOk :: Bool
bisimNonEquivalentOk =
  not (bisimilarStates bisimInputs [0, 1, 2] [0, 1] bisim3Body bisim2Body 1 0)

-- | Behavioural agreement on an input stream: related initial states produce
-- identical outputs.
bisimStreamOk :: Bool
bisimStreamOk =
  runSomeBody (SomeBody 0 bisim3Body) [False, True, False, False, True]
    == runSomeBody (SomeBody 0 bisim2Body) [False, True, False, False, True]

-- | Carrier-isomorphism implies bisimulation, but not conversely.  Two
-- isomorphic two-state machines (states relabelled @10,11@ vs @0,1@) are
-- bisimilar via the renaming relation.
bisimCarrierIsoFinerOk :: Bool
bisimCarrierIsoFinerOk =
  let bodyA = bisim2Body
      bodyB :: Body (,) Int (->) Bool Char
      bodyB =
        Body $ \(s, r) ->
          case (s, r) of
            (10, False) -> (11, 'y')
            (10, True) -> (10, 'x')
            (11, False) -> (11, 'x')
            (11, True) -> (10, 'x')
            _ -> (10, 'x')
      rel :: [(Int, Int)]
      rel = [(0, 10), (1, 11)]
   in isBisimulation bisimInputs bodyA bodyB rel
        && bisimilarStates bisimInputs [0, 1] [10, 11] bodyA bodyB 0 10

-- | Exact oracle over a bounded input space.
--
-- Note: the intertwiner tests only exercise 'tensor' in its first slot (the
-- carrier map), with the second slot fed 'id'.  Coverage of 'tensor's payload
-- slot belongs in "Axioma.Channel"; 'hcomposeObservationalOk' also exercises
-- the joint behaviour of 'tensor' through horizontal composition.
circTopic :: Verbosity -> IO [Bool]
circTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Circ / bicategory of bodies oracles"
  sequence
    [ checkV verbosity "counter-to-parity square commutes over bounded inputs" $
        and
          [ downThenAcross counterToParitySq (n, r) == acrossThenDown counterToParitySq (n, r)
          | n <- carrierRange,
            r <- [False, True]
          ],
      checkV verbosity "broken observation disagrees at the named input (4, False)" $
        downThenAcross brokenSq (4, False) /= acrossThenDown brokenSq (4, False),
      checkV verbosity "reset drift disagrees at the named input (0, True)" $
        downThenAcross resetDriftSq (0, True) /= acrossThenDown resetDriftSq (0, True),
      checkV verbosity "pointed cascade agrees with stream composition" $
        cascadeStreamOk [3, 1, 4, 1, 5],
      checkV verbosity "pointed cascade is associative on input lists" $
        cascadeAssocOk [3, 1, 4, 1, 5],
      checkV verbosity "cascadeSome agrees with reference implementation" $
        cascadeAgreesWithReferenceOk [3, 1, 4, 1, 5],
      checkV verbosity "right whisker agrees with stream composition" $
        rightWhiskerObservationalOk [False, True, True, False, True],
      checkV verbosity "right whisker preserves the square" rightWhiskerSquareOk,
      checkV verbosity "left whisker agrees with stream composition" $
        leftWhiskerObservationalOk [1, 2, 3, 4, 5],
      checkV verbosity "left whisker preserves the square" leftWhiskerSquareOk,
      checkV verbosity "horizontal composition agrees with stream composition" $
        hcomposeObservationalOk [False, True, True, False, True],
      checkV verbosity "horizontal composition preserves the square" hcomposeSquareOk,
      checkV verbosity "vcomp side condition holds over bounded inputs" vcompSideConditionOk,
      checkV verbosity "vertical composition preserves commutation" vcompOk,
      checkV verbosity "left unitor witness commutes" unitorLeftOk,
      checkV verbosity "right unitor witness commutes" unitorRightOk,
      checkV verbosity "associator witness commutes" associatorOk,
      checkV verbosity "strength coherence (strength f == tensor id f)" strengthCoherenceOk,
      checkV verbosity "boundary whisker preserves the square" whiskerSqSquareOk,
      checkV verbosity "Moore-split poles agree with the Mealy bodies" polesMatchBodyOk,
      checkV verbosity "interchange law (source)" $
        all interchangeSourceOk [(n, r) | n <- carrierRange, r <- [0, 1, 2, 3]],
      checkV verbosity "interchange law (target)" $
        all interchangeTargetOk [(b, r) | b <- [False, True], r <- [0, 1, 2, 3]],
      checkV verbosity "feedback running-sum behaviour" runningSumFeedbackOk,
      checkV verbosity "feedback vanishing (A2)" vanishingOk,
      checkV verbosity "feedback tightening (A1)" tighteningOk,
      checkV verbosity "feedback joining (A3)" joiningOk,
      checkV verbosity "feedback superposing (A4)" superposingOk,
      checkV verbosity "feedback sliding (A5)" slidingOk,
      checkV verbosity "feedback yanking fails" yankingFailsOk,
      checkV verbosity "Either flowchart behaviour" eitherBehaviourOk,
      checkV verbosity "Either strength coherence (strength f == tensor id f)" eitherStrengthCoherenceOk,
      checkV verbosity "Either left unitor witness commutes" eitherUnitorLeftOk,
      checkV verbosity "Either right unitor witness commutes" eitherUnitorRightOk,
      checkV verbosity "Either cascade associativity" eitherCascadeAssocOk,
      checkV verbosity "Elgot fixed point" elgotFixedPointOk,
      checkV verbosity "Elgot naturality" elgotNaturalityOk,
      checkV verbosity "Either yanking (swap) halts with identity" eitherYankOk,
      checkV verbosity "bisimulation max relation (3-state vs 2-state)" bisimMaxOk,
      checkV verbosity "bisimulation relation check" bisimRelationOk,
      checkV verbosity "bisimilar initial states" bisimInitialStatesOk,
      checkV verbosity "non-bisimilar states are not related" bisimNonEquivalentOk,
      checkV verbosity "bisimilar machines agree on streams" bisimStreamOk,
      checkV verbosity "carrier-iso implies bisimulation" bisimCarrierIsoFinerOk
    ]
