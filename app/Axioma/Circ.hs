-- | Circ / bicategory of bodies oracles.
module Axioma.Circ
  ( circTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Body (Body (..), SomeBody (..), runSomeBody)
import Circuit.Channel (Strength (..))
import Circuit.Circ
  ( Sq (..),
    acrossThenDown,
    associatorSq,
    cascadeBody,
    cascadeSome,
    downThenAcross,
    hcompose,
    leftWhisker,
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
        all interchangeTargetOk [(b, r) | b <- [False, True], r <- [0, 1, 2, 3]]
    ]
