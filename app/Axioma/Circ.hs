-- | Circ / bicategory of bodies oracles.
module Axioma.Circ
  ( circTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Body (Body (..), SomeBody (..), runSomeBody)
import Circuit.Circ
  ( Sq (..),
    acrossThenDown,
    cascadeSome,
    downThenAcross,
    hcompose,
    leftWhisker,
    rightWhisker,
    whiskerSq,
  )
import Circuit.Poles (Poles (..), box, iomap, poles0)
import Control.Monad (when)
import Data.Bifunctor (first)

-- | Exact-oracle range for the intertwiner checks.
carrierRange :: [Int]
carrierRange = [-16 .. 16]

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

-- | Bodies for the observational cascade tests.  They are intentionally
-- non-commuting so that composition order is observable.
delayBody :: Body (,) Int (->) Int Int
delayBody = Body $ \(s, a) -> (a, s)

summerBody :: Body (,) Int (->) Int Int
summerBody = Body $ \(s, a) -> (s + a, s + a)

doublerBody :: Body (,) Int (->) Int Int
doublerBody = Body $ \(s, _) -> (s * 2, s * 2)

-- | Stream-composition oracle: pointed cascade agrees with running the two
-- bodies in sequence on the input list.
cascadeStreamOk :: [Int] -> Bool
cascadeStreamOk xs =
  let f = SomeBody 0 delayBody
      g = SomeBody 0 summerBody
   in runSomeBody (cascadeSome g f) xs == runSomeBody g (runSomeBody f xs)

-- | Associativity oracle: pointed cascade is associative on input lists.
cascadeAssocOk :: [Int] -> Bool
cascadeAssocOk xs =
  let f = SomeBody 0 delayBody
      g = SomeBody 0 summerBody
      h = SomeBody 1 doublerBody
   in runSomeBody (cascadeSome h (cascadeSome g f)) xs
        == runSomeBody (cascadeSome (cascadeSome h g) f) xs

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

-- | Plain boundary maps for the interchange test.  'boundaryF' precomposes the
-- input; 'boundaryG' postcomposes the output.
boundaryF :: Bool -> Bool
boundaryF = not

boundaryG :: Char -> Char
boundaryG 'x' = 'y'
boundaryG 'y' = 'x'
boundaryG c = c

-- | 'boundaryF' lifted to a 'Body' morphism.  State is threaded through
-- unchanged; only the payload is mapped.
bodyF :: Body (,) s (->) Bool Bool
bodyF = Body $ \(s, a) -> (s, boundaryF a)

-- | 'boundaryG' lifted to a 'Body' morphism.
bodyG :: Body (,) s (->) Char Char
bodyG = Body $ \(s, c) -> (s, boundaryG c)

-- | Bodies for the horizontal 2-cell tests.  They thread a secondary state
-- while leaving the payload alone.
rightBody :: Body (,) Int (->) Char Char
rightBody = Body $ \(s, x) -> (s + 1, x)

leftBody :: Body (,) Int (->) Char Bool
leftBody = Body $ \(s, x) -> (s + 1, x == 'x')

-- | The Moore-split 'Poles' representations agree with the original Mealy
-- bodies at the chosen seeds.
polesMatchBodyOk :: Bool
polesMatchBodyOk =
  all
    (\r -> morphism (box @() counterPoles) (0, r) == morphism counterBody (0, r))
    [False, True]
    && all
      (\r -> morphism (box @() parityPoles) (False, r) == morphism parityBody (False, r))
      [False, True]

-- | Interchange law, source side: boundary whisker on 'Sq' equals 'iomap' on
-- the 'Poles' representation.
interchangeSourceOk :: Bool -> Bool
interchangeSourceOk r =
  let polesSide = box @() (iomap bodyF bodyG counterPoles)
      bodySide = sqSrc (whiskerSq boundaryF boundaryG counterToParitySq)
   in morphism polesSide (0, r) == morphism bodySide (0, r)

-- | Interchange law, target side.
interchangeTargetOk :: Bool -> Bool
interchangeTargetOk r =
  let polesSide = box @() (iomap bodyF bodyG parityPoles)
      bodySide = sqTgt (whiskerSq boundaryF boundaryG counterToParitySq)
   in morphism polesSide (False, r) == morphism bodySide (False, r)

-- | A second commuting square, payload 'Char' throughout, used for horizontal
-- composition.
flipEchoBody :: Body (,) Int (->) Char Char
flipEchoBody = Body $ \(n, x) -> (n + 1, x)

flipParityEchoBody :: Body (,) Bool (->) Char Char
flipParityEchoBody = Body $ first not

flipEchoSq :: Sq (,) (->) Int Bool Char Char
flipEchoSq = Sq odd flipEchoBody flipParityEchoBody

-- | Exact oracle over a bounded input space.
--
-- Note: the intertwiner tests only exercise 'tensor' in its first slot (the
-- carrier map), with the second slot fed 'id'.  Coverage of 'tensor's payload
-- slot belongs in "Axioma.Channel".
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
        cascadeStreamOk [1, 2, 3, 4, 5],
      checkV verbosity "pointed cascade is associative on input lists" $
        cascadeAssocOk [1, 2, 3, 4, 5],
      checkV verbosity "right whisker preserves the square" $
        let sq = rightWhisker counterToParitySq rightBody
         in and
              [ downThenAcross sq ((n, s), r) == acrossThenDown sq ((n, s), r)
              | n <- carrierRange,
                s <- carrierRange,
                r <- [False, True]
              ],
      checkV verbosity "left whisker preserves the square" $
        let sq = leftWhisker leftBody counterToParitySq
         in and
              [ downThenAcross sq ((s, n), x) == acrossThenDown sq ((s, n), x)
              | n <- carrierRange,
                s <- carrierRange,
                x <- ['x', 'y']
              ],
      checkV verbosity "horizontal composition preserves the square" $
        let sq = hcompose flipEchoSq counterToParitySq
         in and
              [ downThenAcross sq ((n, s), r) == acrossThenDown sq ((n, s), r)
              | n <- carrierRange,
                s <- carrierRange,
                r <- [False, True]
              ],
      checkV verbosity "Moore-split poles agree with the Mealy bodies" polesMatchBodyOk,
      checkV verbosity "interchange law (source, False)" $ interchangeSourceOk False,
      checkV verbosity "interchange law (source, True)" $ interchangeSourceOk True,
      checkV verbosity "interchange law (target, False)" $ interchangeTargetOk False,
      checkV verbosity "interchange law (target, True)" $ interchangeTargetOk True,
      checkV verbosity "boundary whisker preserves the square" $
        let sq = whiskerSq boundaryF boundaryG counterToParitySq
         in and
              [ downThenAcross sq (n, r) == acrossThenDown sq (n, r)
              | n <- carrierRange,
                r <- [False, True]
              ]
    ]
