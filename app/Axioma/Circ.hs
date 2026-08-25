-- | Circ / bicategory of bodies oracles.
module Axioma.Circ
  ( circTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Body (Body (..), SomeBody (..), runSomeBody)
import Circuit.Circ (Sq (..), acrossThenDown, cascadeSome, downThenAcross)
import Control.Monad (when)

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
        cascadeAssocOk [1, 2, 3, 4, 5]
    ]
