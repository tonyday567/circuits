-- | Circ / bicategory of bodies oracles.
module Axioma.Circ
  ( circTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Body (Body (..))
import Circuit.Circ (Sq (..), acrossThenDown, downThenAcross)
import Control.Monad (when)

-- | Counter with reset: state is an 'Int', payload is a reset flag.
--
-- Output is the parity of the /new/ state.
counterBody :: Body (,) Int (->) Bool Bool
counterBody = Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', odd n')

-- | Boolean flip with reset: state is a 'Bool', payload is a reset flag.
--
-- Output is the new state.
parityBody :: Body (,) Bool (->) Bool Bool
parityBody = Body $ \(b, r) -> let b' = not r && not b in (b', b')

-- | Carrier map: counter parity agrees with boolean state.
counterToParitySq :: Sq (,) (->) Int Bool Bool Bool
counterToParitySq = Sq odd counterBody parityBody

-- | One-token mutation: observe even-ness instead of odd-ness.
brokenBody :: Body (,) Int (->) Bool Bool
brokenBody = Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', even n')

brokenSq :: Sq (,) (->) Int Bool Bool Bool
brokenSq = Sq odd brokenBody parityBody

-- | Exact oracle over a bounded input space.
circTopic :: Verbosity -> IO [Bool]
circTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Circ / bicategory of bodies oracles"
  sequence
    [ checkV verbosity "counter-to-parity square commutes over bounded inputs" $
        and
          [ downThenAcross counterToParitySq (n, r) == acrossThenDown counterToParitySq (n, r)
          | n <- [-16 .. 16],
            r <- [False, True]
          ],
      checkV verbosity "broken observation fails at least one input" $
        not $
          and
            [ downThenAcross brokenSq (n, r) == acrossThenDown brokenSq (n, r)
            | n <- [-16 .. 16],
              r <- [False, True]
            ]
    ]
