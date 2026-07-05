{-# LANGUAGE ScopedTypeVariables #-}

-- | Round-trip tests between direct GADTs and signature-based syntax.
module Main where

import Circuit.Signature
import Circuit.Net qualified as N
import Circuit.Trace qualified as C
import Circuit.Traced (Traced (..))
import Control.Category
import Test.QuickCheck
import Prelude hiding (id, (.))

type Arr = (->)

type T = (,)

-- ---------------------------------------------------------------------------
-- Trace round trips

circuits :: [C.Trace T Arr Int Int]
circuits =
  [ C.Arr (+1),
    C.Arr (*2),
    C.Arr (*2) . C.Arr (+1),
    C.Knot (\(acc, x) -> (x, acc + x))
  ]

prop_circuit_direct_roundtrip :: Property
prop_circuit_direct_roundtrip =
  conjoin
    [ forAll arbitrary $ \x ->
        C.run (sigToTrace (traceToSig c)) x == C.run c x
      | c <- circuits
    ]

sigCircuits :: [SigTrace T Arr Int Int]
sigCircuits =
  [ Lift (+1),
    Op (L (SigCompose (Lift (*2)) (Lift (+1)))),
    Op (R (SigKnot (Lift (\(acc, x) -> (x, acc + x)))))
  ]

prop_circuit_sig_roundtrip :: Property
prop_circuit_sig_roundtrip =
  conjoin
    [ forAll arbitrary $ \x ->
        fold (traceToSig (sigToTrace s)) x == fold s x
      | s <- sigCircuits
    ]

-- ---------------------------------------------------------------------------
-- Net round trips

nets :: [N.Net T Arr Int Int]
nets =
  [ N.Lift (+1),
    N.Compose (N.Lift (*2)) (N.Lift (+1)),
    N.Compose N.Plus (N.Compose (N.Par (N.Lift (*2)) (N.Lift (+3))) N.Copy),
    N.Knot (N.Lift (\(acc, x) -> (x, acc + x)))
  ]

prop_net_direct_roundtrip :: Property
prop_net_direct_roundtrip =
  conjoin
    [ forAll arbitrary $ \x ->
        N.weave (sigToNet (netToSig n)) x == N.weave n x
      | n <- nets
    ]

prop_net_melt_via_signature :: Property
prop_net_melt_via_signature =
  conjoin
    [ forAll arbitrary $ \x ->
        fold (sigMelt (netToSig n)) x == N.weave n x
      | n <- nets
    ]

netsPair :: [N.Net T Arr (Int, Int) (Int, Int)]
netsPair = [N.Swap]

prop_net_pair_roundtrip :: Property
prop_net_pair_roundtrip =
  conjoin
    [ forAll arbitrary $ \x ->
        N.weave (sigToNet (netToSig n)) x == N.weave n x
      | n <- netsPair
    ]

-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "circuit direct -> sig -> direct"
  quickCheck prop_circuit_direct_roundtrip
  putStrLn "sig -> direct -> sig"
  quickCheck prop_circuit_sig_roundtrip
  putStrLn "net direct -> sig -> direct"
  quickCheck prop_net_direct_roundtrip
  putStrLn "net melt via signature"
  quickCheck prop_net_melt_via_signature
  putStrLn "net pair direct -> sig -> direct"
  quickCheck prop_net_pair_roundtrip
