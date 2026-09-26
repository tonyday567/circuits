module Axioma.SemiTensor
  ( semiTensorTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (id, (.))
import Circuit.GMachine (Poles (..), close)
import Circuit.Tensor (Const (..), Distributive (..), SemiTensor (..))
import Circuit.Traced (Assoc (..))
import Control.Monad (when)
import Prelude hiding (id, read, (.))

namedC :: Const Char String
namedC = Const "payload"

tryTensorIdConst :: Bool
tryTensorIdConst = tensor id id namedC == namedC

tryTensorComposeConst :: Bool
tryTensorComposeConst =
  tensor (f2 . f1) (g2 . g1) v == (tensor f2 g2 . tensor f1 g1) v
  where
    v = Const 7 :: Const Char Int
    f1 :: Char -> Char
    f1 = succ
    f2 :: Char -> Char
    f2 = pred
    g1 :: Int -> Int
    g1 = (+ 1)
    g2 :: Int -> String
    g2 = show

tryAssocRoundTripConst :: Bool
tryAssocRoundTripConst =
  assoc' (assoc v) == v && assoc (assoc' w) == w
  where
    v = Const (7, "seven") :: Const (Const Bool Int) (Int, String)
    w = Const (Const (7, "seven")) :: Const Char (Const Bool (Int, String))

tryPolesAbsorbConst :: Bool
tryPolesAbsorbConst =
  machine (Const (write p "abc")) == Const (close p "abc")
  where
    p :: Poles Int (->) String Int
    p = Poles length (+ 1)
    machine :: Const String Int -> Const Int Int
    machine = tensor (write p) (read p)

smallRange :: [Int]
smallRange = [-2 .. 2]

distlRoundTripOk :: Bool
distlRoundTripOk =
  let space = [(n, e) | n <- smallRange, e <- [Left 'a' :: Either Char Bool, Right False, Right True]]
      fwd = distl :: (Int, Either Char Bool) -> Either (Int, Char) (Int, Bool)
      bwd = distl' :: Either (Int, Char) (Int, Bool) -> (Int, Either Char Bool)
   in all (\x -> bwd (fwd x) == x) space
        && all ((\y -> fwd (bwd y) == y) . fwd) space

distrRoundTripOk :: Bool
distrRoundTripOk =
  let space = [(e, n) | e <- [Left 'a' :: Either Char Bool, Right False, Right True], n <- smallRange]
      fwd = distr :: (Either Char Bool, Int) -> Either (Char, Int) (Bool, Int)
      bwd = distr' :: Either (Char, Int) (Bool, Int) -> (Either Char Bool, Int)
   in all (\x -> bwd (fwd x) == x) space
        && all ((\y -> fwd (bwd y) == y) . fwd) space

semiTensorTopic :: Verbosity -> IO [Bool]
semiTensorTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "SemiTensor oracles"
  sequence
    [ checkV verbosity "semitensor Const: tensor id id is the identity on a named value" tryTensorIdConst,
      checkV verbosity "semitensor Const: tensor (f . g) (h . k) is composition; a leg swap is ill-typed here" tryTensorComposeConst,
      checkV verbosity "assoc Const: round trip pins the heterogeneous payload" tryAssocRoundTripConst,
      checkV verbosity "poles at Const: the write leg is the absorb, commit from the input alone" tryPolesAbsorbConst,
      checkV verbosity "Distributive distl round-trip" distlRoundTripOk,
      checkV verbosity "Distributive distr round-trip" distrRoundTripOk
    ]
