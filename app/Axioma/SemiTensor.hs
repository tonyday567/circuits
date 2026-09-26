-- | SemiTensor oracles: 'Const', the forgetful semigroupoidal tensor, at
-- @(->)@.
--
-- The positive witnesses run: 'tensor' functoriality at 'Const' on named,
-- payload-carrying values with distinct payload types — a leg swap is a
-- type error here, as in the GMooreT witnesses; the 'Assoc' round trip on
-- a heterogeneously nested payload; and a 'Circuit.GMachine.Poles'
-- write/read pair built into a 'Const' machine, where the write leg is the
-- absorb and the run commits from the input alone.
--
-- The negative half cannot be a runtime witness, and none is faked: there
-- is no right unitor at 'Const' — a tryUnitr would have to inhabit
-- @Const ch (Unit Const) -> ch@, eliminating a phantom unit by
-- manufacturing a payload from nothing, and the type does not even form,
-- since 'Unit' has no 'Const' case. There is no braid either — a payload
-- cannot be swapped with a phantom. The left unitor alone would be free
-- (@unitl (Const x) = x@), but one unitor is not a unit, so 'Const'
-- receives 'SemiTensor' and 'Assoc' instances only, never 'Unital',
-- 'Tensor', or 'Action'.
module Axioma.SemiTensor
  ( semiTensorTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (id, (.))
import Circuit.GMachine (Poles (..), close)
import Circuit.Tensor (Const (..), SemiTensor (..))
import Circuit.Traced (Assoc (..))
import Control.Monad (when)
import Prelude hiding (id, read, (.))

-- | A named 'Const' value for the functoriality witnesses: phantom
-- 'Char', payload 'String' — the types differ, so a tensor that maps the
-- payload with the first arrow does not typecheck here.
namedC :: Const Char String
namedC = Const "payload"

-- | tensor id id runs as the identity on the named value.
tryTensorIdConst :: Bool
tryTensorIdConst = tensor id id namedC == namedC

-- | tensor (f2 . f1) (g2 . g1) runs as tensor f2 g2 . tensor f1 g1, with
-- f on the phantom leg and g on the payload leg. An implementation that
-- wired the payload to the first arrow is a type error, not a silent
-- swap: the payload is Int, the first arrow is Char -> Char.
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

-- | Round trip through the 'Const' associator on a heterogeneously nested
-- payload, (Int, String). The payload is pinned: an associator that
-- touched the payload would have to re-nest the pair.
tryAssocRoundTripConst :: Bool
tryAssocRoundTripConst =
  assoc' (assoc v) == v && assoc (assoc' w) == w
  where
    v = Const (7, "seven") :: Const (Const Bool Int) (Int, String)
    w = Const (Const (7, "seven")) :: Const Char (Const Bool (Int, String))

-- | A 'Poles' write/read pair built into a 'Const' machine:
-- @tensor (write p) (read p)@ — the write leg is the absorb, so the run
-- commits from the input alone: feeding the written channel value through
-- reproduces 'close'.
tryPolesAbsorbConst :: Bool
tryPolesAbsorbConst =
  machine (Const (write p "abc")) == Const (close p "abc")
  where
    p :: Poles Int (->) String Int
    p = Poles length (+ 1)
    machine :: Const String Int -> Const Int Int
    machine = tensor (write p) (read p)

semiTensorTopic :: Verbosity -> IO [Bool]
semiTensorTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "SemiTensor oracles"
  sequence
    [ checkV verbosity "semitensor Const: tensor id id is the identity on a named value" tryTensorIdConst,
      checkV verbosity "semitensor Const: tensor (f . g) (h . k) is composition; a leg swap is ill-typed here" tryTensorComposeConst,
      checkV verbosity "assoc Const: round trip pins the heterogeneous payload" tryAssocRoundTripConst,
      checkV verbosity "poles at Const: the write leg is the absorb, commit from the input alone" tryPolesAbsorbConst
    ]
