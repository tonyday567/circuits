-- | SemiTensor oracles: 'Const', the forgetful semigroupoidal tensor, at
-- @(->)@, and the 'Distributive' laws at @(,)@ over 'Either'.
--
-- The positive witnesses run: 'tensor' functoriality at 'Const' on named,
-- payload-carrying values with distinct payload types — a leg swap is a
-- type error here, as in the MooreT witnesses; the 'Assoc' round trip on
-- a heterogeneously nested payload; and a 'Circuit.Machine.Poles'
-- triple built into a 'Const' machine, where the write leg is the
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
import Circuit.Machine (Poles (..), close)
import Circuit.Tensor (Const (..), Distributive (..), SemiTensor (..))
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
-- @tensor j o@ — 'Const' discards its left arrow, so the write leg is
-- the absorb and the run commits from the input alone: feeding the
-- written channel value through reproduces 'close'.
tryPolesAbsorbConst :: Bool
tryPolesAbsorbConst =
  case p of
    Poles j _ o -> tensor j o (Const (j "abc")) == Const (close p "abc")
  where
    p :: Poles Int (->) String Int
    p = Poles length length (+ 1)

-- * Distributivity

-- | Exact-oracle range for the distributor round trips.
smallRange :: [Int]
smallRange = [-2 .. 2]

-- | Left distributor round-trip.  The iso @(a, b + c) ≅ (a,b) + (a,c)@ is
-- its own inverse up to the class methods.  The doctests cover forward
-- application only; this pins cancellation, so a @distl'@ with swapped
-- 'Left'/'Right' recovery — self-consistent on every forward doctest — is
-- caught.  The sum side is heterogeneous ('Char' vs 'Bool'), so a
-- recovery swap is observable.
distlRoundTripOk :: Bool
distlRoundTripOk =
  let space = [(n, e) | n <- smallRange, e <- [Left 'a' :: Either Char Bool, Right False, Right True]]
      fwd = distl :: (Int, Either Char Bool) -> Either (Int, Char) (Int, Bool)
      bwd = distl' :: Either (Int, Char) (Int, Bool) -> (Int, Either Char Bool)
   in all (\x -> bwd (fwd x) == x) space
        && all ((\y -> fwd (bwd y) == y) . fwd) space

-- | Right distributor round-trip, same witness shape.
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
