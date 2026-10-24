-- | These oracles: the derived-'These' reference block.
--
-- The hand-written 'These' instances for 'Circuit.Tensor' and
-- 'Circuit.Traced' have no surviving structural witness (only 'Trace
-- These' has doctests).  This topic pins each of them against an
-- independent reference built from living @(,)@ + 'Either' vocabulary via
-- the distributive iso @These a b ≅ a + b + a×b@ — the iso and the
-- references use only base 'tensor' / unitors / 'braid' / 'strength' /
-- 'assoc' / 'outerSwap', never the hand-written 'These' instances.
--
-- These are the strongest witnesses in the wave-4 rehome set: each
-- catches a /consistent-but-wrong/ 'These' instance that round-trip
-- checks miss, because agreement is checked against a reference with a
-- different shape of recursion.  The 'These' channels here are wider than
-- 1x1 — 'Char', 'Bool', 'Int', and nested 'These' — so wire swaps are
-- observable, not silently re-routed.
module Axioma.These
  ( theseTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (id, (.))
import Circuit.Tensor (SemiTensor (..), Symmetric (..), Unital (..))
import Circuit.Traced (Assoc (..), OuterSwap (..), Strength (..))
import Control.Monad (when)
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

-- * The distributive iso and derived references

-- | Isomorphism between hand-written 'These' and the distributive-derived
-- representation @a + b + a×b@.
theseToEither :: These a b -> Either a (Either b (a, b))
theseToEither = \case
  This a -> Left a
  That b -> Right (Left b)
  These a b -> Right (Right (a, b))

eitherToThese :: Either a (Either b (a, b)) -> These a b
eitherToThese = \case
  Left a -> This a
  Right (Left b) -> That b
  Right (Right (a, b)) -> These a b

-- | Reference 'tensor' for 'These' derived from @(,)@ and 'Either' via
-- the iso.  Uses only the base 'SemiTensor' instances, not the
-- hand-written 'SemiTensor These' instance.
refTheseTensor :: (a -> b) -> (c -> d) -> These a c -> These b d
refTheseTensor f g = eitherToThese . tensor f (tensor g (tensor f g)) . theseToEither

-- | Reference left unitor for 'These' derived from the base unitors and
-- the annihilator: @These Void a ≅ 0 + (a + 0×a) ≅ a@.
refTheseUnitl :: These Void a -> a
refTheseUnitl = either absurd (either id (absurd . fst)) . theseToEither

-- | Reference right unitor for 'These': @These a Void ≅ a + (0 + a×0) ≅ a@.
refTheseUnitr :: These a Void -> a
refTheseUnitr = either id (either absurd (absurd . snd)) . theseToEither

-- | Reference braid for 'These' derived from the iso.
refTheseBraid :: These a b -> These b a
refTheseBraid = eitherToThese . go . theseToEither
  where
    go (Left a) = Right (Left a)
    go (Right (Left b)) = Left b
    go (Right (Right (a, b))) = Right (Right (b, a))

-- | Reference 'strength' for 'These' derived from the iso.
refTheseStrength :: (b -> c) -> These a b -> These a c
refTheseStrength f = eitherToThese . go . theseToEither
  where
    go (Left a) = Left a
    go (Right (Left b)) = Right (Left (f b))
    go (Right (Right (a, b))) = Right (Right (a, f b))

-- | Nested iso for the derived 'These' associator: unfold the outer
-- 'These', then unfold the carrier inside the product/coproduct pieces.
theseToEitherNested ::
  These (These a b) c ->
  Either (Either a (Either b (a, b))) (Either c (Either a (Either b (a, b)), c))
theseToEitherNested x = case theseToEither x of
  Left y -> Left (theseToEither y)
  Right (Left c) -> Right (Left c)
  Right (Right (y, c)) -> Right (Right (theseToEither y, c))

-- | Convert the nested representation of @These a (These b c)@ into the
-- target iso @Either a (Either (These b c) (a, These b c))@.
theseAssocOut ::
  Either a (Either (Either b (Either c (b, c))) (a, Either b (Either c (b, c)))) ->
  Either a (Either (These b c) (a, These b c))
theseAssocOut (Left a) = Left a
theseAssocOut (Right (Left y)) = Right (Left (eitherToThese y))
theseAssocOut (Right (Right (a, y))) = Right (Right (a, eitherToThese y))

-- | Reference 'assoc' for 'These' derived from the distributive
-- representation.  Pattern-matches on the nested @(,)@ / 'Either' shape
-- rather than on 'These' constructors, so agreement with the hand-written
-- instance is a genuine cross-check.
refTheseAssoc :: These (These a b) c -> These a (These b c)
refTheseAssoc = eitherToThese . theseAssocOut . go . theseToEitherNested
  where
    go (Left (Left a)) = Left a
    go (Left (Right (Left b))) = Right (Left (Left b))
    go (Left (Right (Right (a, b)))) = Right (Right (a, Left b))
    go (Right (Left c)) = Right (Left (Right (Left c)))
    go (Right (Right (Left a, c))) = Right (Right (a, Right (Left c)))
    go (Right (Right (Right (Left b), c))) = Right (Left (Right (Right (b, c))))
    go (Right (Right (Right (Right (a, b)), c))) = Right (Right (a, Right (Right (b, c))))

-- | Nested iso for @These a (These b c)@.
theseToEitherNested' ::
  These a (These b c) ->
  Either a (Either (Either b (Either c (b, c))) (a, Either b (Either c (b, c))))
theseToEitherNested' x = case theseToEither x of
  Left a -> Left a
  Right (Left y) -> Right (Left (theseToEither y))
  Right (Right (a, y)) -> Right (Right (a, theseToEither y))

-- | Convert the nested representation of @These (These a b) c@ into the
-- target iso @Either (These a b) (Either c (These a b, c))@.
theseAssocPrimeOut ::
  Either (Either a (Either b (a, b))) (Either c (Either a (Either b (a, b)), c)) ->
  Either (These a b) (Either c (These a b, c))
theseAssocPrimeOut (Left y) = Left (eitherToThese y)
theseAssocPrimeOut (Right (Left c)) = Right (Left c)
theseAssocPrimeOut (Right (Right (z, c))) = Right (Right (eitherToThese z, c))

-- | Reference 'assoc'' for 'These' (inverse direction).
refTheseAssoc' :: These a (These b c) -> These (These a b) c
refTheseAssoc' = eitherToThese . theseAssocPrimeOut . go . theseToEitherNested'
  where
    go (Left a) = Left (Left a)
    go (Right (Left (Left b))) = Left (Right (Left b))
    go (Right (Left (Right (Left c)))) = Right (Left c)
    go (Right (Left (Right (Right (b, c))))) = Right (Right (Right (Left b), c))
    go (Right (Right (a, Left b))) = Left (Right (Right (a, b)))
    go (Right (Right (a, Right (Left c)))) = Right (Right (Left a, c))
    go (Right (Right (a, Right (Right (b, c))))) = Right (Right (Right (Right (a, b)), c))

-- | Convert the nested representation of @These b (These a c)@ into the
-- target iso @Either b (Either (These a c) (b, These a c))@.
theseOuterSwapOut ::
  Either b (Either (Either a (Either c (a, c))) (b, Either a (Either c (a, c)))) ->
  Either b (Either (These a c) (b, These a c))
theseOuterSwapOut (Left b) = Left b
theseOuterSwapOut (Right (Left y)) = Right (Left (eitherToThese y))
theseOuterSwapOut (Right (Right (b, y))) = Right (Right (b, eitherToThese y))

-- | Reference 'outerSwap' for 'These' derived from the iso.
refTheseOuterSwap :: These a (These b c) -> These b (These a c)
refTheseOuterSwap = eitherToThese . theseOuterSwapOut . go . theseToEitherNested'
  where
    go (Left a) = Right (Left (Left a))
    go (Right (Left (Left b))) = Left b
    go (Right (Left (Right (Left c)))) = Right (Left (Right (Left c)))
    go (Right (Left (Right (Right (b, c))))) = Right (Right (b, Right (Left c)))
    go (Right (Right (a, Left b))) = Right (Right (b, Left a))
    go (Right (Right (a, Right (Left c)))) = Right (Left (Right (Right (a, c))))
    go (Right (Right (a, Right (Right (b, c))))) = Right (Right (b, Right (Right (a, c))))

-- * Agreement oracles

-- | Hand-written 'SemiTensor These' agrees with the reference derived
-- from @(,)@ and 'Either'.  The space covers all three constructors with
-- heterogeneous types ('Int', 'Bool'), so a bimap leg swap is observable.
derivedTheseTensorOk :: Bool
derivedTheseTensorOk =
  let f = (+ 1) :: Int -> Int
      g = not
      space = [This 0, This 1, That False, That True, These 0 False, These 1 True]
   in all (\x -> refTheseTensor f g x == tensor f g x) space

-- | Hand-written left unitor agrees with the derived reference.
-- @These Void a@ is inhabited only through 'That', since 'This' and
-- 'These' require a 'Void'.
derivedTheseUnitlOk :: Bool
derivedTheseUnitlOk =
  let space = [That n | n <- [0, 1, 2]] :: [These Void Int]
   in all (\x -> refTheseUnitl x == unitl x) space

-- | Hand-written right unitor agrees with the derived reference.
-- @These a Void@ is inhabited only through 'This'.
derivedTheseUnitrOk :: Bool
derivedTheseUnitrOk =
  let space = [This n | n <- [0, 1, 2]] :: [These Int Void]
   in all (\x -> refTheseUnitr x == unitr x) space

-- | Hand-written 'Symmetric These' braid agrees with the derived reference —
-- including the product swap in the 'These' case, which a round-trip
-- check cannot see.
derivedTheseBraidOk :: Bool
derivedTheseBraidOk =
  let space = [This 0, This 1, That 'a', That 'b', These 0 'a', These 1 'b'] :: [These Int Char]
   in all (\x -> refTheseBraid x == braid x) space

-- | Hand-written 'Strength These' agrees with the derived reference.
derivedTheseStrengthOk :: Bool
derivedTheseStrengthOk =
  let f = (+ 1) :: Int -> Int
      space = [This 'a', That 0, That 1, These 'a' 0, These 'b' (-1)]
   in all (\x -> refTheseStrength f x == strength f x) space

-- | Hand-written 'Assoc These' agrees with the derived reference on all
-- eight constructor shapes of @These (These (These Bool ()) Char) Int@ —
-- the space exercises every constructor combination, so a swap of any
-- single shape is caught.
derivedTheseAssocOk :: Bool
derivedTheseAssocOk =
  let shapes n b c =
        [ That n,
          This (That c),
          This (This (This b)),
          This (This (That ())),
          This (This (These b ())),
          This (These (This b) c),
          This (These (That ()) c),
          This (These (These b ()) c)
        ] ::
          [These (These (These Bool ()) Char) Int]
      space = concat [shapes n b c | n <- [-1, 0, 1] :: [Int], b <- [False, True], c <- ['x', 'y']]
   in all (\x -> refTheseAssoc x == assoc x) space

-- | Hand-written 'Assoc These' inverse agrees with the derived reference
-- on the seven shapes of @These Bool (These () Char)@.
derivedTheseAssocPrimeOk :: Bool
derivedTheseAssocPrimeOk =
  let shapes a b c =
        [ This a,
          That (This b),
          That (That c),
          That (These b c),
          These a (This b),
          These a (That c),
          These a (These b c)
        ] ::
          [These Bool (These () Char)]
      space = concat [shapes a b c | a <- [False, True], b <- [()], c <- ['x', 'y']]
   in all (\x -> refTheseAssoc' x == assoc' x) space

-- | Hand-written 'OuterSwap These' agrees with the derived reference — the
-- deepest pin of outerSwap-These anywhere: a wrong-side swap on any of the
-- seven shapes is caught, including swaps that keep the involution law
-- (the involution witnesses cannot see those).
derivedTheseOuterSwapOk :: Bool
derivedTheseOuterSwapOk =
  let shapes a b c =
        [ This a,
          That (This b),
          That (That c),
          That (These b c),
          These a (This b),
          These a (That c),
          These a (These b c)
        ] ::
          [These Bool (These () Char)]
      space = concat [shapes a b c | a <- [False, True], b <- [()], c <- ['x', 'y']]
   in all (\x -> refTheseOuterSwap x == outerSwap x) space

theseTopic :: Verbosity -> IO [Bool]
theseTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "These oracles: hand-written instances vs the derived (,) + Either reference"
  sequence
    [ checkV verbosity "derived These tensor agrees with hand-written" derivedTheseTensorOk,
      checkV verbosity "derived These unitl agrees with hand-written" derivedTheseUnitlOk,
      checkV verbosity "derived These unitr agrees with hand-written" derivedTheseUnitrOk,
      checkV verbosity "derived These braid agrees with hand-written" derivedTheseBraidOk,
      checkV verbosity "derived These strength agrees with hand-written" derivedTheseStrengthOk,
      checkV verbosity "derived These assoc agrees with hand-written" derivedTheseAssocOk,
      checkV verbosity "derived These assoc' agrees with hand-written" derivedTheseAssocPrimeOk,
      checkV verbosity "derived These outerSwap agrees with hand-written" derivedTheseOuterSwapOk
    ]
