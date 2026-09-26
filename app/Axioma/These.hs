module Axioma.These
  ( theseTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (id, (.))
import Circuit.Tensor (Action (..), SemiTensor (..), Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..))
import Control.Monad (when)
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

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

refTheseTensor :: (a -> b) -> (c -> d) -> These a c -> These b d
refTheseTensor f g = eitherToThese . tensor f (tensor g (tensor f g)) . theseToEither

refTheseUnitl :: These Void a -> a
refTheseUnitl = either absurd (either id (absurd . fst)) . theseToEither

refTheseUnitr :: These a Void -> a
refTheseUnitr = either id (either absurd (absurd . snd)) . theseToEither

refTheseBraid :: These a b -> These b a
refTheseBraid = eitherToThese . go . theseToEither
  where
    go (Left a) = Right (Left a)
    go (Right (Left b)) = Left b
    go (Right (Right (a, b))) = Right (Right (b, a))

refTheseStrength :: (b -> c) -> These a b -> These a c
refTheseStrength f = eitherToThese . go . theseToEither
  where
    go (Left a) = Left a
    go (Right (Left b)) = Right (Left (f b))
    go (Right (Right (a, b))) = Right (Right (a, f b))

theseToEitherNested ::
  These (These a b) c ->
  Either (Either a (Either b (a, b))) (Either c (Either a (Either b (a, b)), c))
theseToEitherNested x = case theseToEither x of
  Left y -> Left (theseToEither y)
  Right (Left c) -> Right (Left c)
  Right (Right (y, c)) -> Right (Right (theseToEither y, c))

theseAssocOut ::
  Either a (Either (Either b (Either c (b, c))) (a, Either b (Either c (b, c)))) ->
  Either a (Either (These b c) (a, These b c))
theseAssocOut (Left a) = Left a
theseAssocOut (Right (Left y)) = Right (Left (eitherToThese y))
theseAssocOut (Right (Right (a, y))) = Right (Right (a, eitherToThese y))

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

theseToEitherNested' ::
  These a (These b c) ->
  Either a (Either (Either b (Either c (b, c))) (a, Either b (Either c (b, c))))
theseToEitherNested' x = case theseToEither x of
  Left a -> Left a
  Right (Left y) -> Right (Left (theseToEither y))
  Right (Right (a, y)) -> Right (Right (a, theseToEither y))

theseAssocPrimeOut ::
  Either (Either a (Either b (a, b))) (Either c (Either a (Either b (a, b)), c)) ->
  Either (These a b) (Either c (These a b, c))
theseAssocPrimeOut (Left y) = Left (eitherToThese y)
theseAssocPrimeOut (Right (Left c)) = Right (Left c)
theseAssocPrimeOut (Right (Right (z, c))) = Right (Right (eitherToThese z, c))

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

theseSlideOut ::
  Either b (Either (Either a (Either c (a, c))) (b, Either a (Either c (a, c)))) ->
  Either b (Either (These a c) (b, These a c))
theseSlideOut (Left b) = Left b
theseSlideOut (Right (Left y)) = Right (Left (eitherToThese y))
theseSlideOut (Right (Right (b, y))) = Right (Right (b, eitherToThese y))

refTheseSlide :: These a (These b c) -> These b (These a c)
refTheseSlide = eitherToThese . theseSlideOut . go . theseToEitherNested'
  where
    go (Left a) = Right (Left (Left a))
    go (Right (Left (Left b))) = Left b
    go (Right (Left (Right (Left c)))) = Right (Left (Right (Left c)))
    go (Right (Left (Right (Right (b, c))))) = Right (Right (b, Right (Left c)))
    go (Right (Right (a, Left b))) = Right (Right (b, Left a))
    go (Right (Right (a, Right (Left c)))) = Right (Left (Right (Right (a, c))))
    go (Right (Right (a, Right (Right (b, c))))) = Right (Right (b, Right (Right (a, c))))

derivedTheseTensorOk :: Bool
derivedTheseTensorOk =
  let f = (+ 1) :: Int -> Int
      g = not
      space = [This 0, This 1, That False, That True, These 0 False, These 1 True]
   in all (\x -> refTheseTensor f g x == tensor f g x) space

derivedTheseUnitlOk :: Bool
derivedTheseUnitlOk =
  let space = [That n | n <- [0, 1, 2]] :: [These Void Int]
   in all (\x -> refTheseUnitl x == unitl x) space

derivedTheseUnitrOk :: Bool
derivedTheseUnitrOk =
  let space = [This n | n <- [0, 1, 2]] :: [These Int Void]
   in all (\x -> refTheseUnitr x == unitr x) space

derivedTheseBraidOk :: Bool
derivedTheseBraidOk =
  let space = [This 0, This 1, That 'a', That 'b', These 0 'a', These 1 'b'] :: [These Int Char]
   in all (\x -> refTheseBraid x == braid x) space

derivedTheseStrengthOk :: Bool
derivedTheseStrengthOk =
  let f = (+ 1) :: Int -> Int
      space = [This 'a', That 0, That 1, These 'a' 0, These 'b' (-1)]
   in all (\x -> refTheseStrength f x == strength f x) space

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

derivedTheseSlideOk :: Bool
derivedTheseSlideOk =
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
   in all (\x -> refTheseSlide x == slide x) space

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
      checkV verbosity "derived These slide agrees with hand-written" derivedTheseSlideOk
    ]
