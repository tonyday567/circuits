module Axioma.Traced
  ( tracedTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (Op (..), id, runK, runOp, (.), (.>))
import Circuit.Syntax (Syntax (..), eval)
import Circuit.Tensor (Action (..), SemiTensor (..), Tensor, superpose)
import Circuit.Trace (Trace)
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Control.Monad (when)
import Data.Bifunctor (first)
import Data.Functor.Identity (Identity (..))
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

theseSlidePresenceOk :: Bool
theseSlidePresenceOk =
  let presenceInput :: These Char (These Char Char) -> (Bool, Bool, Bool)
      presenceInput = \case
        This _ -> (True, False, False)
        That (This _) -> (False, True, False)
        That (That _) -> (False, False, True)
        That (These _ _) -> (False, True, True)
        These _ (This _) -> (True, True, False)
        These _ (That _) -> (True, False, True)
        These _ (These _ _) -> (True, True, True)
      presenceOutput :: These Char (These Char Char) -> (Bool, Bool, Bool)
      presenceOutput = \case
        This _ -> (False, True, False)
        That (This _) -> (True, False, False)
        That (That _) -> (False, False, True)
        That (These _ _) -> (True, False, True)
        These _ (This _) -> (True, True, False)
        These _ (That _) -> (False, True, True)
        These _ (These _ _) -> (True, True, True)
      cases :: [These Char (These Char Char)]
      cases =
        [ This 'a',
          That (This 'b'),
          That (That 'c'),
          That (These 'b' 'c'),
          These 'a' (This 'b'),
          These 'a' (That 'c'),
          These 'a' (These 'b' 'c')
        ]
   in all (\x -> presenceInput x == presenceOutput (slide x)) cases

pairSlideInvolutionOk :: Bool
pairSlideInvolutionOk =
  let x = (1, (2, 3)) :: (Int, (Int, Int))
   in (slide . slide) x == x

eitherSlideInvolutionOk :: Bool
eitherSlideInvolutionOk =
  let l = Left 1 :: Either Int (Either Bool Char)
      m = Right (Left True)
      r = Right (Right 'c')
   in all (\x -> (slide . slide) x == x) [l, m, r]

kIdentitySlideInvolutionOk :: Bool
kIdentitySlideInvolutionOk =
  let x = (1, (2, 3)) :: (Int, (Int, Int))
   in runK (slide . slide) x == Identity x

opSlideInvolutionOk :: Bool
opSlideInvolutionOk =
  let swapTwice :: Op (->) (Int, (Int, Int)) (Int, (Int, Int))
      swapTwice = slide . slide
   in runOp swapTwice (1, (2, 3)) == (1, (2, 3))

theseSlideInvolutionOk :: Bool
theseSlideInvolutionOk =
  let x = These 'a' (These 'b' 'c' :: These Char Char)
   in (slide . slide) x == (x :: These Char (These Char Char))

pairSlideDecomposeOk :: Bool
pairSlideDecomposeOk =
  let decompose :: (Int, (Int, Int)) -> (Int, (Int, Int))
      decompose = assoc' .> tensor braid id .> assoc
      inputs = [(1, (2, 3)), (0, (5, 7))]
   in all (\x -> decompose x == slide x) inputs

eitherSlideDecomposeOk :: Bool
eitherSlideDecomposeOk =
  let decompose :: Either Int (Either Bool Char) -> Either Bool (Either Int Char)
      decompose = assoc' .> tensor braid id .> assoc
      inputs = [Left 1, Right (Left True), Right (Right 'c')]
   in all (\x -> decompose x == slide x) inputs

eitherAssocRoundTripOk :: Bool
eitherAssocRoundTripOk =
  let xs = [Left (Left 1), Left (Right True), Right 'c'] :: [Either (Either Int Bool) Char]
      ys = [Left 1, Right (Left True), Right (Right 'c')] :: [Either Int (Either Bool Char)]
   in all (\x -> (assoc' . assoc) x == x) xs
        && all (\y -> (assoc . assoc') y == y) ys

theseAssocRoundTripOk :: Bool
theseAssocRoundTripOk =
  let xs = [This (This 'a'), This (That True), That 1, These (This 'a') 1] :: [These (These Char Bool) Int]
      ys = [This 'a', That (This True), That (That 1), These 'a' (That 1)] :: [These Char (These Bool Int)]
   in all (\x -> (assoc' . assoc) x == x) xs
        && all (\y -> (assoc . assoc') y == y) ys

pairAssocCancelOk :: Bool
pairAssocCancelOk =
  let y = (1, (2, 3)) :: (Int, (Int, Int))
   in (assoc . assoc') y == y

traceEitherStrengthOk :: Bool
traceEitherStrengthOk =
  let f :: Either Int Int -> Either Int Int
      f (Right n) = Left n
      f (Left 0) = Right 42
      f (Left n) = Left (n - 1)
      t :: Trace Either (->) Int Int
      t = yank (Lift f)
      leftOnly = Left 5 :: Either Int Int
      payload = Right 3 :: Either Int Int
   in eval t 3 == 42
        && eval (strength t) leftOnly == strength (eval t) leftOnly
        && eval (strength t) payload == strength (eval t) payload

superposeEitherFusionOk :: Bool
superposeEitherFusionOk =
  let step :: Either Int Int -> Either Int Int
      step (Right n) = Left n
      step (Left 0) = Right 100
      step (Left n) = Left (n - 1)
      x, y :: Trace Either (->) Int Int
      x = yank (Lift step)
      y = yank (Lift step)
      fallback :: Either Int Int -> Either Int Int
      fallback = tensor (eval x) (eval y)
   in eval (superpose x y) (Left 3) == fallback (Left 3)
        && eval (superpose x y) (Right 5) == fallback (Right 5)

superposeComposedOk :: Bool
superposeComposedOk =
  let k1 :: ([Int], Int) -> ([Int], [Int])
      k1 (ns, x) = (1 : ns, take 3 ns ++ [x])
      composed :: Trace (,) (->) Int [Int]
      composed = yank (Lift k1) . Lift (+ 100)
      other :: Trace (,) (->) Int Int
      other = Lift (* 2)
      fused :: (Int, Int) -> ([Int], Int)
      fused = eval (superpose composed other)
      independent :: (Int, Int) -> ([Int], Int)
      independent = eval (tensor composed other)
   in fused (3, 4) == independent (3, 4)

pairStrengthCoherenceOk :: Bool
pairStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space = [(s, x) | s <- [-2 .. 2], x <- [-2 .. 2]] :: [(Int, Int)]
   in all (\p -> strength f p == tensor id f p) space

eitherStrengthCoherenceOk :: Bool
eitherStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space = [Left 'a', Right 0, Right 1, Left 'b']
   in all (\x -> strength f x == tensor id f x) space

theseStrengthCoherenceOk :: Bool
theseStrengthCoherenceOk =
  let f = (+ 1) :: Int -> Int
      space =
        [ This 'a',
          That 0,
          That 1,
          These 'b' 2,
          These 'c' (-1)
        ]
   in all (\x -> strength f x == tensor id f x) space

uniformitySrcOpen :: Either Void (Either Int Int) -> Either Void (Either Int Int)
uniformitySrcOpen (Right (Right a)) = Right (Left a)
uniformitySrcOpen (Right (Left n)) = Right (Right (if odd n then 7 else 9))
uniformitySrcOpen (Left v) = absurd v

uniformityTgtOpen :: Either Void (Either Bool Int) -> Either Void (Either Bool Int)
uniformityTgtOpen (Right (Right a)) = Right (Left (odd a))
uniformityTgtOpen (Right (Left b)) = Right (Right (if b then 7 else 9))
uniformityTgtOpen (Left v) = absurd v

uniformityHypothesisOk :: Bool
uniformityHypothesisOk =
  let h :: Either Int Int -> Either Bool Int
      h = first odd
      payloadSpace :: [Either Void (Either Int Int)]
      payloadSpace = map Right [Right 0, Right 1, Right 2, Left 0, Left 1, Left 2]
   in all (\x -> fmap h (uniformitySrcOpen x) == uniformityTgtOpen (fmap h x)) payloadSpace

uniformitySrcClosed :: Either (Either Void Int) Int -> Either (Either Void Int) Int
uniformitySrcClosed = assoc .> uniformitySrcOpen .> assoc'

uniformityTgtClosed :: Either (Either Void Bool) Int -> Either (Either Void Bool) Int
uniformityTgtClosed = assoc .> uniformityTgtOpen .> assoc'

uniformityOk :: Bool
uniformityOk =
  let traceOk = all (\n -> yank uniformitySrcClosed n == yank uniformityTgtClosed n) [0 .. 3]
   in uniformityHypothesisOk && traceOk

data Z3 = Z0 | Z1 | Z2
  deriving (Eq, Show)

nextZ3 :: Z3 -> Z3
nextZ3 Z0 = Z1
nextZ3 Z1 = Z2
nextZ3 Z2 = Z0

slidingF :: Either Void (Either Z3 Int) -> Either Void (Either Z3 Int)
slidingF (Right (Right a))
  | even a = Right (Left Z0)
slidingF (Right (Right _)) = Right (Left Z1)
slidingF (Right (Left Z0)) = Right (Right 10)
slidingF (Right (Left Z1)) = Right (Right 20)
slidingF (Right (Left Z2)) = Right (Right 30)
slidingF (Left v) = absurd v

slidingH :: Either Void (Either Z3 Int) -> Either Void (Either Z3 Int)
slidingH (Right (Left z)) = Right (Left (nextZ3 z))
slidingH (Right (Right a)) = Right (Right a)
slidingH (Left v) = absurd v

slidingLhsClosed, slidingRhsClosed :: Either (Either Void Z3) Int -> Either (Either Void Z3) Int
slidingLhsClosed = assoc .> (slidingH . slidingF) .> assoc'
slidingRhsClosed = assoc .> (slidingF . slidingH) .> assoc'

slidingOk :: Bool
slidingOk =
  all (\n -> yank slidingLhsClosed n == yank slidingRhsClosed n) [0 .. 3]

tracedTopic :: Verbosity -> IO [Bool]
tracedTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Traced oracles: base structural laws and their composite spends"
  sequence
    [ checkV verbosity "Channel These slide preserves presence on all 7 cases" theseSlidePresenceOk,
      checkV verbosity "Channel (,) slide . slide == id" pairSlideInvolutionOk,
      checkV verbosity "Channel Either slide . slide == id on all three injections" eitherSlideInvolutionOk,
      checkV verbosity "Channel K Identity slide . slide == id" kIdentitySlideInvolutionOk,
      checkV verbosity "Channel Op slide . slide == id pointwise (the Op instance spends involution)" opSlideInvolutionOk,
      checkV verbosity "Channel These slide . slide == id where types permit" theseSlideInvolutionOk,
      checkV verbosity "slide decomposes as assoc' . tensor braid id . assoc at (,)" pairSlideDecomposeOk,
      checkV verbosity "slide decomposes as assoc' . tensor braid id . assoc at Either" eitherSlideDecomposeOk,
      checkV verbosity "associator round trip at Either in both directions" eitherAssocRoundTripOk,
      checkV verbosity "associator round trip at These in both directions" theseAssocRoundTripOk,
      checkV verbosity "Channel (,) assoc . assoc' == id (the half not doctested)" pairAssocCancelOk,
      checkV verbosity "Trace Either strength: eval-then-strengthen == strengthen-then-eval" traceEitherStrengthOk,
      checkV verbosity "superpose fusion agrees with the fallback on the Either tensor" superposeEitherFusionOk,
      checkV verbosity "superpose composed shape agrees with independent evaluation" superposeComposedOk,
      checkV verbosity "strength coherence (strength f == tensor id f)" pairStrengthCoherenceOk,
      checkV verbosity "Either strength coherence (strength f == tensor id f)" eitherStrengthCoherenceOk,
      checkV verbosity "These strength coherence (strength f == tensor id f)" theseStrengthCoherenceOk,
      checkV verbosity "Either uniformity: feedback respects non-injective two-cell" uniformityOk,
      checkV verbosity "Either sliding (dinaturality) for isomorphism" slidingOk
    ]
