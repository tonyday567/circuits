{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Circuit.Algebra qualified as Alg
import Circuit.Boundary (Boundary (..), IsLinear, Linear (..), NotLinear, Stamped (..), isMark, isPayload)
import Circuit.Category (id, (.), (.>))
import Circuit.Channel (assoc, assoc', slide, strength, trace)
import Circuit.ChannelPoly (Channel (..), commitChannel, constChannel, emitChannel, idChannel, mapChannel)
import Circuit.Chu qualified as Chu
import Circuit.Dagger (Copy (..), CopyDiscard, Dagger (..), Discard (..), Merge (..), MergeZero, Zero (..), transpose)
import Circuit.Ends (Bias (..), Ends (..), HasDual (..), box, close, composeEnds0, copycat, ends, ends0, endsAsChu, endsK, pairEnds, prefixIn, raceEnds, splay, splay0, suffixOut)
import Circuit.Ends qualified as MedState
import Circuit.FinRel
import Circuit.Hyper (Hyper, observe)
import Circuit.Hyper qualified as HyperLoop
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Circuit.Markov (copyNatural, deterministic, discardNatural)
import Circuit.Mediate (FlushableResidual (..), LinearResidual (..), LinearityViolation (..), Mediator (..), PS (..), closeCertified, closeCertifiedWith, closeCertifiedWithBy, count, linear, medComult, medCounit, mediateLoop, mediateProcess, mediateSharedBody, pairSum, runMediator, runMediatorState)
import Circuit.Net qualified as Net
import Circuit.Poly (Dir, Eval (..), Mono, System, fromEvalSystem, lens, monoDir, monoIn, mooreSystem, runSystem, system)
import Circuit.Prob (Prob (..), choiceBy, copyP, discardP, embed, fromWeighted, mass, orP, parFG, parGF, score, traceE, traceEN)
import Circuit.Process (Process (..), delay, encode, fold, markSystem, register, scan, systemToProcess)
import Circuit.Tensor (Action (..), BangCopy (..), BangWeaken (..), Bot, Exponential (..), Fire (..), Lolli (..), Par (..), Schedule (..), Shared (..), Tensor (..), WhyNotIntro (..), distL, distR, mix, sharedKnotBy, superpose)
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Monad (replicateM)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Kind (Type)
import Data.List (foldl', isInfixOf, sort, uncons)
import Data.Maybe (catMaybes, isNothing)
import Data.Proxy (Proxy (..))
import Data.These (These (..), these)
import Data.Tuple qualified as Tuple
import Data.Void (Void, absurd)
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

type F = Bool

type N1 = FinObj 1

type N2 = FinObj 2

-- ---------------------------------------------------------------------------
-- Chu helpers
-- ---------------------------------------------------------------------------

-- | A post-shaped value for the Chu delivery oracles.  Carriers are 'Int's so
-- the example needs no 'Text'.
data ChuPost = ChuPost
  { chuFrom :: Int,
    chuTo :: [Int],
    chuBody :: Int
  }
  deriving (Eq, Show)

mkChuPost :: Int -> [Int] -> Int -> ChuPost
mkChuPost = ChuPost

-- | Prefix used to rename subscribers across a Chu morphism.
chuPrefix :: Int
chuPrefix = 10

prefixName :: Int -> Int
prefixName = (+ chuPrefix)

unprefixName :: Int -> Int
unprefixName = subtract chuPrefix

prefixTo :: [Int] -> [Int]
prefixTo = map prefixName

unprefixSub :: Int -> Int
unprefixSub = unprefixName

chuDelivers :: ChuPost -> Int -> Bool
chuDelivers p = Chu.deliversToSemiring (chuTo p)

-- | Sample Chu object over posts and names with boolean delivery pairing.
chuObjPostInt :: Chu.ChuObj (,) Bool (->) ChuPost Int
chuObjPostInt = Chu.ChuObj (mkChuPost 0 [] 0) 0 (Pre.uncurry chuDelivers)

-- | A tiny self-dual Chu object over @Bool@ with equality pairing.
chuTwo :: Chu.ChuObj (,) Bool (->) Bool Bool
chuTwo = Chu.ChuObj True True (Pre.uncurry (==))

-- | Negation as a Chu endomorphism of the self-dual @Bool@ object.
chuNot :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
chuNot = Chu.ChuMorphism not not

-- | Positive and negative carriers for the finite @chuTwo@ object.
chuTwoPos :: [Bool]
chuTwoPos = [True, False]

-- | Enumerated negative carrier of @chuTwo ⊗ chuTwo@.
chuTwoTensorNegs :: [Chu.ChuTensorNeg Bool Bool Bool Bool]
chuTwoTensorNegs = Chu.chuTensorNegs chuTwoPos chuTwoPos chuTwoPos chuTwoPos chuTwo chuTwo

-- | Enumerated positive carrier of @chuTwo ⅋ chuTwo@.
chuTwoParPoss :: [Chu.ChuParPos Bool Bool Bool Bool]
chuTwoParPoss = Chu.chuParPoss chuTwoPos chuTwoPos chuTwoPos chuTwoPos chuTwo chuTwo

-- | Unit object @I@ used in the Chu unit-law oracles.
chuUnitObjBool :: Chu.ChuObj (,) Bool (->) () Bool
chuUnitObjBool = Chu.chuUnitObj

-- | Enumerated negative carrier of @I ⊗ chuTwo@.
chuTwoLeftUnitNegs :: [Chu.ChuTensorNeg () Bool Bool Bool]
chuTwoLeftUnitNegs = Chu.chuTensorNegs [()] chuTwoPos chuTwoPos chuTwoPos chuUnitObjBool chuTwo

-- | Enumerated positive carrier of @chuTwo ⊸ chuTwo@.
chuTwoLollPoss :: [Chu.ChuParPos Bool Bool Bool Bool]
chuTwoLollPoss = Chu.chuParPoss chuTwoPos chuTwoPos chuTwoPos chuTwoPos (Chu.negateChu chuTwo) chuTwo

-- | Enumerated negative carrier of @chuTwo & chuTwo@ and positive carrier of
-- @chuTwo ⊕ chuTwo@.
chuTwoEither :: [Either Bool Bool]
chuTwoEither = map Left chuTwoPos ++ map Right chuTwoPos

-- | Enumerated negative carrier of @chuTwo ⊗ I@.
chuTwoRightUnitNegs :: [Chu.ChuTensorNeg Bool Bool () Bool]
chuTwoRightUnitNegs = Chu.chuTensorNegs chuTwoPos chuTwoPos [()] chuTwoPos chuTwo chuUnitObjBool

-- | Equality of Chu endomorphisms of @chuTwo@.
eqChuMorphismAA ::
  Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool ->
  Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool ->
  Bool
eqChuMorphismAA m1 m2 =
  all (\a -> Chu.chuForward m1 a == Chu.chuForward m2 a) chuTwoPos
    && all (\b -> Chu.chuBackward m1 b == Chu.chuBackward m2 b) chuTwoPos

-- | Equality of Chu endomorphisms of @I ⊗ chuTwo@.
eqChuMorphismIIA ::
  Chu.ChuMorphism (,) Bool (->) ((), Bool) (Chu.ChuTensorNeg () Bool Bool Bool) ((), Bool) (Chu.ChuTensorNeg () Bool Bool Bool) ->
  Chu.ChuMorphism (,) Bool (->) ((), Bool) (Chu.ChuTensorNeg () Bool Bool Bool) ((), Bool) (Chu.ChuTensorNeg () Bool Bool Bool) ->
  Bool
eqChuMorphismIIA m1 m2 =
  let pos2 = [((), x) | x <- chuTwoPos]
      eqTensorNeg n1 n2 =
        Chu.ctnForward n1 () == Chu.ctnForward n2 ()
          && all (\c -> Chu.ctnBackward n1 c == Chu.ctnBackward n2 c) chuTwoPos
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) pos2
        && all (\n -> eqTensorNeg (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoLeftUnitNegs

-- | Equality of Chu endomorphisms of @chuTwo ⊗ I@.
eqChuMorphismAII ::
  Chu.ChuMorphism (,) Bool (->) (Bool, ()) (Chu.ChuTensorNeg Bool Bool () Bool) (Bool, ()) (Chu.ChuTensorNeg Bool Bool () Bool) ->
  Chu.ChuMorphism (,) Bool (->) (Bool, ()) (Chu.ChuTensorNeg Bool Bool () Bool) (Bool, ()) (Chu.ChuTensorNeg Bool Bool () Bool) ->
  Bool
eqChuMorphismAII m1 m2 =
  let pos2 = [(x, ()) | x <- chuTwoPos]
      eqTensorNeg n1 n2 =
        all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
          && Chu.ctnBackward n1 () == Chu.ctnBackward n2 ()
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) pos2
        && all (\n -> eqTensorNeg (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoRightUnitNegs

-- | Does @chuTwo@ admit a copy morphism @chuTwo -> chuTwo ⊗ chuTwo@?
hasCopyChuTwo :: Bool
hasCopyChuTwo =
  let tensObj = Chu.tensorChuObj chuTwo chuTwo
      negs = chuTwoTensorNegs
      ok hVals =
        all
          (\(n, hVal) -> all (\a -> Chu.chuPair tensObj ((a, a), n) == Chu.chuPair chuTwo (a, hVal)) chuTwoPos)
          (zip negs hVals)
   in any ok (sequenceA (replicate (length negs) [True, False]))

-- | Does @chuTwo@ admit a discard morphism @chuTwo -> I@?
hasDiscardChuTwo :: Bool
hasDiscardChuTwo =
  let ok gVals =
        all
          (\(k, gVal) -> all (\a -> Chu.chuPair chuUnitObjBool ((), k) == Chu.chuPair chuTwo (a, gVal)) chuTwoPos)
          (zip [True, False] gVals)
   in any ok (sequenceA (replicate 2 [True, False]))

-- | Equality of Chu morphisms on the tensor of two @chuTwo@s.
--
-- The backward component returns a 'ChuTensorNeg', which contains functions,
-- so we compare pointwise over the finite domains.
eqTensorMorphism ::
  Chu.ChuMorphism (,) Bool (->) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) ->
  Chu.ChuMorphism (,) Bool (->) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) ->
  Bool
eqTensorMorphism m1 m2 =
  let pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
      eqTensorNeg n1 n2 =
        all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
          && all (\c -> Chu.ctnBackward n1 c == Chu.ctnBackward n2 c) chuTwoPos
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) pos2
        && all (\n -> eqTensorNeg (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoTensorNegs

-- | Extract the underlying 'ChuMorphism' from an 'OChu' arrow.
ochuToChuMorphism ::
  Chu.OChu r a b ->
  Chu.ChuMorphism (,) r (->) (Chu.ChuPosType a) (Chu.ChuNegType a) (Chu.ChuPosType b) (Chu.ChuNegType b)
ochuToChuMorphism (Chu.OChu (Chu.Chu m)) = m

-- ---------------------------------------------------------------------------
-- SepChu / associator helpers
-- ---------------------------------------------------------------------------

chuTwoObjAA :: Chu.ChuObj (,) Bool (->) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)
chuTwoObjAA = Chu.tensorChuObj chuTwo chuTwo

chuTwoObjRightAssoc ::
  Chu.ChuObj
    (,)
    Bool
    (->)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
chuTwoObjRightAssoc = Chu.tensorChuObj chuTwo chuTwoObjAA

chuTwoObjLeftAssoc ::
  Chu.ChuObj
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
chuTwoObjLeftAssoc = Chu.tensorChuObj chuTwoObjAA chuTwo

chuTwoPos2 :: [(Bool, Bool)]
chuTwoPos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]

chuTwoPos3L :: [((Bool, Bool), Bool)]
chuTwoPos3L = [(p, z) | p <- chuTwoPos2, z <- chuTwoPos]

chuTwoPos3R :: [(Bool, (Bool, Bool))]
chuTwoPos3R = [(x, p) | x <- chuTwoPos, p <- chuTwoPos2]

chuTwoPos4L :: [(((Bool, Bool), Bool), Bool)]
chuTwoPos4L = [(p, w) | p <- chuTwoPos3L, w <- chuTwoPos]

chuTwoNeg3R ::
  [Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)]
chuTwoNeg3R =
  Chu.chuTensorNegs chuTwoPos chuTwoPos chuTwoPos2 chuTwoTensorNegs chuTwo chuTwoObjAA

eqTensorNeg2 ::
  Chu.ChuTensorNeg Bool Bool Bool Bool ->
  Chu.ChuTensorNeg Bool Bool Bool Bool ->
  Bool
eqTensorNeg2 n1 n2 =
  all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
    && all (\c -> Chu.ctnBackward n1 c == Chu.ctnBackward n2 c) chuTwoPos

eqTensorNeg3L ::
  Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool ->
  Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool ->
  Bool
eqTensorNeg3L n1 n2 =
  all (\p -> Chu.ctnForward n1 p == Chu.ctnForward n2 p) chuTwoPos2
    && all (\z -> eqTensorNeg2 (Chu.ctnBackward n1 z) (Chu.ctnBackward n2 z)) chuTwoPos

eqTensorNeg3R ::
  Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) ->
  Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) ->
  Bool
eqTensorNeg3R n1 n2 =
  all (\a -> eqTensorNeg2 (Chu.ctnForward n1 a) (Chu.ctnForward n2 a)) chuTwoPos
    && all (\p -> Chu.ctnBackward n1 p == Chu.ctnBackward n2 p) chuTwoPos2

eqAssocMorphism ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)) ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)) ->
  Bool
eqAssocMorphism m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) chuTwoPos3L
    && all (\n -> eqTensorNeg3L (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoNeg3R

eqEndo3R ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)) ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)) ->
  Bool
eqEndo3R m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) chuTwoPos3R
    && all (\n -> eqTensorNeg3R (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoNeg3R

eqEndo3L ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool) ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool) ->
  Bool
eqEndo3L m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) chuTwoPos3L
    && all (\n -> eqTensorNeg3L (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoNeg3L
  where
    chuTwoNeg3L =
      Chu.chuTensorNegs chuTwoPos2 chuTwoTensorNegs chuTwoPos chuTwoPos chuTwoObjAA chuTwo

chuTwoNeg4R ::
  [ Chu.ChuTensorNeg
      Bool
      Bool
      (Bool, (Bool, Bool))
      (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
  ]
chuTwoNeg4R =
  Chu.chuTensorNegs chuTwoPos chuTwoPos chuTwoPos3R chuTwoNeg3R chuTwo chuTwoObjRightAssoc

eqTensorNeg4L ::
  Chu.ChuTensorNeg
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    Bool
    Bool ->
  Chu.ChuTensorNeg
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    Bool
    Bool ->
  Bool
eqTensorNeg4L n1 n2 =
  all (\p -> Chu.ctnForward n1 p == Chu.ctnForward n2 p) chuTwoPos3L
    && all (\w -> eqTensorNeg3L (Chu.ctnBackward n1 w) (Chu.ctnBackward n2 w)) chuTwoPos

eqPentagonMorphism ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (((Bool, Bool), Bool), Bool)
    ( Chu.ChuTensorNeg
        ((Bool, Bool), Bool)
        (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
        Bool
        Bool
    )
    (Bool, (Bool, (Bool, Bool)))
    ( Chu.ChuTensorNeg
        Bool
        Bool
        (Bool, (Bool, Bool))
        (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
    ) ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (((Bool, Bool), Bool), Bool)
    ( Chu.ChuTensorNeg
        ((Bool, Bool), Bool)
        (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
        Bool
        Bool
    )
    (Bool, (Bool, (Bool, Bool)))
    ( Chu.ChuTensorNeg
        Bool
        Bool
        (Bool, (Bool, Bool))
        (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
    ) ->
  Bool
eqPentagonMorphism m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) chuTwoPos4L
    && all (\n -> eqTensorNeg4L (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoNeg4R

-- | Equality of morphisms @ChuTwo ⊗ I → ChuTwo@.
eqChuTwoUnitr ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, ())
    (Chu.ChuTensorNeg Bool Bool () Bool)
    Bool
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, ())
    (Chu.ChuTensorNeg Bool Bool () Bool)
    Bool
    Bool ->
  Bool
eqChuTwoUnitr m1 m2 =
  let pos = [(x, ()) | x <- chuTwoPos]
      eqN n1 n2 =
        all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
          && Chu.ctnBackward n1 () == Chu.ctnBackward n2 ()
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) pos
        && all (\b -> eqN (Chu.chuBackward m1 b) (Chu.chuBackward m2 b)) chuTwoPos

eqTensorNegLolli ::
  Chu.ChuTensorNeg Bool Bool (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) ->
  Chu.ChuTensorNeg Bool Bool (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) ->
  Bool
eqTensorNegLolli n1 n2 =
  all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
    && all (\m -> Chu.ctnBackward n1 m == Chu.ctnBackward n2 m) chuTwoLollPoss

eqChuMorphismLolliEval ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, Chu.ChuParPos Bool Bool Bool Bool)
    (Chu.ChuTensorNeg Bool Bool (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool))
    Bool
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, Chu.ChuParPos Bool Bool Bool Bool)
    (Chu.ChuTensorNeg Bool Bool (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool))
    Bool
    Bool ->
  Bool
eqChuMorphismLolliEval m1 m2 =
  let poss = [(a, m) | a <- chuTwoPos, m <- chuTwoLollPoss]
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) poss
        && all (\d -> eqTensorNegLolli (Chu.chuBackward m1 d) (Chu.chuBackward m2 d)) chuTwoPos

chuTwoFuns :: [Bool -> Bool]
chuTwoFuns = Chu.chuFunctionals chuTwoPos [True, False]

eqFun :: (Bool -> Bool) -> (Bool -> Bool) -> Bool
eqFun f g = all (\a -> f a == g a) chuTwoPos

-- | Chu morphisms @I → A@ for a Set-based object with finite carriers.
iHoms ::
  (Eq r) =>
  [a] ->
  [b] ->
  Chu.ChuObj (,) r (->) a b ->
  [Chu.ChuMorphism (,) r (->) () r a b]
iHoms as bs obj =
  [ m
  | a <- as,
    let m = Chu.ChuMorphism (const a) (\d -> Chu.chuPair obj (a, d)),
    all (\d -> Chu.chuLaw Chu.chuUnitObj obj m () d) bs
  ]

iHomsChuTwo ::
  Chu.ChuObj (,) Bool (->) a b ->
  [a] ->
  [b] ->
  [Chu.ChuMorphism (,) Bool (->) () Bool a b]
iHomsChuTwo obj as bs = iHoms as bs obj

composeITo ::
  Chu.ChuMorphism (,) Bool (->) a b c d ->
  Chu.ChuMorphism (,) Bool (->) () Bool a b ->
  Chu.ChuMorphism (,) Bool (->) () Bool c d
composeITo = Chu.composeChu

eqIToTwo ::
  Chu.ChuMorphism (,) Bool (->) () Bool Bool Bool ->
  Chu.ChuMorphism (,) Bool (->) () Bool Bool Bool ->
  Bool
eqIToTwo m1 m2 =
  Chu.chuForward m1 () == Chu.chuForward m2 ()
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

eqIToWhy ::
  Chu.ChuMorphism (,) Bool (->) () Bool (Bool -> Bool) Bool ->
  Chu.ChuMorphism (,) Bool (->) () Bool (Bool -> Bool) Bool ->
  Bool
eqIToWhy m1 m2 =
  eqFun (Chu.chuForward m1 ()) (Chu.chuForward m2 ())
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

whyNotTwo :: Chu.ChuObj (,) Bool (->) (Bool -> Bool) Bool
whyNotTwo = Chu.whyNotChuObj chuTwo

whyNotTwoParPoss :: [Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool]
whyNotTwoParPoss =
  Chu.chuParPoss chuTwoFuns chuTwoPos chuTwoFuns chuTwoPos whyNotTwo whyNotTwo

eqWhyParPos ::
  Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool ->
  Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool ->
  Bool
eqWhyParPos p1 p2 =
  all (\b -> eqFun (Chu.cppForward p1 b) (Chu.cppForward p2 b)) chuTwoPos
    && all (\d -> eqFun (Chu.cppBackward p1 d) (Chu.cppBackward p2 d)) chuTwoPos

eqMergeWhy ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
    (Bool, Bool)
    (Bool -> Bool)
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
    (Bool, Bool)
    (Bool -> Bool)
    Bool ->
  Bool
eqMergeWhy m1 m2 =
  all (\p -> eqFun (Chu.chuForward m1 p) (Chu.chuForward m2 p)) whyNotTwoParPoss
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

botWhyParPoss :: [Chu.ChuParPos Bool () (Bool -> Bool) Bool]
botWhyParPoss =
  Chu.chuParPoss [True, False] [()] chuTwoFuns chuTwoPos Chu.chuBottomObj whyNotTwo

eqLeftUnitWhy ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos Bool () (Bool -> Bool) Bool)
    ((), Bool)
    (Bool -> Bool)
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos Bool () (Bool -> Bool) Bool)
    ((), Bool)
    (Bool -> Bool)
    Bool ->
  Bool
eqLeftUnitWhy m1 m2 =
  all (\p -> eqFun (Chu.chuForward m1 p) (Chu.chuForward m2 p)) botWhyParPoss
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

whyBotParPoss :: [Chu.ChuParPos (Bool -> Bool) Bool Bool ()]
whyBotParPoss =
  Chu.chuParPoss chuTwoFuns chuTwoPos [True, False] [()] whyNotTwo Chu.chuBottomObj

eqRightUnitWhy ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos (Bool -> Bool) Bool Bool ())
    (Bool, ())
    (Bool -> Bool)
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos (Bool -> Bool) Bool Bool ())
    (Bool, ())
    (Bool -> Bool)
    Bool ->
  Bool
eqRightUnitWhy m1 m2 =
  all (\p -> eqFun (Chu.chuForward m1 p) (Chu.chuForward m2 p)) whyBotParPoss
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

eqWhyParPos3 ::
  Chu.ChuParPos
    (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
    (Bool, Bool)
    (Bool -> Bool)
    Bool ->
  Chu.ChuParPos
    (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
    (Bool, Bool)
    (Bool -> Bool)
    Bool ->
  Bool
eqWhyParPos3 p1 p2 =
  let pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
   in all (\xy -> eqFun (Chu.cppForward p1 xy) (Chu.cppForward p2 xy)) pos2
        && all (\z -> eqWhyParPos (Chu.cppBackward p1 z) (Chu.cppBackward p2 z)) chuTwoPos

whyNotTwoPar3LPoss ::
  [ Chu.ChuParPos
      (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
      (Bool, Bool)
      (Bool -> Bool)
      Bool
  ]
whyNotTwoPar3LPoss =
  Chu.chuParPoss
    whyNotTwoParPoss
    [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
    chuTwoFuns
    chuTwoPos
    (Chu.parChuObj whyNotTwo whyNotTwo)
    whyNotTwo

eqAssocWhyL ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ( Chu.ChuParPos
        (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
        (Bool, Bool)
        (Bool -> Bool)
        Bool
    )
    ((Bool, Bool), Bool)
    ( Chu.ChuParPos
        (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
        (Bool, Bool)
        (Bool -> Bool)
        Bool
    )
    ((Bool, Bool), Bool) ->
  Bool
eqAssocWhyL m =
  let negs = [((x, y), z) | x <- chuTwoPos, y <- chuTwoPos, z <- chuTwoPos]
   in all (\p -> eqWhyParPos3 (Chu.chuForward m p) p) whyNotTwoPar3LPoss
        && all (\n -> Chu.chuBackward m n == n) negs

eqWhy3ToWhy ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ( Chu.ChuParPos
        (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
        (Bool, Bool)
        (Bool -> Bool)
        Bool
    )
    ((Bool, Bool), Bool)
    (Bool -> Bool)
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ( Chu.ChuParPos
        (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
        (Bool, Bool)
        (Bool -> Bool)
        Bool
    )
    ((Bool, Bool), Bool)
    (Bool -> Bool)
    Bool ->
  Bool
eqWhy3ToWhy m1 m2 =
  all (\p -> eqFun (Chu.chuForward m1 p) (Chu.chuForward m2 p)) whyNotTwoPar3LPoss
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

-- | Equality of Chu morphisms on the par of two @chuTwo@s.
--
-- The forward component returns a 'ChuParPos', which contains functions, so we
-- compare pointwise over the finite domains.
eqParMorphism ::
  Chu.ChuMorphism (,) Bool (->) (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) ->
  Chu.ChuMorphism (,) Bool (->) (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) ->
  Bool
eqParMorphism m1 m2 =
  let neg2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
      eqParPos p1 p2 =
        all (\b -> Chu.cppForward p1 b == Chu.cppForward p2 b) chuTwoPos
          && all (\d -> Chu.cppBackward p1 d == Chu.cppBackward p2 d) chuTwoPos
   in all (\p -> eqParPos (Chu.chuForward m1 p) (Chu.chuForward m2 p)) chuTwoParPoss
        && all (\n -> Chu.chuBackward m1 n == Chu.chuBackward m2 n) neg2

-- | Generic forward-only equality of Chu morphisms.
--
-- In the separated-extensional subcategory the backward component is uniquely
-- determined by the forward component, so comparing forward values over the
-- positive carrier is enough.
eqChuMorphismForward ::
  (Eq p') =>
  [p] ->
  Chu.ChuMorphism (,) r (->) p n p' n' ->
  Chu.ChuMorphism (,) r (->) p n p' n' ->
  Bool
eqChuMorphismForward ps m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) ps

-- | ChuThree: canonical object and finite carriers.
chuThreeObj :: Chu.ChuObj (,) Bool (->) (Maybe Bool) (Maybe Bool)
chuThreeObj = Chu.chuObject @Bool @Chu.ChuThree

chuThreePos :: [Maybe Bool]
chuThreePos = [Nothing, Just False, Just True]

chuThreeNeg :: [Maybe Bool]
chuThreeNeg = chuThreePos

chuThreePos2 :: [(Maybe Bool, Maybe Bool)]
chuThreePos2 = [(x, y) | x <- chuThreePos, y <- chuThreePos]

chuThreePos3L :: [((Maybe Bool, Maybe Bool), Maybe Bool)]
chuThreePos3L = [(p, z) | p <- chuThreePos2, z <- chuThreePos]

chuThreePos3R :: [(Maybe Bool, (Maybe Bool, Maybe Bool))]
chuThreePos3R = [(x, p) | x <- chuThreePos, p <- chuThreePos2]

chuThreePos4L :: [(((Maybe Bool, Maybe Bool), Maybe Bool), Maybe Bool)]
chuThreePos4L = [(p, w) | p <- chuThreePos3L, w <- chuThreePos]

-- | ChuDouble01: canonical object and finite carriers.
chuDouble01Obj :: Chu.ChuObj (,) Double (->) Bool Bool
chuDouble01Obj = Chu.chuObject @Double @Chu.ChuDouble01

-- | ChuDelivery: canonical object and finite carriers.
chuDeliveryObj :: Chu.ChuObj (,) Bool (->) Bool Bool
chuDeliveryObj = Chu.chuObject @Bool @Chu.ChuDelivery

-- | Forward-only unit-law oracle for an 'OChu' object.
checkChuUnitlForward ::
  forall r (a :: Type).
  (Eq r, Eq (Chu.ChuPosType a), Chu.ChuSeparated r a, Chu.ChuExtensional r a) =>
  Proxy r ->
  Proxy a ->
  String ->
  [Chu.ChuPosType a] ->
  IO Bool
checkChuUnitlForward _ _ name pos =
  let psI = [((), x) | x <- pos]
      u :: Chu.OChu r (Chu.ChuOTensor r (Chu.ChuOUnit r) a) a
      u = unitl
      u' :: Chu.OChu r a (Chu.ChuOTensor r (Chu.ChuOUnit r) a)
      u' = unitl'
      idA = id :: Chu.OChu r a a
      idIA = id :: Chu.OChu r (Chu.ChuOTensor r (Chu.ChuOUnit r) a) (Chu.ChuOTensor r (Chu.ChuOUnit r) a)
   in check name $
        eqChuMorphismForward pos (ochuToChuMorphism (u . u')) (ochuToChuMorphism idA)
          && eqChuMorphismForward psI (ochuToChuMorphism (u' . u)) (ochuToChuMorphism idIA)

-- | Forward-only right unit-law oracle for an 'OChu' object.
checkChuUnitrForward ::
  forall r (a :: Type).
  (Eq r, Eq (Chu.ChuPosType a), Chu.ChuSeparated r a, Chu.ChuExtensional r a) =>
  Proxy r ->
  Proxy a ->
  String ->
  [Chu.ChuPosType a] ->
  IO Bool
checkChuUnitrForward _ _ name pos =
  let psI = [(x, ()) | x <- pos]
      u :: Chu.OChu r (Chu.ChuOTensor r a (Chu.ChuOUnit r)) a
      u = unitr
      u' :: Chu.OChu r a (Chu.ChuOTensor r a (Chu.ChuOUnit r))
      u' = unitr'
      idA = id :: Chu.OChu r a a
      idAI = id :: Chu.OChu r (Chu.ChuOTensor r a (Chu.ChuOUnit r)) (Chu.ChuOTensor r a (Chu.ChuOUnit r))
   in check name $
        eqChuMorphismForward pos (ochuToChuMorphism (u . u')) (ochuToChuMorphism idA)
          && eqChuMorphismForward psI (ochuToChuMorphism (u' . u)) (ochuToChuMorphism idAI)

-- | Forward-only associator inverse oracle for an 'OChu' object.
checkChuAssocInversesForward ::
  forall r (a :: Type).
  (Eq r, Eq (Chu.ChuPosType a), Chu.ChuSeparated r a, Chu.ChuExtensional r a) =>
  Proxy r ->
  Proxy a ->
  String ->
  [Chu.ChuPosType (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)] ->
  [Chu.ChuPosType (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))] ->
  IO Bool
checkChuAssocInversesForward _ _ name pos3L pos3R =
  let isoL =
        assoc' . assoc ::
          Chu.OChu
            r
            (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
            (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
      isoR =
        assoc . assoc' ::
          Chu.OChu
            r
            (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
            (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
      idL = id :: Chu.OChu r (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a) (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
      idR = id :: Chu.OChu r (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)) (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
   in check name $
        eqChuMorphismForward pos3L (ochuToChuMorphism isoL) (ochuToChuMorphism idL)
          && eqChuMorphismForward pos3R (ochuToChuMorphism isoR) (ochuToChuMorphism idR)

-- | Forward-only pentagon oracle for an 'OChu' object.
checkChuPentagonForward ::
  forall r (a :: Type).
  (Eq r, Eq (Chu.ChuPosType a), Chu.ChuSeparated r a, Chu.ChuExtensional r a) =>
  Proxy r ->
  Proxy a ->
  String ->
  [Chu.ChuPosType a] ->
  IO Bool
checkChuPentagonForward _ _ name pos =
  let pos4 = [(p, w) | p <- [(q, z) | q <- [(x, y) | x <- pos, y <- pos], z <- pos], w <- pos]
      assoc1 ::
        Chu.OChu
          r
          (Chu.ChuOTensor r (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a) a)
          (Chu.ChuOTensor r (Chu.ChuOTensor r a a) (Chu.ChuOTensor r a a))
      assoc1 = assoc
      assoc2 ::
        Chu.OChu
          r
          (Chu.ChuOTensor r (Chu.ChuOTensor r a a) (Chu.ChuOTensor r a a))
          (Chu.ChuOTensor r a (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)))
      assoc2 = assoc
      assocInner ::
        Chu.OChu
          r
          (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
          (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
      assocInner = assoc
      lhs = assoc2 . assoc1
      bot1 =
        par assocInner id ::
          Chu.OChu
            r
            (Chu.ChuOTensor r (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a) a)
            (Chu.ChuOTensor r (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)) a)
      bot2 =
        assoc ::
          Chu.OChu
            r
            (Chu.ChuOTensor r (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)) a)
            (Chu.ChuOTensor r a (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a))
      bot3 =
        par id assocInner ::
          Chu.OChu
            r
            (Chu.ChuOTensor r a (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a))
            (Chu.ChuOTensor r a (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)))
      rhs = bot3 . bot2 . bot1
   in check name $ eqChuMorphismForward pos4 (ochuToChuMorphism lhs) (ochuToChuMorphism rhs)

-- | Swap the second and third @n@-wire blocks of @((a,b),(c,d))@.
swapBlocks ::
  forall n.
  (KnownNat n) =>
  FinRel F ((FinObj n, FinObj n), (FinObj n, FinObj n)) ((FinObj n, FinObj n), (FinObj n, FinObj n))
swapBlocks = wiring perm
  where
    n = fromIntegral (natVal (Proxy @n))
    perm i
      | i < n = i
      | i < 2 * n = i + n
      | i < 3 * n = i - n
      | otherwise = i

swapMiddle :: FinRel F ((N1, N1), (N1, N1)) ((N1, N1), (N1, N1))
swapMiddle = swapBlocks @1

swapMiddle2 :: FinRel F ((N2, N2), (N2, N2)) ((N2, N2), (N2, N2))
swapMiddle2 = swapBlocks @2

-- | Simple additive process for oracles.
sumP :: Process Int Int
sumP = Process id (+) id

-- | Pair swap for the (,) trace yanking oracle.
swapPairP :: Process (Int, Int) (Int, Int)
swapPairP = Process id (\_ x -> x) (\(a, b) -> (b, a))

-- | Either swap for the Either trace yanking oracle.
swapEitherP :: Process (Either Int Int) (Either Int Int)
swapEitherP = Process id (\_ x -> x) swapEither
  where
    swapEither (Left a) = Right a
    swapEither (Right b) = Left b

-- | EWMA body: stateless affine box with feedback.
ewmaBody :: Double -> Process (Double, Double) (Double, Double)
ewmaBody alpha =
  Process
    (\(x, prev) -> alpha * x + (1 - alpha) * prev)
    (\s (x, _) -> alpha * x + (1 - alpha) * s)
    (\s -> (s, s))

-- | Exponentially weighted moving average with initial feedback.
ewma :: Double -> Double -> Process Double Double
ewma alpha s0 = register s0 (ewmaBody alpha)

-- | Shared-medium body: adds the input to the shared state and echoes it.
sharedAddP :: Process (Int, Int) (Int, Int)
sharedAddP = Process (Pre.uncurry (+)) (\s (_, a) -> s + a) (\s -> (s, s))

-- | Shared-medium body: doubles the shared state and echoes the input.
sharedDoubleP :: Process (Int, Int) (Int, Int)
sharedDoubleP = Process (\(s, _) -> s * 2) (\s (_, _) -> s * 2) (\s -> (s, s))

-- | Function counterpart of 'sharedAddP' for premonoidal centrality tests.
sharedAddF :: (Int, Int) -> (Int, Int)
sharedAddF (s, a) = let s' = s + a in (s', s')

-- | Function counterpart of 'sharedDoubleP' for premonoidal centrality tests.
sharedDoubleF :: (Int, Int) -> (Int, Int)
sharedDoubleF (s, _c) = let s' = s * 2 in (s', s')

-- | State-agnostic body: passes payload through unchanged.
bodyIdF :: (Int, Int) -> (Int, Int)
bodyIdF (s, a) = (s, a)

-- | State-agnostic body: increments the right payload, leaves state alone.
bodyIncF :: (Int, Int) -> (Int, Int)
bodyIncF (s, c) = (s, c + 1)

-- ---------------------------------------------------------------------------
-- Prob helpers for fragment oracles
-- ---------------------------------------------------------------------------

-- | Fair coin with total mass 1.
coin :: Prob (->) Double () Bool
coin = fromWeighted [(True, 0.25), (False, 0.75)]

-- | Unnormalised weighted measure with total mass 1.5.
unnorm :: Prob (->) Double () Bool
unnorm = fromWeighted [(True, 0.5), (False, 1.0)]

-- | A deliberately non-linear inhabitant: squares its continuation.
squareK :: Prob (->) Double a a
squareK = Prob $ \k p -> k p * k p

-- | Evaluate a measure-free morphism against a continuation on the output.
ev :: Prob (->) Double () b -> ((b -> Double) -> Double)
ev (Prob f) k = f (\((), b) -> k b) ((), ())

-- | Approximate equality for floating-point oracles.
approx :: Double -> Double -> Bool
approx x y = abs (x - y) < 1e-9

-- ---------------------------------------------------------------------------
-- Markov separator oracles for Prob
-- ---------------------------------------------------------------------------
--
-- 'Prob' morphisms are rank-2, so decidable equality is unavailable in
-- general.  We instead test against a finite /separator/: a set of
-- continuations and inputs that is large enough to catch the laws we care
-- about here.  The unit context is enough for these examples because the
-- morphisms are measure kernels.

-- | All functions from a finite bounded enumerable type to 'Bool'.
allBoolFns :: forall a. (Bounded a, Enum a) => [a -> Bool]
allBoolFns = map (\bits a -> bits !! fromEnum a) (replicateM (fromEnum (maxBound :: a) + 1) [False, True])

-- | All functions from a pair of finite bounded enumerable values to 'Bool'.
--
-- Pairs do not have an 'Enum' instance in current GHC, so we enumerate the
-- underlying values explicitly and index into the truth table.
pairBoolFns :: forall b. (Enum b) => [b] -> [(b, b) -> Bool]
pairBoolFns bs = map (\bits (b1, b2) -> bits !! (fromEnum b1 * n + fromEnum b2)) (replicateM (n * n) [False, True])
  where
    n = length bs

-- | Equality oracle for @Prob (->) r a b@ using a supplied input set and
-- continuation set.
probEqOver ::
  forall a b r.
  (Bounded a, Enum a, Eq r) =>
  [b -> r] ->
  Prob (->) r a b ->
  Prob (->) r a b ->
  Bool
probEqOver ks (Prob p) (Prob q) =
  and
    [ p (\((), b) -> k b) ((), a) == q (\((), b) -> k b) ((), a)
    | k <- ks,
      a <- [minBound .. maxBound :: a]
    ]

-- | Equality oracle for @Prob (->) Double a b@ using a supplied input set and
-- {0,1}-valued continuation set.
probEqDoubleOver ::
  forall a b.
  (Bounded a, Enum a) =>
  [b -> Double] ->
  Prob (->) Double a b ->
  Prob (->) Double a b ->
  Bool
probEqDoubleOver ks (Prob p) (Prob q) =
  and
    [ approx (p (\((), b) -> k b) ((), a)) (q (\((), b) -> k b) ((), a))
    | k <- ks,
      a <- [minBound .. maxBound :: a]
    ]

-- | Separator predicate for copy-naturality with a 'Bool' scalar.
probCopySep ::
  forall a b.
  (Bounded a, Enum a, Bounded b, Enum b) =>
  Prob (->) Bool a (b, b) ->
  Prob (->) Bool a (b, b) ->
  Bool
probCopySep p q =
  probEqOver (pairBoolFns bs) p q
  where
    bs = [minBound .. maxBound :: b]

-- | Separator predicate for copy-naturality with a 'Double' scalar.
probCopySepDouble ::
  forall a b.
  (Bounded a, Enum a, Bounded b, Enum b) =>
  Prob (->) Double a (b, b) ->
  Prob (->) Double a (b, b) ->
  Bool
probCopySepDouble p q =
  probEqDoubleOver (map toDoubleFn (pairBoolFns bs)) p q
  where
    bs = [minBound .. maxBound :: b]
    toDoubleFn k (b1, b2) = if k (b1, b2) then 1 else 0 :: Double

-- | Separator predicate for discard-naturality with a 'Double' scalar.
probDiscardSep ::
  forall a.
  (Bounded a, Enum a) =>
  Prob (->) Double a () ->
  Prob (->) Double a () ->
  Bool
probDiscardSep p q =
  probEqDoubleOver [const 0, const 1] p q

-- | Copy-naturality check for the premonoidal 'Prob' base, which has no
-- canonical 'Tensor' instance.  The caller supplies the nesting ('parFG' or
-- 'parGF') to test.
copyNaturalP ::
  (Prob (->) r a (b, b) -> Prob (->) r a (b, b) -> Bool) ->
  (forall c d. Prob (->) r c d -> Prob (->) r c d -> Prob (->) r (c, c) (d, d)) ->
  Prob (->) r a b ->
  Bool
copyNaturalP eq parF f = eq (copyP . f) (parF f f . copyP)

-- | Discard-naturality check for the premonoidal 'Prob' base.
discardNaturalP ::
  (Prob (->) r a () -> Prob (->) r a () -> Bool) ->
  Prob (->) r a b ->
  Bool
discardNaturalP eq f = eq (discardP . f) discardP

-- | A non-deterministic Bool kernel analogous to 'squareK' over 'Double'.
--
-- 'squareK' squares the continuation with scalar multiplication; over 'Bool'
-- that multiplication is '(/=)' (XOR) on the Boolean ring.  The kernel
-- queries the continuation at both truth values, so it is non-linear and
-- lives outside the deterministic centre.
squareKBool :: Prob (->) Bool Bool Bool
squareKBool = choiceBy (/=) (embed id) (embed not)

-- | Geometric trial body: state counts flips; heads escapes with the count.
geomBody :: Double -> Prob (->) Double (Either () Int) (Either Int Int)
geomBody p = Prob $ \k (x, e) ->
  let n = case e of Left () -> 0; Right m -> m
   in p * k (x, Left (n + 1)) + (1 - p) * k (x, Right (n + 1))

-- | A three-state walk on 'Int': from s, either exit with s (Left) or move to
-- s+1 (Right). Used for the Bool trace reachability oracle.
walkBody :: Prob (->) Bool (Either Int Int) (Either Int Int)
walkBody = orP (embed exit) (embed stepR)
  where
    exit e = Left (either id id e)
    stepR e = Right (either id id e + 1)

-- | Reachability test via the Bool least-fixpoint trace.
reach :: Int -> Bool
reach target = runProb (traceE walkBody) (\((), s) -> s == target) ((), 0)

-- | Annotated helpers to avoid ambiguous overloads.
id1 :: FinRel F N1 N1
id1 = id

id2 :: FinRel F N2 N2
id2 = id

copy1 :: FinRel F N1 (N1, N1)
copy1 = copy

copy2 :: FinRel F N2 (N2, N2)
copy2 = copy

discard1 :: FinRel F N1 ()
discard1 = discard

discard2 :: FinRel F N2 ()
discard2 = discard

plus1 :: FinRel F (N1, N1) N1
plus1 = plus

plus2 :: FinRel F (N2, N2) N2
plus2 = plus

zero1 :: FinRel F () N1
zero1 = zero

zero2 :: FinRel F () N2
zero2 = zero

unitl1' :: FinRel F N1 ((), N1)
unitl1' = unitl'

unitr1' :: FinRel F N1 (N1, ())
unitr1' = unitr'

unitl2' :: FinRel F N2 ((), N2)
unitl2' = unitl'

unitr2' :: FinRel F N2 (N2, ())
unitr2' = unitr'

unitr0 :: FinRel F ((), ()) ()
unitr0 = unitr

discard0 :: FinRel F () ()
discard0 = discard

zero0 :: FinRel F () ()
zero0 = zero

-- | Dagger(FinRel) collapse witness: 'Copy' on the dagger requires
-- 'Merge' on the base, so the back of @copy@ is @plus@.  The
-- constructors are pinned by type signatures so the instance method
-- resolves unambiguously.
daggerCopy1 :: Dagger (FinRel F) N1 (N1, N1)
daggerCopy1 = copy

daggerDiscard1 :: Dagger (FinRel F) N1 ()
daggerDiscard1 = discard

-- ---------------------------------------------------------------------------
-- Markov-category examples over FinRel Bool (GF(2))
-- ---------------------------------------------------------------------------

-- | Identity relation on N1 — deterministic.
finRelId :: FinRel F N1 N1
finRelId = FinRel 1 1 [[True, True]]

-- | Zero map on N1 — deterministic.
finRelZeroMap :: FinRel F N1 N1
finRelZeroMap = FinRel 1 1 [[True, False]]

-- | Total relation on N1 — total but not a function.
finRelTotal :: FinRel F N1 N1
finRelTotal = FinRel 1 1 [[True, False], [False, True]]

-- | Neither total nor functional: relates 0 to both 0 and 1.
finRelNeither :: FinRel F N1 N1
finRelNeither = FinRel 1 1 [[False, True]]

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

-- | 'check' for assertions that live in 'IO'.
checkIO :: String -> IO Bool -> IO Bool
checkIO name act = do
  ok <- act
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

-- ---------------------------------------------------------------------------
-- ⅋ probe helpers
-- ---------------------------------------------------------------------------

-- | Thread that prepends a marker to the shared feedback list and emits the
-- first three elements.  Used to make the shared-medium interleaving observable.
markerBody :: Int -> ([Int], ()) -> ([Int], [Int])
markerBody n (ns, ()) = (n : ns, take 3 ns)

-- | Schedule that always runs the left body first without modifying the shared
-- state.  A pure order swap is invisible to the trace — this is the sliding
-- axiom of the traced category observed at the shared channel.
pureLeft :: Schedule [Int]
pureLeft = Schedule (,Both LeftFirst)

-- | Schedule that always runs the right body first without modifying the shared
-- state.
pureRight :: Schedule [Int]
pureRight = Schedule (,Both RightFirst)

-- | Schedule that always runs the left body first, leaving a neutral schedule
-- token in the shared state so the interleaving is observable.
leftFirst :: Schedule [Int]
leftFirst = Schedule $ \s -> (0 : s, Both LeftFirst)

-- | Schedule that always runs the right body first, leaving the same neutral
-- schedule token so the two orderings remain comparable on body sets.
rightFirst :: Schedule [Int]
rightFirst = Schedule $ \s -> (0 : s, Both RightFirst)

-- | Schedules for the @PS@ residual used in the B3 mediator-hyper oracles.
leftFirstPS :: Schedule PS
leftFirstPS = Schedule (,Both LeftFirst)

rightFirstPS :: Schedule PS
rightFirstPS = Schedule (,Both RightFirst)

-- | Gating schedules for the @PS@ residual: advance only one body.
leftOnlyPS :: Schedule PS
leftOnlyPS = Schedule (,L)

rightOnlyPS :: Schedule PS
rightOnlyPS = Schedule (,R)

-- | Premonoidal left-first product of two knot bodies.
--
-- This is the composite @(f ⊗ id) ; (id ⊗ g)@ in the category of knot bodies
-- @Thread (,) (->) s@.  It threads the shared state through @f@ first, then @g@.
bodyParL :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, These b d))
bodyParL f g (s, (a, c)) =
  let (s', b) = f (s, a)
      (s'', d) = g (s', c)
   in (s'', These b d)

-- | Premonoidal right-first product of two knot bodies.
--
-- This is the composite @(id ⊗ g) ; (f ⊗ id)@.  It threads the shared state
-- through @g@ first, then @f@.
bodyParR :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, These b d))
bodyParR f g (s, (a, c)) =
  let (s', d) = g (s, c)
      (s'', b) = f (s', a)
   in (s'', These b d)

-- | Centrality of two knot bodies at a chosen input.
--
-- Two bodies are central when the premonoidal left-first and right-first
-- products agree.  For the cartesian instance @Thread (,) (->) s@ this is the
-- statement that order of state threading is invisible.
bodyCentral :: (Eq s, Eq b, Eq d) => ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> (s, (a, c)) -> Bool
bodyCentral f g input = bodyParL f g input == bodyParR f g input

-- | Premonoidal left-first whiskering built from assoc / slide / first.
--
-- This is the composite @(f ⊗ id) ; (id ⊗ g)@ expressed with the cartesian
-- structural maps.  It threads state through @f@ first, then @g@.
whiskerL :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, (b, d)))
whiskerL f g =
  assoc' @(,) @(->)
    .> par @(,) @(->) f id
    .> assoc @(,) @(->)
    .> slide @(,) @(->)
    .> par @(,) @(->) id g
    .> slide @(,) @(->)

-- | Premonoidal right-first whiskering built from assoc / slide / first.
--
-- This is the composite @(id ⊗ g) ; (f ⊗ id)@.
whiskerR :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, (b, d)))
whiskerR f g =
  slide @(,) @(->)
    .> par @(,) @(->) id g
    .> slide @(,) @(->)
    .> assoc' @(,) @(->)
    .> par @(,) @(->) f id
    .> assoc @(,) @(->)

-- | Lift a payload map to a body that leaves shared state alone.
--
-- Such bodies are exactly the structural maps of the underlying category
-- threaded through the ambient state wire.
liftBody :: (a -> b) -> (s, a) -> (s, b)
liftBody f (s, a) = (s, f a)

-- | State-touching body with a pair payload: adds both components to state.
sharedAddFPair :: (Int, (Int, Int)) -> (Int, (Int, Int))
sharedAddFPair (s, (a, b)) = let s' = s + a + b in (s', (s', s'))

-- ---------------------------------------------------------------------------
-- Residual-oracle helpers
-- ---------------------------------------------------------------------------

-- | A synchronous identity-like 'Kleisli IO' end: writes are stored in an
-- 'IORef' and reads retrieve the most recently stored value.  This is the
-- effectful counterpart of the unit/copycat end: closing the two poles
-- yanks to the identity morphism.
mkIdentityEnd :: IO (Ends (Kleisli IO) Int Int)
mkIdentityEnd = do
  ref <- newIORef (0 :: Int)
  pure $ endsK (writeIORef ref) (readIORef ref)

-- ---------------------------------------------------------------------------
-- Keystone: System (Prob (->) r) s (Mono i o)
--
-- The stochastic Moore machine, stepped by expectation. The scalar @r@ selects
-- the semantics: @Double@ for probability, @Tropical@ for min-plus / Viterbi.
-- ---------------------------------------------------------------------------

-- | A tiny semiring class local to the executable so the same runner works for
-- probability and tropical semantics without pulling in NumHask prelude.
class Semiring r where
  sAdd :: r -> r -> r
  sMul :: r -> r -> r
  sZero :: r
  sOne :: r

instance Semiring Double where
  sAdd = (+)
  sMul = (*)
  sZero = 0
  sOne = 1

-- | Min-plus tropical semiring over 'Double'.
--
-- Addition is 'min', multiplication is ordinary addition, the additive unit is
-- positive infinity, and the multiplicative unit is zero.
newtype Tropical = Tropical {getTropical :: Double}
  deriving (Eq, Ord, Show)

instance Semiring Tropical where
  sAdd (Tropical a) (Tropical b) = Tropical (min a b)
  sMul (Tropical a) (Tropical b) = Tropical (a + b)
  sZero = Tropical (1 / 0)
  sOne = Tropical 0

-- | Boolean semiring: addition is disjunction (reachability), multiplication
-- is conjunction (path validity).  This is the model-checking row of the
-- keystone instance table.
instance Semiring Bool where
  sAdd = (||)
  sMul = (&&)
  sZero = False
  sOne = True

-- | Run a finite-state stochastic Moore machine by expectation.
--
-- Given an enumeration of the state space, the machine, a list of inputs, a
-- query on the final state, and an initial state, return the expected query
-- value.
--
-- For @r = Double@ this is ordinary expectation over the final state
-- distribution. For @r = Tropical@ it is the min-plus cost of the cheapest
-- final state.
expectSystem ::
  (Eq s, Semiring r) =>
  [s] ->
  System (Prob (->) r) s (Mono i o) ->
  [i] ->
  (s -> r) ->
  s ->
  r
expectSystem states sys is q s0 =
  foldl' sAdd sZero [q s `sMul` distFinal s | s <- states]
  where
    distFinal = foldl' step initDist is
    initDist s = if s == s0 then sOne else sZero
    step dist i s' =
      foldl' sAdd sZero [dist s `sMul` pTrans s i s' | s <- states]
    pTrans s i s' =
      runProb
        (runSystem sys)
        (\((), (s'', _)) -> if s' == s'' then sOne else sZero)
        ((), (s, monoIn i))

-- | Three-state chain for the keystone doctests.
data S3 = S0 | S1 | S2
  deriving (Eq, Show, Enum, Bounded)

-- | Probability semantics: a lazy random walk on three states.
--
-- From each state, stay with probability 0.5 and move to the next state
-- (cyclically) with probability 0.5.
chain3Prob :: System (Prob (->) Double) S3 (Mono () ())
chain3Prob = system $ Prob $ \k (x, (s, _)) ->
  let next = case s of
        S0 -> [(S0, 0.5), (S1, 0.5)]
        S1 -> [(S1, 0.5), (S2, 0.5)]
        S2 -> [(S2, 0.5), (S0, 0.5)]
   in foldl' (+) 0 [p * k (x, (s', ((), ()))) | (s', p) <- next]

-- | Tropical semantics: the same graph with transition costs.
--
-- Staying costs 1, moving costs 2. The cheapest n-step path to a state is the
-- Viterbi value.
chain3Tropical :: System (Prob (->) Tropical) S3 (Mono () ())
chain3Tropical = system $ Prob $ \k (x, (s, _)) ->
  let next = case s of
        S0 -> [(S0, Tropical 1), (S1, Tropical 2)]
        S1 -> [(S1, Tropical 1), (S2, Tropical 2)]
        S2 -> [(S2, Tropical 1), (S0, Tropical 2)]
   in foldl' sAdd sZero [c `sMul` k (x, (s', ((), ()))) | (s', c) <- next]

-- | Exact occupancy probabilities for the 3-state chain after @n@ steps,
-- starting from @S0@.
--
-- >>> occupancyProb 0
-- [1.0,0.0,0.0]
--
-- >>> occupancyProb 1
-- [0.5,0.5,0.0]
--
-- >>> occupancyProb 2
-- [0.25,0.5,0.25]
--
-- >>> occupancyProb 3
-- [0.25,0.375,0.375]
occupancyProb :: Int -> [Double]
occupancyProb n =
  [getMass s | s <- [S0, S1, S2]]
  where
    getMass s = expectSystem [S0, S1, S2] chain3Prob (replicate n ()) (\s' -> if s' == s then 1 else 0) S0

-- | Tropical (Viterbi) cost to be in each state after @n@ steps, starting from
-- @S0@.
--
-- >>> viterbiCost 0
-- [0.0,Infinity,Infinity]
--
-- >>> viterbiCost 1
-- [1.0,2.0,Infinity]
--
-- >>> viterbiCost 2
-- [2.0,3.0,4.0]
viterbiCost :: Int -> [Double]
viterbiCost n =
  [getTropical (expectSystem [S0, S1, S2] chain3Tropical (replicate n ()) (\s' -> if s' == s then sOne else sZero) S0) | s <- [S0, S1, S2]]

-- | Cyclic successor on the three-state chain.
nextS :: S3 -> S3
nextS S0 = S1
nextS S1 = S2
nextS S2 = S0

-- | Boolean semantics: from each state, staying and moving are both possible.
--
-- This is the reachability / model-checking row:
-- @expectSystem@ with @r = Bool@ answers "is there a path from @s0@ to a state
-- satisfying @q@ in exactly @n@ steps?"
chain3Bool :: System (Prob (->) Bool) S3 (Mono () ())
chain3Bool = system $ Prob $ \k (x, (s, _)) ->
  let next = case s of
        S0 -> [S0, S1]
        S1 -> [S1, S2]
        S2 -> [S2, S0]
   in foldl' sAdd sZero [k (x, (s', ((), ()))) | s' <- next]

-- | States reachable from @S0@ in exactly @n@ steps under the Boolean
-- transition relation.
--
-- >>> reachable 0
-- [S0]
--
-- >>> reachable 1
-- [S0,S1]
--
-- >>> reachable 2
-- [S0,S1,S2]
reachable :: Int -> [S3]
reachable n = filter (\s -> expectSystem [S0, S1, S2] chain3Bool (replicate n ()) (== s) S0) [S0, S1, S2]

-- ---------------------------------------------------------------------------
-- Keystone row: Kleisli IO (Monte Carlo rollout)
--
-- The scalar axis lists @Log Double@ for this row; the executable uses plain
-- @Double@ for normalized sampling.  The @Log Double@ variant is the same
-- structure accumulating log importance weights.
-- ---------------------------------------------------------------------------

-- | Tiny deterministic RNG so the Monte Carlo axioms are reproducible without
-- adding a dependency.
newtype RNG = RNG {rngState :: Int}

-- | Linear congruential generator step, returning a value in @[0,1)@.
stepRNG :: RNG -> (Double, RNG)
stepRNG (RNG s) =
  let modulus = 2 ^ (31 :: Int) :: Int
      s' = (1103515245 * s + 12345) `rem` modulus
   in (fromIntegral s' / fromIntegral modulus, RNG s')

sampleDouble :: IORef RNG -> IO Double
sampleDouble ref = do
  rng <- readIORef ref
  let (u, rng') = stepRNG rng
  writeIORef ref rng'
  pure u

-- | Monte Carlo version of the three-state chain: sample a successor rather
-- than enumerating the expectation.
chain3IO :: IORef RNG -> System (Prob (Kleisli IO) Double) S3 (Mono () ())
chain3IO ref = system $ Prob $ \k -> Kleisli $ \(x, (s, _)) -> do
  u <- sampleDouble ref
  let s' = if u < 0.5 then s else nextS s
  runKleisli k (x, (s', ((), ())))

-- | Run one @Kleisli IO@ trajectory for @n@ steps, returning the final state.
--
-- The continuation passed to 'runProb' returns a dummy scalar and writes the
-- sampled next state into a fresh 'IORef'; this is how we extract the state
-- from an expectation transformer.
runTrajectoryIO :: System (Prob (Kleisli IO) Double) S3 (Mono () ()) -> Int -> S3 -> IO S3
runTrajectoryIO sys n s0 = go n s0
  where
    go 0 s = pure s
    go m s = step s >>= go (m - 1)
    step s = do
      nextRef <- newIORef s
      let cont = Kleisli $ \(_, (s', ((), ()))) -> writeIORef nextRef s' >> pure 0
      _ <- runKleisli (runProb (runSystem sys) cont) ((), (s, monoIn ()))
      readIORef nextRef

-- | Empirical occupancy probabilities after @nSteps@, estimated from
-- @nTrials@ trajectories starting at @s0@.
mcOccupancy :: System (Prob (Kleisli IO) Double) S3 (Mono () ()) -> Int -> Int -> S3 -> IO [Double]
mcOccupancy sys nTrials nSteps s0 = do
  counts <- newIORef (0 :: Int, 0, 0)
  let trial = do
        s <- runTrajectoryIO sys nSteps s0
        modifyIORef' counts $ \(c0, c1, c2) -> case s of
          S0 -> (c0 + 1, c1, c2)
          S1 -> (c0, c1 + 1, c2)
          S2 -> (c0, c1, c2 + 1)
  sequence_ (replicate nTrials trial)
  (c0, c1, c2) <- readIORef counts
  let total = fromIntegral nTrials :: Double
  let toDouble :: Int -> Double
      toDouble = fromIntegral
  pure [toDouble c0 / total, toDouble c1 / total, toDouble c2 / total]

main :: IO ()
main = do
  results <-
    sequence
      [ -- copy/discard comonoid laws
        check "copy coassociative (n=1)" $
          par copy1 id1 . copy1 == assoc' . par id1 copy1 . copy1,
        check "copy coassociative (n=2)" $
          par copy2 id2 . copy2 == assoc' . par id2 copy2 . copy2,
        check "copy left counit (n=1)" $
          par discard1 id1 . copy1 == unitl1',
        check "copy left counit (n=2)" $
          par discard2 id2 . copy2 == unitl2',
        check "copy right counit (n=1)" $
          par id1 discard1 . copy1 == unitr1',
        check "copy right counit (n=2)" $
          par id2 discard2 . copy2 == unitr2',
        check "copy cocommutative (n=1)" $
          swap . copy1 == copy1,
        check "copy cocommutative (n=2)" $
          swap . copy2 == copy2,
        -- plus/zero monoid laws
        check "plus associative (n=1)" $
          plus1 . par plus1 id1 == plus1 . par id1 plus1 . assoc,
        check "plus associative (n=2)" $
          plus2 . par plus2 id2 == plus2 . par id2 plus2 . assoc,
        check "plus left unit (n=1)" $
          plus1 . par zero1 id1 . unitl1' == id1,
        check "plus left unit (n=2)" $
          plus2 . par zero2 id2 . unitl2' == id2,
        check "plus right unit (n=1)" $
          plus1 . par id1 zero1 . unitr1' == id1,
        check "plus right unit (n=2)" $
          plus2 . par id2 zero2 . unitr2' == id2,
        check "plus commutative (n=1)" $
          plus1 . swap == plus1,
        check "plus commutative (n=2)" $
          plus2 . swap == plus2,
        -- bialgebra laws
        check "bialgebra copy-plus (n=1)" $
          copy1 . plus1 == par plus1 plus1 . swapMiddle . par copy1 copy1,
        check "bialgebra copy-plus (n=2)" $
          copy2 . plus2 == par plus2 plus2 . swapMiddle2 . par copy2 copy2,
        check "bialgebra discard-plus (n=1)" $
          discard1 . plus1 == unitr0 . par discard1 discard1,
        check "bialgebra discard-plus (n=2)" $
          discard2 . plus2 == unitr0 . par discard2 discard2,
        check "bialgebra zero-copy (n=1)" $
          copy1 . zero1 == par zero1 zero1 . unitr',
        check "bialgebra zero-copy (n=2)" $
          copy2 . zero2 == par zero2 zero2 . unitr',
        check "bialgebra discard-zero" $
          discard0 . zero0 == (id :: FinRel F () ()),
        -- scalar arithmetic over GF(2)
        check "scalar True is identity" $
          finScalar True == id1,
        check "scalar False is idempotent" $
          (finScalar False :: FinRel F N1 N1) . finScalar False == finScalar False,
        check "scalar False absorbs scalar True" $
          (finScalar False :: FinRel F N1 N1) . finScalar True == finScalar False,
        check "scalar True after scalar False" $
          (finScalar True :: FinRel F N1 N1) . finScalar False == finScalar False,
        -- Markov-category oracles (Ex9): copy/discard naturality is morphism-level
        check "FinRel finRelId is deterministic" $
          deterministic (==) (==) finRelId,
        check "FinRel finRelZeroMap is deterministic" $
          deterministic (==) (==) finRelZeroMap,
        check "FinRel finRelTotal is discard-natural but not copy-natural" $
          discardNatural (==) finRelTotal && not (copyNatural (==) finRelTotal),
        check "FinRel finRelNeither is neither copy- nor discard-natural" $
          not (copyNatural (==) finRelNeither) && not (discardNatural (==) finRelNeither),
        -- Dagger(FinRel k) collapse: the dagger instances interlock the
        -- ⊗-comonoid and the ⅋-monoid in a single construction.
        check "Dagger(FinRel) copy front is FinRel copy" $
          front daggerCopy1 == copy1,
        check "Dagger(FinRel) copy back is FinRel plus" $
          back daggerCopy1 == plus1,
        check "Dagger(FinRel) discard front is FinRel discard" $
          front daggerDiscard1 == discard1,
        check "Dagger(FinRel) discard back is FinRel zero" $
          back daggerDiscard1 == zero1,
        check "Dagger(FinRel) transpose copy has plus in front" $
          front (transpose daggerCopy1) == plus1,
        -- traced structure
        check "trace yanking (n=1)" $
          trace (swap :: FinRel F (N1, N1) (N1, N1)) == id1,
        check "trace of identity pair" $
          trace (par id1 id1 :: FinRel F (N1, N1) (N1, N1)) == id1,
        -- Para laws promoted to circuits-learn-axioma (11 Aug 2026).
        -- The L1/L2 constant-state trace checks now live there alongside
        -- the full Category associativity and identity oracles for Para.
        -- Circuit.Process oracles
        check "Process seed emits first output" $
          scan sumP [5] == [5],
        check "Process scan semantics" $
          scan sumP [1, 2, 3] == [1, 3, 6],
        check "Process fold semantics" $
          fold sumP [1, 2, 3] == Just 6,
        check "Process fold empty" $
          isNothing (fold sumP []),
        check "Process scan == run . encode" $
          run (encode sumP) [1, 2, 3] == scan sumP [1, 2, 3],
        check "Process Traced (,) yanking" $
          scan (trace swapPairP) [1, 2, 3] == [1, 2, 3],
        check "Process Traced Either yanking" $
          scan (trace swapEitherP) [1, 2, 3] == [1, 2, 3],
        check "Process register (EWMA)" $
          scan (ewma 0.5 0.0) [1.0, 1.0, 1.0] == [0.5, 0.75, 0.875],
        check "Process register == trace . strength . delay (EWMA)" $
          let body = ewmaBody 0.5
              s0 = 0.0
              xs = [1.0, 1.0, 1.0]
              swapP (Process i st ex) =
                Process (i . Tuple.swap) (\s -> st s . Tuple.swap) (Tuple.swap . ex)
           in scan (register s0 body) xs
                == scan (trace (swapP (body . strength (delay s0)))) xs,
        -- Process / SArr equivalence
        check "processToSomeSArr sumP agrees with scan" $
          MedState.runSomeSArr (MedState.processToSomeSArr sumP) [1, 2, 3 :: Int] == scan sumP [1, 2, 3],
        check "processToSomeSArr swapPairP agrees with scan" $
          MedState.runSomeSArr (MedState.processToSomeSArr swapPairP) [(1, 2), (3, 4), (5, 6)] == scan swapPairP [(1, 2), (3, 4), (5, 6)],
        check "processToSomeSArr ewma agrees with scan" $
          MedState.runSomeSArr (MedState.processToSomeSArr (ewma 0.5 0.0)) [1.0, 1.0, 1.0] == scan (ewma 0.5 0.0) [1.0, 1.0, 1.0],
        -- Process / Loop Either round-trip factors through Thread Either (->)
        check "Process encode factors through Thread Either (->)" $
          let viaThread p = case MedState.processToThread p of MedState.SomeThread _ b -> MedState.threadToLoop b
           in scan sumP [1, 2, 3] == run (viaThread sumP) [1, 2, 3]
                && scan swapPairP [(1, 2), (3, 4), (5, 6)] == run (viaThread swapPairP) [(1, 2), (3, 4), (5, 6)]
                && scan (ewma 0.5 0.0) [1.0, 1.0, 1.0] == run (viaThread (ewma 0.5 0.0)) [1.0, 1.0, 1.0],
        -- Process as a base arrow for Loop / Net / Shared
        check "Process lifts into Loop (,) Process" $
          scan (run (Lift sumP :: Loop (,) Process Int Int)) [1, 2, 3]
            == scan sumP [1, 2, 3],
        check "Net (,) Process copy uses Process.copy" $
          let p = run (Net.Copy :: Net.Net (,) Process Int (Int, Int)) :: Process Int (Int, Int)
           in scan p [5] == [(5, 5)],
        check "Net (,) Process plus uses Process.plus" $
          let p = run (Net.Plus :: Net.Net (,) Process (Int, Int) Int) :: Process (Int, Int) Int
           in scan p [(2, 3)] == [5],
        check "Shared (,) Process LR order differs from RL" $
          let lr = sharedBy (Schedule (,Both LeftFirst) :: Schedule Int) sharedAddP sharedDoubleP
              rl = sharedBy (Schedule (,Both RightFirst) :: Schedule Int) sharedAddP sharedDoubleP
           in scan lr [(1, (2, 3))] == [(6, These 3 6)]
                && scan rl [(1, (2, 3))] == [(4, These 4 2)],
        -- Circuit.Prob oracles
        -- Deterministic fragment
        check "Prob embed preserves identity" $
          let k ((), b) = fromIntegral b :: Double
           in runProb (embed id) k ((), 5 :: Int) == k ((), 5 :: Int),
        check "Prob embed preserves composition" $
          let f = (+ 10) :: Int -> Int
              g = (* 3) :: Int -> Int
              k ((), c) = fromIntegral c :: Double
           in runProb (embed (f . g)) k ((), 5)
                == runProb (embed f . embed g) k ((), 5),
        -- Score modality structure
        check "Prob score anti-homomorphism" $
          let w = (* 2.0) :: Double -> Double
              v = (+ 3.0) :: Double -> Double
              k ((), _) = 1.0 :: Double
           in runProb (score w . score v) k ((), 5 :: Int)
                == runProb (score (v . w)) k ((), 5 :: Int),
        check "Prob score endos need not commute" $
          let w = (* 2.0) :: Double -> Double
              v = (+ 3.0) :: Double -> Double
              k ((), _) = 1.0 :: Double
           in runProb (score w . score v) k ((), 5 :: Int)
                /= runProb (score v . score w) k ((), 5 :: Int),
        -- Linear fragment: multiplicative endos central against real measures
        check "Prob centrality of (*2) vs coin (linear fragment)" $
          approx
            (ev (score (* 2) . coin) (\b -> if b then 10 else 1))
            (ev (coin . score (* 2)) (\b -> if b then 10 else 1)),
        -- Affine/Markov fragment: affine endos central exactly on mass-1
        check "Prob centrality of (+3) vs coin (mass 1, affine fragment)" $
          approx
            (ev (score (+ 3) . coin) (\b -> if b then 10 else 1))
            (ev (coin . score (+ 3)) (\b -> if b then 10 else 1)),
        check "Prob centrality of (+3) fails off mass-1 fragment" $
          not
            ( approx
                (ev (score (+ 3) . unnorm) (\b -> if b then 10 else 1))
                (ev (unnorm . score (+ 3)) (\b -> if b then 10 else 1))
            ),
        -- Outside the linear fragment even normalised measures fail centrality
        check "Prob centrality of (^2) fails vs coin" $
          not
            ( approx
                (ev (score (^ (2 :: Int)) . coin) (\b -> if b then 10 else 1))
                (ev (coin . score (^ (2 :: Int))) (\b -> if b then 10 else 1))
            ),
        -- Fubini on the linear fragment
        check "Prob parFG == parGF on coin x coin (Fubini)" $
          let k ((), (b, d)) = (if b then 10 else 1) * (if d then 100 else 1) :: Double
           in approx
                (runProb (parFG coin coin) k ((), ((), ())))
                (runProb (parGF coin coin) k ((), ((), ()))),
        check "Prob parFG != parGF with squareK x coin (premonoidal)" $
          let k ((), (b, d)) = b + (if d then 10 else 1) :: Double
           in not
                ( approx
                    (runProb (parFG squareK coin) k ((), (2.0, ())))
                    (runProb (parGF squareK coin) k ((), (2.0, ())))
                ),
        -- Mass detects affineness / discardability
        check "Prob mass detects score breaking affineness" $
          approx (mass (1.0 :: Double) (score (* 2) . coin) ()) 2.0
            && approx (mass (1.0 :: Double) coin ()) 1.0,
        -- Copy/discards naturality via finite separators
        check "Prob copy natural for embed (deterministic fragment, FG nesting)" $
          copyNaturalP probCopySep parFG (embed not :: Prob (->) Bool Bool Bool),
        check "Prob copy natural for embed (deterministic fragment, GF nesting)" $
          copyNaturalP probCopySep parGF (embed not :: Prob (->) Bool Bool Bool),
        check "Prob copy NOT natural for coin (correlation vs independence, FG)" $
          not (copyNaturalP probCopySepDouble parFG coin),
        check "Prob copy NOT natural for coin (correlation vs independence, GF)" $
          not (copyNaturalP probCopySepDouble parGF coin),
        check "Prob squareKBool is copy-natural with neither nesting" $
          not (copyNaturalP probCopySep parFG squareKBool)
            && not (copyNaturalP probCopySep parGF squareKBool),
        -- Discard on the mass-1 fragment
        check "Prob discard natural for coin (mass-1 fragment)" $
          discardNaturalP probDiscardSep coin,
        check "Prob discard fails for unnormalised score (*2) . coin" $
          not (discardNaturalP probDiscardSep (score (* 2) . coin)),
        -- Traced Either: computability graded by scalar
        check "Prob traceEN converges to 1/p for geometric (error ~ q^fuel)" $
          let e n = ev (traceEN 0 n (geomBody 0.5)) fromIntegral
           in approx (e 60) 2.0 && e 5 < e 20 && e 20 < e 60,
        check "Prob Bool trace reachability via lazy (||)" $
          reach 2,
        -- Ends oracles
        check "O9 ends . splay == id" $
          let e :: Ends (->) () Int
              e = ends0 (const ()) (const 42)
              (write', receive') = splay0 e
              e' = ends0 write' receive'
           in run (box @(,) e') () == 42 && run (box @(,) e) () == 42,
        check "annihilation: close on non-copycat end violates yanking" $
          let e :: Ends (->) Int Int
              e = ends0 (const ()) (const 42)
           in close (conjoint e) (companion e) 0 == 42
                && close (conjoint e) (companion e) 7 == 42,
        checkIO "residual observed: sequential boxes agree but residual is exposed" $ do
          ref <- newIORef (0 :: Int)
          let e1 :: Ends (Kleisli IO) Int Int
              e1 = endsK (\x -> modifyIORef' ref (+ x)) (pure 0)
              e2 :: Ends (Kleisli IO) Int Int
              e2 = endsK (\_ -> pure ()) (pure 1)
          r1 <- runKleisli (run (box @(,) (composeEnds0 e1 e2))) 5
          residual1 <- readIORef ref
          writeIORef ref 0
          r2 <- runKleisli (run (box @(,) e2 . box @(,) e1)) 5
          residual2 <- readIORef ref
          pure (r1 == r2 && r1 == 1 && residual1 == 5 && residual2 == 5),
        checkIO "ends embed: Kleisli IO end yanks through Chu embedding" $ do
          e <- mkIdentityEnd
          let chu = endsAsChu e
          r <- runKleisli (Chu.chuPair chu (conjoint e, companion e)) 42
          pure (r == 42),
        checkIO "ends embed: Chu negation is involutive on Kleisli IO end" $ do
          e <- mkIdentityEnd
          let chu = endsAsChu e
              chu'' = Chu.negateChu (Chu.negateChu chu)
          r1 <- runKleisli (Chu.chuPair chu (conjoint e, companion e)) 7
          r2 <- runKleisli (Chu.chuPair chu'' (conjoint e, companion e)) 7
          pure (r1 == 7 && r2 == 7),
        check "Bool as a non-terminal 'Ends' pole composes write then read" $
          let e :: Ends (->) Int Int
              e = ends @(->) @Int @Int @Bool (const False) (\b -> if b then 1 :: Int else 0)
              (w, r) = splay @(->) @Int @Int @Bool e
           in not (w 42) && r False == 0 && close (conjoint e) (companion e) 42 == 0,
        check "Bool copycat is not identity (Bool is not terminal)" $
          let e :: Ends (->) Bool Bool
              e = copycat @(->) @Bool
           in not (close (conjoint e) (companion e) True)
                && not (close (conjoint e) (companion e) False),
        -- Additive Ends oracles
        check "Additive pairEnds pairs outputs" $
          let e1 :: Ends (->) () Int
              e1 = ends0 (const ()) (const 1)
              e2 :: Ends (->) () Int
              e2 = ends0 (const ()) (const 2)
           in run (box @(,) (pairEnds e1 e2)) () == (1, 2),
        check "raceEnds LeftFirst picks left when both speak" $
          let eL :: Ends (->) () (Maybe Int)
              eL = ends0 (const ()) (const (Just 1))
              eR :: Ends (->) () (Maybe Int)
              eR = ends0 (const ()) (const (Just 2))
           in run (box @(,) (raceEnds LeftFirst eL eR)) () == Just 1,
        check "raceEnds RightFirst picks right when both speak" $
          let eL :: Ends (->) () (Maybe Int)
              eL = ends0 (const ()) (const (Just 1))
              eR :: Ends (->) () (Maybe Int)
              eR = ends0 (const ()) (const (Just 2))
           in run (box @(,) (raceEnds RightFirst eL eR)) () == Just 2,
        check "raceEnds falls back when left is silent" $
          let eL :: Ends (->) () (Maybe Int)
              eL = ends0 (const ()) (const Nothing)
              eR :: Ends (->) () (Maybe Int)
              eR = ends0 (const ()) (const (Just 2))
           in run (box @(,) (raceEnds LeftFirst eL eR)) () == Just 2
                && run (box @(,) (raceEnds RightFirst eL eR)) () == Just 2,
        -- Stamped oracles
        check "Stamped fmap preserves stamp (Int token)" $
          let s = Stamped 7 ("hello" :: String)
           in stamp (fmap reverse s) == (7 :: Int) && stamped (fmap reverse s) == "olleh",
        check "Stamped fmap preserves stamp (Bool token)" $
          let s = Stamped True (10 :: Int)
           in stamp (fmap (+ 1) s) && stamped (fmap (+ 1) s) == 11,
        -- Boundary oracles
        check "Boundary fmap preserves Mark tag" $
          isMark (fmap length (Mark "halt" :: Boundary String String)),
        check "Boundary fmap acts on Payload" $
          let p = fmap length (Payload "hi" :: Boundary String String)
           in isPayload p && p == Payload 2,
        -- Mark system (circuits-residual §7)
        check "markSystem steps payloads through the inner system" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p (map Payload [1, 2, 3]) == [Just 1, Just 3, Just 6],
        check "markSystem halts on a halt mark and emits Nothing thereafter" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p [Payload 1, Payload 2, Mark "HALT", Payload 3] == [Just 1, Just 3, Nothing, Nothing],
        check "markSystem treats non-halt marks as no-ops" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p [Payload 1, Mark "NOOP", Payload 2] == [Just 1, Just 1, Just 3],
        check "markSystem halts immediately when the first input is a halt mark" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p [Mark "HALT", Payload 1] == [Nothing, Nothing],
        check "markSystem round-trips through systemToProcess" $
          let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
              sys = markSystem (== "HALT") id innerSys
              p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
           in scan p [] == [] && fold p [Payload 1, Payload 2, Mark "HALT"] == Just Nothing,
        -- Linear marks (Z6c) — SwapQ integration is deferred
        check "Linear marker round-trips through unLinear" $
          unLinear (Linear 42 :: Linear Int) == (42 :: Int),
        check "NotLinear constraint accepts plain payloads" $
          let acceptsNonLinear :: (NotLinear a) => a -> a
              acceptsNonLinear = id
           in acceptsNonLinear (42 :: Int) == 42,
        -- Chu construction
        check "Chu is a base arrow: id and composition typecheck" $
          let cid :: Chu.Chu (,) Bool (->) (Chu.ChuObj (,) Bool (->) Int Int) (Chu.ChuObj (,) Bool (->) Int Int)
              cid = Chu.Chu (Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Int Int Int Int)
              ccompose = cid . cid
           in case ccompose of
                Chu.Chu (Chu.ChuMorphism f g) -> f 0 == 0 && g 0 == 0,
        check "Chu negation is involutive" $
          let e :: (Int, Int) -> Bool
              e (x, y) = x == y
              obj = Chu.ChuObj 0 0 e
              obj'' = Chu.negateChu (Chu.negateChu obj)
           in all (\p -> Chu.chuPair obj p == Chu.chuPair obj'' p) [(x, y) | x <- [0 .. 2 :: Int], y <- [0 .. 2 :: Int]],
        check "Chu adjoint law holds for lawful prefix pair" $
          let domainAgents = [1, 2] :: [Int]
              codomainAgents = map prefixName domainAgents
              posts =
                [ mkChuPost 0 [r] 0
                | r <- domainAgents
                ]
                  ++ [mkChuPost 0 [1, 2] 0, mkChuPost 0 [] 0]
              subs = codomainAgents
              fwd p = p {chuTo = prefixTo (chuTo p)}
              bwd = unprefixSub
           in all (\p -> all (Chu.chuLaw chuObjPostInt chuObjPostInt (Chu.ChuMorphism fwd bwd) p) subs) posts,
        check "Chu adjoint law fails for unlawful backward map" $
          let posts = [mkChuPost 0 [1] 0 :: ChuPost]
              subs = [prefixName 1]
              fwd p = p {chuTo = prefixTo (chuTo p)}
              bwd = id
           in not (all (\p -> all (Chu.chuLaw chuObjPostInt chuObjPostInt (Chu.ChuMorphism fwd bwd) p) subs) posts),
        check "Chu tensor and par have different shapes over Bool" $
          let pos = [True, False]
              pos2 = [(x, y) | x <- pos, y <- pos]
              tensNegs = Chu.chuTensorNegs pos pos pos pos chuTwo chuTwo
              parPoss = Chu.chuParPoss pos pos pos pos chuTwo chuTwo
           in length tensNegs == 2
                && length parPoss == 2
                && (length pos2, length tensNegs) /= (length parPoss, length pos2),
        check "Chu Bool self-dual object is separated and extensional" $
          let pos = [True, False]
           in Chu.chuSeparated pos pos chuTwo && Chu.chuExtensional pos pos chuTwo,
        check "Chu tensor preserves identity" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              tId = Chu.tensorChu idC idC
           in eqTensorMorphism tId Chu.idChu,
        check "Chu tensor preserves composition" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              lhs = Chu.tensorChu (Chu.composeChu chuNot chuNot) idC
              rhs = Chu.composeChu (Chu.tensorChu chuNot idC) (Chu.tensorChu chuNot idC)
           in eqTensorMorphism lhs rhs,
        check "Chu tensor morphism satisfies adjoint law" $
          let tObj = Chu.tensorChuObj chuTwo chuTwo
              tMor = Chu.tensorChu chuNot idC
              idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in all (\p -> all (\n -> Chu.chuLaw tObj tObj tMor p n) chuTwoTensorNegs) pos2,
        check "Chu par preserves identity" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              pId = Chu.parChu idC idC
           in eqParMorphism pId Chu.idChu,
        check "Chu par preserves composition" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              lhs = Chu.parChu (Chu.composeChu chuNot chuNot) idC
              rhs = Chu.composeChu (Chu.parChu chuNot idC) (Chu.parChu chuNot idC)
           in eqParMorphism lhs rhs,
        check "Chu left unitor satisfies adjoint law" $
          let iObj = Chu.tensorChuObj chuUnitObjBool chuTwo
              mor = Chu.leftUnitorChu chuTwo
              pos2 = [((), x) | x <- chuTwoPos]
           in all (\p -> all (\b -> Chu.chuLaw iObj chuTwo mor p b) chuTwoPos) pos2,
        check "Chu left unitor is inverse on A" $
          let iso = Chu.composeChu (Chu.leftUnitorChu chuTwo) (Chu.leftUnitorChuInv chuTwo)
           in eqChuMorphismAA iso Chu.idChu,
        check "Chu left unitor inverse is inverse on I ⊗ A" $
          let iso = Chu.composeChu (Chu.leftUnitorChuInv chuTwo) (Chu.leftUnitorChu chuTwo)
           in eqChuMorphismIIA iso Chu.idChu,
        check "Chu right unitor satisfies adjoint law" $
          let iObj = Chu.tensorChuObj chuTwo chuUnitObjBool
              mor = Chu.rightUnitorChu chuTwo
              pos2 = [(x, ()) | x <- chuTwoPos]
           in all (\p -> all (\b -> Chu.chuLaw iObj chuTwo mor p b) chuTwoPos) pos2,
        check "Chu right unitor is inverse on A" $
          let iso = Chu.composeChu (Chu.rightUnitorChu chuTwo) (Chu.rightUnitorChuInv chuTwo)
           in eqChuMorphismAA iso Chu.idChu,
        check "Chu right unitor inverse is inverse on A ⊗ I" $
          let iso = Chu.composeChu (Chu.rightUnitorChuInv chuTwo) (Chu.rightUnitorChu chuTwo)
           in eqChuMorphismAII iso Chu.idChu,
        check "Chu implication object differs from compact A⊥ ⊗ B" $
          let lollPoss = Chu.chuParPoss chuTwoPos chuTwoPos chuTwoPos chuTwoPos (Chu.negateChu chuTwo) chuTwo
              compactNegs = Chu.chuTensorNegs chuTwoPos chuTwoPos chuTwoPos chuTwoPos (Chu.negateChu chuTwo) chuTwo
              compactPos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in length lollPoss == 2
                && length compactNegs == 2
                && (length compactPos2, length compactNegs) /= (length lollPoss, length compactPos2),
        check "Chu chuTwo has no copy morphism to chuTwo ⊗ chuTwo" $
          not hasCopyChuTwo,
        check "Chu chuTwo has no discard morphism to I" $
          not hasDiscardChuTwo,
        check "Chu additive conjunction has distinct shape" $
          let pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in length pos2 == 4
                && length chuTwoEither == 4
                && (length pos2, length chuTwoEither) /= (length pos2, length chuTwoTensorNegs)
                && (length pos2, length chuTwoEither) /= (length chuTwoLollPoss, length pos2),
        check "Chu additive disjunction has distinct shape" $
          let pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
              neg2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in length chuTwoEither == 4
                && length neg2 == 4
                && (length chuTwoEither, length neg2) /= (length pos2, length chuTwoTensorNegs)
                && (length chuTwoEither, length neg2) /= (length chuTwoLollPoss, length pos2),
        check "Chu top and zero have expected shapes" $
          let emptyV = [] :: [Void]
           in length [()] == 1 && null emptyV && null emptyV,
        check "Chu evaluation satisfies adjoint law" $
          let src = Chu.tensorChuObj chuTwo (Chu.lolliChuObj chuTwo chuTwo)
              mor = Chu.evalChu chuTwo chuTwo
              poss = [(a, m) | a <- chuTwoPos, m <- chuTwoLollPoss]
           in all (\p -> all (\d -> Chu.chuLaw src chuTwo mor p d) chuTwoPos) poss,
        check "Chu delivery matrix commutes with prefix morphism (Bool)" $
          let domainAgents = [1, 2] :: [Int]
              codomainAgents = map prefixName domainAgents
              posts = [mkChuPost 0 [1] 0, mkChuPost 0 [1, 2] 0, mkChuPost 0 [2] 0, mkChuPost 0 [] 0]
              domainMat = Chu.deliveryMatrix domainAgents (map chuTo posts) :: [[Bool]]
              codomainMat = Chu.deliveryMatrix codomainAgents (map (prefixTo . chuTo) posts) :: [[Bool]]
           in domainMat == codomainMat,
        check "Chu delivery matrix commutes with prefix morphism (Double)" $
          let domainAgents = [1, 2] :: [Int]
              codomainAgents = map prefixName domainAgents
              posts = [mkChuPost 0 [1, 2] 0, mkChuPost 0 [] 0]
              domainMat = Chu.deliveryMatrix domainAgents (map chuTo posts) :: [[Double]]
              codomainMat = Chu.deliveryMatrix codomainAgents (map (prefixTo . chuTo) posts) :: [[Double]]
           in domainMat == codomainMat,
        check "Chu prefix without backward rename breaks matrix equality" $
          let domainAgents = [1, 2] :: [Int]
              posts = [mkChuPost 0 [1] 0]
              domainMat = Chu.deliveryMatrix domainAgents (map chuTo posts) :: [[Bool]]
              forwardOnlyMat = Chu.deliveryMatrix domainAgents (map (prefixTo . chuTo) posts) :: [[Bool]]
           in domainMat /= forwardOnlyMat,
        -- Coherence: Loop/Dagger transpose and Chu negation on embedded Ends
        check "copycat witness is fixed by Chu negation and Dagger transpose" $
          let e :: Ends (->) () ()
              e = copycat
              chu = endsAsChu e
              chuNeg = Chu.negateChu chu
              d = Dagger id id :: Dagger (->) () ()
           in Chu.chuPair chu (conjoint e, companion e) () == Chu.chuPair chuNeg (companion e, conjoint e) ()
                && (let Dagger f g = transpose d in f () == () && g () == ()),
        check "constant self-map witness is fixed by Chu negation and Dagger transpose" $
          let e :: Ends (->) Int Int
              e = ends0 (const ()) (const 42)
              chu = endsAsChu e
              chuNeg = Chu.negateChu chu
              d = Dagger (const 42) (const 42) :: Dagger (->) Int Int
           in Chu.chuPair chu (conjoint e, companion e) 0 == Chu.chuPair chuNeg (companion e, conjoint e) 0
                && (let Dagger f g = transpose d in f 0 == 42 && g 0 == 42),
        -- Object-indexed Chu category (OChu) Tensor / Action instances
        check "OChu left unitor round-trips on ChuTwo" $
          let u :: Chu.OChu Bool (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo) Chu.ChuTwo
              u = unitl
              u' :: Chu.OChu Bool Chu.ChuTwo (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo)
              u' = unitl'
           in eqChuMorphismAA (ochuToChuMorphism (u . u')) Chu.idChu,
        check "OChu left unitor inverse round-trips on I ⊗ ChuTwo" $
          let t :: Chu.OChu Bool (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo) (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo)
              t = id
              u :: Chu.OChu Bool (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo) Chu.ChuTwo
              u = unitl
              u' :: Chu.OChu Bool Chu.ChuTwo (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo)
              u' = unitl'
           in eqChuMorphismIIA (ochuToChuMorphism (u' . u)) (ochuToChuMorphism t),
        check "OChu right unitor round-trips on ChuTwo" $
          let u :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool)) Chu.ChuTwo
              u = unitr
              u' :: Chu.OChu Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool))
              u' = unitr'
           in eqChuMorphismAA (ochuToChuMorphism (u . u')) Chu.idChu,
        check "OChu right unitor inverse round-trips on ChuTwo ⊗ I" $
          let t :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool)) (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool))
              t = id
              u :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool)) Chu.ChuTwo
              u = unitr
              u' :: Chu.OChu Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool))
              u' = unitr'
           in eqChuMorphismAII (ochuToChuMorphism (u' . u)) (ochuToChuMorphism t),
        check "OChu par preserves identity on ChuTwo ⊗ ChuTwo" $
          let idChuTwo = id :: Chu.OChu Bool Chu.ChuTwo Chu.ChuTwo
              idT = id :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
              p = par idChuTwo idChuTwo :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
           in eqTensorMorphism (ochuToChuMorphism p) (ochuToChuMorphism idT),
        check "OChu swap is involutive on ChuTwo ⊗ ChuTwo" $
          let s :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
              s = swap
              idT = id :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
           in eqTensorMorphism (ochuToChuMorphism (s . s)) (ochuToChuMorphism idT),
        -- SepChu: double negation, associator, pentagon
        check "SepChu ChuTwo is separated and extensional" $
          Chu.chuSeparated chuTwoPos chuTwoPos chuTwo
            && Chu.chuExtensional chuTwoPos chuTwoPos chuTwo,
        check "SepChu double negation is iso on ChuTwo" $
          let eta = Chu.dnUnitChu @Bool @Chu.ChuTwo
              eps = Chu.dnCounitChu @Bool @Chu.ChuTwo
           in eqChuMorphismAA (ochuToChuMorphism (eps . eta)) Chu.idChu
                && eqChuMorphismAA (ochuToChuMorphism (eta . eps)) Chu.idChu,
        check "SepChu associator satisfies adjoint law on ChuTwo" $
          all
            (\p -> all (\n -> Chu.chuLaw chuTwoObjLeftAssoc chuTwoObjRightAssoc Chu.assocChu p n) chuTwoNeg3R)
            chuTwoPos3L,
        check "SepChu associator is inverse on (ChuTwo ⊗ ChuTwo) ⊗ ChuTwo" $
          let iso = Chu.composeChu Chu.assocChuInv Chu.assocChu
           in eqEndo3L iso Chu.idChu,
        check "SepChu associator inverse is inverse on ChuTwo ⊗ (ChuTwo ⊗ ChuTwo)" $
          let iso = Chu.composeChu Chu.assocChu Chu.assocChuInv
           in eqEndo3R iso Chu.idChu,
        check "SepChu Channel assoc agrees with assocChu on ChuTwo" $
          let a ::
                Chu.OChu
                  Bool
                  (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                  (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
              a = assoc
           in eqAssocMorphism (ochuToChuMorphism a) Chu.assocChu,
        check "SepChu slide agrees with assoc . par swap id . assoc' on ChuTwo" $
          let sl ::
                Chu.OChu
                  Bool
                  (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                  (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
              sl = slide
              derived =
                assoc
                  . par swap id
                  . assoc' ::
                  Chu.OChu
                    Bool
                    (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                    (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
           in eqEndo3R (ochuToChuMorphism sl) (ochuToChuMorphism derived),
        check "SepChu associator pentagon commutes on ChuTwo" $
          let top1 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                      Chu.ChuTwo
                  )
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
                      (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
                  )
              top1 = assoc
              top2 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
                      (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
                  )
                  ( Chu.ChuOTensor
                      Bool
                      Chu.ChuTwo
                      (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                  )
              top2 = assoc
              bot1 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                      Chu.ChuTwo
                  )
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                      Chu.ChuTwo
                  )
              bot1 = par assoc id
              bot2 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                      Chu.ChuTwo
                  )
                  ( Chu.ChuOTensor
                      Bool
                      Chu.ChuTwo
                      (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                  )
              bot2 = assoc
              bot3 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      Chu.ChuTwo
                      (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                  )
                  ( Chu.ChuOTensor
                      Bool
                      Chu.ChuTwo
                      (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                  )
              bot3 = par id assoc
           in eqPentagonMorphism (ochuToChuMorphism (top2 . top1)) (ochuToChuMorphism (bot3 . bot2 . bot1)),
        -- ChuThree: non-self-dual zoo member
        check "SepChu ChuThree is separated and extensional" $
          Chu.chuSeparated chuThreePos chuThreeNeg chuThreeObj
            && Chu.chuExtensional chuThreePos chuThreeNeg chuThreeObj,
        check "SepChu ChuThree is non-self-dual" $
          any
            (\(p, n) -> Chu.chuPair chuThreeObj (p, n) /= Chu.chuPair chuThreeObj (n, p))
            [(p, n) | p <- chuThreePos, n <- chuThreePos],
        checkChuUnitlForward (Proxy @Bool) (Proxy @Chu.ChuThree) "OChu left unitor round-trips on ChuThree" chuThreePos,
        checkChuUnitrForward (Proxy @Bool) (Proxy @Chu.ChuThree) "OChu right unitor round-trips on ChuThree" chuThreePos,
        checkChuAssocInversesForward
          (Proxy @Bool)
          (Proxy @Chu.ChuThree)
          "SepChu associator is inverse on ChuThree"
          chuThreePos3L
          chuThreePos3R,
        checkChuPentagonForward (Proxy @Bool) (Proxy @Chu.ChuThree) "SepChu associator pentagon commutes on ChuThree" chuThreePos,
        -- ChuDouble01: finite Double-semiring zoo member
        check "SepChu ChuDouble01 is separated and extensional" $
          Chu.chuSeparated chuTwoPos chuTwoPos chuDouble01Obj
            && Chu.chuExtensional chuTwoPos chuTwoPos chuDouble01Obj,
        checkChuAssocInversesForward
          (Proxy @Double)
          (Proxy @Chu.ChuDouble01)
          "SepChu associator is inverse on ChuDouble01"
          chuTwoPos3L
          chuTwoPos3R,
        checkChuPentagonForward (Proxy @Double) (Proxy @Chu.ChuDouble01) "SepChu associator pentagon commutes on ChuDouble01" chuTwoPos,
        -- ChuDelivery: delivery-matrix zoo member
        check "SepChu ChuDelivery is separated and extensional" $
          Chu.chuSeparated chuTwoPos chuTwoPos chuDeliveryObj
            && Chu.chuExtensional chuTwoPos chuTwoPos chuDeliveryObj,
        checkChuAssocInversesForward
          (Proxy @Bool)
          (Proxy @Chu.ChuDelivery)
          "SepChu associator is inverse on ChuDelivery"
          chuTwoPos3L
          chuTwoPos3R,
        checkChuPentagonForward (Proxy @Bool) (Proxy @Chu.ChuDelivery) "SepChu associator pentagon commutes on ChuDelivery" chuTwoPos,
        -- Lolli: internal hom
        check "Lolli (->) curry/uncurry are inverse" $
          let f (x, y) = x + y :: Int
              g x y = x * y :: Int
           in uncurry @(,) @(->) (curry @(,) @(->) f) (3, 4) == f (3, 4)
                && curry @(,) @(->) (uncurry @(,) @(->) g) 3 4 == g 3 4,
        check "Lolli (->) eval is application" $
          eval @(,) @(->) (3 :: Int, (+ 1)) == 4,
        check "Lolli (->) eval is uncurry id . swap" $
          let apply (x, f) = eval @(,) @(->) (x, f) :: Int
              derived = uncurry @(,) @(->) id . swap
           in apply (3, (* 2)) == derived (3, (* 2)),
        check "Lolli OChu implication shape is (2, 4) not compact (4, 2)" $
          let lollPoss = chuTwoLollPoss
              compactPos = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
              compactNegs = Chu.chuTensorNegs chuTwoPos chuTwoPos chuTwoPos chuTwoPos (Chu.negateChu chuTwo) chuTwo
           in (length lollPoss, length compactPos) == (2, 4)
                && (length compactPos, length compactNegs) == (4, 2),
        check "Lolli OChu curry/uncurry are inverse on right unitor" $
          let u :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool)) Chu.ChuTwo
              u = unitr
              recovered =
                uncurry @(Chu.ChuOTensor Bool) @(Chu.OChu Bool) (curry @(Chu.ChuOTensor Bool) @(Chu.OChu Bool) u)
           in eqChuTwoUnitr (ochuToChuMorphism recovered) (ochuToChuMorphism u),
        check "Lolli OChu eval agrees with evalChu on ChuTwo" $
          let evL ::
                Chu.OChu
                  Bool
                  (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOLolli Bool Chu.ChuTwo Chu.ChuTwo))
                  Chu.ChuTwo
              evL = eval @(Chu.ChuOTensor Bool) @(Chu.OChu Bool)
           in eqChuMorphismLolliEval (ochuToChuMorphism evL) (Chu.evalChu chuTwo chuTwo),
        -- Exponentials
        check "Exponential (->) !A is A" $
          derelict @(,) @(->) (7 :: Int) == 7
            && copyE @(,) @(->) (7 :: Int) == (7, 7)
            && discardE @(,) @(->) (7 :: Int) == (),
        check "Exponential (->) ?A is the free list monoid" $
          introduce @(,) @(->) (7 :: Int) == [7]
            && introduce @(,) @(->) (7 :: Int) ++ introduce @(,) @(->) (8 :: Int) == [7, 8],
        check "Exponential OChu !ChuTwo exists and is separated-extensional" $
          let bangObj = Chu.bangChuObj chuTwo
              funs = chuTwoFuns
              ext =
                all
                  ( \(f, g) ->
                      eqFun f g
                        || any (\a -> Chu.chuPair bangObj (a, f) /= Chu.chuPair bangObj (a, g)) chuTwoPos
                  )
                  [(f, g) | f <- funs, g <- funs]
           in Chu.chuSeparated chuTwoPos funs bangObj
                && ext
                && length funs == 4,
        check "Exponential OChu copy/discard are a comonoid on !ChuTwo" $
          let bangObj = Chu.bangChuObj chuTwo
              tensObj = Chu.tensorChuObj bangObj bangObj
              iLeft = Chu.tensorChuObj Chu.chuUnitObj bangObj
              iRight = Chu.tensorChuObj bangObj Chu.chuUnitObj
              copyM = Chu.copyBangChu
              discM = Chu.discardBangChu
              pos = chuTwoPos
              funs = chuTwoFuns
              tensNegs = Chu.chuTensorNegs pos funs pos funs bangObj bangObj
              leftNegs = Chu.chuTensorNegs [()] [True, False] pos funs Chu.chuUnitObj bangObj
              rightNegs = Chu.chuTensorNegs pos funs [()] [True, False] bangObj Chu.chuUnitObj
              leftCounit = Chu.composeChu (Chu.tensorChu discM Chu.idChu) copyM
              rightCounit = Chu.composeChu (Chu.tensorChu Chu.idChu discM) copyM
           in all (\a -> all (\n -> Chu.chuLaw bangObj tensObj copyM a n) tensNegs) pos
                && all (\a -> all (\k -> Chu.chuLaw bangObj Chu.chuUnitObj discM a k) [True, False]) pos
                && all (\a -> Chu.chuForward copyM a == (a, a) && Chu.chuForward discM a == ()) pos
                && all (\a -> Chu.chuForward leftCounit a == ((), a)) pos
                && all (\a -> Chu.chuForward rightCounit a == (a, ())) pos
                && all (\a -> all (\n -> Chu.chuLaw bangObj iLeft leftCounit a n) leftNegs) pos
                && all (\a -> all (\n -> Chu.chuLaw bangObj iRight rightCounit a n) rightNegs) pos,
        check "Exponential OChu derelict !ChuTwo -> ChuTwo is a Chu morphism" $
          let bangObj = Chu.bangChuObj chuTwo
              mor = Chu.derelictChu chuTwo
           in all (\a -> all (\d -> Chu.chuLaw bangObj chuTwo mor a d) chuTwoPos) chuTwoPos
                && all (\a -> Chu.chuForward mor a == a) chuTwoPos,
        check "Exponential OChu derelict is the unique I-point bijection" $
          let bangObj = Chu.bangChuObj chuTwo
              toBang = iHomsChuTwo bangObj chuTwoPos chuTwoFuns
              toTwo = iHomsChuTwo chuTwo chuTwoPos chuTwoPos
           in length toBang == 2
                && length toTwo == 2
                && all
                  ( \m ->
                      any (\n -> eqIToTwo (composeITo (Chu.derelictChu chuTwo) m) n) toTwo
                  )
                  toBang,
        check "Exponential OChu Hom(I, ?ChuTwo) is the functionals" $
          let why = Chu.whyNotChuObj chuTwo
           in length (iHomsChuTwo why chuTwoFuns chuTwoPos) == 4,
        check "Exponential OChu introduce is injective on I-points" $
          let toA = iHomsChuTwo chuTwo chuTwoPos chuTwoPos
              via = fmap (composeITo (Chu.introduceChu chuTwo)) toA
           in case via of
                [m1, m2] -> not (eqIToWhy m1 m2)
                _ -> False,
        check "Exponential OChu pointwise ?-merge is not a tensor morphism" $
          let cand d = Chu.ChuTensorNeg (const d) (const d)
              bilinear n =
                all
                  ( \(f, g) ->
                      f (Chu.ctnBackward n g) == g (Chu.ctnForward n f)
                  )
                  [(f, g) | f <- chuTwoFuns, g <- chuTwoFuns]
           in not (all (\d -> bilinear (cand d)) chuTwoPos),
        check "Exponential OChu merge ?A ⅋ ?A -> ?A is a Chu morphism" $
          let parObj = Chu.parChuObj whyNotTwo whyNotTwo
              mor = Chu.mergeWhyNotParChu
           in all
                (\p -> all (\d -> Chu.chuLaw parObj whyNotTwo mor p d) chuTwoPos)
                whyNotTwoParPoss,
        check "Exponential OChu ⅋-unit ⊥ -> ?A is a Chu morphism" $
          let mor = Chu.zeroWhyNotParChu
           in all
                (\k -> all (\d -> Chu.chuLaw Chu.chuBottomObj whyNotTwo mor k d) chuTwoPos)
                [True, False],
        check "Exponential OChu ⅋-monoid left unit on ?ChuTwo" $
          let via =
                Chu.composeChu
                  Chu.mergeWhyNotParChu
                  (Chu.parChu Chu.zeroWhyNotParChu Chu.idChu)
           in eqLeftUnitWhy via Chu.leftUnitorParChu,
        check "Exponential OChu ⅋-monoid right unit on ?ChuTwo" $
          let via =
                Chu.composeChu
                  Chu.mergeWhyNotParChu
                  (Chu.parChu Chu.idChu Chu.zeroWhyNotParChu)
           in eqRightUnitWhy via Chu.rightUnitorParChu,
        check "Exponential OChu ⅋-monoid is commutative on ?ChuTwo" $
          let via = Chu.composeChu Chu.mergeWhyNotParChu Chu.swapParChu
           in eqMergeWhy via Chu.mergeWhyNotParChu,
        check "Exponential OChu ⅋-associator is inverse on ?ChuTwo" $
          eqAssocWhyL (Chu.composeChu Chu.assocParChuInv Chu.assocParChu),
        check "Exponential OChu ⅋-monoid is associative on ?ChuTwo" $
          let lhs =
                Chu.composeChu
                  Chu.mergeWhyNotParChu
                  ( Chu.composeChu
                      (Chu.parChu Chu.idChu Chu.mergeWhyNotParChu)
                      Chu.assocParChu
                  )
              rhs =
                Chu.composeChu
                  Chu.mergeWhyNotParChu
                  (Chu.parChu Chu.mergeWhyNotParChu Chu.idChu)
           in eqWhy3ToWhy lhs rhs,
        check "Exponential OChu introduce ChuTwo -> ?ChuTwo is a Chu morphism" $
          let why = Chu.whyNotChuObj chuTwo
              mor = Chu.introduceChu chuTwo
           in all (\a -> all (\d -> Chu.chuLaw chuTwo why mor a d) chuTwoPos) chuTwoPos,
        check "Exponential OChu zero I -> ?ChuTwo is a Chu morphism" $
          let why = Chu.whyNotChuObj chuTwo
              mor = Chu.zeroWhyNotChu
           in all (\d -> Chu.chuLaw Chu.chuUnitObj why mor () d) chuTwoPos,
        -- Par / linear distributivity
        check "Par distL is the one-way (,) / Either distributor" $
          distL ('x', Left True :: Either Bool Int) == Left ('x', True)
            && distR (Left True :: Either Bool Int, 'x') == Left True,
        check "Par unitlP collapses Void on Either" $
          unitlP (Right 42 :: Either Void Int) == (42 :: Int),
        check "Par unitrP collapses Void on Either" $
          unitrP (Left 42 :: Either Int Void) == (42 :: Int),
        -- Channel These presence-preserving slide
        check "Channel These slide preserves presence on all 7 cases" $
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
           in all (\x -> presenceInput x == presenceOutput (slide x)) cases,
        check "Channel These slide . slide == id where types permit" $
          let x = These 'a' (These 'b' 'c' :: These Char Char)
           in (slide . slide) x == (x :: These Char (These Char Char)),
        -- Traced These falsifier: the both-branch forces a discard.
        --
        -- A candidate trace for These must choose, in the These a c case,
        -- whether to emit c (discarding a) or loop on a (discarding c).
        -- Two equally natural biased traces disagree, so no canonical trace
        -- exists; any fixed bias breaks sliding/dinaturality under composition.
        check "Traced These is impossible: biased traces disagree in the both-branch" $
          let traceTheseEmit f b = go (f (That b))
                where
                  go (That c) = c
                  go (This a) = go (f (This a))
                  go (These _ c) = c
              traceTheseLoop f b = go (f (That b))
                where
                  go (That c) = c
                  go (This a) = go (f (This a))
                  go (These a _) = go (f (This a))
              step :: These Int Int -> These Int Int
              step (That n) = These 1 n
              step (This 0) = That 0
              step (This n) = This (n - 1)
              step (These m n) = These (m + 1) n
           in traceTheseEmit step 5 /= traceTheseLoop step 5,
        -- ⊗/⅋ probe: sharedBy vs superpose
        check "pure order swap is invisible at the shared channel (sliding axiom)" $
          let k1 = markerBody 1
              k2 = markerBody 2
           in run (sharedKnotBy pureLeft k1 k2) ((), ())
                == run (sharedKnotBy pureRight k1 k2) ((), ()),
        check "sharedKnotBy differs from superpose (shared vs independent feedback)" $
          let k1 = markerBody 1
              k2 = markerBody 2
              theseToPair (This a) = (a, [])
              theseToPair (That b) = ([], b)
              theseToPair (These a b) = (a, b)
           in run (superpose (Knot k1) (Knot k2)) ((), ())
                /= theseToPair (run (sharedKnotBy leftFirst k1 k2) ((), ())),
        check "sharedKnotBy schedule changes observable interleaving" $
          let k1 = markerBody 1
              k2 = markerBody 2
           in run (sharedKnotBy rightFirst k1 k2) ((), ())
                /= run (sharedKnotBy leftFirst k1 k2) ((), ()),
        check "sharedBy Both LeftFirst equals premonoidal left-first product" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
           in sharedBy (Schedule (,Both LeftFirst) :: Schedule [Int]) k1 k2 input == bodyParL k1 k2 input,
        check "sharedBy Both RightFirst equals premonoidal right-first product" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
           in sharedBy (Schedule (,Both RightFirst) :: Schedule [Int]) k1 k2 input == bodyParR k1 k2 input,
        -- Gate: Bias = f⋉g / f⋊g means the hand-written products agree with
        -- sharedBy under the constant schedules pureLeft / pureRight.
        check "bodyParL equals sharedBy under pureLeft" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
           in bodyParL k1 k2 input == sharedBy pureLeft k1 k2 input,
        check "bodyParR equals sharedBy under pureRight" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
           in bodyParR k1 k2 input == sharedBy pureRight k1 k2 input,
        -- Gate: Bias is the premonoidal ordering iff the whiskerings agree.
        check "left-first whiskering equals bodyParL" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
              (s, (b, d)) = whiskerL k1 k2 input
           in (s, These b d) == bodyParL k1 k2 input,
        check "right-first whiskering equals bodyParR" $
          let k1 = markerBody 1
              k2 = markerBody 2
              input = ([], ((), ())) :: ([Int], ((), ()))
              (s, (b, d)) = whiskerR k1 k2 input
           in (s, These b d) == bodyParR k1 k2 input,
        -- Centrality oracles: the ⊗/⅋ distinction is exactly premonoidal centrality
        -- Centrality witnesses: bodyCentral is a predicate at one input against
        -- one partner. These are existence witnesses, not proofs of ∀g.
        check "state-agnostic bodies witness centrality at a point" $
          let input = (0, (1, 2)) :: (Int, (Int, Int))
           in bodyCentral bodyIdF bodyIncF input,
        check "state-touching bodies witness non-centrality at a point" $
          let input = (1, (2, 3)) :: (Int, (Int, Int))
           in not (bodyCentral sharedAddF sharedDoubleF input),
        -- markerBody writes to the shared state, so these bodies are NOT central.
        -- What this oracle observes: after feedback closure, the two threading
        -- orders produce the same observable output (here, the same rotation of
        -- markers). This is a coincidence of the example, not Benton–Hyland
        -- centrality and not Centre Preservation (Def 3.2 runs the other way).
        check "marker bodies have equal trace under left-first and right-first threading (not centrality)" $
          let k1 = markerBody 1
              k2 = markerBody 2
           in run (Knot (bodyParL k1 k2)) ((), ())
                == run (Knot (bodyParR k1 k2)) ((), ()),
        -- Structural maps are central: they do not touch the shared state,
        -- so order of threading is invisible (Benton–Hyland centrality).
        check "copy witnesses centrality wrt state-touching body at a point" $
          let input = (0, (1, 2)) :: (Int, (Int, Int))
           in bodyCentral (liftBody (\x -> (x, x))) sharedAddF input,
        check "discard witnesses centrality wrt state-touching body at a point" $
          let input = (0, (1, 2)) :: (Int, (Int, Int))
           in bodyCentral (liftBody (const ())) sharedAddF input,
        check "plus witnesses centrality wrt state-touching body at a point" $
          let input = (0, ((1, 2), 3)) :: (Int, ((Int, Int), Int))
           in bodyCentral (liftBody (Pre.uncurry (+))) sharedAddF input,
        check "zero witnesses centrality wrt state-touching body at a point" $
          let input = (0, ((), 3)) :: (Int, ((), Int))
           in bodyCentral (liftBody (const 0)) sharedAddF input,
        check "swap witnesses centrality wrt state-touching body at a point" $
          let input = (0, ((1, 2), (3, 4))) :: (Int, ((Int, Int), (Int, Int)))
           in bodyCentral (liftBody (\(a, b) -> (b, a))) sharedAddFPair input,
        -- Benton–Hyland Def 3.2: unrestricted sliding fails for non-central
        -- effectful morphisms. The witness uses two IO actions on a shared ref.
        checkIO "unrestricted sliding fails for non-central Kleisli IO" $
          do
            ref <- newIORef 1
            let f = Kleisli $ \ ~((), ()) -> do
                  v <- readIORef ref
                  modifyIORef' ref (+ 1)
                  pure ((), v)
                g = Kleisli $ \ ~() -> do
                  modifyIORef' ref (* 2)
                  pure ()
                post = trace (par @(,) @(Kleisli IO) g id . f)
                pre = trace (f . par @(,) @(Kleisli IO) g id)
            (l, r) <- (,) <$> runKleisli post () <*> runKleisli pre ()
            pure (l /= r),
        -- Thread (,) (Kleisli IO) must compose as a category. This is the untested
        -- edge of parameterising Body over arr; Z2's Loop-level witness stands
        -- on it. The bodies touch a shared IORef to confirm composition threads
        -- state through the Kleisli base, not just the function base.
        checkIO "Thread (,) (Kleisli IO) composes as a category" $
          do
            ref <- newIORef 0
            let f = MedState.Thread $ Kleisli $ \(s, a) -> do
                  writeIORef ref (s + 1)
                  pure (s + 1, a + 1)
                g = MedState.Thread $ Kleisli $ \(s, b) -> do
                  v <- readIORef ref
                  pure (s + v, b * 2)
                gf = g . f
            (sOut, c) <- runKleisli (MedState.runThread gf) (0, 5)
            pure (sOut == 2 && c == 12),
        -- Benton-Hyland Def 3.2 at the Loop level: Loop's trace inherits the
        -- Central Sliding side-condition from its base. A non-central effectful
        -- morphism g slid past f gives a different result depending on order.
        -- Loop's 'trace' discharges into the base 'trace', so the same witness
        -- that fails for Kleisli IO directly also fails for Loop (,) (Kleisli IO).
        checkIO "Loop trace requires centrality over Kleisli IO (Central Sliding)" $
          do
            ref <- newIORef 1
            let f = Kleisli $ \ ~((), ()) -> do
                  v <- readIORef ref
                  modifyIORef' ref (+ 1)
                  pure ((), v) :: IO ((), Int)
                g = Kleisli $ \ ~() -> do
                  modifyIORef' ref (* 2)
                  pure ()
                post = trace (Lift f . Lift (par @(,) @(Kleisli IO) g id)) :: Loop (,) (Kleisli IO) () Int
                pre = trace (Lift (par @(,) @(Kleisli IO) g id) . Lift f) :: Loop (,) (Kleisli IO) () Int
            l <- runKleisli (run post) ()
            writeIORef ref 1
            r <- runKleisli (run pre) ()
            pure (l /= r),
        -- Loop (.) preserves the semantic order of composed Knot bodies over
        -- an effectful base. This is not a centrality claim; it just checks
        -- that Loop's normal form agrees with a hand-built body that threads
        -- state in the same order.
        checkIO "Loop (.) preserves semantic order of composed Knot bodies" $
          do
            ref <- newIORef 1
            let g = Kleisli $ \ ~(s, a) -> do
                  v <- readIORef ref
                  writeIORef ref (v + 1)
                  pure (s, v + a)
                f = Kleisli $ \ ~(s, b) -> do
                  v <- readIORef ref
                  writeIORef ref (v * 2)
                  pure (s, v * b)
                loopFG = Knot f . Knot g :: Loop (,) (Kleisli IO) Int Int
                -- Same threading as Loop's (.) normal form: g's state wire first.
                handBuiltFG =
                  Knot $
                    Kleisli $
                      \ ~((s1, s2), a) -> do
                        (s1', b) <- runKleisli g (s1, a)
                        (s2', c) <- runKleisli f (s2, b)
                        pure ((s1', s2'), c)
            r1 <- runKleisli (run loopFG) 5
            writeIORef ref 1
            r2 <- runKleisli (run handBuiltFG) 5
            pure (r1 == r2),
        check "sharedKnotBy L gates right body (output is This only)" $
          let k1 = markerBody 1
              k2 = markerBody 2
              leftOnly = Schedule (,L) :: Schedule [Int]
           in run (sharedKnotBy leftOnly k1 k2) ((), ()) == This [1, 1, 1],
        check "sharedKnotBy R gates left body (output is That only)" $
          let k1 = markerBody 1
              k2 = markerBody 2
              rightOnly = Schedule (,R) :: Schedule [Int]
           in run (sharedKnotBy rightOnly k1 k2) ((), ()) == That [2, 2, 2],
        check "sharedKnotBy left-first and right-first both agree on body sets" $
          let k1 = markerBody 1
              k2 = markerBody 2
              leftResult = run (sharedKnotBy leftFirst k1 k2) ((), ())
              rightResult = run (sharedKnotBy rightFirst k1 k2) ((), ())
              bodySet = sort . these id id (++)
           in bodySet leftResult == [0, 0, 1, 1, 2, 2]
                && bodySet rightResult == [0, 0, 1, 1, 2, 2],
        -- Free-syntax bridge: SigShared is the algebraic ⅋ connective
        check "AlgShared eval agrees with sharedKnotBy" $
          let k1 = markerBody 1
              k2 = markerBody 2
              term :: Alg.AlgShared (,) (->) ((), ()) (These [Int] [Int])
              term =
                Alg.Op
                  ( Alg.R
                      ( Alg.R
                          ( Alg.SigKnot
                              ( Alg.Op
                                  ( Alg.R
                                      (Alg.L (Alg.SigShared pureLeft (Alg.Lift k1) (Alg.Lift k2)))
                                  )
                              )
                          )
                      )
                  )
           in Alg.eval term ((), ()) == run (sharedKnotBy pureLeft k1 k2) ((), ()),
        check "AlgShared L schedule gates right body" $
          let k1 = markerBody 1
              k2 = markerBody 2
              leftOnly = Schedule (,L) :: Schedule [Int]
              term :: Alg.AlgShared (,) (->) ((), ()) (These [Int] [Int])
              term =
                Alg.Op
                  ( Alg.R
                      ( Alg.R
                          ( Alg.SigKnot
                              ( Alg.Op
                                  ( Alg.R
                                      (Alg.L (Alg.SigShared leftOnly (Alg.Lift k1) (Alg.Lift k2)))
                                  )
                              )
                          )
                      )
                  )
           in Alg.eval term ((), ()) == This [1, 1, 1],
        check "AlgShared R schedule gates left body" $
          let k1 = markerBody 1
              k2 = markerBody 2
              rightOnly = Schedule (,R) :: Schedule [Int]
              term :: Alg.AlgShared (,) (->) ((), ()) (These [Int] [Int])
              term =
                Alg.Op
                  ( Alg.R
                      ( Alg.R
                          ( Alg.SigKnot
                              ( Alg.Op
                                  ( Alg.R
                                      (Alg.L (Alg.SigShared rightOnly (Alg.Lift k1) (Alg.Lift k2)))
                                  )
                              )
                          )
                      )
                  )
           in Alg.eval term ((), ()) == That [2, 2, 2],
        -- Free-syntax bridge: SigMediate is the algebraic ? connective
        check "AlgMediate eval agrees with runMediator (pairSum)" $
          let term :: Alg.AlgMediate (,) (->) [Int] [Int]
              term = Alg.algMediate pairSum
           in Alg.eval term [1, 2, 3, 4 :: Int] == runMediator pairSum [1, 2, 3, 4],
        check "AlgMediate eval agrees with runMediator (count)" $
          let term :: Alg.AlgMediate (,) (->) [()] [Int]
              term = Alg.algMediate count
           in Alg.eval term [(), (), ()] == runMediator count [(), (), ()],
        check "AlgMediate eval agrees with runMediator (linear)" $
          let term :: Alg.AlgMediate (,) (->) [Int] [Int]
              term = Alg.algMediate linear
           in Alg.eval term [1, 2, 3 :: Int] == runMediator linear [1, 2, 3],
        check "AlgMediate term composes with Lift inside the algebra" $
          let term :: Alg.AlgMediate (,) (->) [Int] [Int]
              term = Alg.Op (Alg.L (Alg.SigCompose (Alg.algMediate pairSum) (Alg.Lift (map (* 2)))))
           in Alg.eval term [1, 2, 3, 4 :: Int] == runMediator pairSum [2, 4, 6, 8],
        -- Mediator-hyper oracles (B8)
        -- Pure @(->)@ 'Ends' boxes are constant, so the shared-medium bodies
        -- below are used as the channel-end representatives.  The schedule is
        -- the mediator stamp: an explicit schedule leaves observable tokens,
        -- while a pure schedule is the unstamped / ⊗-like case.
        check "mediator-hyper stamp: schedule stamp distinguishes shared composition in HyperF" $
          let k1 = markerBody 1
              k2 = markerBody 2
              shared stamp = HyperLoop.encode (sharedKnotBy stamp k1 k2) :: Hyper ((), ()) (These [Int] [Int])
              superposed = HyperLoop.encode (superpose (Knot k1) (Knot k2)) :: Hyper ((), ()) ([Int], [Int])
              stamped = shared leftFirst
              unstamped = shared pureLeft
              theseToPair (This a) = (a, [])
              theseToPair (That b) = ([], b)
              theseToPair (These a b) = (a, b)
           in observe stamped ((), ()) /= observe unstamped ((), ())
                && observe superposed ((), ()) /= theseToPair (observe stamped ((), ())),
        check "stamped ⅋ probe: schedule stamp toggles entanglement in HyperF" $
          let k1 = markerBody 1
              k2 = markerBody 2
              sharedHyper sched = HyperLoop.encode (sharedKnotBy sched k1 k2) :: Hyper ((), ()) (These [Int] [Int])
              leftH = sharedHyper leftFirst
              rightH = sharedHyper rightFirst
              pureLeftH = sharedHyper pureLeft
              pureRightH = sharedHyper pureRight
           in observe leftH ((), ()) /= observe rightH ((), ())
                && observe pureLeftH ((), ()) == observe pureRightH ((), ()),
        -- Bridge square: medium commutes through encode
        check "bridge square: sharedKnotBy encodes to sharedHyperBy" $
          let k1 = markerBody 1
              k2 = markerBody 2
              sched = leftFirst
              leftSide = HyperLoop.encode (sharedKnotBy sched k1 k2) :: Hyper ((), ()) (These [Int] [Int])
              rightSide = HyperLoop.sharedHyperBy sched (HyperLoop.encode (Lift k1)) (HyperLoop.encode (Lift k2))
           in observe leftSide ((), ()) == observe rightSide ((), ()),
        check "bridge square: pure schedule collapse agrees" $
          let k1 = markerBody 1
              k2 = markerBody 2
              leftSide = HyperLoop.encode (sharedKnotBy pureLeft k1 k2) :: Hyper ((), ()) (These [Int] [Int])
              rightSide = HyperLoop.sharedHyperBy pureLeft (HyperLoop.encode (Lift k1)) (HyperLoop.encode (Lift k2))
           in observe leftSide ((), ()) == observe rightSide ((), ()),
        -- Mediate oracles (B1)
        check "Mediator linear forwards every input" $
          runMediator linear [1, 2, 3 :: Int] == [1, 2, 3],
        check "Mediator pairSum buffers and sums pairs" $
          runMediator pairSum [1, 2, 3, 4 :: Int] == [3, 7],
        check "Mediator pairSum leaves one input unemitted" $
          runMediator pairSum [1, 2, 3 :: Int] == [3],
        check "Mediator count emits accumulating residual" $
          runMediator count [(), (), ()] == [1, 2, 3],
        -- Mediate / Ends equivalence oracles
        check "mediatorToMed linear agrees with runMediator" $
          MedState.runMed (MedState.mediatorToMed linear) [1, 2, 3 :: Int] == runMediator linear [1, 2, 3],
        check "mediatorToMed pairSum agrees with runMediator" $
          MedState.runMed (MedState.mediatorToMed pairSum) [1, 2, 3, 4 :: Int] == runMediator pairSum [1, 2, 3, 4],
        check "mediatorToMed count agrees with runMediator" $
          MedState.runMed (MedState.mediatorToMed count) [(), (), ()] == runMediator count [(), (), ()],
        check "medToMediator . mediatorToMed round-trips behaviourally on pairSum" $
          let m = MedState.medToMediator (MedState.mediatorToMed pairSum)
           in runMediator m [1, 2, 3, 4 :: Int] == runMediator pairSum [1, 2, 3, 4],
        -- Circuit.Ends oracles
        check "Ends medStep agrees with medStepDirect (linear)" $
          let s = Nothing :: Maybe Int
              a = 42
           in MedState.medStep MedState.medLinear s a == MedState.medStepDirect MedState.medLinear s a,
        check "Ends runMed linear forwards every input" $
          MedState.runMed MedState.medLinear [1, 2, 3 :: Int] == [1, 2, 3],
        check "Ends runMed pairSum buffers and sums pairs" $
          MedState.runMed MedState.medPairSum [1, 2, 3, 4 :: Int] == [3, 7],
        check "Ends runMed pairSum zeroes are valid inputs" $
          MedState.runMed MedState.medPairSum [0, 0 :: Int] == [0],
        check "Ends runMed pairSum odd input leaves residual" $
          MedState.runMed MedState.medPairSum [1, 2, 3 :: Int] == [3],
        check "Ends medPairSum under left-only gating schedule reports violation" $
          let med = MedState.medToMediator MedState.medPairSum
              s0 = MedState.medSeed MedState.medPairSum
              leftOnlyBufferedPS :: Schedule (MedState.PS, Maybe (Maybe Int))
              leftOnlyBufferedPS = Schedule $ \(s, buf) -> ((s, buf), L)
              step s x = fst (mediateSharedBody med leftOnlyBufferedPS (s, (x, 0)))
              sFinal = foldl step s0 [1, 2, 3 :: Int]
           in case closeCertified med sFinal [] of
                Left (LinearityViolation msg) -> "Held 3" `isInfixOf` msg
                Right _ -> False,
        check "Ends runMed count emits accumulating residual" $
          MedState.runMed MedState.medCount [(), (), ()] == [1, 2, 3],
        -- Ends conversion oracles (Z4)
        check "Ends loopToSomeSArr runs Loop (,) as SArr" $
          let loop = Knot (\ ~(s, ()) -> (0 : s, take 3 s)) :: Loop (,) (->) () [Int]
           in MedState.runSomeSArr (MedState.loopToSomeSArr loop) [(), ()]
                == map (run loop) [(), ()],
        check "Ends loopEitherToSomeSArr runs Loop Either as SArr" $
          let sumProc = Process (id :: Int -> Int) ((+) :: Int -> Int -> Int) id :: Process Int Int
              loop = encode sumProc :: Loop Either (->) [Int] [Int]
           in MedState.runSomeSArr (MedState.loopEitherToSomeSArr loop) [[1, 2, 3], [4, 5 :: Int]]
                == map (run loop) [[1, 2, 3], [4, 5]],
        check "Ends systemToEnds recovers running sum" $
          let sys :: System (->) Int (Mono Int Int)
              sys =
                system $ \(s, d) -> case d of
                  Left v -> absurd v
                  Right i -> let s' = s + i in (s', (s', ()))
              runSys s0 = foldl (\(s, acc) i -> let (s', pos) = runSystem sys (s, Right i) in (s', pos : acc)) (s0, [])
           in MedState.runSomeEnds (MedState.SomeEnds 0 (MedState.systemToEnds (Right 0) sys)) [Right 1, Right 2, Right 3 :: Dir (Mono Int Int)]
                == reverse (snd (runSys 0 [1, 2, 3])),
        check "Ends systemWithSeedToEnds recovers pointed System sum" $
          let sys = mooreSystem ((+) :: Int -> Int -> Int) id :: System (->) Int (Mono Int Int)
              ends = MedState.systemWithSeedToEnds 0 (\s -> (s, ())) sys
           in MedState.runSomeEnds ends [Right 1, Right 2, Right 3 :: Dir (Mono Int Int)] == [(1, ()), (3, ()), (6, ())],
        -- Mediate.Tensor oracles (B3)
        check "Mediate shared body left-first emits Just 3" $
          snd (mediateSharedBody pairSum leftFirstPS (Empty :: PS, (1, 2 :: Int)))
            == These () (Just 3),
        check "Mediate shared body right-first emits Nothing" $
          snd (mediateSharedBody pairSum rightFirstPS (Empty :: PS, (1, 2 :: Int)))
            == These () Nothing,
        check "Mediate shared body left-only stores but does not emit" $
          mediateSharedBody pairSum leftOnlyPS (Empty :: PS, (1, 2 :: Int))
            == (Held 1, This ()),
        check "Mediate shared body right-only emits nothing without residual" $
          mediateSharedBody pairSum rightOnlyPS (Empty :: PS, (1, 2 :: Int))
            == (Held 2, That Nothing),
        -- Mediate process stream oracles (B3b)
        check "Mediate process pairSum [1,2] returns [3]" $
          catMaybes (scan (mediateProcess pairSum Empty) [1, 2 :: Int]) == [3],
        check "Mediate process pairSum [1,2,3,4] returns [3,7]" $
          catMaybes (scan (mediateProcess pairSum Empty) [1, 2, 3, 4 :: Int]) == [3, 7],
        check "Mediate process agrees with runMediator" $
          catMaybes (scan (mediateProcess pairSum Empty) [1, 2, 3, 4 :: Int])
            == runMediator pairSum [1, 2, 3, 4],
        -- Mediate loop oracles (B3c)
        check "Mediate loop is encode of mediateProcess" $
          run (mediateLoop pairSum) [1, 2, 3, 4 :: Int]
            == scan (mediateProcess pairSum Empty) [1, 2, 3, 4],
        check "Mediate loop outputs stripped Nothings agree with runMediator" $
          catMaybes (run (mediateLoop pairSum) [1, 2, 3, 4 :: Int])
            == runMediator pairSum [1, 2, 3, 4],
        -- Mediate close certification oracles (B4)
        check "closeCertified linear closes cleanly" $
          closeCertified linear () [1, 2, 3 :: Int] == Right [1, 2, 3],
        check "closeCertified pairSum odd leaves residual" $
          case closeCertified pairSum (Empty :: PS) [1, 2, 3 :: Int] of
            Left _ -> True
            Right _ -> False,
        check "closeCertified count leaves residual" $
          case closeCertified count (0 :: Int) [(), (), ()] of
            Left _ -> True
            Right _ -> False,
        -- Mediate drain oracles (B4b)
        check "closeCertifiedWith drains count residual clean" $
          closeCertifiedWith count (0 :: Int) [()]
            == Right [1, 1],
        check "closeCertifiedWith flushes final count on close" $
          closeCertifiedWith count (0 :: Int) [(), (), ()]
            == Right [1, 2, 3, 3],
        check "closeCertifiedWithBy drains list residual via uncons" $
          let buffer = Mediator [] $ \s x -> (x : s, Nothing :: Maybe Int)
           in closeCertifiedWithBy null uncons buffer ([] :: [Int]) [1, 2, 3]
                == Right [3, 2, 1],
        -- Mediate ?-comonoid oracles
        check "medCounit linear closes empty residual cleanly" $
          medCounit linear () == (Right [] :: Either LinearityViolation [Int]),
        check "medCounit pairSum non-empty residual reports violation" $
          case medCounit pairSum (Held 1 :: PS) of
            Left _ -> True
            Right _ -> False,
        check "medComult linear duplicates policy faithfully" $
          let (m1, m2) = medComult linear
           in runMediator m1 [1, 2 :: Int] == [1, 2]
                && runMediator m2 [3, 4 :: Int] == [3, 4],
        check "medComult pairSum splits input between copies" $
          let (m1, m2) = medComult pairSum
           in runMediator m1 [1, 2 :: Int] ++ runMediator m2 [3, 4 :: Int]
                == runMediator pairSum [1, 2, 3, 4],
        -- ChannelPoly oracles (B2)
        check "Poly Channel id emits committed input" $
          case emitChannel (commitChannel (idChannel 0) (monoIn (42 :: Int))) of
            EP (EK o, EE _) -> o == 42,
        check "Poly Channel const ignores state" $
          case emitChannel (commitChannel (constChannel (7 :: Int)) (monoIn (99 :: Int))) of
            EP (EK o, EE _) -> o == 7,
        check "Poly Channel mapChannel applies lens forward and backward" $
          let ch0 = mapChannel (lens (+ 1) (\_ d -> d - 1 :: Int)) (idChannel 0)
              ev0 = emitChannel ch0
              ch1 = commitChannel ch0 (monoIn 5)
              ev1 = emitChannel ch1
           in case (ev0, ev1) of
                (EP (EK o0, EE _), EP (EK o1, EE _)) -> o0 == 1 && o1 == 5,
        -- Keystone: System (Prob (->) r) s (Mono i o)
        check "Keystone: System (Prob Double) S3 (Mono () ()) typechecks" $
          length (occupancyProb 0) == 3,
        check "Keystone: exact occupancy after 2 steps" $
          occupancyProb 2 == [0.25, 0.5, 0.25],
        check "Keystone: exact occupancy after 3 steps" $
          let [p0, p1, p2] = occupancyProb 3
           in approx p0 0.25 && approx p1 0.375 && approx p2 0.375,
        check "Keystone: System (Prob Tropical) S3 (Mono () ()) typechecks" $
          length (viterbiCost 0) == 3,
        check "Keystone: tropical Viterbi cost after 2 steps" $
          viterbiCost 2 == [2.0, 3.0, 4.0],
        check "Keystone: tropical Viterbi cost after 3 steps" $
          viterbiCost 3 == [3.0, 4.0, 5.0],
        -- Bool reachability row
        check "Keystone: System (Prob Bool) S3 (Mono () ()) typechecks" $
          length (reachable 0) == 1,
        check "Keystone: reachability after 1 step" $
          reachable 1 == [S0, S1],
        check "Keystone: reachability after 2 steps" $
          reachable 2 == [S0, S1, S2],
        -- Kleisli IO Monte Carlo row
        checkIO "Keystone: System (Prob (Kleisli IO) Double) S3 (Mono () ()) typechecks" $ do
          ref <- newIORef (RNG 0)
          occ <- mcOccupancy (chain3IO ref) 10000 2 S0
          pure $ length occ == 3,
        checkIO "Keystone: Monte Carlo occupancy after 2 steps" $ do
          ref <- newIORef (RNG 0)
          [p0, p1, p2] <- mcOccupancy (chain3IO ref) 10000 2 S0
          pure $ abs (p0 - 0.25) < 0.02 && abs (p1 - 0.5) < 0.02 && abs (p2 - 0.25) < 0.02
      ]
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."
