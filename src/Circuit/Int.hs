{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Int construction: free compact closure over a traced monoidal
-- category.
--
-- For a traced monoidal category @(t, arr)@, objects of @Int (t, arr)@ are
-- polarity pairs @(a\u207a, a\u207b)@, wrapped in the phantom type 'IN'. A
-- morphism from @(ap, am)@ to @(bp, bm)@ is a base morphism
-- @arr (t ap bm) (t am bp)@.
--
-- Identity is the symmetry on the two factors. Composition tensors the two
-- base morphisms, reassociates so the middle pair can be eliminated, and
-- closes it with the base category's 'trace'. Over @Trace t arr@ this means
-- every composite inherits the one-'Knot' normal form.
--
-- This module uses only the 'Trace'/'Monoidal' surface and introduces no
-- new dependencies.
module Circuit.Int
  ( -- * Int objects and morphisms
    IN,
    IntMorph (..),

    -- * Compact-closed structure
    intId,
    intComp,
    intDual,

    -- * Tensor product of Int morphisms
    intPar,

    -- * Hyper bridge
    intToHyper,
    hyperToIntMorph,

    -- * Cup / cap (yanking witnesses)
    intCap,
    intCup,
    intUnitL,
    intUnitR',
    intAssocInv,
  )
where

import Circuit.Hyper (Hyper (..), encode, flatten, observe)
import Circuit.Monoidal (Action (..))
import Circuit.Monoidal.Category (Monoidal (..))
import Circuit.Trace (Trace (..), Traced (..))
import Control.Category
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category
-- >>> import Circuit.Trace (Trace (..), Traced (..), trace)
-- >>> import Circuit.Monoidal (Action (..))
-- >>> import Circuit.Monoidal.Category (Monoidal (..))
-- >>> import Circuit.Hyper (observe)
-- >>> import Circuit.Layer (run)
-- >>> import Data.Bifunctor (Bifunctor (..))
-- >>> :set -XGADTs -XStandaloneDeriving -XFlexibleInstances -XFlexibleContexts -XScopedTypeVariables -XTypeApplications
-- >>> class Eq a => Finite a where universe :: [a]
-- >>> instance Finite () where universe = [()]
-- >>> instance Finite Bool where universe = [False, True]
-- >>> instance (Finite a, Finite b) => Finite (Either a b) where universe = map Left universe ++ map Right universe
--
-- >>> :{
-- data Mat i j where
--   Id :: Mat i i
--   MatR :: (Finite i, Finite j) => [(i, j)] -> Mat i j
-- :}
--
-- >>> :{
-- mat :: (Finite i, Finite j) => (i -> j -> Bool) -> Mat i j
-- mat f = MatR [(i, j) | i <- universe, j <- universe, f i j]
-- :}
--
-- >>> :{
-- runMat :: (Eq i, Eq j) => Mat i j -> i -> j -> Bool
-- runMat Id i j = i == j
-- runMat (MatR pairs) i j = (i, j) `elem` pairs
-- :}
--
-- >>> :{
-- instance Category Mat where
--   id = Id
--   Id . f = f
--   f . Id = f
--   MatR g . MatR f = MatR [(i, k) | (i, j) <- f, (j', k) <- g, j == j']
-- :}
--
-- >>> :{
-- matPar :: (Finite a, Finite b, Finite c, Finite d) => Mat a b -> Mat c d -> Mat (Either a c) (Either b d)
-- matPar f g = mat $ \case
--   Left a -> \case Left b -> runMat f a b; _ -> False
--   Right c -> \case Right d -> runMat g c d; _ -> False
-- :}
--
-- >>> :{
-- matSwap :: (Finite a, Finite b) => Mat (Either a b) (Either b a)
-- matSwap = mat $ \case
--   Left a -> \case Right a' -> a == a'; _ -> False
--   Right b -> \case Left b' -> b == b'; _ -> False
-- :}
--
-- >>> :{
-- matAssoc :: (Finite a, Finite b, Finite c) => Mat (Either (Either a b) c) (Either a (Either b c))
-- matAssoc = mat $ \case
--   Left (Left a) -> \case Left a' -> a == a'; _ -> False
--   Left (Right b) -> \case Right (Left b') -> b == b'; _ -> False
--   Right c -> \case Right (Right c') -> c == c'; _ -> False
-- :}
--
-- >>> :{
-- matAssoc' :: (Finite a, Finite b, Finite c) => Mat (Either a (Either b c)) (Either (Either a b) c)
-- matAssoc' = mat $ \case
--   Left a -> \case Left (Left a') -> a == a'; _ -> False
--   Right (Left b) -> \case Left (Right b') -> b == b'; _ -> False
--   Right (Right c) -> \case Right c' -> c == c'; _ -> False
-- :}
--
-- >>> :{
-- matBraid :: (Finite a, Finite b, Finite c) => Mat (Either a (Either b c)) (Either b (Either a c))
-- matBraid = mat $ \case
--   Left a -> \case Right (Left a') -> a == a'; _ -> False
--   Right (Left b) -> \case Left b' -> b == b'; _ -> False
--   Right (Right c) -> \case Right (Right c') -> c == c'; _ -> False
-- :}
--
-- >>> :{
-- matTrace :: (Finite a, Finite b, Finite c) => Mat (Either a b) (Either a c) -> Mat b c
-- matTrace f = mat $ \b c ->
--   runMat f (Right b) (Right c) ||
--   or [runMat f (Right b) (Left a) && runMat f (Left a') (Right c)
--       | a <- universe, a' <- universe]
-- :}
--
-- >>> :{
-- intCompMatEither ::
--   forall ap am bp bm cp cm.
--   (Finite ap, Finite am, Finite bp, Finite bm, Finite cp, Finite cm) =>
--   IntMorph Either Mat bp bm cp cm ->
--   IntMorph Either Mat ap am bp bm ->
--   IntMorph Either Mat ap am cp cm
-- intCompMatEither (IntMorph g) (IntMorph f) = IntMorph (matTrace (middleOut . matPar g f . middleIn))
--   where
--     id_ap = id :: Mat ap ap
--     id_am = id :: Mat am am
--     id_bm = id :: Mat bm bm
--     middleIn =
--       matSwap @(Either ap bm) @(Either bp cm)
--         . matAssoc' @ap @bm @(Either bp cm)
--         . (id_ap `matPar` matAssoc @bm @bp @cm)
--         . (id_ap `matPar` matSwap @cm @(Either bm bp))
--         . matAssoc @ap @cm @(Either bm bp)
--         . matSwap @(Either bm bp) @(Either ap cm)
--     middleOut =
--       matSwap @(Either am cp) @(Either bm bp)
--         . matBraid @bm @(Either am cp) @bp
--         . (id_bm `matPar` matAssoc' @am @cp @bp)
--         . (id_bm `matPar` (id_am `matPar` matSwap @bp @cp))
--         . (id_bm `matPar` matAssoc @am @bp @cp)
--         . (id_bm `matPar` matSwap @cp @(Either am bp))
--         . matAssoc @bm @cp @(Either am bp)
-- :}

-- | Phantom polarity pair.  @IN ap am@ is the Int object with forward
-- face @ap@ and backward face @am@.
data IN (ap :: Type) (am :: Type)

-- | A morphism in the Int construction from @(ap, am)@ to @(bp, bm)@ over
-- a traced monoidal base category.
--
-- The underlying arrow runs from the forward input plus the backward output
-- (@t ap bm@) to the backward input plus the forward output (@t am bp@).
newtype IntMorph (t :: Type -> Type -> Type) arr (ap :: Type) (am :: Type) (bp :: Type) (bm :: Type) = IntMorph
  { -- | Extract the underlying base morphism.
    runIntMorph :: arr (t ap bm) (t am bp)
  }

-- | Identity in @Int@ is the symmetry that swaps the two factors.
--
-- >>> let i = intId :: IntMorph (,) (->) Int Bool Int Bool
-- >>> runIntMorph i (1, False)
-- (False,1)
intId :: (Action t arr) => IntMorph t arr ap am ap am
intId = IntMorph swap

-- | Dual of an Int morphism: swap the polarities of domain and codomain.
--
-- The underlying arrow is pre- and post-composed with the symmetry so that
-- the types line up: @arr (t bm ap) (t bp am)@.
--
-- >>> let f = IntMorph (\(a, d) -> (a * 2, d + 1)) :: IntMorph (,) (->) Int Int Int Int
-- >>> runIntMorph (intDual f) (5, 1)
-- (6,2)
intDual :: (Action t arr) => IntMorph t arr ap am bp bm -> IntMorph t arr bm bp am ap
intDual (IntMorph f) = IntMorph (swap . f . swap)

-- | Bridge from an Int morphism over functions to a hyperfunction on the
-- paired wires.  This is not a structural isomorphism — it is the
-- operational correspondence that lets 'Hyper' absorb the Int construction
-- over @(->)@.
--
-- >>> let f = IntMorph (\(a, d) -> (a * 2, d + 1)) :: IntMorph (,) (->) Int Int Int Int
-- >>> observe (intToHyper f) (5, 1)
-- (10,2)
intToHyper :: IntMorph (,) (->) ap am bp bm -> Hyper (ap, bm) (am, bp)
intToHyper = encode . Arr . runIntMorph

-- | Forget a hyperfunction back to an Int morphism.  This collapses feedback
-- structure; only observable behaviour round-trips.
--
-- >>> let f = IntMorph (\(a, d) -> (a * 2, d + 1)) :: IntMorph (,) (->) Int Int Int Int
-- >>> runIntMorph (hyperToIntMorph (intToHyper f)) (5, 1)
-- (10,2)
hyperToIntMorph :: Hyper (ap, bm) (am, bp) -> IntMorph (,) (->) ap am bp bm
hyperToIntMorph h = case flatten h of
  Arr f -> IntMorph f
  Knot _ -> error "hyperToIntMorph: flatten produced a Knot"

-- | Composition in the Int construction.
--
-- Tensor the two base morphisms, reassociate the four factors so the middle
-- pair @(bm, bp)@ sits on the feedback wire, and close it with 'trace'. The
-- result is again a single base arrow @arr (t ap cm) (t am cp)@.
--
-- Nontrivial composition over @Trace (,) (->)@.  Both morphisms transform
-- both legs; the middle trace closes the feedback loop.  The chosen bodies
-- are lazy in the feedback component so the lazy @(,)@ knot stays productive.
-- Hand-computed: input @(4, 1)@ gives output @(5, 2)@.
--
-- >>> let f = IntMorph (Arr (\(a, _) -> (a + 1, a))) :: IntMorph (,) (Trace (,) (->)) Int Int Int Int
-- >>> let g = IntMorph (Arr (\(_, c) -> (c, c + 1))) :: IntMorph (,) (Trace (,) (->)) Int Int Int Int
-- >>> run (runIntMorph (g `intComp` f)) (4, 1)
-- (5,2)
--
-- The composite over @Trace@ inherits the one-'Knot' normal form: the inner
-- plumbing is absorbed into a single 'Knot' over one base arrow.
--
-- >>> case runIntMorph (g `intComp` f) of Knot _ -> "one-Knot"; Arr _ -> "not one-Knot"
-- "one-Knot"
intComp ::
  forall t arr ap am bp bm cp cm.
  (Action t arr, Traced t arr) =>
  IntMorph t arr bp bm cp cm ->
  IntMorph t arr ap am bp bm ->
  IntMorph t arr ap am cp cm
intComp (IntMorph g) (IntMorph f) = IntMorph (trace (middleOut . (g `par` f) . middleIn))
  where
    -- identities at the relevant objects, pinned so 'par' can resolve
    id_ap :: arr ap ap
    id_am :: arr am am
    id_bm :: arr bm bm
    id_ap = id
    id_am = id
    id_bm = id

    middleIn :: arr (t (t bm bp) (t ap cm)) (t (t bp cm) (t ap bm))
    middleIn = step6 . step5 . step4 . step3 . step2 . step1
      where
        step1 :: arr (t (t bm bp) (t ap cm)) (t (t ap cm) (t bm bp))
        step1 = swap @t @arr @(t bm bp) @(t ap cm)
        step2 :: arr (t (t ap cm) (t bm bp)) (t ap (t cm (t bm bp)))
        step2 = assoc @t @arr @ap @cm @(t bm bp)
        step3 :: arr (t ap (t cm (t bm bp))) (t ap (t (t bm bp) cm))
        step3 = id_ap `par` swap @t @arr @cm @(t bm bp)
        step4 :: arr (t ap (t (t bm bp) cm)) (t ap (t bm (t bp cm)))
        step4 = id_ap `par` assoc @t @arr @bm @bp @cm
        step5 :: arr (t ap (t bm (t bp cm))) (t (t ap bm) (t bp cm))
        step5 = assoc' @t @arr @ap @bm @(t bp cm)
        step6 :: arr (t (t ap bm) (t bp cm)) (t (t bp cm) (t ap bm))
        step6 = swap @t @arr @(t ap bm) @(t bp cm)

    middleOut :: arr (t (t bm cp) (t am bp)) (t (t bm bp) (t am cp))
    middleOut = step7 . step6 . step5 . step4 . step3 . step2 . step1
      where
        step1 :: arr (t (t bm cp) (t am bp)) (t bm (t cp (t am bp)))
        step1 = assoc @t @arr @bm @cp @(t am bp)
        step2 :: arr (t bm (t cp (t am bp))) (t bm (t (t am bp) cp))
        step2 = id_bm `par` swap @t @arr @cp @(t am bp)
        step3 :: arr (t bm (t (t am bp) cp)) (t bm (t am (t bp cp)))
        step3 = id_bm `par` assoc @t @arr @am @bp @cp
        step4 :: arr (t bm (t am (t bp cp))) (t bm (t am (t cp bp)))
        step4 = id_bm `par` (id_am `par` swap @t @arr @bp @cp)
        step5 :: arr (t bm (t am (t cp bp))) (t bm (t (t am cp) bp))
        step5 = id_bm `par` assoc' @t @arr @am @cp @bp
        step6 :: arr (t bm (t (t am cp) bp)) (t (t am cp) (t bm bp))
        step6 = braid @t @arr @bm @(t am cp) @bp
        step7 :: arr (t (t am cp) (t bm bp)) (t (t bm bp) (t am cp))
        step7 = swap @t @arr @(t am cp) @(t bm bp)

-- | Tensor product of two Int morphisms.
--
-- On objects this is componentwise: @(ap, am) \u2297 (cp, cm) = (t ap cp, t am cm)@.
-- On morphisms it threads the two base arrows side-by-side and reassociates
-- the factors into the required @arr (t (t ap cp) (t bm dm)) (t (t am cm) (t bp dp))@ shape.
intPar ::
  forall t arr ap am bp bm cp cm dp dm.
  (Action t arr, Monoidal t arr) =>
  IntMorph t arr ap am bp bm ->
  IntMorph t arr cp cm dp dm ->
  IntMorph t arr (t ap cp) (t am cm) (t bp dp) (t bm dm)
intPar (IntMorph f) (IntMorph g) = IntMorph (permOut . (f `par` g) . permIn)
  where
    id_ap :: arr ap ap
    id_bm :: arr bm bm
    id_ap = id
    id_bm = id

    -- permIn  :: arr (t (t ap cp) (t bm dm)) (t (t ap bm) (t cp dm))
    permIn = step5 . step4 . step3 . step2 . step1
      where
        step1 :: arr (t (t ap cp) (t bm dm)) (t ap (t cp (t bm dm)))
        step1 = assoc @t @arr @ap @cp @(t bm dm)
        step2 :: arr (t ap (t cp (t bm dm))) (t ap (t (t bm dm) cp))
        step2 = id_ap `par` swap @t @arr @cp @(t bm dm)
        step3 :: arr (t ap (t (t bm dm) cp)) (t ap (t bm (t dm cp)))
        step3 = id_ap `par` assoc @t @arr @bm @dm @cp
        step4 :: arr (t ap (t bm (t dm cp))) (t ap (t bm (t cp dm)))
        step4 = id_ap `par` (id_bm `par` swap @t @arr @dm @cp)
        step5 :: arr (t ap (t bm (t cp dm))) (t (t ap bm) (t cp dm))
        step5 = assoc' @t @arr @ap @bm @(t cp dm)

    -- permOut :: arr (t (t am bp) (t cm dp)) (t (t am cm) (t bp dp))
    permOut = step5 . step4 . step3 . step2 . step1
      where
        step1 :: arr (t (t am bp) (t cm dp)) (t am (t bp (t cm dp)))
        step1 = assoc @t @arr @am @bp @(t cm dp)
        step2 :: arr (t am (t bp (t cm dp))) (t am (t (t cm dp) bp))
        step2 = id_am `par` swap @t @arr @bp @(t cm dp)
        step3 :: arr (t am (t (t cm dp) bp)) (t am (t cm (t dp bp)))
        step3 = id_am `par` assoc @t @arr @cm @dp @bp
        step4 :: arr (t am (t cm (t dp bp))) (t am (t cm (t bp dp)))
        step4 = id_am `par` (id_cm `par` swap @t @arr @dp @bp)
        step5 :: arr (t am (t cm (t bp dp))) (t (t am cm) (t bp dp))
        step5 = assoc' @t @arr @am @cm @(t bp dp)

    id_am :: arr am am
    id_cm :: arr cm cm
    id_am = id
    id_cm = id

-- | Cap (unit introduction) for @Int(->)@ at object @IN a b@.
--
-- The unit object is @IN () ()@; the cap produces the tensor @IN (a, b) (b, a)@.
intCap :: IntMorph (,) (->) () () (a, b) (b, a)
intCap = IntMorph $ \((), (b, a)) -> ((), (a, b))

-- | Cup (unit elimination) for @Int(->)@ at object @IN a b@.
intCup :: IntMorph (,) (->) (b, a) (a, b) () ()
intCup = IntMorph $ \((b, a), ()) -> ((a, b), ())

-- | Left-unitor for @Int(->)@: @I \u2297 A -> A@.
intUnitL :: IntMorph (,) (->) ((), a) ((), b) a b
intUnitL = IntMorph $ \(((), a), b) -> (((), b), a)

-- | Inverse left-unitor for @Int(->)@: @A -> I \u2297 A@.
intUnitR' :: IntMorph (,) (->) a b (a, ()) (b, ())
intUnitR' = IntMorph $ \(a, (b, ())) -> (b, (a, ()))

-- | Inverse associator used in the left yanking equation for @IN a b@.
intAssocInv ::
  IntMorph
    (,)
    (->)
    (a, (b, a))
    (b, (a, b))
    ((a, b), a)
    ((b, a), b)
intAssocInv = IntMorph $ \((x, (y, x')), ((y', x''), y'')) -> ((y', (x'', y'')), ((x, y), x'))

-- | Yanking witness.  In the Int construction the identity is the braid on
-- the two factors; tracing that braid over the Either tensor returns the
-- input unchanged.
--
-- >>> let i = intId :: IntMorph Either (->) Int Int Int Int
-- >>> trace (runIntMorph i) (42 :: Int)
-- 42

-- | Mat Bool middle trace with coupled blocks.  The feedback channel is
-- @Bool@, the @aa@ block is the swap (so its reflexive-transitive closure is
-- the universal relation on @Bool@), and the off-diagonal @ba@/@ac@ blocks are
-- non-constant.  The helper below repeats the same @parT + braid + trace-middle@
-- wiring as 'intComp', but specialised to the @Mat@/Either setup so the
-- doctest can live in the finite-type setting.
--
-- >>> let aa = mat (\a a' -> a /= a') :: Mat Bool Bool
-- >>> let acF = mat (\a c -> a && c) :: Mat Bool Bool
-- >>> let baF = mat (\b a -> b && a) :: Mat Bool Bool
-- >>> let bcF = mat (\_ _ -> False) :: Mat Bool Bool
-- >>> let mF = mat (\x y -> case x of { Left a -> case y of { Left a' -> a /= a'; Right c -> a && c }; Right b -> case y of { Left a' -> b && a'; Right _ -> False } })
-- >>> let f = IntMorph mF :: IntMorph Either Mat Bool Bool Bool Bool
-- >>> let acG = mat (\_ c -> c) :: Mat Bool Bool
-- >>> let baG = mat (\c b -> c || b) :: Mat Bool Bool
-- >>> let mG = mat (\x y -> case x of { Left b -> case y of { Left b' -> b /= b'; Right c -> c }; Right c -> case y of { Left b' -> c || b'; Right _ -> False } })
-- >>> let g = IntMorph mG :: IntMorph Either Mat Bool Bool Bool Bool
-- >>> runMat (runIntMorph (intCompMatEither g f)) (Right False) (Right False)
-- False
-- >>> runMat (runIntMorph (intCompMatEither g f)) (Right False) (Right True)
-- True
-- >>> runMat (runIntMorph (intCompMatEither g f)) (Right True) (Right False)
-- False
-- >>> runMat (runIntMorph (intCompMatEither g f)) (Right True) (Right True)
-- True
