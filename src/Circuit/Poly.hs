{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Sketch: the category Poly.
--
-- Polynomial objects are syntactic expressions, promoted to a kind:
--
--     p, q ::= Y              the identity polynomial
--           |  Const A        a constant set
--           |  Exp A          y^A
--           |  Sum p q        coproduct
--           |  Prod p q       cartesian product
--
-- The kind @Poly@ is promoted, so polynomial expressions live at the type
-- level.  'Eval' is a GADT that witnesses the value shape of @p(x)@.  We use
-- a GADT rather than a type family because 'Eval' is not injective in @x@;
-- the GADT lets GHC keep track of the evaluation variable without ambiguity.
--
-- Morphisms are natural transformations between the induced polynomial
-- functors, equivalently bundle maps (positions forward, directions
-- backward).
module Circuit.Poly
  ( -- * Polynomial expressions
    Poly (..),
    Eval (..),

    -- * Morphisms
    Morphism (..),
    runMorphism,

    -- * Dynamical systems
    System,
    step,
  )
where

import Control.Category
import Data.Bifunctor
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- | Syntactic polynomial objects, promoted to a kind.
data Poly = Y
  | Const Type
  | Exp Type
  | Sum Poly Poly
  | Prod Poly Poly

-- | Values of a polynomial functor @p@ evaluated at @x@.
--
-- The constructors mirror the polynomial grammar.  'EP' and 'ES' wrap the
-- standard product and coproduct of Haskell ('(,)' and 'Either'); they are
-- not reimplemented, only tagged so that the polynomial shape remains
-- inspectable.
data Eval (p :: Poly) (x :: Type) where
  EY :: x -> Eval 'Y x
  EK :: c -> Eval ('Const c) x
  EE :: (a -> x) -> Eval ('Exp a) x
  ES :: Either (Eval p x) (Eval q x) -> Eval ('Sum p q) x
  EP :: (Eval p x, Eval q x) -> Eval ('Prod p q) x

instance Functor (Eval p) where
  fmap f = \case
    EY x -> EY (f x)
    EK c -> EK c
    EE g -> EE (f . g)
    ES e -> ES (bimap (fmap f) (fmap f) e)
    EP (a, b) -> EP (fmap f a, fmap f b)

-- | A morphism @p -> q@ in Poly, encoded as a natural transformation
-- between the evaluated functors.
--
-- By the Yoneda / sigma universal property, this is equivalent to a
-- bundle map: a function on positions together with a contravariant
-- family of functions on directions.
data Morphism (p :: Poly) (q :: Poly) where
  -- | Identity morphism.
  Id :: Morphism p p
  -- | Covariant embedding of a plain function into constants.
  ConstMap :: (a -> b) -> Morphism ('Const a) ('Const b)
  -- | Contravariant embedding of a plain function into exponentials.
  ExpMap :: (a -> b) -> Morphism ('Exp b) ('Exp a)
  -- | Sequential composition.
  Compose :: Morphism q r -> Morphism p q -> Morphism p r
  -- | Parallel composition (cartesian product of morphisms).
  Par :: Morphism p p' -> Morphism q q' -> Morphism ('Prod p q) ('Prod p' q')
  -- | Coproduct injections.
  Inl :: Morphism p ('Sum p q)
  Inr :: Morphism q ('Sum p q)
  -- | Coproduct case analysis.
  Case :: Morphism p r -> Morphism q r -> Morphism ('Sum p q) r
  -- | Product projections.
  Fst :: Morphism ('Prod p q) p
  Snd :: Morphism ('Prod p q) q
  -- | Product pairing.
  Pair :: Morphism r p -> Morphism r q -> Morphism r ('Prod p q)

instance Category Morphism where
  id = Id
  (.) = Compose

-- | Interpret a 'Morphism' as a natural transformation.
runMorphism :: Morphism p q -> (forall x. Eval p x -> Eval q x)
runMorphism = \case
  Id -> id
  ConstMap f -> \(EK a) -> EK (f a)
  ExpMap f -> \(EE g) -> EE (g . f)
  Compose g f -> runMorphism g . runMorphism f
  Par f g -> \(EP (a, b)) -> EP (runMorphism f a, runMorphism g b)
  Inl -> ES . Left
  Inr -> ES . Right
  Case f g -> \case
    ES (Left a) -> runMorphism f a
    ES (Right b) -> runMorphism g b
  Fst -> \(EP (a, _)) -> a
  Snd -> \(EP (_, b)) -> b
  Pair f g -> \r -> EP (runMorphism f r, runMorphism g r)

-- | A dynamical system with interface @p@ and state type @s@.
--
-- For the polynomial @Prod (Const o) (Exp i)@ this is the usual Moore
-- machine: expose an output @o@ and accept an input @i@ to determine the
-- next state.
type System s (p :: Poly) = s -> Eval p s

-- | Run one step: observe the current @p@-output from state @s@.
step :: System s p -> s -> Eval p s
step = id
