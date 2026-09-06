{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The generic substrate for modular circuit syntax, plus the free-layer
-- / free-forgetful adjunction tower.
--
-- This module holds the à-la-carte machinery: signatures, the free
-- construction over a signature, algebras, and the universal folds. Each
-- concrete language layer ('Circuit.Trace.Trace', 'Circuit.Net.SMC',
-- 'Circuit.Net.Net', ...) is obtained by choosing a signature sum and adding
-- smart constructors and structural instances on top of this substrate.
--
-- The design is a profunctor-shaped variation of the classic "datatypes à la
-- carte":
--
-- * A 'Sig' is a signature functor indexed by a base arrow @arr@ and a
--   recursive arrow @rec@.
-- * @'Syntax' sig arr@ is the free construction over @sig@ with generators
--   drawn from @arr@.
-- * An 'Algebra' interprets the operations of a signature into a target arrow.
-- * 'evalInto' is the universal fold out of the free construction; 'eval' is
--   the same fold back into the base arrow.
--
-- The second half of the module is the layer tower. 'Layer' generalises the
-- free construction from signature sums to any arrow transformer @f@, with
-- 'unit' / 'run' / 'bind' as the generic include / same-category / target
-- fold vocabulary, and 'Free' (the free category) as the prime example.
-- Concrete layers:
--
-- * @run@ Free — free category
-- * @run@ SMC — free symmetric monoidal category (in "Circuit.Net")
-- * @run@ Trace — free traced monoidal category (in "Circuit.Trace")
-- * @run@ Net — free symmetric monoidal category with bimonoid (in "Circuit.Net")
--
-- 'Law' says what the /target/ category must satisfy to receive a 'bind'
-- fold; 'Run' says what the /base/ category must satisfy for a same-category
-- 'run'; and 'Bind' captures any extra source constraints needed when the
-- free syntax has structural rows. The hom-set isomorphism is stated once,
-- generically:
--
-- @
--   bind h . unit = h              (β)
--   bind unit      = id            (η)
--   run            = bind id       (coherence, where both sides are defined)
-- @
--
-- Composition of layers is just nesting — no new operator, no bespoke
-- coherence lemmas.
module Circuit.Syntax
  ( -- * Signatures
    Sig,
    (:+:) (..),

    -- * Syntax and algebra
    Syntax (..),
    Algebra (..),
    eval,
    evalInto,

    -- * Sequential composition
    SigCompose (..),

    -- * Free-layer / free-forgetful adjunction tower
    Cat2,
    (:~>),
    Layer (..),

    -- * Free category (Layer example)
    Free (..),
  )
where

import Circuit.Category (Category (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Kind (Constraint, Type)
import Prelude hiding (id, (.))

-- Signature functors

-- | A signature describes a set of constructors for a profunctor.
--
-- * @arr@ — the base arrow (used for constructor constraints)
-- * @rec@ — the recursive arrow type being defined
-- * @a@, @b@ — input and output objects
type Sig = (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type

-- | Coproduct of signatures.
data (sig1 :+: sig2) arr rec a b where
  L :: sig1 arr rec a b -> (sig1 :+: sig2) arr rec a b
  R :: sig2 arr rec a b -> (sig1 :+: sig2) arr rec a b

infixr 6 :+:

-- Free construction over a signature

-- | The free construction over a signature.
data Syntax (sig :: Sig) (arr :: Type -> Type -> Type) a b where
  Lift :: arr a b -> Syntax sig arr a b
  Oper :: sig arr (Syntax sig arr) a b -> Syntax sig arr a b

-- | Algebra for a signature. Interprets operations of a signature over
-- source arrow @arr@ into a target arrow @arr'@.
--
-- * @emb@ maps base arrows of the source into the target.
-- * @rec@ maps recursive sub-terms into the target.
class Algebra (sig :: Sig) (arr :: Type -> Type -> Type) (arr' :: Type -> Type -> Type) where
  type Ctx sig arr arr' :: Constraint
  type Ctx sig arr arr' = ()
  alg ::
    (Ctx sig arr arr') =>
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    sig arr rec a b ->
    arr' a b

-- | Coproduct algebra dispatches to the appropriate component.
instance (Algebra sig1 arr arr', Algebra sig2 arr arr') => Algebra (sig1 :+: sig2) arr arr' where
  type Ctx (sig1 :+: sig2) arr arr' = (Ctx sig1 arr arr', Ctx sig2 arr arr')
  alg emb rec (L op) = alg emb rec op
  alg emb rec (R op) = alg emb rec op

-- | Fold a free construction into a target arrow using its algebra.
--
-- The embedding @emb@ maps base arrows of the source into the target.
-- For folding to the same arrow, use 'eval'.
evalInto ::
  (Category arr', Algebra sig arr arr', Ctx sig arr arr') =>
  (forall x y. arr x y -> arr' x y) ->
  Syntax sig arr a b ->
  arr' a b
evalInto emb (Lift f) = emb f
evalInto emb (Oper op) = alg emb (evalInto emb) op

-- | Fold a free construction into its own base arrow.
eval ::
  (Category arr, Algebra sig arr arr, Ctx sig arr arr) =>
  Syntax sig arr a b ->
  arr a b
eval = evalInto id

-- Sequential composition

-- | Sequential composition.
data SigCompose arr rec a b where
  SigCompose :: rec b c -> rec a b -> SigCompose arr rec a c

instance Algebra SigCompose arr arr' where
  type Ctx SigCompose arr arr' = Category arr'
  alg ::
    forall (rec :: Type -> Type -> Type) (a :: Type) (c :: Type).
    (Ctx SigCompose arr arr') =>
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigCompose arr rec a c ->
    arr' a c
  alg _ rec (SigCompose @_ @_ @_ @_ @_ g f) = rec g . rec f

-- Common syntax combinations

-- | Free category.
type AlgCat arr = Syntax SigCompose arr

-- Instances for the free category

instance (Category arr) => Category (AlgCat arr) where
  id = Lift id
  f . g = Oper (SigCompose f g)

instance (Category arr, Assoc t arr) => Assoc t (AlgCat arr) where
  assoc = Lift assoc
  assoc' = Lift assoc'

instance (Category arr, Slide t arr) => Slide t (AlgCat arr) where
  slide = Lift slide

instance (Category arr, Strength t arr) => Strength t (AlgCat arr) where
  strength f = Lift (strength (eval f))

instance (Category arr, Yank t arr) => Yank t (AlgCat arr) where
  yank body = Lift (yank (eval body))

-- * Free-layer / free-forgetful adjunction tower

-- | The kind of Haskell categories: type-to-type hom-sets.
type Cat2 = Type -> Type -> Type

-- | An arrow-to-arrow mapping (a natural transformation between
-- profunctors).
type arr :~> arr' = forall x y. arr x y -> arr' x y

-- | A free construction over a base arrow.
--
-- * 'unit' includes the generators.
-- * 'run' folds the free syntax back into the same base category.
-- * 'bind' folds the free syntax into any 'Law'-abiding target.
class Layer (f :: Cat2 -> Cat2) where
  -- | What the target category must satisfy to receive a 'bind' fold.
  -- 'run' only needs the base category's own structure.
  type Law f (arr' :: Cat2) :: Constraint

  -- | What the base category must satisfy to receive a 'run' fold back into
  -- itself.  Defaults to no extra constraints.
  type Run f (arr :: Cat2) :: Constraint

  type Run f arr = ()

  -- | Extra constraints the /source/ category must satisfy for a 'bind'
  -- fold.  Defaults to no extra constraints.
  type Bind f (arr :: Cat2) :: Constraint

  type Bind f arr = ()

  -- | Include a base arrow as a single generator.
  unit :: (Category arr) => arr :~> f arr

  -- | Fold the free syntax into the same base category.
  --
  -- Defaults to @'bind' 'id'@, so the single eliminator vocabulary is
  -- coherent wherever it type-checks. Instances may still override this
  -- with a direct implementation if the weaker constraints of 'Run' do
  -- not already imply 'Law' and 'Bind'.
  run ::
    (Run f arr, Law f arr, Bind f arr) =>
    f arr a b ->
    arr a b
  run = bind id

  -- | The universal fold out of the free construction into any
  -- 'Law'-abiding target category.
  bind ::
    (Law f arr', Bind f arr) =>
    (arr :~> arr') ->
    f arr a b ->
    arr' a b

-- * Free category

-- | The free category over a base arrow.
--
-- The two constructors are 'FreeLift', which embeds a base arrow, and
-- 'FreeCompose', which sequences two free morphisms.  The universal fold out
-- of 'Free' is 'run'.
--
-- >>> run (FreeLift (+1) :: Free (->) Int Int) 5
-- 6
-- >>> run (FreeCompose (FreeLift (+1)) (FreeLift (*2)) :: Free (->) Int Int) 5
-- 11
data Free arr a b where
  -- | Embed a base arrow.
  FreeLift :: arr a b -> Free arr a b
  -- | Sequential composition.
  FreeCompose :: Free arr b c -> Free arr a b -> Free arr a c

instance (Category arr) => Category (Free arr) where
  id = FreeLift id
  (.) = FreeCompose

-- | Layer instance for the free category.
--
-- Without object constraints, folding is just recursive application of
-- the target category's composition.
instance Layer Free where
  type Law Free arr' = Category arr'
  type Run Free arr = Category arr
  type Bind Free arr = ()
  unit = FreeLift
  bind :: forall arr' arr a b. (Law Free arr') => (arr :~> arr') -> Free arr a b -> arr' a b
  bind h (FreeLift f) = h f
  bind h (FreeCompose @_ @_ g f) = bind h g . bind h f

-- | Lift the 'Channel' structure through 'Free'.
instance (Assoc t arr) => Assoc t (Free arr) where
  assoc = FreeLift assoc
  assoc' = FreeLift assoc'

instance (Slide t arr) => Slide t (Free arr) where
  slide = FreeLift slide

-- | Lift the 'Channel' structure through 'Free'.
--
-- A morphism is run back to the base arrow before tensoring with the
-- feedback channel.
instance (Strength t arr) => Strength t (Free arr) where
  strength = FreeLift . strength . run

-- | Lift the 'Yank' class through 'Free'.
--
-- A loop body in @Free arr@ is run back to the base arrow before calling
-- the base 'yank'.
instance (Yank t arr) => Yank t (Free arr) where
  yank = FreeLift . yank . run
