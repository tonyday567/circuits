{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Circuit.Bimonoid
  ( Copy (..),
    Discard (..),
    Merge (..),
    Zero (..),
    CopyDiscard,
    MergeZero,
    Bimonoid,
    SigCopy (..),
    SigDiscard (..),
    SigCopyDiscard,
    SigPlus (..),
    SigZero (..),
    SigMergeZero,
    Affine,
    Relevant,
    Cartesian,
    CoAffine,
    CoRelevant,
    CopyT (..),
    DiscardT (..),
    MergeT (..),
    ZeroT (..),
    BimonoidT,
    Dagger (..),
    transpose,
  )
where

import Circuit.Category (Category (..))
import Circuit.Syntax (Algebra (..), (:+:) (..))
import Circuit.Tensor (Action (..), SemiTensor (..), Tensor, Unit, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

class Merge arr a where
  plus :: arr (a, a) a

class Zero arr a where
  zero :: arr () a

type MergeZero arr a = (Merge arr a, Zero arr a)

instance Merge (->) () where
  plus _ = ()
  {-# INLINE plus #-}

instance Zero (->) () where
  zero _ = ()
  {-# INLINE zero #-}

instance Merge (->) Int where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Int where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Integer where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Integer where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Double where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Double where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Float where
  plus = uncurry (+)
  {-# INLINE plus #-}

instance Zero (->) Float where
  zero _ = 0
  {-# INLINE zero #-}

instance Merge (->) Bool where
  plus = uncurry (||)
  {-# INLINE plus #-}

instance Zero (->) Bool where
  zero _ = False
  {-# INLINE zero #-}

instance (Merge (->) a, Merge (->) b) => Merge (->) (a, b) where
  plus ((a, b), (a', b')) = (plus (a, a'), plus (b, b'))
  {-# INLINE plus #-}

instance (Zero (->) a, Zero (->) b) => Zero (->) (a, b) where
  zero u = (zero u, zero u)
  {-# INLINE zero #-}

instance (Merge (->) a, Zero (->) a) => Merge (->) [a] where
  plus (xs, ys) = go xs ys
    where
      go [] [] = []
      go [] (y : ys') = plus (zero (), y) : go [] ys'
      go (x : xs') [] = plus (x, zero ()) : go xs' []
      go (x : xs') (y : ys') = plus (x, y) : go xs' ys'
  {-# INLINE plus #-}

instance Zero (->) [a] where
  zero _ = []
  {-# INLINE zero #-}

class Copy arr a where
  copy :: arr a (a, a)

class Discard arr a where
  discard :: arr a ()

type CopyDiscard arr a = (Copy arr a, Discard arr a)

type Bimonoid arr a = (Copy arr a, Discard arr a, Merge arr a, Zero arr a)

class (CopyT t arr a, DiscardT t arr a, MergeT t arr a, ZeroT t arr a) => BimonoidT t arr a

instance (CopyT t arr a, DiscardT t arr a, MergeT t arr a, ZeroT t arr a) => BimonoidT t arr a

class (Tensor t arr) => CopyT t arr a where
  copyT :: arr a (t a a)

class (Tensor t arr) => DiscardT t arr a where
  discardT :: arr a (Unit t)

class (Tensor t arr) => MergeT t arr a where
  plusT :: arr (t a a) a

class (Tensor t arr) => ZeroT t arr a where
  zeroT :: arr (Unit t) a

data Dagger arr a b = Dagger
  { front :: arr a b,
    back :: arr b a
  }

transpose :: Dagger arr a b -> Dagger arr b a
transpose (Dagger f g) = Dagger g f

instance (Category arr) => Category (Dagger arr) where
  id = Dagger id id
  {-# INLINE id #-}

  Dagger f g . Dagger f' g' = Dagger (f . f') (g' . g)
  {-# INLINE (.) #-}

instance (Strength t arr) => Strength t (Dagger arr) where
  strength (Dagger f g) = Dagger (strength f) (strength g)
  {-# INLINE strength #-}

instance (Yank t arr) => Yank t (Dagger arr) where
  yank (Dagger f g) = Dagger (yank f) (yank g)
  {-# INLINE yank #-}

instance (Copy arr a, Merge arr a) => Copy (Dagger arr) a where
  copy = Dagger copy plus
  {-# INLINE copy #-}

instance (Discard arr a, Zero arr a) => Discard (Dagger arr) a where
  discard = Dagger discard zero
  {-# INLINE discard #-}

instance (Merge arr a, Copy arr a) => Merge (Dagger arr) a where
  plus = Dagger plus copy
  {-# INLINE plus #-}

instance (Zero arr a, Discard arr a) => Zero (Dagger arr) a where
  zero = Dagger zero discard
  {-# INLINE zero #-}

instance {-# INCOHERENT #-} (CopyT t arr a, MergeT t arr a) => CopyT t (Dagger arr) a where
  copyT = Dagger (copyT @t) (plusT @t)
  {-# INLINE copyT #-}

instance {-# INCOHERENT #-} (DiscardT t arr a, ZeroT t arr a) => DiscardT t (Dagger arr) a where
  discardT = Dagger (discardT @t) (zeroT @t)
  {-# INLINE discardT #-}

instance {-# INCOHERENT #-} (MergeT t arr a, CopyT t arr a) => MergeT t (Dagger arr) a where
  plusT = Dagger (plusT @t) (copyT @t)
  {-# INLINE plusT #-}

instance {-# INCOHERENT #-} (ZeroT t arr a, DiscardT t arr a) => ZeroT t (Dagger arr) a where
  zeroT = Dagger (zeroT @t) (discardT @t)
  {-# INLINE zeroT #-}

instance (Unital t arr) => Unital t (Dagger arr) where
  unitl = Dagger unitl unitl'
  {-# INLINE unitl #-}
  unitl' = Dagger unitl' unitl
  {-# INLINE unitl' #-}
  unitr = Dagger unitr unitr'
  {-# INLINE unitr #-}
  unitr' = Dagger unitr' unitr
  {-# INLINE unitr' #-}

instance (SemiTensor t arr) => SemiTensor t (Dagger arr) where
  tensor (Dagger f g) (Dagger f' g') = Dagger (tensor f f') (tensor g g')
  {-# INLINE tensor #-}

instance (Tensor t arr) => Tensor t (Dagger arr)

instance (Action t arr) => Action t (Dagger arr) where
  braid = Dagger braid braid
  {-# INLINE braid #-}

instance (Assoc t arr) => Assoc t (Dagger arr) where
  assoc = Dagger assoc assoc'
  assoc' = Dagger assoc' assoc

instance (Slide t arr) => Slide t (Dagger arr) where
  slide = Dagger slide slide

type Affine arr a = Discard arr a

type Relevant arr a = Copy arr a

type Cartesian arr a = (Copy arr a, Discard arr a)

type CoAffine arr a = Zero arr a

type CoRelevant arr a = Merge arr a

instance Copy (->) () where
  copy u = (u, u)
  {-# INLINE copy #-}

instance Discard (->) () where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Int where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Int where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Integer where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Integer where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Double where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Double where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Float where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Float where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) Bool where
  copy a = (a, a)
  {-# INLINE copy #-}

instance Discard (->) Bool where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) (a, b) where
  copy ab = (ab, ab)
  {-# INLINE copy #-}

instance Discard (->) (a, b) where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) [a] where
  copy as = (as, as)
  {-# INLINE copy #-}

instance Discard (->) [a] where
  discard _ = ()
  {-# INLINE discard #-}

instance Copy (->) (Maybe a) where
  copy m = (m, m)
  {-# INLINE copy #-}

instance Discard (->) (Maybe a) where
  discard _ = ()
  {-# INLINE discard #-}

data SigCopy (w :: Type -> Type -> Type) arr rec a b where
  SigCopy ::
    (CopyT w arr a) =>
    SigCopy w arr rec a (w a a)

instance Algebra (SigCopy w) arr arr' where
  type Ctx (SigCopy w) arr arr' = ()
  alg emb _ SigCopy = emb (copyT @w)

data SigDiscard (w :: Type -> Type -> Type) arr rec a b where
  SigDiscard ::
    (DiscardT w arr a) =>
    SigDiscard w arr rec a (Unit w)

instance Algebra (SigDiscard w) arr arr' where
  type Ctx (SigDiscard w) arr arr' = ()
  alg emb _ SigDiscard = emb (discardT @w)

type SigCopyDiscard w = SigCopy w :+: SigDiscard w

data SigPlus (w :: Type -> Type -> Type) arr rec a b where
  SigPlus ::
    (MergeT w arr a) =>
    SigPlus w arr rec (w a a) a

instance Algebra (SigPlus w) arr arr' where
  type Ctx (SigPlus w) arr arr' = ()
  alg emb _ SigPlus = emb (plusT @w)

data SigZero (w :: Type -> Type -> Type) arr rec a b where
  SigZero ::
    (ZeroT w arr a) =>
    SigZero w arr rec (Unit w) a

instance Algebra (SigZero w) arr arr' where
  type Ctx (SigZero w) arr arr' = ()
  alg emb _ SigZero = emb (zeroT @w)

type SigMergeZero w = SigPlus w :+: SigZero w

instance {-# OVERLAPPABLE #-} (Copy arr a, Tensor (,) arr) => CopyT (,) arr a where
  copyT = copy
  {-# INLINE copyT #-}

instance {-# OVERLAPPABLE #-} (Discard arr a, Tensor (,) arr) => DiscardT (,) arr a where
  discardT = discard
  {-# INLINE discardT #-}

instance {-# OVERLAPPABLE #-} (Merge arr a, Tensor (,) arr) => MergeT (,) arr a where
  plusT = plus
  {-# INLINE plusT #-}

instance MergeT Either (->) a where
  plusT = either id id
  {-# INLINE plusT #-}

instance {-# OVERLAPPABLE #-} (Zero arr a, Tensor (,) arr) => ZeroT (,) arr a where
  zeroT = zero
  {-# INLINE zeroT #-}
