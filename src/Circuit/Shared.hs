{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Circuit.Shared
  ( Pick (..),
    Schedule (..),
    Shared (..),
    transcriptSharedBy,
    Stamped (..),
    SigShared (..),
    AlgShared,
  )
where

import Circuit.Category (K (..))
import Circuit.Syntax
  ( Algebra (..),
    SigCompose,
    Syntax,
    (:+:),
  )
import Circuit.Tensor (Bias (..), Tensor)
import Circuit.Trace (SigYank)
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.These (These (..))
import Prelude hiding (id, (.))

data Pick = PickL | PickR | Both Bias
  deriving (Eq, Show)

newtype Schedule s = Schedule
  { chooseS :: s -> (s, Pick)
  }

class (Tensor t arr) => Shared t arr where
  sharedBy ::
    Schedule s ->
    arr (t s a) (t s b) ->
    arr (t s c) (t s d) ->
    arr (t s (t a c)) (t s (These b d))

instance Shared (,) (->) where
  sharedBy sched f g (s, (a, c)) =
    let (s', pick) = chooseS sched s
     in case pick of
          PickL ->
            let (s'', b) = f (s', a)
             in (s'', This b)
          PickR ->
            let (s'', d) = g (s', c)
             in (s'', That d)
          Both LeftFirst ->
            let (s'', b) = f (s', a)
                (s''', d) = g (s'', c)
             in (s''', These b d)
          Both RightFirst ->
            let (s'', d) = g (s', c)
                (s''', b) = f (s'', a)
             in (s''', These b d)
  {-# INLINE sharedBy #-}

instance (Monad m) => Shared (,) (K m) where
  sharedBy sched (K f) (K g) =
    K $ \(s, (a, c)) -> do
      let (s', pick) = chooseS sched s
      case pick of
        PickL -> do
          (s'', b) <- f (s', a)
          pure (s'', This b)
        PickR -> do
          (s'', d) <- g (s', c)
          pure (s'', That d)
        Both LeftFirst -> do
          (s'', b) <- f (s', a)
          (s''', d) <- g (s'', c)
          pure (s''', These b d)
        Both RightFirst -> do
          (s'', d) <- g (s', c)
          (s''', b) <- f (s'', a)
          pure (s''', These b d)
  {-# INLINE sharedBy #-}

data Stamped r a = Stamped
  { stamp :: r,
    stamped :: a
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Bifunctor Stamped where
  bimap f g (Stamped r a) = Stamped (f r) (g a)

transcriptSharedBy ::
  Schedule s ->
  ((s, a) -> (s, b)) ->
  ((s, c) -> (s, d)) ->
  s ->
  [(a, c)] ->
  [Stamped Pick (These b d)]
transcriptSharedBy sched f g s0 = go s0
  where
    go _ [] = []
    go s (x : xs) =
      let pick = snd (chooseS sched s)
          (s', out) = sharedBy sched f g (s, x)
       in Stamped pick out : go s' xs

data SigShared (t :: Type -> Type -> Type) arr rec i o where
  SigShared ::
    Schedule s ->
    rec (t s a) (t s b) ->
    rec (t s c) (t s d) ->
    SigShared t arr rec (t s (t a c)) (t s (These b d))

instance (Shared t arr') => Algebra (SigShared t) arr arr' where
  type Ctx (SigShared t) arr arr' = Shared t arr'
  alg _ rec (SigShared sched f g) = sharedBy sched (rec f) (rec g)

type AlgShared t arr = Syntax (SigCompose :+: SigShared t :+: SigYank t) arr
