{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

-- | Hyperfunctions: the final encoding of traced monoidal categories.
--
-- A @Hyper@ is completely determined by its dual. To get a @b@ you must
-- provide a continuation that can itself produce an @a@.
--
-- The underlying construction is parameterised by a base category @arr@;
-- @Hyper@ itself is the function-category specialisation:
--
-- @
-- type Hyper = HyperF (->)
-- @
--
-- The two named targets are:
--
-- * @Hyper@ — arrows run in 'Data.Functor.Identity.Identity' and knots tie
--   by Haskell laziness.
-- * @'HyperF' ('Control.Arrow.Kleisli' m)@ — arrows run in @m@ and knots tie
--   with 'mfix'.
--
-- @HyperF@ lives in the same module so the function API is literally a
-- specialisation of the generic one.
--
-- === doctests
--
-- >>> import Circuit.Hyper
-- >>> import Circuit.Channel (trace)
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Data.Functor.Identity (Identity (..))
--
-- >>> let body = liftH (Kleisli (\(xs, ()) -> Identity (0 : xs, take 3 xs)) :: Kleisli Identity ([Int], ()) ([Int], [Int]))
-- >>> runIdentity (observeH (trace body) ())
-- [0,0,0]
module Circuit.Hyper
  ( -- * Parameterised hyperfunctions
    HyperF (..),
    Hyper,
    pattern Hyper,

    -- * Base-category structure
    HyperBase (..),

    -- * Generic constructors and eliminators
    liftH,
    observeH,
    baseH,
    pushH,
    runHyperH,

    -- * Function-category hyperfunctions
    lift,
    observe,
    base,
    push,
    runHyper,

    -- * Either-loop state machine
    encodeEither,
    runEither,

    -- * Kleisli aliases
    liftArr,
    observeArr,
    baseArr,
    pushArr,
    runHyperArr,
  )
where

import Circuit.Category (Category (..), ObDict (..), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Control.Arrow (Kleisli (..))
import Control.Monad.Fix (MonadFix, mfix)
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.Profunctor
import Prelude hiding (id, (.))

-- $setup
-- >> import Prelude hiding (id, (.))
-- >> import Data.Profunctor
-- >> let h = lift (+1) :: Hyper Int Int
-- >> let f1 = (*2) :: Int -> Int
-- >> let g1 = (+10) :: Int -> Int
-- >> let f2 = (+3) :: Int -> Int
-- >> let g2 = (*100) :: Int -> Int

-- | A hyperfunction from @a@ to @b@ over the base category @arr@.
--
-- To produce a @b@ in @arr@ you must supply a continuation that can
-- produce an @a@.
newtype HyperF arr a b = HyperF
  { -- | Feed a continuation into the hyperfunction.
    invoke :: arr (HyperF arr b a) b
  }

-- | The function-category hyperfunction.
type Hyper = HyperF (->)

-- | Bidirectional pattern for the function-category hyperfunction.
pattern Hyper :: (HyperF (->) b a -> b) -> Hyper a b
pattern Hyper f = HyperF f

{-# COMPLETE Hyper :: Hyper #-}

-- ---------------------------------------------------------------------------
-- Base-category structure
-- ---------------------------------------------------------------------------

-- | Enough structure on a base category @arr@ to give 'HyperF arr' a
-- traced monoidal category structure.
--
-- * 'Run' is the underlying functor in which arrows are evaluated.
-- * 'runArr' / 'mkArr' witness that @arr@ is concretely represented by
--   functions into 'Run'.
-- * 'fixRun' ties the recursive knot used by the trace.
class (Category arr, Monad (Run arr)) => HyperBase arr where
  -- | Underlying effect functor for evaluating arrows.
  type Run arr :: Type -> Type

  -- | Evaluate an arrow at a value.
  runArr :: arr a b -> a -> Run arr b

  -- | Build an arrow from a function into 'Run'.
  mkArr :: (a -> Run arr b) -> arr a b

  -- | Fixed-point operator for 'Run'.
  fixRun :: (a -> Run arr a) -> Run arr a

-- | Function category: arrows run in the identity monad and knots tie
-- by Haskell laziness.
instance HyperBase (->) where
  type Run (->) = Identity
  runArr f a = Identity (f a)
  mkArr f = runIdentity . f
  fixRun f = let x = f (runIdentity x) in x

-- | Kleisli arrows: arrows run in the monad and knots tie with 'mfix'.
instance (MonadFix m) => HyperBase (Kleisli m) where
  type Run (Kleisli m) = m
  runArr = runKleisli
  mkArr = Kleisli
  fixRun = mfix

-- ---------------------------------------------------------------------------
-- Generic constructors and eliminators
-- ---------------------------------------------------------------------------

-- | Push a base morphism onto a hyperfunction.
pushH ::
  (HyperBase arr) =>
  arr a b ->
  HyperF arr a b ->
  HyperF arr a b
pushH f h = HyperF $ mkArr $ \k -> do
  a_val <- runArr (invoke k) h
  runArr f a_val

-- | Embed a base morphism into a hyperfunction.
--
-- This is the coinductive character of the construction: the morphism is
-- pushed onto every future continuation.
liftH :: (HyperBase arr) => arr a b -> HyperF arr a b
liftH f = pushH f (liftH f)

-- | A constant hyperfunction.
baseH :: (HyperBase arr) => b -> HyperF arr a b
baseH b = HyperF $ mkArr $ \_ -> pure b

-- | Extract the underlying arrow as a function into 'Run'.
observeH :: (HyperBase arr) => HyperF arr a b -> a -> Run arr b
observeH h a = runArr (invoke h) (baseH a)

-- | Close the self-referential loop.
runHyperH ::
  forall arr a.
  (HyperBase arr) =>
  HyperF arr a a ->
  Run arr a
runHyperH h = fixRun @arr $ \a -> runArr (invoke h) (baseH a)

-- ---------------------------------------------------------------------------
-- Generic instances
-- ---------------------------------------------------------------------------

instance (HyperBase arr) => Category (HyperF arr) where
  type Ob (HyperF arr) a = Ob arr a
  id = liftH id
  f . g = HyperF $ mkArr $ \k -> runArr (invoke f) (g . k)

instance (HyperBase arr, Channel (,) arr) => Channel (,) (HyperF arr) where
  assoc = liftH assoc
  assoc' = liftH assoc'
  slide = liftH slide
  withTensorOb ::
    forall a b r.
    ObDict (HyperF arr) a ->
    ObDict (HyperF arr) b ->
    ((Ob (HyperF arr) (a, b)) => r) ->
    r
  withTensorOb ObDict ObDict =
    withTensorOb @(,) @arr @a @b @r
      (ObDict :: ObDict arr a)
      (ObDict :: ObDict arr b)

instance (HyperBase arr, Strength (,) arr) => Strength (,) (HyperF arr) where
  strength h = liftH $ mkArr $ \(a, b) -> (a,) <$> observeH h b
  withStrengthOb ::
    forall a b c r.
    ObDict (HyperF arr) a ->
    ObDict (HyperF arr) b ->
    ObDict (HyperF arr) c ->
    ((Ob (HyperF arr) (a, b), Ob (HyperF arr) (a, c)) => r) ->
    r
  withStrengthOb ObDict ObDict ObDict =
    withStrengthOb @(,) @arr @a @b @c @r
      (ObDict :: ObDict arr a)
      (ObDict :: ObDict arr b)
      (ObDict :: ObDict arr c)

instance
  ( HyperBase arr,
    Strength (,) arr
  ) =>
  Traced (,) (HyperF arr)
  where
  trace = traceHyper
    where
      traceHyper ::
        forall a b c.
        HyperF arr (a, b) (a, c) ->
        HyperF arr b c
      traceHyper body =
        HyperF $
          mkArr $ \k ->
            snd
              <$> fixRun @arr
                ( \pair -> do
                    let cont =
                          HyperF $
                            mkArr $ \_ -> do
                              a_val <- observeH k (snd pair)
                              pure (fst pair, a_val)
                    runArr (invoke body) cont
                )

-- ---------------------------------------------------------------------------
-- Function-category hyperfunctions
-- ---------------------------------------------------------------------------

-- | Embed a plain function into a hyperfunction.
--
-- .> observe (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift = liftH

-- | Extract a plain function from a hyperfunction.
--
-- .> observe (lift reverse) "hello"
-- "olleh"
observe :: Hyper a b -> (a -> b)
observe h = runIdentity . observeH h

-- | Ignores the input and returns a constant value.
--
-- .> observe (base 42) undefined
-- 42
base :: a -> Hyper b a
base = baseH

-- | Push a plain function onto a hyperfunction.
--
-- .> observe (push (+1) (lift (*2))) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push = pushH

-- | Close the self-referential loop.
--
-- .> runHyper (Hyper $ \_ -> 42 :: Int)
-- 42
--
-- .> runHyper (Hyper $ \h -> invoke h (Hyper $ \_ -> 0) + 1) :: Int
-- 1
runHyper :: Hyper a a -> a
runHyper = runIdentity . runHyperH

-- | Encode an Either-loop as a self-referential 'Hyper'.
--
-- Whereas 'encode' handles the @(,)@ tensor using 'Hyper''s own 'Traced'
-- instance, this preserves the Either-loop state in the function domain.
-- @Left a@ feeds back; @Right c@ terminates with output.
--
-- .> :{
-- let step = \case
--       Right n | n < 3 -> Left (n + 1)
--       Right n         -> Right n
--       Left n  | n < 3 -> Left (n + 1)
--       Left n          -> Right n
-- :}
--
-- .> runEither step (0 :: Int)
-- 3
encodeEither ::
  (Either a b -> Either a c) ->
  Hyper (Either a b -> c) (Either a b -> c)
encodeEither f = h
  where
    h =
      Hyper
        ( \k s ->
            case f s of
              Right c -> c
              Left a -> invoke k h (Left a)
        )

-- | Run an 'encodeEither'-encoded circuit from initial input @b@.
--
-- 'encodeEither' embeds the Either state machine into 'Hyper', 'runHyper'
-- ties the self-referential knot, and @Right b@ injects the initial state.
--
-- .> :{
-- let step = \case
--       Right n | n < 3 -> Left (n + 1)
--       Right n         -> Right n
--       Left n  | n < 3 -> Left (n + 1)
--       Left n          -> Right n
-- :}
--
-- .> runEither step (0 :: Int)
-- 3
runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = runHyper (encodeEither f) (Right b)

-- * Instances

-- | 'Traced' instance for @Hyper@ with the @(,)@ tensor.
--
-- Routes the self-reference through explicit @Hyper@ values:
--
--   1. @invoke body cont@ calls the body, which will eventually ask @cont@
--      for an @(a, b)@ — the feedback pair.
--   2. @cont@ captures @a@ from @body@'s output (@fst pair@) and feeds it
--      back as the first component of its return. This is the knot: @a@
--      cycles through @body -> pair -> cont -> body@.
--   3. @invoke k (Hyper (const (snd pair)))@ converts the output @c@ to a
--      @b@ for @cont@'s return type — purely type plumbing.
--
-- .> let body = lift (\(xs, ()) -> (0:xs, take 3 xs))
-- .> observe (trace body) ()
-- [0,0,0]

-- | 'Profunctor' instance for @Hyper@.
--
-- 'dimap' routes both input and output through the continuation
-- structure.
--
-- Profunctor identity: dimap id id = id
--
-- .> observe (dimap id id h) 5
-- 6
--
-- Profunctor composition: dimap f g . dimap f' g' = dimap (f' . f) (g . g')
--
-- .> observe (dimap f1 g1 (dimap f2 g2 h)) 5
-- 1410
-- .> observe (dimap (f2 . f1) (g1 . g2) h) 5
-- 1410
--
-- lmap f = dimap f id
--
-- .> observe (lmap ((*2) :: Int -> Int) h) 5
-- 11
-- .> observe (dimap ((*2) :: Int -> Int) id h) 5
-- 11
--
-- rmap g = dimap id g
--
-- .> observe (rmap ((*2) :: Int -> Int) h) 5
-- 12
-- .> observe (dimap id ((*2) :: Int -> Int) h) 5
-- 12
instance Profunctor Hyper where
  dimap f g h = Hyper $ g . invoke h . dimap g f
  lmap f h = Hyper $ invoke h . rmap f
  rmap f h = Hyper $ f . invoke h . lmap f

instance Functor (Hyper a) where
  fmap = rmap

-- ---------------------------------------------------------------------------
-- Kleisli aliases
-- ---------------------------------------------------------------------------

-- | Alias for 'pushH' on @Kleisli m@.
pushArr ::
  (MonadFix m) =>
  Kleisli m a b ->
  HyperF (Kleisli m) a b ->
  HyperF (Kleisli m) a b
pushArr = pushH

-- | Alias for 'liftH' on @Kleisli m@.
liftArr :: (MonadFix m) => Kleisli m a b -> HyperF (Kleisli m) a b
liftArr = liftH

-- | Alias for 'baseH' on @Kleisli m@.
baseArr :: (MonadFix m) => b -> HyperF (Kleisli m) a b
baseArr = baseH

-- | Alias for 'observeH' on @Kleisli m@.
observeArr ::
  (MonadFix m) =>
  HyperF (Kleisli m) a b ->
  a ->
  m b
observeArr = observeH

-- | Alias for 'runHyperH' on @Kleisli m@.
runHyperArr ::
  (MonadFix m) =>
  HyperF (Kleisli m) a a ->
  m a
runHyperArr = runHyperH
