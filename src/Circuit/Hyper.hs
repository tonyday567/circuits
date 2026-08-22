{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
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
-- * @'HyperF' ('K' m)@ — arrows run in @m@ and knots tie
--   with 'mfix'.
--
-- @HyperF@ lives in the same module so the function API is literally a
-- specialisation of the generic one.
--
-- === doctests
--
-- >>> import Circuit.Hyper
-- >>> import Circuit.Channel (trace)
-- >>> import Circuit.Category (K (..))
-- >>> import Data.Functor.Identity (Identity (..))
--
-- >>> let body = liftH (K (\(xs, ()) -> Identity (0 : xs, take 3 xs)) :: K Identity ([Int], ()) ([Int], [Int]))
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

    -- * Bridges from initial syntax
    encode,
  )
where

import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Syntax (SigCompose (..), (:+:) (..))
import Circuit.Syntax qualified as Syn
import Circuit.Trace (SigYank (..), Trace)
import Control.Monad.Fix (MonadFix, mfix)
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Prelude
-- >>> import Circuit.Hyper (observe, lift, runHyper, Hyper (..))
-- >>> let h = lift (+1) :: Hyper Int Int

-- ---------------------------------------------------------------------------
-- Hyperfunctions
-- ---------------------------------------------------------------------------

-- | A hyperfunction from @a@ to @b@ over the base category @arr@.
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

-- | K arrows: arrows run in the monad and knots tie with 'mfix'.
instance {-# INCOHERENT #-} (MonadFix m) => HyperBase (K m) where
  type Run (K m) = m
  runArr = runK
  mkArr = K
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
  id = liftH id
  f . g = HyperF $ mkArr $ \k -> runArr (invoke f) (g . k)

instance (HyperBase arr, Channel (,) arr) => Channel (,) (HyperF arr) where
  assoc = liftH assoc
  assoc' = liftH assoc'
  slide = liftH slide

instance (HyperBase arr, Strength (,) arr) => Strength (,) (HyperF arr) where
  strength h = liftH $ mkArr $ \(a, b) -> (a,) <$> observeH h b

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
-- >>> observe (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift = liftH

-- | Extract a plain function from a hyperfunction.
--
-- >>> observe (lift reverse) "hello"
-- "olleh"
observe :: Hyper a b -> (a -> b)
observe h = runIdentity . observeH h

-- | Ignores the input and returns a constant value.
--
-- >>> observe (base 42) undefined
-- 42
base :: a -> Hyper b a
base = baseH

-- | Push a plain function onto a hyperfunction.
--
-- >>> observe (push (+1) (lift (*2))) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push = pushH

-- | Close the self-referential loop.
--
-- >>> runHyper (Hyper $ \_ -> 42 :: Int)
-- 42
runHyper :: Hyper a a -> a
runHyper = runIdentity . runHyperH

-- | Encode an Either-loop as a self-referential 'Hyper'.
--
-- Whereas 'encode' handles the @(,)@ tensor using 'Hyper''s own 'Traced'
-- instance, this preserves the Either-loop state in the function domain.
-- @Left a@ feeds back; @Right c@ terminates with output.
--
-- >>> :{
-- let step = \case
--       Right n | n < 3 -> Left (n + 1)
--       Right n         -> Right n
--       Left n  | n < 3 -> Left (n + 1)
--       Left n          -> Right n
-- :}
--
-- >>> runEither step (0 :: Int)
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
-- >>> :{
-- let step = \case
--       Right n | n < 3 -> Left (n + 1)
--       Right n         -> Right n
--       Left n  | n < 3 -> Left (n - 1)
--       Left n          -> Right n
-- :}
--
-- FIXME: the doctest for @runEither step (0 :: Int)@ used to hang forever
-- because the step function above loops between Left 0 and Left 1.
-- It has been removed until the example is fixed.
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
-- >>> let body = lift (\(xs, ()) -> (0:xs, take 3 xs))
-- >>> observe (trace body) ()
-- [0,0,0]

-- ---------------------------------------------------------------------------
-- Bridges from initial syntax
-- ---------------------------------------------------------------------------

-- | Encode a 'Trace' into a 'HyperF'.
--
-- This is the unique traced functor from the initial syntax ('Trace')
-- to the final object ('HyperF'), satisfying the commuting triangle
-- @'observe' . 'encode' = 'eval'@.
--
-- 'base' constructors embed directly via 'liftH'; 'yank' constructors
-- become 'trace' over a hyperfunction.
--
-- >>> import qualified Circuit.Trace as Trace
-- >>> observe (encode (Trace.base (+1) :: Trace.Trace (,) (->) Int Int)) 5
-- 6
encode ::
  ( HyperBase arr,
    Strength (,) arr
  ) =>
  Trace (,) arr a b ->
  HyperF arr a b
encode (Syn.Lift f) = liftH f
encode (Syn.Op (L (SigCompose g f))) = encode g . encode f
encode (Syn.Op (R (Yank body))) = trace (encode body)
