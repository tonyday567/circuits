{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

-- | Hyperfunctions: the final encoding of traced monoidal categories.
--
-- A @Hyper@ is completely determined by its dual. To get a @b@ you must
-- provide a continuation that can itself produce an @a@.
--
-- @Hyper@ is the function-category specialisation:
--
-- @
-- type Hyper = HyperA (->)
-- @
--
-- The two named targets are:
--
-- * @Hyper@ — arrows are plain functions and knots tie by Haskell laziness.
-- * @'HyperA' ('K' m)@ — arrows are Kleisli arrows and knots tie with 'mfix'.
--
-- They share the same newtype, but the constructors and eliminators are
-- specialised because the two bases have different notions of observation and
-- fixed point.
--
-- === doctests
--
-- >>> import Circuit.Hyper
-- >>> import Circuit.Traced (yank)
-- >>> import Circuit.Category (K (..))
-- >>> import Data.Functor.Identity (Identity (..))
--
-- >>> let body = liftK (K (\(xs, ()) -> Identity (0 : xs, take 3 xs)) :: K Identity ([Int], ()) ([Int], [Int]))
-- >>> runIdentity (observeK (yank body) ())
-- [0,0,0]
module Circuit.Hyper
  ( -- * Parameterised hyperfunctions
    HyperA (..),
    Hyper,
    pattern Hyper,

    -- * Function-category hyperfunctions
    lift,
    observe,
    baseHyper,
    push,
    runHyper,

    -- * Kleisli hyperfunctions
    liftK,
    observeK,
    baseK,
    pushK,
    runHyperK,

    -- * Either-loop state machine
    encodeEither,
    runEither,

    -- * Bridges from initial syntax
    encode,
    encodeK,
  )
where

import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Circuit.Syntax (SigCompose (..), (:+:) (..))
import Circuit.Syntax qualified as Syn
import Circuit.Trace (SigYank (..), Trace)
import Control.Monad.Fix (MonadFix, mfix)
import Data.Functor.Identity (Identity (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Prelude
-- >>> import Circuit.Hyper (observe, lift, runHyper, Hyper (..))
-- >>> let h = lift (+1) :: Hyper Int Int

-- * Hyperfunctions

-- | A hyperfunction from @a@ to @b@ over the base category @arr@.
newtype HyperA arr a b = HyperA
  { -- | Feed a continuation into the hyperfunction.
    invoke :: arr (HyperA arr b a) b
  }

-- | The function-category hyperfunction.
type Hyper = HyperA (->)

-- | Bidirectional pattern for the function-category hyperfunction.
pattern Hyper :: (HyperA (->) b a -> b) -> Hyper a b
pattern Hyper f = HyperA f

{-# COMPLETE Hyper :: Hyper #-}

-- * Function-category hyperfunctions

-- | Embed a plain function into a hyperfunction.
--
-- >>> observe (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- | Extract a plain function from a hyperfunction.
--
-- >>> observe (lift reverse) "hello"
-- "olleh"
observe :: Hyper a b -> (a -> b)
observe h a = invoke h (baseHyper a)

-- | Ignores the input and returns a constant value.
--
-- >>> observe (baseHyper 42) undefined
-- 42
baseHyper :: a -> Hyper b a
baseHyper b = HyperA $ \_ -> b

-- | Push a plain function onto a hyperfunction.
--
-- >>> observe (push (+1) (lift (*2))) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = HyperA $ \k -> f (invoke k h)

-- | Close the self-referential loop.
--
-- >>> runHyper (Hyper $ \_ -> 42 :: Int)
-- 42
runHyper :: Hyper a a -> a
runHyper h = let a = invoke h (baseHyper a) in a

-- * Kleisli hyperfunctions

-- | Embed a Kleisli arrow into a hyperfunction.
liftK :: (Monad m) => K m a b -> HyperA (K m) a b
liftK f = pushK f (liftK f)

-- | Extract the underlying Kleisli arrow from a hyperfunction.
observeK :: (Monad m) => HyperA (K m) a b -> a -> m b
observeK h a = runK (invoke h) (baseK a)

-- | A constant Kleisli hyperfunction.
baseK :: (Monad m) => b -> HyperA (K m) a b
baseK b = HyperA $ K $ \_ -> pure b

-- | Push a Kleisli arrow onto a hyperfunction.
pushK :: (Monad m) => K m a b -> HyperA (K m) a b -> HyperA (K m) a b
pushK f h = HyperA $ K $ \k -> do
  a_val <- runK (invoke k) h
  runK f a_val

-- | Close the self-referential loop using 'mfix'.
runHyperK :: (MonadFix m) => HyperA (K m) a a -> m a
runHyperK h = mfix $ \a -> runK (invoke h) (baseK a)

-- * Function-category instances

instance Category Hyper where
  id = lift id
  f . g = HyperA $ \k -> invoke f (g . k)

instance Assoc (,) Hyper where
  assoc = lift assoc
  assoc' = lift assoc'

instance Slide (,) Hyper where
  slide = lift slide

instance Strength (,) Hyper where
  strength h = lift $ \(a, b) -> (a, observe h b)

instance Yank (,) Hyper where
  yank body = HyperA $ \k ->
    let pair = invoke body cont
        cont = HyperA $ \_ -> (fst pair, observe k (snd pair))
     in snd pair

-- * Kleisli instances

instance (Monad m) => Category (HyperA (K m)) where
  id = liftK id
  f . g = HyperA $ K $ \k -> runK (invoke f) (g . k)

instance (Monad m) => Assoc (,) (HyperA (K m)) where
  assoc = liftK assoc
  assoc' = liftK assoc'

instance (Monad m) => Slide (,) (HyperA (K m)) where
  slide = liftK slide

instance (Monad m) => Strength (,) (HyperA (K m)) where
  strength h = liftK $ K $ \(a, b) -> (a,) <$> observeK h b

instance (MonadFix m) => Yank (,) (HyperA (K m)) where
  yank body = HyperA $ K $ \k -> do
    pair <- mfix $ \pair -> do
      let cont =
            HyperA $ K $ \_ -> do
              b <- observeK k (snd pair)
              pure (fst pair, b)
      runK (invoke body) cont
    pure (snd pair)

-- * Either-loop state machine

-- | Encode an Either-loop as a self-referential 'Hyper'.
--
-- Whereas 'encode' handles the @(,)@ tensor using @Hyper@'s own 'Yank'
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
--       Left n  | n < 3 -> Left (n + 1)
--       Left n          -> Right n
-- :}
--
-- >>> runEither step (0 :: Int)
-- 3
runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = runHyper (encodeEither f) (Right b)

-- * Bridges from initial syntax

-- | Encode a function-category 'Trace' into a 'Hyper'.
--
-- This is the unique traced functor from the initial syntax ('Trace')
-- to the final object ('Hyper'), satisfying the commuting triangle
-- @'observe' . 'encode' = 'Circuit.Syntax.eval'@.
--
-- 'baseHyper' and 'baseK' constructors embed directly via 'lift'; 'Circuit.Trace.yank'
-- constructors become 'yank' over a hyperfunction.
--
-- >>> import qualified Circuit.Trace as Trace
-- >>> observe (encode (Trace.base (+1) :: Trace.Trace (,) (->) Int Int)) 5
-- 6
encode ::
  Trace (,) (->) a b ->
  Hyper a b
encode (Syn.Lift f) = lift f
encode (Syn.Op (L (SigCompose g f))) = encode g . encode f
encode (Syn.Op (R (YankBody body))) = yank (encode body)

-- | Encode a Kleisli 'Trace' into a @'HyperA' ('K' m)@.
encodeK ::
  (MonadFix m) =>
  Trace (,) (K m) a b ->
  HyperA (K m) a b
encodeK (Syn.Lift f) = liftK f
encodeK (Syn.Op (L (SigCompose g f))) = encodeK g . encodeK f
encodeK (Syn.Op (R (YankBody body))) = yank (encodeK body)
