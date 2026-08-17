{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Structural semantics for traced monoidal categories.
--
-- This module collects the structural superclass chain
-- @Channel → Strength → Traced@ and all base instances for the standard
-- base arrows @(->)@ and @Control.Arrow.Kleisli m@.  These classes
-- describe the monoidal structure, tensorial strength, and feedback-fixing
-- trace that underlie the syntax in "Circuit.Loop".
--
-- 'assoc' and 'assoc'' here reassociate /rightward/ and /leftward/
-- respectively. The monomorphic helpers in "Circuit.Tensor" have the same
-- names but the opposite directions. Also, 'slide' here is the slide
-- @t a (t b c) -> t b (t a c)@; the symmetric braiding @t a b -> t b a@
-- lives in Circuit.Tensor as swap. Where both structures exist,
-- @slide = assoc' .> par swap id .> assoc@.
--
-- Kind-polymorphic: @t@ and @arr@ share object kind (inferred via PolyKinds).
module Circuit.Channel
  ( Channel (..),
    Strength (..),
    strengthD,
    Traced (..),

    -- * Discrete discharge kit
    compD,
    assocD,
    assocD',
    braidD,
    traceD,
  )
where

import Circuit.Category (Category (..), Discrete (..), ObDict (..), withObDict)
import Control.Arrow (Kleisli (..))
import Control.Monad.Fix (MonadFix, mfix)
import Data.Bifunctor
import Data.Kind (Type)
import Data.These (These (..))
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XLambdaCase
-- >>> import Circuit.Category ((.>))
-- >>> import Circuit.Channel (Traced (..))
-- >>> import Circuit.Tensor (unitl, unitl')
-- >>> import Control.Arrow (Kleisli (..), runKleisli)
-- >>> import Data.Void (Void)

-- ===========================================================================
-- Channel
-- ===========================================================================

-- | A monoidal structure on the tensor @t@ internal to the category @arr@.
--
-- Provides the associator and braiding required to reassociate and swap
-- nested tensor values inside an arrow. This is the structure that traced
-- categories inherit as a superclass.
--
-- Object constraints live on 'Category' / 'Traced', not on these structure
-- maps — free constructions over unconstrained bases stay lightweight.
class (Category arr) => Channel t arr where
  -- | Reassociate to the right: @t (t a b) c -> t a (t b c)@.
  assoc ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t b c),
      Ob arr (t (t a b) c),
      Ob arr (t a (t b c))
    ) =>
    arr (t (t a b) c) (t a (t b c))

  -- | Inverse reassociation: @t a (t b c) -> t (t a b) c@.
  assoc' ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t b c),
      Ob arr (t (t a b) c),
      Ob arr (t a (t b c))
    ) =>
    arr (t a (t b c)) (t (t a b) c)

  -- | Swap the two outer positions, leaving the inner payload in place:
  -- @t a (t b c) -> t b (t a c)@.
  slide ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t b c),
      Ob arr (t a c),
      Ob arr (t a (t b c)),
      Ob arr (t b (t a c))
    ) =>
    arr (t a (t b c)) (t b (t a c))

  -- | Derive the tensor object constraint from its components.
  withTensorOb ::
    forall a b r.
    ObDict arr a ->
    ObDict arr b ->
    ((Ob arr (t a b)) => r) ->
    r

-- | Cartesian monoidal structure for @(,)@.
--
-- >>> assoc ((1, 2), 3) :: (Int, (Int, Int))
-- (1,(2,3))
--
-- >>> assoc' (1, (2, 3)) :: ((Int, Int), Int)
-- ((1,2),3)
--
-- >>> (assoc .> assoc') ((1, 2), 3) :: ((Int, Int), Int)
-- ((1,2),3)
--
-- >>> slide (1, (2, 3)) :: (Int, (Int, Int))
-- (2,(1,3))
instance Channel (,) (->) where
  assoc ~(~(a, b), c) = (a, (b, c))
  assoc' ~(a, ~(b, c)) = ((a, b), c)
  slide ~(a, ~(b, c)) = (b, (a, c))
  withTensorOb ObDict ObDict x = x

-- | Cocartesian monoidal structure for @Either@.
--
-- >>> assoc (Left (Left 1) :: Either (Either Int Bool) Char) :: Either Int (Either Bool Char)
-- Left 1
--
-- >>> assoc' (Left 1 :: Either Int (Either Bool Char)) :: Either (Either Int Bool) Char
-- Left (Left 1)
--
-- >>> slide (Left 1 :: Either Int (Either Bool Char)) :: Either Bool (Either Int Char)
-- Right (Left 1)
instance Channel Either (->) where
  assoc (Left (Left a)) = Left a
  assoc (Left (Right b)) = Right (Left b)
  assoc (Right c) = Right (Right c)
  assoc' (Left a) = Left (Left a)
  assoc' (Right (Left b)) = Left (Right b)
  assoc' (Right (Right c)) = Right c
  slide (Left a) = Right (Left a)
  slide (Right (Left b)) = Left b
  slide (Right (Right c)) = Right (Right c)
  withTensorOb ObDict ObDict x = x

-- | Inclusive monoidal structure for @These@.
--
-- @These@ sits above both @(,)@ and 'Either': 'This' is the residual-only
-- branch, 'That' is the payload-only branch, and 'These' carries both.
instance Channel These (->) where
  assoc (This (This a)) = This a
  assoc (This (That b)) = That (This b)
  assoc (This (These a b)) = These a (This b)
  assoc (That c) = That (That c)
  assoc (These (This a) c) = These a (That c)
  assoc (These (That b) c) = That (These b c)
  assoc (These (These a b) c) = These a (These b c)
  assoc' (This a) = This (This a)
  assoc' (That (This b)) = This (That b)
  assoc' (That (That c)) = That c
  assoc' (That (These b c)) = These (That b) c
  assoc' (These a (This b)) = This (These a b)
  assoc' (These a (That c)) = These (This a) c
  assoc' (These a (These b c)) = These (These a b) c
  slide (This a) = That (This a)
  slide (That (This b)) = This b
  slide (That (That c)) = That (That c)
  slide (That (These b c)) = These b (That c)
  slide (These a (This b)) = These b (This a)
  slide (These a (That c)) = That (These a c)
  slide (These a (These b c)) = These b (These a c)
  withTensorOb ObDict ObDict x = x

-- ===========================================================================
-- Strength
-- ===========================================================================

-- | Tensorial strength for a tensor @t@ inside a category @arr@.
--
-- 'strength' opens a feedback loop, tensoring a plain morphism with the
-- feedback channel. It is /not/ a syntactic inverse of 'trace'; it is the
-- strength ("tensorial strength") of the tensor @t@ acting on morphisms.
class (Channel t arr) => Strength t arr where
  strength ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t a c)
    ) =>
    arr b c ->
    arr (t a b) (t a c)

  -- | Derive the strength object constraints from their components.
  withStrengthOb ::
    forall a b c r.
    ObDict arr a ->
    ObDict arr b ->
    ObDict arr c ->
    ((Ob arr (t a b), Ob arr (t a c)) => r) ->
    r

-- | Discrete 'strength': discharge 'Ob' constraints with 'withOb'.
strengthD ::
  forall t arr a b c.
  (Strength t arr, Discrete arr) =>
  arr b c ->
  arr (t a b) (t a c)
strengthD f =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t a c) $
            strength f

-- | Cartesian tensorial strength for @(,)@.
--
-- The implementation uses explicit projections so that the result pair
-- constructor exists before the feedback channel is forced; this keeps
-- fused 'Circuit.Loop.Knot' bodies productive even when the body has a strict
-- top-level pattern on the recursive channel.
--
-- >>> strength (+1) (error "forced" :: (Int, Int)) `seq` ()
-- ()
instance Strength (,) (->) where
  strength f p = (fst p, f (snd p))
  withStrengthOb ObDict ObDict ObDict x = x

-- | Either tensorial strength for @Either@.
--
-- 'strength' is the functorial action under 'Either'.
instance Strength Either (->) where
  strength = fmap
  withStrengthOb ObDict ObDict ObDict x = x

-- | Inclusive tensorial strength for @These@.
--
-- 'strength' applies the payload morphism to the 'That' branch and the
-- 'These' branch, leaving the 'This' residual branch untouched.
instance Strength These (->) where
  strength _ (This a) = This a
  strength f (That b) = That (f b)
  strength f (These a b) = These a (f b)
  withStrengthOb ObDict ObDict ObDict x = x

-- ===========================================================================
-- Traced
-- ===========================================================================

-- | A trace over a morphism @arr@ and tensor @t@.
--
-- @trace@ closes the feedback loop, eliminating the tensor channel.
-- It extends the 'Strength' structure with the feedback-fixing operation.
--
-- Object constraints on the feedback channel (@a@) let constrained
-- categories (e.g. matrices needing @Finite@ / @KnownNat@) instance
-- this class lawfully.
--
-- Law note: the traced-category Sliding axiom is restricted in the
-- premonoidal setting. Benton & Hyland, "Traced Premonoidal Categories"
-- (2003, Def 3.2) replace unrestricted Sliding with /Central Sliding/:
-- a morphism @g@ may slide past the trace only when @g@ is central.
-- Dually, /Centre Preservation/ says @trace f@ is central whenever @f@ is.
-- This class does not enforce the side-conditions at the type level; lawful
-- instances must guarantee them by construction. See the @circuits-axioma@
-- oracles "unrestricted sliding fails for non-central Kleisli IO" and
-- "Loop trace requires centrality over Kleisli IO" for witnesses that the
-- side-condition is not vacuous.
class (Strength t arr) => Traced t arr where
  trace ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t a c)
    ) =>
    arr (t a b) (t a c) ->
    arr b c

-- * Cartesian tensor — lazy knot

-- | The cartesian trace ties a lazy knot: the feedback value @a@ and
-- output @c@ are produced simultaneously in a single recursive binding.
--
-- Only works in a lazy setting — the feedback value is a self-referential
-- thunk.  In a strict language this binding is circular and divergent.
-- Haskell's lazy evaluation makes cyclic sharing possible without an
-- explicit fixpoint operator.
--
-- >>> :{
-- let powers (ns, ()) =
--       (1 : map (*2) ns, take 5 ns)
-- :}
--
-- >>> trace powers () :: [Integer]
-- [1,2,4,8,16]
--
-- >>> trace (\(acc, x) -> (acc, x + 1)) 5
-- 6
--
-- Vanishing (a): tracing over the unit does nothing.
--
-- The unit is @()@ for the @(,)@ tensor. The unitor laws say that
-- threading a plain payload through the unit channel is the same as
-- applying the payload morphism directly.
--
-- >>> let f = (+1) :: Int -> Int
-- >>> trace (unitl' . f . unitl :: ((), Int) -> ((), Int)) 5
-- 6
--
-- >>> trace ((unitl' . (+ 3) . unitl) :: ((), Int) -> ((), Int)) 0
-- 3
--
-- Yanking: tracing a swap is the identity.
--
-- >>> let swap (x, y) = (y, x)
-- >>> trace swap 42
-- 42
--
-- >>> trace ((\(a, b) -> (b, a)) :: (Int, Int) -> (Int, Int)) 42
-- 42
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f (x, a) = (x, a)
-- >>> trace ((\(x, a) -> (x, a + 1)) . f . (\(x, a) -> (x, a * 2))) 5
-- 11
--
-- Sliding: a morphism on the channel slides from one side to the other.
--
-- >>> let swap (x, y) = (y, x)
-- >>> trace ((\(a, b) -> (b, a + 1)) . (\(a, b) -> (b, a)) :: (Int, Int) -> (Int, Int)) 5
-- 6
--
-- >>> trace ((\(a, b) -> (b + 1, a)) :: (Int, Int) -> (Int, Int)) 5
-- 6
--
-- Strength: an independent payload wire is invisible to the trace.
--
-- >>> let f (x, c) = (x, c + 1)
-- >>> let g (x, (a, c)) = (x', (a * 2, d)) where (x', d) = f (x, c)
-- >>> trace g (3, 5)
-- (6,6)
--
-- >>> trace ((\(x, (p, q)) -> (x, (p + 7, q + 1))) :: (Int, (Int, Int)) -> (Int, (Int, Int))) (0, 5)
-- (7,6)
instance Traced (,) (->) where
  trace f b = let ~(a, c) = f (a, b) in c

-- * Either tensor — iteration

-- | The Either trace iterates: 'Left' feeds back (continue), 'Right'
-- terminates (exit). A compact, under-appreciated pattern for loops in Haskell.
--
-- >>> :{
-- let fac (n, acc) | n <= 1    = Right acc
--                  | otherwise = Left (n - 1, n * acc)
-- :}
--
-- >>> trace (either fac fac) (5, 1 :: Int)
-- 120
--
-- >>> :{
-- let countdown = \case
--       Left n | n > 0 -> Left (n - 1)
--              | otherwise -> Right n
--       Right n | n > 0 -> Left (n - 1)
--               | otherwise -> Right n
-- :}
--
-- >>> trace countdown (3 :: Int)
-- 0
--
-- Vanishing (a): tracing over the unit does nothing.
--
-- The unit is 'Data.Void.Void' for the 'Either' tensor. The unitor
-- laws say that threading a plain payload through the unit channel is the
-- same as applying the payload morphism directly.
--
-- >>> let f = (+1) :: Int -> Int
-- >>> trace (unitl' . f . unitl :: Either Void Int -> Either Void Int) 5
-- 6
--
-- >>> trace ((unitl' . (+ 3) . unitl) :: Either Void Int -> Either Void Int) 0
-- 3
--
-- Yanking: tracing a swap is the identity.
--
-- >>> :{
-- let swapEither (Left x)  = Right x
--     swapEither (Right x) = Left x
-- :}
--
-- >>> trace swapEither 42
-- 42
--
-- >>> trace ((\e -> case e of Left a -> Right a; Right a -> Left a) :: Either Int Int -> Either Int Int) 42
-- 42
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f = fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int)
-- >>> trace (f :: Either Void Int -> Either Void Int) 5
-- 11
--
-- >>> trace (fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int) :: Either Void Int -> Either Void Int) 5
-- 11
instance Traced Either (->) where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)

-- ===========================================================================
-- Kleisli m — monoidal structure
-- ===========================================================================

-- | Cartesian monoidal structure for @Kleisli m@ with @(,)@.
instance (Monad m) => Channel (,) (Kleisli m) where
  assoc = Kleisli $ \ ~(~(a, b), c) -> pure (a, (b, c))
  assoc' = Kleisli $ \ ~(a, ~(b, c)) -> pure ((a, b), c)
  slide = Kleisli $ \ ~(a, ~(b, c)) -> pure (b, (a, c))
  withTensorOb ObDict ObDict x = x

-- | Cocartesian monoidal structure for @Kleisli m@ with 'Either'.
instance (Monad m) => Channel Either (Kleisli m) where
  assoc = Kleisli $ \case
    Left (Left a) -> pure (Left a)
    Left (Right b) -> pure (Right (Left b))
    Right c -> pure (Right (Right c))
  assoc' = Kleisli $ \case
    Left a -> pure (Left (Left a))
    Right (Left b) -> pure (Left (Right b))
    Right (Right c) -> pure (Right c)
  slide = Kleisli $ \case
    Left a -> pure (Right (Left a))
    Right (Left b) -> pure (Left b)
    Right (Right c) -> pure (Right (Right c))
  withTensorOb ObDict ObDict x = x

-- | Inclusive monoidal structure for @Kleisli m@ with 'These'.
instance (Monad m) => Channel These (Kleisli m) where
  assoc =
    Kleisli $
      pure . \case
        This (This a) -> This a
        This (That b) -> That (This b)
        This (These a b) -> These a (This b)
        That c -> That (That c)
        These (This a) c -> These a (That c)
        These (That b) c -> That (These b c)
        These (These a b) c -> These a (These b c)
  assoc' =
    Kleisli $
      pure . \case
        This a -> This (This a)
        That (This b) -> This (That b)
        That (That c) -> That c
        That (These b c) -> These (That b) c
        These a (This b) -> This (These a b)
        These a (That c) -> These (This a) c
        These a (These b c) -> These (These a b) c
  slide =
    Kleisli $
      pure . \case
        This a -> That (This a)
        That (This b) -> This b
        That (That c) -> That (That c)
        That (These b c) -> These b (That c)
        These a (This b) -> These b (This a)
        These a (That c) -> That (These a c)
        These a (These b c) -> These b (These a c)
  withTensorOb ObDict ObDict x = x

-- * Kleisli m (,) — lazy knot via MonadFix

-- | Traced for @Kleisli m@ with the cartesian tensor, requiring @MonadFix m@.
--
-- The lazy knot is tied via 'mfix'. The feedback channel is lazy in the
-- recursive binding — the body must not force the feedback value before
-- producing it, or 'mfix' will diverge (just as the pure @(,)@ trace
-- black-holes on strict fields).
--
-- >>> :{
-- let fibs = Kleisli $ \(fibs, ()) ->
--       pure (0 : 1 : zipWith (+) fibs (drop 1 fibs), take 3 fibs)
-- :}
--
-- >>> runKleisli (trace fibs) ()
-- [0,1,1]
instance (Monad m) => Strength (,) (Kleisli m) where
  strength (Kleisli f) =
    Kleisli
      ( \p -> do
          c <- f (snd p)
          pure (fst p, c)
      )
  withStrengthOb ObDict ObDict ObDict x = x

instance (MonadFix m) => Traced (,) (Kleisli m) where
  trace (Kleisli f) =
    Kleisli
      ( \b -> do
          (_, c) <- mfix $ \ ~(s, _) -> f (s, b)
          pure c
      )

-- * Kleisli m Either — iteration for any Monad

-- | Traced for @Kleisli m@ with the 'Either' tensor, for any @Monad m@.
--
-- Iterates by feeding 'Left' back into the step function until a 'Right'
-- is produced. Uses plain recursion — builds stack proportional to
-- iteration count.
--
-- >>> :{
-- let countTo target = Kleisli $ \case
--       Left n | n < target -> pure (Left (n + 1))
--              | otherwise  -> pure (Right n)
--       Right ()            -> pure (Left 0)
-- :}
--
-- >>> runKleisli (trace (countTo (3 :: Int))) ()
-- 3
--
-- This instance is @OVERLAPPABLE@: the IO-specific instance below takes
-- priority for @IO@, providing constant-stack iteration via delimited
-- continuations.
instance (Monad m) => Strength Either (Kleisli m) where
  strength (Kleisli f) =
    Kleisli $ \case
      Left a -> pure (Left a)
      Right b -> Right <$> f b
  withStrengthOb ObDict ObDict ObDict x = x

-- | Inclusive tensorial strength for @Kleisli m@ with 'These'.
instance (Monad m) => Strength These (Kleisli m) where
  strength (Kleisli f) =
    Kleisli $ \case
      This a -> pure (This a)
      That b -> That <$> f b
      These a b -> These a <$> f b
  withStrengthOb ObDict ObDict ObDict x = x

instance {-# OVERLAPPABLE #-} (Monad m) => Traced Either (Kleisli m) where
  trace (Kleisli f) =
    Kleisli $ \b -> go (Right b)
    where
      go x =
        f x >>= \case
          Right c -> pure c
          Left a -> go (Left a)

-- * Kleisli IO Either — delimited continuations (constant stack)

-- | GHC delimited-continuation primops.
data PromptTag a = PromptTag (PromptTag# a)

-- | Create a new prompt tag for delimited continuations.
newPromptTag :: IO (PromptTag a)
newPromptTag =
  IO
    ( \s ->
        case newPromptTag# s of
          (# s', t #) -> (# s', PromptTag t #)
    )

-- | Run an IO computation under a prompt boundary.
prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

-- | Captures the continuation up to the nearest prompt with the matching tag.
control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

-- | Traced for @Kleisli IO@ with 'Either' tensor.
--
-- Each iteration re-establishes the prompt boundary. When @control0@
-- fires on @Left a@, it captures the continuation, wraps it around
-- the next loop step, and jumps back to the prompt — constant stack.
--
-- >>> :{
-- let exit42 = Kleisli $ \case
--       Right () -> pure (Right (42 :: Int))
-- :}
--
-- >>> runKleisli (trace exit42) ()
-- 42
instance {-# OVERLAPPING #-} Traced Either (Kleisli IO) where
  trace (Kleisli body) =
    Kleisli
      ( \initial -> do
          tag <- newPromptTag
          let go x =
                prompt tag $
                  body x
                    >>= ( \case
                            Right c -> pure c
                            Left a -> control0 tag (\k -> k (go (Left a)))
                        )
          go (Right initial)
      )

-- ===========================================================================
-- Discrete discharge kit
-- ===========================================================================

-- | Discrete composition: compose two arrows while discharging 'Ob'
-- constraints with 'withOb'.
compD ::
  forall arr a b c.
  (Discrete arr) =>
  arr b c ->
  arr a b ->
  arr a c
compD f g =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        f . g

-- | Discrete associator: reassociate leftward while discharging 'Ob'
-- constraints.
assocD ::
  forall t arr a b c.
  (Channel t arr, Discrete arr) =>
  arr (t (t a b) c) (t a (t b c))
assocD =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t b c) $
            withOb @arr @(t (t a b) c) $
              withOb @arr @(t a (t b c)) $
                assoc

-- | Discrete associator inverse: reassociate rightward while discharging
-- 'Ob' constraints.
assocD' ::
  forall t arr a b c.
  (Channel t arr, Discrete arr) =>
  arr (t a (t b c)) (t (t a b) c)
assocD' =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t b c) $
            withOb @arr @(t a (t b c)) $
              withOb @arr @(t (t a b) c) $
                assoc'

-- | Discrete braiding: slide a wire past a nested pair while discharging
-- 'Ob' constraints.
braidD ::
  forall t arr a b c.
  (Channel t arr, Discrete arr) =>
  arr (t a (t b c)) (t b (t a c))
braidD =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t b c) $
          withOb @arr @(t a c) $
            withOb @arr @(t a (t b c)) $
              withOb @arr @(t b (t a c)) $
                slide

-- | Discrete trace: eliminate a feedback loop while discharging 'Ob'
-- constraints.
traceD ::
  forall t arr a b c.
  (Traced t arr, Discrete arr) =>
  arr (t a b) (t a c) ->
  arr b c
traceD f =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t a c) $
            trace f
