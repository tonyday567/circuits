{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Structural semantics for traced monoidal categories.
--
-- This module collects the structural superclass chain
-- @Assoc → Slide → Strength → Yank@ and all base instances for the standard
-- base arrows @(->)@ and @K m@.  These classes describe the monoidal
-- associator, the slide (braiding-with-payload), tensorial strength, and
-- feedback-fixing trace that underlie the syntax in "Circuit.Trace".
--
-- 'assoc' and 'assoc'' here reassociate /rightward/ and /leftward/
-- respectively. The monomorphic helpers in "Circuit.Tensor" have the same
-- names but the opposite directions. Also, 'slide' here is the slide
-- @t a (t b c) -> t b (t a c)@; the symmetric braiding @t a b -> t b a@
-- lives in Circuit.Tensor as braid. Where both structures exist,
-- @slide = assoc' .> tensor braid id .> assoc@.
--
-- @t@ and @arr@ are monomorphic at 'Type' so that downstream type-family
-- carriers (for example in @circuits-chu@) can write explicit signatures.
module Circuit.Traced
  ( Assoc (..),
    Slide (..),
    Strength (..),
    Yank (..),
    TraceC,
  )
where

import Circuit.Category (Category (..), K (..), Op (..))
import Control.Monad.Fix (MonadFix, mfix)
import Data.Kind (Type)
import Data.These (These (..))
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XLambdaCase
-- >>> import Circuit.Category ((.>))
-- >>> import Circuit.Traced (Yank (..))
-- >>> import Circuit.Tensor (unitl, unitl')
-- >>> import Circuit.Category (K (..), runK)
-- >>> import Circuit.Category (Op (..))
-- >>> import Data.Void (Void)

-- * Associator

-- | The associator for a tensor @t@ internal to the category @arr@.
--
-- Provides the two directions of reassociation required by a monoidal
-- structure. This is the first layer that traced categories inherit as a
-- superclass.
--
-- The previous quantified superclass that stated closure of an object
-- constraint under the tensor has been removed along with the @Ob@
-- apparatus; composite-object legitimacy is an audit concern.
class
  (Category arr) =>
  Assoc (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type)
  where
  -- | Reassociate to the right: @t (t a b) c -> t a (t b c)@.
  assoc ::
    arr (t (t a b) c) (t a (t b c))

  -- | Inverse reassociation: @t a (t b c) -> t (t a b) c@.
  assoc' ::
    arr (t a (t b c)) (t (t a b) c)

-- | Cartesian associator for @(,)@.
--
-- >>> assoc ((1, 2), 3) :: (Int, (Int, Int))
-- (1,(2,3))
--
-- >>> assoc' (1, (2, 3)) :: ((Int, Int), Int)
-- ((1,2),3)
--
-- >>> (assoc .> assoc') ((1, 2), 3) :: ((Int, Int), Int)
-- ((1,2),3)
instance Assoc (,) (->) where
  assoc ~(~(a, b), c) = (a, (b, c))
  assoc' ~(a, ~(b, c)) = ((a, b), c)

-- | Cocartesian associator for @Either@.
--
-- >>> assoc (Left (Left 1) :: Either (Either Int Bool) Char) :: Either Int (Either Bool Char)
-- Left 1
--
-- >>> assoc' (Left 1 :: Either Int (Either Bool Char)) :: Either (Either Int Bool) Char
-- Left (Left 1)
instance Assoc Either (->) where
  assoc (Left (Left a)) = Left a
  assoc (Left (Right b)) = Right (Left b)
  assoc (Right c) = Right (Right c)
  assoc' (Left a) = Left (Left a)
  assoc' (Right (Left b)) = Left (Right b)
  assoc' (Right (Right c)) = Right c

-- | Inclusive associator for @These@.
--
-- @These@ sits above both @(,)@ and 'Either': 'This' is the residual-only
-- branch, 'That' is the payload-only branch, and 'These' carries both.
instance Assoc These (->) where
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

-- | Opposite category: structural morphisms are reversed.
--
-- @Op arr@ reverses every arrow, so the associator uses the inverse direction
-- and the slide (an involution for the standard tensors) stays the same.
instance (Assoc t arr) => Assoc t (Op arr) where
  assoc = Op assoc'
  assoc' = Op assoc

-- * Slide

-- | The slide for a tensor @t@ internal to the category @arr@.
--
-- 'slide' swaps the two outer positions, leaving the inner payload in place:
-- @t a (t b c) -> t b (t a c)@. It is the structural half-braid used by the
-- sliding axiom of a traced category.
class
  (Category arr) =>
  Slide (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type)
  where
  -- | Swap the two outer positions, leaving the inner payload in place:
  -- @t a (t b c) -> t b (t a c)@.
  slide ::
    arr (t a (t b c)) (t b (t a c))

-- | Cartesian slide for @(,)@.
--
-- >>> slide (1, (2, 3)) :: (Int, (Int, Int))
-- (2,(1,3))
instance Slide (,) (->) where
  slide ~(a, ~(b, c)) = (b, (a, c))

-- | Cocartesian slide for @Either@.
--
-- >>> slide (Left 1 :: Either Int (Either Bool Char)) :: Either Bool (Either Int Char)
-- Right (Left 1)
instance Slide Either (->) where
  slide (Left a) = Right (Left a)
  slide (Right (Left b)) = Left b
  slide (Right (Right c)) = Right (Right c)

-- | Inclusive slide for @These@.
instance Slide These (->) where
  slide (This a) = That (This a)
  slide (That (This b)) = This b
  slide (That (That c)) = That (That c)
  slide (That (These b c)) = These b (That c)
  slide (These a (This b)) = These b (This a)
  slide (These a (That c)) = That (These a c)
  slide (These a (These b c)) = These b (These a c)

-- | Opposite category: slide is an involution, so it stays the same.
instance (Slide t arr) => Slide t (Op arr) where
  slide = Op slide

-- * Strength

-- | Tensorial strength for a tensor @t@ inside a category @arr@.
--
-- 'strength' tensors a plain morphism with the ambient channel. It is
-- /not/ a syntactic inverse of 'yank'; it is the strength
-- ("tensorial strength") of the tensor @t@ acting on morphisms.
class (Assoc t arr, Slide t arr) => Strength (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) where
  strength ::
    arr b c ->
    arr (t a b) (t a c)

-- | Cartesian tensorial strength for @(,)@.
--
-- The implementation uses explicit projections so that the result pair
-- constructor exists before the feedback channel is forced; this keeps
-- fused 'Circuit.Trace.yank' bodies productive even when the body has a strict
-- top-level pattern on the recursive channel.
--
-- >>> strength (+1) (error "forced" :: (Int, Int)) `seq` ()
-- ()
instance Strength (,) (->) where
  strength f p = (fst p, f (snd p))

-- | Either tensorial strength for @Either@.
--
-- 'strength' is the functorial action under 'Either'.
instance Strength Either (->) where
  strength = fmap

-- | Inclusive tensorial strength for @These@.
--
-- 'strength' applies the payload morphism to the 'That' branch and the
-- 'These' branch, leaving the 'This' residual branch untouched.
instance Strength These (->) where
  strength _ (This a) = This a
  strength f (That b) = That (f b)
  strength f (These a b) = These a (f b)

-- | Opposite category: strength is reversed along with the base arrow.
instance (Strength t arr) => Strength t (Op arr) where
  strength (Op f) = Op (strength f)

-- * Yank

-- | A trace over a morphism @arr@ and tensor @t@.
--
-- @yank@ closes the feedback loop, eliminating the tensor channel.
-- It extends the 'Strength' structure with the feedback-fixing operation.
--
-- Object constraints on the feedback channel (@a@) used to let constrained
-- categories instance this class lawfully; those constraints are now
-- explicit at the instance site rather than inherited from a constraint
-- family.
--
-- Law note: the traced-category Sliding axiom is restricted in the
-- premonoidal setting. Benton & Hyland, "Traced Premonoidal Categories"
-- (2003, Def 3.2) replace unrestricted Sliding with /Central Sliding/:
-- a morphism @g@ may slide past the trace only when @g@ is central.
-- Dually, /Centre Preservation/ says @yank f@ is central whenever @f@ is.
-- This class does not enforce the side-conditions at the type level; lawful
-- instances must guarantee them by construction. See the @circuits-axioma@
-- sliding oracles for witnesses that the side-condition is not vacuous.
class (Strength t arr) => Yank (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) where
  yank ::
    arr (t a b) (t a c) ->
    arr b c

-- | Constraint synonym bundling the four structural layers of a traced
-- monoidal category.
type TraceC t arr = (Assoc t arr, Slide t arr, Strength t arr, Yank t arr)

-- * Cartesian tensor — lazy knot

-- | The cartesian yank ties a lazy knot: the feedback value @a@ and
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
-- >>> yank powers () :: [Integer]
-- [1,2,4,8,16]
--
-- >>> yank (\(acc, x) -> (acc, x + 1)) 5
-- 6
--
-- Vanishing (a): tracing over the unit does nothing.
--
-- The unit is @()@ for the @(,)@ tensor. The unitor laws say that
-- threading a plain payload through the unit channel is the same as
-- applying the payload morphism directly.
--
-- >>> let f = (+1) :: Int -> Int
-- >>> yank (unitl' . f . unitl :: ((), Int) -> ((), Int)) 5
-- 6
--
-- >>> yank ((unitl' . (+ 3) . unitl) :: ((), Int) -> ((), Int)) 0
-- 3
--
-- Yanking: tracing a braid is the identity.
--
-- >>> let braid (x, y) = (y, x)
-- >>> yank braid 42
-- 42
--
-- >>> yank ((\(a, b) -> (b, a)) :: (Int, Int) -> (Int, Int)) 42
-- 42
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f (x, a) = (x, a)
-- >>> yank ((\(x, a) -> (x, a + 1)) . f . (\(x, a) -> (x, a * 2))) 5
-- 11
--
-- Sliding: a morphism on the channel slides from one side to the other.
--
-- >>> let braid (x, y) = (y, x)
-- >>> yank ((\(a, b) -> (b, a + 1)) . (\(a, b) -> (b, a)) :: (Int, Int) -> (Int, Int)) 5
-- 6
--
-- >>> yank ((\(a, b) -> (b + 1, a)) :: (Int, Int) -> (Int, Int)) 5
-- 6
--
-- Strength: an independent payload wire is invisible to the trace.
--
-- >>> let f (x, c) = (x, c + 1)
-- >>> let g (x, (a, c)) = (x', (a * 2, d)) where (x', d) = f (x, c)
-- >>> yank g (3, 5)
-- (6,6)
--
-- >>> yank ((\(x, (p, q)) -> (x, (p + 7, q + 1))) :: (Int, (Int, Int)) -> (Int, (Int, Int))) (0, 5)
-- (7,6)
instance Yank (,) (->) where
  yank f b = let ~(a, c) = f (a, b) in c

-- * Either tensor — iteration

-- | The Either yank iterates: 'Left' feeds back (continue), 'Right'
-- terminates (exit). A compact, under-appreciated pattern for loops in Haskell.
--
-- >>> :{
-- let fac (n, acc) | n <= 1    = Right acc
--                  | otherwise = Left (n - 1, n * acc)
-- :}
--
-- >>> yank (either fac fac) (5, 1 :: Int)
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
-- >>> yank countdown (3 :: Int)
-- 0
--
-- Vanishing (a): tracing over the unit does nothing.
--
-- The unit is 'Data.Void.Void' for the 'Either' tensor. The unitor
-- laws say that threading a plain payload through the unit channel is
-- the same as applying the payload morphism directly.
--
-- >>> let f = (+1) :: Int -> Int
-- >>> yank (unitl' . f . unitl :: Either Void Int -> Either Void Int) 5
-- 6
--
-- >>> yank ((unitl' . (+ 3) . unitl) :: Either Void Int -> Either Void Int) 0
-- 3
--
-- Yanking: tracing a braid is the identity.
--
-- >>> :{
-- let swapEither (Left x)  = Right x
--     swapEither (Right x) = Left x
-- :}
--
-- >>> yank swapEither 42
-- 42
--
-- >>> yank ((\e -> case e of Left a -> Right a; Right a -> Left a) :: Either Int Int -> Either Int Int) 42
-- 42
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f = fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int)
-- >>> yank (f :: Either Void Int -> Either Void Int) 5
-- 11
--
-- >>> yank (fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int) :: Either Void Int -> Either Void Int) 5
-- 11
instance Yank Either (->) where
  yank f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)

-- * K m — monoidal structure

-- | Cartesian associator for @K m@ with @(,)@.
instance (Monad m) => Assoc (,) (K m) where
  assoc = K $ \ ~(~(a, b), c) -> pure (a, (b, c))
  assoc' = K $ \ ~(a, ~(b, c)) -> pure ((a, b), c)

-- | Cocartesian associator for @K m@ with 'Either'.
instance (Monad m) => Assoc Either (K m) where
  assoc = K $ \case
    Left (Left a) -> pure (Left a)
    Left (Right b) -> pure (Right (Left b))
    Right c -> pure (Right (Right c))
  assoc' = K $ \case
    Left a -> pure (Left (Left a))
    Right (Left b) -> pure (Left (Right b))
    Right (Right c) -> pure (Right c)

-- | Inclusive associator for @K m@ with 'These'.
instance (Monad m) => Assoc These (K m) where
  assoc =
    K $
      pure . \case
        This (This a) -> This a
        This (That b) -> That (This b)
        This (These a b) -> These a (This b)
        That c -> That (That c)
        These (This a) c -> These a (That c)
        These (That b) c -> That (These b c)
        These (These a b) c -> These a (These b c)
  assoc' =
    K $
      pure . \case
        This a -> This (This a)
        That (This b) -> This (That b)
        That (That c) -> That c
        That (These b c) -> These (That b) c
        These a (This b) -> This (These a b)
        These a (That c) -> These (This a) c
        These a (These b c) -> These (These a b) c

-- | Cartesian slide for @K m@ with @(,)@.
instance (Monad m) => Slide (,) (K m) where
  slide = K $ \ ~(a, ~(b, c)) -> pure (b, (a, c))

-- | Cocartesian slide for @K m@ with 'Either'.
instance (Monad m) => Slide Either (K m) where
  slide = K $ \case
    Left a -> pure (Right (Left a))
    Right (Left b) -> pure (Left b)
    Right (Right c) -> pure (Right (Right c))

-- | Inclusive slide for @K m@ with 'These'.
instance (Monad m) => Slide These (K m) where
  slide =
    K $
      pure . \case
        This a -> That (This a)
        That (This b) -> This b
        That (That c) -> That (That c)
        That (These b c) -> These b (That c)
        These a (This b) -> These b (This a)
        These a (That c) -> That (These a c)
        These a (These b c) -> These b (These a c)

-- * K m (,) — lazy knot via MonadFix

-- | Strength for @K m@ with the cartesian tensor.
--
-- The implementation keeps the feedback channel lazy so that fused
-- 'Circuit.Trace.yank' bodies remain productive.
instance (Monad m) => Strength (,) (K m) where
  strength (K f) =
    K
      ( \p -> do
          c <- f (snd p)
          pure (fst p, c)
      )

-- | Yank for @K m@ with the cartesian tensor, requiring @MonadFix m@.
--
-- The lazy knot is tied via 'mfix'. The feedback channel is lazy in the
-- recursive binding — the body must not force the feedback value before
-- producing it, or 'mfix' will diverge (just as the pure @(,)@ yank
-- black-holes on strict fields).
--
-- >>> :{
-- let fibs = K $ \(fibs, ()) ->
--       pure (0 : 1 : zipWith (+) fibs (drop 1 fibs), take 3 fibs)
-- :}
--
-- >>> runK (yank fibs) ()
-- [0,1,1]
instance (MonadFix m) => Yank (,) (K m) where
  yank (K f) =
    K
      ( \b -> do
          (_, c) <- mfix $ \ ~(s, _) -> f (s, b)
          pure c
      )

-- * K m Either — iteration for any Monad

-- | Either tensorial strength for @K m@, for any @Monad m@.
--
-- This instance is @OVERLAPPABLE@: the IO-specific instance below takes
-- priority for @IO@, providing constant-stack iteration via delimited
-- continuations.
instance (Monad m) => Strength Either (K m) where
  strength (K f) =
    K $ \case
      Left a -> pure (Left a)
      Right b -> Right <$> f b

-- | Inclusive tensorial strength for @K m@ with 'These'.
instance (Monad m) => Strength These (K m) where
  strength (K f) =
    K $ \case
      This a -> pure (This a)
      That b -> That <$> f b
      These a b -> These a <$> f b

-- | Yank for @K m@ with the 'Either' tensor, for any @Monad m@.
--
-- Iterates by feeding 'Left' back into the step function until a 'Right'
-- is produced. Uses plain recursion — builds stack proportional to
-- iteration count.
--
-- >>> :{
-- let countTo target = K $ \case
--       Left n | n < target -> pure (Left (n + 1))
--              | otherwise  -> pure (Right n)
--       Right ()            -> pure (Left 0)
-- :}
--
-- >>> runK (yank (countTo (3 :: Int))) ()
-- 3
instance {-# OVERLAPPABLE #-} (Monad m) => Yank Either (K m) where
  yank (K f) =
    K $ \b -> go (Right b)
    where
      go x =
        f x >>= \case
          Right c -> pure c
          Left a -> go (Left a)

-- * K IO Either — delimited continuations (constant stack)

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

-- | Yank for @K IO@ with 'Either' tensor.
--
-- Each iteration re-establishes the prompt boundary. When @control0@
-- fires on @Left a@, it captures the continuation, wraps it around
-- the next loop step, and jumps back to the prompt — constant stack.
--
-- >>> :{
-- let exit42 = K $ \case
--       Right () -> pure (Right (42 :: Int))
-- :}
--
-- >>> runK (yank exit42) ()
-- 42
instance {-# OVERLAPPING #-} Yank Either (K IO) where
  yank (K body) =
    K
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

-- * Op — the co-trace

-- | Yank for the opposite arrow: the co-trace.
--
-- Reversing the arrow reverses the body but not the loop: @yank (Op f)@ is
-- @Op (yank f)@ — the same knot equation, read contravariantly. This
-- completes the structural ladder: @TraceC t (Op arr)@ holds wherever
-- @TraceC t arr@ does, so loops over codata bodies (@Body t ch (Op arr)@)
-- close with the same lazy knot and iteration as data bodies.
--
-- The cartesian co-knot is the knot, verbatim:
--
-- >>> :{
-- let powers (ns, ()) = (1 : map (*2) ns, take 5 ns)
-- :}
--
-- >>> runOp (yank (Op powers)) () :: [Integer]
-- [1,2,4,8,16]
--
-- Co-trace agreement: on a named body, co-yanking the flipped body is the
-- knot itself.
--
-- >>> let acc (s, a) = (s + a, a * 2)
-- >>> yank acc (5 :: Int)
-- 10
-- >>> runOp (yank (Op acc)) (5 :: Int)
-- 10
--
-- The Either co-yank iterates with the same Left-feeds-back / Right-exits
-- convention, driven by the contravariant body:
--
-- >>> :{
-- let halveOrBump = \case
--       Right n -> Left (n + 1)
--       Left n | even n -> Right (n `div` 2)
--              | otherwise -> Left (n + 1)
-- :}
--
-- >>> runOp (yank (Op halveOrBump)) (5 :: Int)
-- 3
instance (Yank t arr) => Yank t (Op arr) where
  yank :: forall a b c. Op arr (t a b) (t a c) -> Op arr b c
  yank (Op f) = Op (yank f)
