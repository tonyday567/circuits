{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The free traced monoidal category, in existential normal form, and the
-- 'Traced' class that gives feedback-loop semantics to a base category.
--
-- @Loop t arr a b@ is the free traced monoidal category over a base
-- morphism @arr@ with tensor @t@. The two constructors encode:
--
--   * 'Lift' — a plain base arrow.
--   * 'Knot' — a feedback loop with a hidden feedback channel.
--
-- The laws of traced monoidal categories are performed by the 'Category'
-- and 'Traced' instances, so every value is already in normal form: at most
-- one 'Knot' at the top, over a base-arrow body.
--
-- For example, a @Loop (,) (->)@ is the initial traced monoidal cartesian
-- category over Haskell functions.
--
-- = Introduce / resolve
--
-- The vocabulary in this module follows the introduce/resolve pattern:
--
--   * 'Knot' introduces feedback; 'trace' resolves it. This is the gold
--     type-changing pair; composition fuses 'Knot's.
--
-- The polar channel ends ('Out', 'In'), their counit ('close'), and
-- their unit ('open') all live in "Circuit.Ends".
--
-- == Interpreting a 'Loop'
--
-- Use 'run' or 'bind' to interpret a 'Loop' into a target category.  The
-- 'Category' and 'Traced' instances of the target discharge the knot; for
-- @(->)@ this is lazy knot-tying, and for 'Either' it is iteration.
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor that pairs a feedback value with a payload.
--   The two tensors provided are @(,)@ (simultaneous / lazy sharing) and
--   'Either' (sequential / iteration).
--
-- * __Feedback value__: The component that travels around the loop (the first
--   parameter of the tensor inside a 'Knot' body).
--
-- * __Payload__: The component that is transformed and emitted (the second
--   parameter of the tensor inside a 'Knot' body).
--
-- * __Feedback channel__: The hidden type @s@ in a 'Knot'. It is the value
--   the abstraction hides.
module Circuit.Trace
  ( -- * Loop
    Loop (..),

    -- * Traced class
    Traced (..),

    -- * Strength class
    Strength (..),

    -- * Stateful IO stages
    cellIO,

    -- * Layer witness
    FreeLoop,
  )
where

import Circuit.Category (Category (..), Discrete (..), (>>>))
import Circuit.Layer (Layer (..), run, (:~>))
import Circuit.Channel (Channel (..))
import Circuit.Strength (Strength (..))
import Control.Arrow (Kleisli (..))
import Control.Monad.Fix (MonadFix, mfix)
import Data.Bifunctor
import Data.IORef
import Data.Kind (Type)
import Data.Profunctor
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Tensor (Tensor (..))
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Circuit.Category ((.), (>>>))
-- >>> import Data.Void (Void)
-- >>> import Prelude hiding (id, (.))

-- | A trace over a morphism @arr@ and tensor @t@.
--
-- @trace@ closes the feedback loop, eliminating the tensor channel.
-- It extends the 'Strength' structure with the feedback-fixing operation.
--
-- Object constraints on the feedback channel (@a@) let constrained
-- categories (e.g. matrices needing 'Finite' / 'KnownNat') instance
-- this class lawfully.
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

-- | The free traced monoidal category over base morphism @arr@ and tensor @t@,
-- in existential normal form.
--
-- Two constructors:
--
--   * 'Lift' — a plain base arrow.
--   * 'Knot' — a feedback loop with hidden channel @s@.
data Loop (t :: Type -> Type -> Type) arr a b where
  -- | A plain base arrow.
  --
  -- >>> run (Lift (+1) :: Loop (,) (->) Int Int) 5
  -- 6
  Lift :: arr a b -> Loop t arr a b
  -- | Tie a feedback loop. The tensor @t@ carries the hidden channel type @s@.
  --
  -- The argument is the base arrow itself, /not/ a 'Lift'-wrapped stage:
  --
  -- >>> run (Knot (\(acc, x) -> (x, acc)) :: Loop (,) (->) Int Int) 42
  -- 42
  --
  -- For the @(,)@ tensor the channel value is self-referential, so the body
  -- must use an irrefutable pattern or otherwise avoid forcing the channel
  -- before producing its constructor:
  --
  -- >>> run (Knot (\ ~(ns, ()) -> (0 : ns, take 3 ns)) :: Loop (,) (->) () [Int]) ()
  -- [0,0,0]
  --
  -- The constructor carries the 'Ob' evidence for the feedback channel in
  -- the /source/ category.  Folding into a different target still needs
  -- 'Discrete' to manufacture the corresponding 'Ob' evidence there.
  Knot :: Ob arr s => arr (t s a) (t s b) -> Loop t arr a b

instance (Strength t arr, Discrete arr) => Category (Loop t arr) where
  type Ob (Loop t arr) a = Ob arr a
  id :: forall a. (Ob arr a) => Loop t arr a a
  id = Lift id
  (.) :: forall a b c. (Ob arr a, Ob arr b, Ob arr c) => Loop t arr b c -> Loop t arr a b -> Loop t arr a c
  Lift f . Lift g = Lift (f . g)
  Knot @_ @s @_ @_ @_ f . Lift g =
    withOb @arr @(t s a) $
      withOb @arr @(t s b) $
        withOb @arr @(t s c) $
          Knot (f . strength g)
  Lift f . Knot @_ @s @_ @_ @_ g =
    withOb @arr @(t s a) $
      withOb @arr @(t s b) $
        withOb @arr @(t s c) $
          Knot (strength f . g)
  Knot @_ @s2 @_ @_ @_ f . Knot @_ @s1 @_ @_ @_ g =
    withOb @arr @(t s2 s1) $
      withOb @arr @(t (t s2 s1) a) $
        withOb @arr @(t s2 (t s1 a)) $
          withOb @arr @(t s2 (t s1 b)) $
            withOb @arr @(t s2 (t s1 c)) $
              withOb @arr @(t s1 a) $
                withOb @arr @(t s1 b) $
                  withOb @arr @(t s1 (t s2 b)) $
                    withOb @arr @(t s2 b) $
                      withOb @arr @(t s2 c) $
                        withOb @arr @(t s1 (t s2 c)) $
                          withOb @arr @(t (t s2 s1) c) $
                            Knot (assoc >>> strength g >>> slide >>> strength f >>> slide >>> assoc')

-- | A discrete base yields a discrete free traced category.
instance (Strength t arr, Discrete arr) => Discrete (Loop t arr) where
  withOb @a x = withOb @arr @a x

instance (Profunctor arr, Bifunctor t) => Profunctor (Loop t arr) where
  dimap f g (Lift h) = Lift (dimap f g h)
  dimap f g (Knot h) = Knot (dimap (second f) (second g) h)
  lmap f (Lift h) = Lift (lmap f h)
  lmap f (Knot h) = Knot (lmap (second f) h)
  rmap g (Lift h) = Lift (rmap g h)
  rmap g (Knot h) = Knot (rmap (second g) h)

instance (Bifunctor t) => Functor (Loop t (->) a) where
  fmap f (Lift g) = Lift (f . g)
  fmap f (Knot g) = Knot (second f . g)

-- | Lift the 'Channel' structure of the base arrow into 'Loop t arr'.
--
-- The 'withOb' ladder is written out inline rather than using
-- 'Circuit.Discrete.assocD' / 'slideD' because importing that kit here would
-- create a cycle: 'Circuit.Discrete' needs 'Traced' (and hence this module).
instance (Strength t arr, Discrete arr) => Channel t (Loop t arr) where
  assoc :: forall a b c. Loop t arr (t (t a b) c) (t a (t b c))
  assoc =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @(t a b) $
              withOb @arr @(t b c) $
                withOb @arr @(t (t a b) c) $
                  withOb @arr @(t a (t b c)) $
                    assoc
  assoc' :: forall a b c. Loop t arr (t a (t b c)) (t (t a b) c)
  assoc' =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @(t a b) $
              withOb @arr @(t b c) $
                withOb @arr @(t a (t b c)) $
                  withOb @arr @(t (t a b) c) $
                    assoc'
  slide :: forall a b c. Loop t arr (t a (t b c)) (t b (t a c))
  slide =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @(t b c) $
              withOb @arr @(t a c) $
                withOb @arr @(t a (t b c)) $
                  withOb @arr @(t b (t a c)) $
                    slide

-- | Lift the 'Strength' class through 'Loop t'.
instance (Strength t arr, Discrete arr) => Strength t (Loop t arr) where
  strength :: forall a b c. (Ob arr a, Ob arr b, Ob arr c, Ob arr (t a b), Ob arr (t a c)) => Loop t arr b c -> Loop t arr (t a b) (t a c)
  strength (Lift f) =
    Lift $
      withOb @arr @a $
        withOb @arr @b $
          withOb @arr @c $
            withOb @arr @(t a b) $
              withOb @arr @(t a c) $
                strength f
  strength (Knot @_ @s @_ @_ @_ f) =
    withOb @arr @(t s (t a b)) $
      withOb @arr @(t a (t s b)) $
        withOb @arr @(t a (t s c)) $
      withOb @arr @(t s b) $
        withOb @arr @(t s c) $
          withOb @arr @(t s (t a c)) $
            Knot (slide >>> strength f >>> slide)

-- | Lift the 'Traced' class through 'Loop t'.
--
-- 'trace' hides a wire as a 'Knot'.
instance (Traced t arr, Discrete arr) => Traced t (Loop t arr) where
  trace ::
    forall a b c.
    (Ob arr a) =>
    Loop t arr (t a b) (t a c) ->
    Loop t arr b c
  trace (Lift f) = Knot f
  trace (Knot @_ @s @_ @_ @_ f) =
    withOb @arr @(t (t s a) b) $
      withOb @arr @(t s (t a b)) $
        withOb @arr @(t s (t a c)) $
          withOb @arr @(t (t s a) c) $
            withOb @arr @(t s a) $
              Knot (assoc >>> f >>> assoc')

-- | Cartesian tensorial strength for @(,)@.
--
-- The implementation uses explicit projections so that the result pair
-- constructor exists before the feedback channel is forced; this keeps
-- fused 'Knot' bodies productive even when the body has a strict
-- top-level pattern on the recursive channel.
--
-- >>> strength (+1) (error "forced" :: (Int, Int)) `seq` ()
-- ()
instance Strength (,) (->) where
  strength f p = (fst p, f (snd p))

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

-- | Either tensorial strength for @Either@.
--
-- 'strength' is the functorial action under 'Either'.
instance Strength Either (->) where
  strength = fmap

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
-- laws say that threading a plain payload through the unit channel is
-- the same as applying the payload morphism directly.
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

-- * Kleisli m — monoidal structure

-- | Cartesian monoidal structure for 'Kleisli' @m@ with @(,)@.
instance (Monad m) => Channel (,) (Kleisli m) where
  assoc = Kleisli $ \ ~(~(a, b), c) -> pure (a, (b, c))
  assoc' = Kleisli $ \ ~(a, ~(b, c)) -> pure ((a, b), c)
  slide = Kleisli $ \ ~(a, ~(b, c)) -> pure (b, (a, c))

-- | Cocartesian monoidal structure for 'Kleisli' @m@ with 'Either'.
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

-- * Kleisli m (,) — lazy knot via MonadFix

-- | Traced for 'Kleisli' @m@ with the cartesian tensor, requiring @'MonadFix' m@.
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

instance (MonadFix m) => Traced (,) (Kleisli m) where
  trace (Kleisli f) =
    Kleisli
      ( \b -> do
          (_, c) <- mfix $ \ ~(s, _) -> f (s, b)
          pure c
      )

-- * Kleisli m Either — iteration for any Monad

-- | Traced for 'Kleisli' @m@ with the 'Either' tensor, for any @'Monad' m@.
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
-- priority for 'IO', providing constant-stack iteration via delimited
-- continuations.
instance (Monad m) => Strength Either (Kleisli m) where
  strength (Kleisli f) =
    Kleisli $ \case
      Left a -> pure (Left a)
      Right b -> Right <$> f b

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

-- | Traced for 'Kleisli' 'IO' with 'Either' tensor.
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

-- * Stateful stages via IORef

-- | Create a stateful 'Kleisli' 'IO' arrow backed by 'IORef'.
--
-- Allocates a mutable reference once, then each invocation reads the
-- current state, applies the transfer function, writes the new state
-- back, and returns the output. The 'IORef' is hidden inside the
-- arrow — callers see a pure @Kleisli IO a b@.
--
-- This breaks the circular dependency that 'MonadFix' requires for
-- the 'Traced' @(,)@ instance: the feedback value is stored in the
-- mutable cell rather than being self-referential. Strict accumulators
-- (counters, frequency tables, running sums) work without diverging.
--
-- >>> acc <- cellIO (0 :: Int) (\s a -> let s' = s + a in pure (s', s'))
-- >>> runKleisli acc 5
-- 5
-- >>> runKleisli acc 3
-- 8
-- >>> runKleisli acc 2
-- 10
cellIO ::
  -- | initial state
  s ->
  -- | transfer: current state and input yield next state and output
  (s -> a -> IO (s, b)) ->
  IO (Kleisli IO a b)
cellIO s0 step = do
  ref <- newIORef s0
  pure $
    Kleisli $ \a -> do
      s <- readIORef ref
      (s', b) <- step s a
      writeIORef ref s'
      pure b

-- | 'Traced' plus 'Discrete' — required to fold free 'Loop'
-- (existential feedback channels need trivial 'Ob' on every type).
class (Traced t arr, Discrete arr) => FreeLoop t arr

instance (Traced t arr, Discrete arr) => FreeLoop t arr

-- | Free traced monoidal category.
instance Layer (Loop t) where
  type Law (Loop t) arr' = FreeLoop t arr'
  type Run (Loop t) arr = (Traced t arr, Discrete arr)
  type Bind (Loop t) arr = ()
  unit = Lift
  run :: forall arr a b. (Run (Loop t) arr, Ob arr a, Ob arr b) => Loop t arr a b -> arr a b
  run (Lift f) = f
  run (Knot @_ @s @_ @_ @_ f) =
    withOb @arr @(t s a) $
      withOb @arr @(t s b) $
        trace f
  bind :: forall arr arr' a b. (Law (Loop t) arr', Ob arr' a, Ob arr' b) => (arr :~> arr') -> Loop t arr a b -> arr' a b
  bind h (Lift f) = h f
  bind h (Knot @_ @s @_ @_ @_ f) =
    withOb @arr' @s $
      withOb @arr' @(t s a) $
        withOb @arr' @(t s b) $
          trace (h f)


