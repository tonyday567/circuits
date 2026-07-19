{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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
-- @Trace t arr a b@ is the free traced monoidal category over a base
-- morphism @arr@ with tensor @t@. The two constructors encode:
--
--   * 'Arr' — a plain base arrow.
--   * 'Knot' — a feedback loop with a hidden feedback channel.
--
-- The laws of traced monoidal categories are performed by the 'Category'
-- and 'Traced' instances, so every value is already in normal form: at most
-- one 'Knot' at the top, over a base-arrow body. There is no separate
-- quotient step and no "Mendler case" in an interpreter.
--
-- For example, a @Trace (,) (->)@ is the initial traced monoidal cartesian
-- category over Haskell functions.
--
-- = Introduce / resolve
--
-- The vocabulary in this module follows the introduce/resolve pattern:
--
--   * 'Knot' introduces feedback; 'trace' resolves it. This is the gold
--     type-changing pair; composition fuses 'Knot's.
--
-- The polar channel ends ('Out', 'In') and their counit ('close')
-- live in "Circuit.Ends"; the unit ('open') lives in "Circuit.Ends.Unit".
--
-- == Three moves on monoidal structure
--
-- When navigating the tower of monoidal structure, three different moves
-- appear:
--
--   * __Planar fragment__ — never introduce 'swap'/'braid'. Fewer morphisms,
--     polar dual ends, planar 'Par'.
--   * __Forget braiding as structure__ (@U : SMC -> MC@) — same arrows, but
--     consumers are constrained to a 'Tensor'-only class so they cannot
--     invoke 'swap' even if the value still contains Swap constructors.
--   * __Run / bind__ — leave free monoidal syntax and interpret into a target
--     category. 'melt' interprets 'Net' rows into 'Trace'; the
--     @Action (,) (Trace t arr)@ instance is what absorbs parallel 'Knot's.
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
  ( -- * Trace
    Trace (..),

    -- * Traced class
    Traced (..),

    -- * Discrete helpers (Ob discharge for free constructions)
    untraceD,
    traceD,
    compD,

    -- * Stateful IO stages
    cellIO,

    -- * Layer witness
    FreeTraced,
  )
where

import Circuit.Classes (Category (..), Discrete (..), (>>>))
import Circuit.Layer (Layer (..), run)
import Circuit.Monoidal.Category (Monoidal (..))
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
-- >>> import Circuit.Monoidal (Tensor (..))
-- >>> import Control.Arrow (Kleisli (..), second)
-- >>> import Circuit.Classes ((.), (>>>))
-- >>> import Data.Either (fromRight)
-- >>> import Data.Profunctor (dimap)
-- >>> import Data.Void (Void)
-- >>> import Prelude hiding (id, (.))

-- | A trace over a morphism @arr@ and tensor @t@.
--
-- @trace@ closes the feedback loop, eliminating the tensor channel.
-- @untrace@ opens the loop, lifting a plain morphism into the tensor.
--
-- Object constraints on the feedback channel (@a@) let constrained
-- categories (e.g. matrices needing 'Finite' / 'KnownNat') instance
-- this class lawfully.
class (Monoidal t arr) => Traced t arr where
  trace ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t a c)
    ) =>
    arr (t a b) (t a c) ->
    arr b c
  untrace ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t a c)
    ) =>
    arr b c ->
    arr (t a b) (t a c)

-- | The free traced monoidal category over base morphism @arr@ and tensor @t@,
-- in existential normal form.
--
-- Two constructors:
--
--   * 'Arr' — a plain base arrow.
--   * 'Knot' — a feedback loop with hidden channel @s@.
data Trace (t :: Type -> Type -> Type) arr a b where
  -- | A plain base arrow.
  --
  -- >>> run (Arr (+1) :: Trace (,) (->) Int Int) 5
  -- 6
  Arr :: arr a b -> Trace t arr a b
  -- | Tie a feedback loop. The tensor @t@ carries the hidden channel type @s@.
  --
  -- The argument is the base arrow itself, /not/ an 'Arr'-wrapped stage:
  --
  -- >>> run (Knot (\(acc, x) -> (x, acc)) :: Trace (,) (->) Int Int) 42
  -- 42
  --
  -- For the @(,)@ tensor the channel value is self-referential, so the body
  -- must use an irrefutable pattern or otherwise avoid forcing the channel
  -- before producing its constructor:
  --
  -- >>> run (Knot (\ ~(ns, ()) -> (0 : ns, take 3 ns)) :: Trace (,) (->) () [Int]) ()
  -- [0,0,0]
  --
  -- Free composition of 'Knot's requires quantified 'Ob' on the base
  -- (@forall x. Ob arr x@), discharged by unconstrained categories.
  Knot :: arr (t s a) (t s b) -> Trace t arr a b

-- | Fusing two '(,)'-'Knot's into one loop. Top-level strict tuple
-- patterns are absorbed because 'untrace' re-emits the channel as a
-- manifest pair of projections.
--
-- >>> let k1 = Knot (\(ns, x) -> (1 : ns, take 3 ns ++ [x])) :: Trace (,) (->) Int [Int]
-- >>> let k2 = Knot (\(ns, xs) -> (2 : ns, sum xs))
-- >>> run (k2 . k1) (0 :: Int)
-- 3
compD :: forall arr a b c. (Discrete arr) => arr b c -> arr a b -> arr a c
compD f g = withOb @arr @a $ withOb @arr @b $ withOb @arr @c $ f . g

idD :: forall arr a. (Discrete arr) => arr a a
idD = withOb @arr @a id

untraceD ::
  forall t arr a b c.
  (Traced t arr, Discrete arr) =>
  arr b c ->
  arr (t a b) (t a c)
untraceD f =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t a c) $
            untrace f

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

assocD ::
  forall t arr a b c.
  (Monoidal t arr, Discrete arr) =>
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

assocD' ::
  forall t arr a b c.
  (Monoidal t arr, Discrete arr) =>
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

braidD ::
  forall t arr a b c.
  (Monoidal t arr, Discrete arr) =>
  arr (t a (t b c)) (t b (t a c))
braidD =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t b c) $
          withOb @arr @(t a c) $
            withOb @arr @(t a (t b c)) $
              withOb @arr @(t b (t a c)) $
                braid

instance (Category arr, Traced t arr, Discrete arr) => Category (Trace t arr) where
  type Ob (Trace t arr) a = Ob arr a
  id = Arr idD
  Arr f . Arr g = Arr (compD f g)
  Knot f . Arr g = Knot (compD f (untraceD g))
  Arr f . Knot g = Knot (compD (untraceD f) g)
  Knot f . Knot g =
    Knot $
      compD assocD' $
        compD braidD $
          compD (untraceD f) $
            compD braidD $
              compD (untraceD g) assocD

-- | Free Trace over functions is discrete (Ob reduces to @()@).
instance (Traced t (->)) => Discrete (Trace t (->)) where
  withOb x = x

instance (Profunctor arr, Bifunctor t) => Profunctor (Trace t arr) where
  dimap f g (Arr h) = Arr (dimap f g h)
  dimap f g (Knot h) = Knot (dimap (second f) (second g) h)
  lmap f (Arr h) = Arr (lmap f h)
  lmap f (Knot h) = Knot (lmap (second f) h)
  rmap g (Arr h) = Arr (rmap g h)
  rmap g (Knot h) = Knot (rmap (second g) h)

instance (Bifunctor t) => Functor (Trace t (->) a) where
  fmap f (Arr g) = Arr (f . g)
  fmap f (Knot g) = Knot (second f . g)

-- | Lift the 'Monoidal' structure of the base arrow into 'Trace t arr'.
instance (Category arr, Traced t arr, Discrete arr) => Monoidal t (Trace t arr) where
  assoc = Arr assocD
  assoc' = Arr assocD'
  braid = Arr braidD

-- | Lift the 'Traced' class through 'Trace t'.
--
-- 'trace' hides a wire as a 'Knot'; 'untrace' exposes it.
instance (Category arr, Traced t arr, Discrete arr) => Traced t (Trace t arr) where
  trace (Arr f) = Knot f
  trace (Knot f) = Knot (compD assocD' (compD f assocD))
  untrace (Arr f) = Arr (untraceD f)
  untrace (Knot f) = Knot (compD braidD (compD (untraceD f) braidD))

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
-- prop> \n -> trace ((unitl' . (+ n) . unitl) :: ((), Int) -> ((), Int)) (0 :: Int) == (n :: Int)
--
-- Yanking: tracing a swap is the identity.
--
-- >>> let swap (x, y) = (y, x)
-- >>> trace swap 42
-- 42
--
-- prop> \x -> trace ((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int))) (x :: Int) == x
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f (x, a) = (x, a)
-- >>> trace (second (+1) . f . second (*2)) 5
-- 11
--
-- prop> \x -> trace (second ((+1) :: Int -> Int) . ((\(a, b) -> (a, b)) :: ((Int, Int) -> (Int, Int))) . second ((*2) :: Int -> Int)) (x :: Int) == x * 2 + 1
--
-- Sliding: a morphism on the channel slides from one side to the other.
--
-- >>> let swap (x, y) = (y, x)
-- >>> trace (second (+1) . swap) 5
-- 6
--
-- >>> trace (swap . second (+1)) 5
-- 6
--
-- prop> \x -> trace (second ((+1) :: Int -> Int) . ((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int)))) (x :: Int) == trace (((\(a, b) -> (b, a)) :: ((Int, Int) -> (Int, Int))) . second ((+1) :: Int -> Int)) x
--
-- Strength: an independent payload wire is invisible to the trace.
--
-- >>> let f (x, c) = (x, c + 1)
-- >>> let g (x, (a, c)) = (x', (a * 2, d)) where (x', d) = f (x, c)
-- >>> trace g (3, 5)
-- (6,6)
--
-- prop> \a c -> trace ((\(x, (p, q)) -> (x, (p + a, q + 1))) :: ((Int, (Int, Int)) -> (Int, (Int, Int)))) (0 :: Int, c :: Int) == (a :: Int, c + 1)
instance Traced (,) (->) where
  trace f b = let ~(a, c) = f (a, b) in c

  -- Projection-based untrace emits a manifest pair, so fused knot bodies
  -- with strict top-level patterns match the constructor without forcing
  -- the recursive channel.
  untrace f p = second f p

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
-- prop> \n -> trace ((unitl' . (+ n) . unitl) :: Either Void Int -> Either Void Int) (0 :: Int) == (n :: Int)
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
-- prop> \x -> trace ((\e -> case e of Left a -> Right a; Right a -> Left a) :: (Either Int Int -> Either Int Int)) (x :: Int) == x
--
-- Tightening: payload morphisms pass freely through the trace.
--
-- >>> let f = fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int)
-- >>> trace (f :: Either Void Int -> Either Void Int) 5
-- 11
--
-- prop> \x -> trace (fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int) :: Either Void Int -> Either Void Int) (x :: Int) == x * 2 + 1
instance Traced Either (->) where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

-- * Kleisli m — monoidal structure

-- | Cartesian monoidal structure for 'Kleisli' @m@ with @(,)@.
instance (Monad m) => Monoidal (,) (Kleisli m) where
  assoc = Kleisli $ \ ~(~(a, b), c) -> pure (a, (b, c))
  assoc' = Kleisli $ \ ~(a, ~(b, c)) -> pure ((a, b), c)
  braid = Kleisli $ \ ~(a, ~(b, c)) -> pure (b, (a, c))

-- | Cocartesian monoidal structure for 'Kleisli' @m@ with 'Either'.
instance (Monad m) => Monoidal Either (Kleisli m) where
  assoc = Kleisli $ \case
    Left (Left a) -> pure (Left a)
    Left (Right b) -> pure (Right (Left b))
    Right c -> pure (Right (Right c))
  assoc' = Kleisli $ \case
    Left a -> pure (Left (Left a))
    Right (Left b) -> pure (Left (Right b))
    Right (Right c) -> pure (Right c)
  braid = Kleisli $ \case
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
instance (MonadFix m) => Traced (,) (Kleisli m) where
  trace (Kleisli f) =
    Kleisli
      ( \b -> do
          (_, c) <- mfix $ \ ~(s, _) -> f (s, b)
          pure c
      )

  untrace (Kleisli f) =
    Kleisli
      ( \p -> do
          c <- f (snd p)
          pure (fst p, c)
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
instance {-# OVERLAPPABLE #-} (Monad m) => Traced Either (Kleisli m) where
  trace (Kleisli f) =
    Kleisli $ \b -> go (Right b)
    where
      go x =
        f x >>= \case
          Right c -> pure c
          Left a -> go (Left a)

  untrace (Kleisli f) =
    Kleisli $ \case
      Left a -> pure (Left a)
      Right b -> Right <$> f b

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

  untrace (Kleisli f) =
    Kleisli
      ( \case
          Left a -> pure (Left a)
          Right b -> Right <$> f b
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

-- | 'Traced' plus 'Discrete' — required to fold free 'Trace'
-- (existential feedback channels need trivial 'Ob' on every type).
class (Traced t arr, Discrete arr) => FreeTraced t arr

instance (Traced t arr, Discrete arr) => FreeTraced t arr

-- | Free traced monoidal category.
instance Layer (Trace t) where
  type Law (Trace t) arr' = FreeTraced t arr'
  unit = Arr
  bind h (Arr f) = h f
  bind h (Knot f) = traceD (h f)


