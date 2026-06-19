{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hyperfunctions: final encoding of traced monoidal categories.
--
-- A hyperfunction (following Kidney & Wu) is a value that is completely
-- defined by its dual: to produce a result of type @b@ you must supply
-- a continuation of type @Hyper b a@.
--
-- 'Hyper' is the /final/ (coinductive) encoding of a traced monoidal
-- category. Its dual, 'Trace' (see "Circuit.Trace"), is the
-- corresponding /initial/ (inductive) encoding. The feedback channel
-- is not represented by an extra constructor; it is structural in the
-- type itself.
module Circuit.Hyper
  ( -- * Hyper
    Hyper (..),

    -- * Construction and elimination
    lift,
    lower,
    base,
    push,
    run,

    -- * Encoding
    encode,
    encodeFree,
    encodeEither,
    runEither,
    flatten,
  )
where

import Circuit.Trace (Trace (..), freeze, realise)
import Circuit.Free qualified as F
import Circuit.Traced
import Prelude hiding (id, (.))

#ifdef __GLASGOW_HASKELL__
import Control.Category
import Data.Profunctor
#else
import Circuit.Classes
#endif

-- $setup
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category
-- >>> import Data.Profunctor
-- >>> import Circuit.Traced (Traced (..))
-- >>> import Circuit.Trace (Trace (..), realise)
-- >>> let h = lift (+1) :: Hyper Int Int
-- >>> let f1 = (*2) :: Int -> Int
-- >>> let g1 = (+10) :: Int -> Int
-- >>> let f2 = (+3) :: Int -> Int
-- >>> let g2 = (*100) :: Int -> Int

-- | A hyperfunction from @a@ to @b@.
--
-- A 'Hyper' is completely determined by its dual. To get a @b@ you must
-- provide a continuation that can itself produce an @a@.
--
-- Two small examples:
--
-- >>> lower (lift (+1)) 41
-- 42
--
-- >>> run (Hyper $ \k -> invoke k (Hyper $ \_ -> 0) + 1)
-- 1
newtype Hyper a b = Hyper
  { -- | Feed a continuation of type @Hyper b a@ into the hyperfunction.
    invoke :: Hyper b a -> b
  }

-- * Construction and elimination

-- | Embed a plain function into a hyperfunction.
--
-- This is where the coinductive character of 'Hyper' lives:
-- @lift f@ creates a hyperfunction by recursively pushing @f@ onto
-- every future continuation that will ever be supplied.
--
-- >>> lower (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- | Extract a plain function from a hyperfunction.
--
-- Supplies the hyperfunction with a constant continuation
-- (@invoke h (Hyper (const a))@), asking: "what output do you produce
-- when the feedback channel feeds back the input @a@?"
--
-- >>> lower (lift reverse) "hello"
-- "olleh"
lower :: Hyper a b -> (a -> b)
lower h a = invoke h (Hyper (const a))

-- | Ignores the input and returns a constant value.
--
-- >>> lower (base 42) undefined
-- 42
base :: a -> Hyper b a
base a = Hyper (const a)

-- | Push a plain function onto a hyperfunction.
--
-- The function @f@ is applied to whatever value the hyperfunction
-- eventually produces. This threads @f@ through the continuation,
-- enabling feedback-aware composition.
--
-- >>> lower (push (+1) (lift (*2))) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = Hyper (\k -> f (invoke k h))

-- | Close the self-referential loop.
--
-- @run h@ feeds the hyperfunction back into itself, tying the knot.
-- This is the fundamental way to eliminate a 'Hyper'.
--
-- >>> run (Hyper $ \_ -> 42 :: Int)
-- 42
--
-- >>> run (Hyper $ \h -> invoke h (Hyper $ \_ -> 0) + 1) :: Int
-- 1
run :: Hyper a a -> a
run h = invoke h (Hyper run)

-- * Properties

-- Faithful embedding: observation recovers the original arrow.
--
-- prop> \x -> lower (lift (+1)) (x :: Int) == x + 1

-- Functoriality: lift respects composition.
--
-- prop> \x -> lower (lift (*2) . lift (+1)) (x :: Int) == (x + 1) * 2

-- * Trace

-- | 'Trace' instance for 'Hyper' with the @(,)@ tensor.
--
-- Transcribes the lazy-knot trace from @(->)@ into Hyper's continuation
-- language. Where @Trace (->) (,)@ can write @let (a, c) = f (a, b) in c@
-- directly, Hyper must route the self-reference through explicit 'Hyper'
-- values:
--
--   1. @invoke body cont@ calls the body, which will eventually ask @cont@
--      for an @(a, b)@ — the feedback pair.
--   2. @cont@ captures @a@ from @body@'s output (@fst pair@) and feeds it
--      back as the first component of its return. This is the knot: @a@
--      cycles through @body → pair → cont → body@.
--   3. @invoke k (Hyper (const (snd pair)))@ converts the output @c@ to a
--      @b@ for @cont@'s return type — purely type plumbing.
--
-- Law: @lower (trace (lift f)) x = trace \@ (->) f x@
--
-- >>> import Circuit.Traced (Traced (..))
-- >>> let body = lift (\(xs, ()) -> (0:xs, take 3 xs))
-- >>> lower (trace body) ()
-- [0,0,0]
instance Traced Hyper (,) where
  trace body = Hyper $ \k ->
    let pair = invoke body cont
        cont = Hyper $ \_ ->
          let a_val = invoke k (Hyper (const (snd pair)))
           in (fst pair, a_val)
     in snd pair
  untrace = lift . fmap . lower

-- * Encoding Trace into Hyper

-- | Encode a 'Free' into a 'Hyper'.
--
-- The lift of the canonical fold 'runFree' into the final encoding.
-- Only needs 'Lift' and 'Compose' — trace structure is handled by 'freeze'.
--
-- Law: @'lower' . 'encodeFree' = 'F.runFree'@ — the two interpreters
-- from 'Free' agree.
--
-- >>> import Circuit.Free qualified as F
-- >>> import Circuit.Trace (freeze)
-- >>> lower (encodeFree (F.Lift (+1))) 5
-- 6
encodeFree :: F.Free (->) a b -> Hyper a b
encodeFree (F.Lift f) = lift f
encodeFree (F.Compose f g) = encodeFree f . encodeFree g

-- | Encode a Trace into a Hyper. Symbol: @(⇨)@.
--
-- This is the unique traced functor from the initial object (Trace)
-- to the final object (Hyper), satisfying the commuting triangle
-- @'lower' . 'encode' = 'realise'@.
--
-- Factors through 'Free': @'encode' = 'encodeFree' . 'freeze'@.
-- 'freeze' dissolves knot constructors into 'Lift' via the base arrow's 'trace';
-- 'encodeFree' lifts the two constructors into Hyper.
--
-- >>> import Circuit.Trace (Trace (..), realise)
-- >>> lower (encode (Lift (+1) :: Trace (,) (->) Int Int)) 5
-- 6
encode :: Trace (,) (->) a b -> Hyper a b
encode = encodeFree . freeze

-- | Encode an Either-loop as a self-referential Hyper.
--
-- Whereas 'encode' handles the @(,)@ tensor using Hyper's own Trace
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
encodeEither :: (Either a b -> Either a c) -> Hyper (Either a b -> c) (Either a b -> c)
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
-- @runEither@ is to @encodeEither@ what @run . lift@ is to plain functions:
-- 'encodeEither' embeds the Either state machine into Hyper, @run@ ties the
-- self-referential knot, and @Right b@ injects the initial state.
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
runEither f b = run (encodeEither f) (Right b)

-- | Flatten a Hyper to a Trace by observing it.
--
-- This is the forgetful map from the final encoding to the initial encoding.
-- All feedback structure is lost; only the observable behaviour remains.
--
-- >>> let h = lift (+ 1)
-- >>> realise (flatten h) 5
-- 6
--
-- Flatten then encode is not identity — the feedback structure is gone:
--
-- >>> let h = lift (+ 1)
-- >>> lower (encode (flatten h)) 5
-- 6
flatten :: Hyper a b -> Trace (,) (->) a b
flatten h = Lift (lower h)

-- * Instances

instance Category Hyper where
  id = lift id
  f . g = Hyper $ \h -> invoke f (g . h)

-- | 'Profunctor' instance for 'Hyper'.
--
-- 'rmap' is not a composition of 'push'; it acts directly on the
-- hyperfunction's output. 'dimap' routes both input and output
-- through the continuation structure.
--
-- Profunctor identity: dimap id id = id
--
-- prop> \x -> lower (dimap id id h) (x :: Int) == x + 1
--
-- Profunctor composition: dimap f g . dimap f' g' = dimap (f' . f) (g . g')
--
-- prop> \x -> lower (dimap f1 g1 (dimap f2 g2 h)) (x :: Int) == lower (dimap (f2 . f1) (g1 . g2) h) x
--
-- lmap f = dimap f id
--
-- prop> \x -> lower (lmap ((*2) :: Int -> Int) h) (x :: Int) == lower (dimap ((*2) :: Int -> Int) id h) x
--
-- rmap g = dimap id g
--
-- prop> \x -> lower (rmap ((*2) :: Int -> Int) h) (x :: Int) == lower (dimap id ((*2) :: Int -> Int) h) x
instance Profunctor Hyper where
  dimap f g h = Hyper $ g . invoke h . dimap g f
  lmap f h = Hyper $ invoke h . rmap f
  rmap f h = Hyper $ f . invoke h . lmap f

instance Functor (Hyper a) where
  fmap = rmap
