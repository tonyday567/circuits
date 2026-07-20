{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hyperfunctions: final encoding of traced monoidal categories.
--
-- A hyperfunction (following Kidney & Wu) is a value that is completely
-- defined by its dual: to produce a result of type @b@ you must supply
-- a continuation of type @Hyper b a@.
--
-- 'Hyper' is the /final/ (coinductive) encoding of a traced monoidal
-- category. Its dual, 'Loop' (see "Circuit.Loop"), is the
-- corresponding /initial/ (inductive) encoding. The feedback channel
-- is not represented by an extra constructor; it is structural in the
-- type itself.
module Circuit.Hyper
  ( -- * Hyper
    Hyper (..),

    -- * Construction and elimination
    lift,
    observe,
    base,
    push,
    runHyper,

    -- * Encoding
    encode,
    encodeFree,
    encodeEither,
    runEither,
    flatten,
  )
where

import Circuit.Category (Category (..), Discrete (..), (.>))
import Circuit.Free qualified as F
import Circuit.Layer (Layer, bind, run, (:~>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Loop (Loop (..))
import Prelude hiding (id, (.))
import Data.Profunctor

-- $setup
-- .> import Prelude hiding (id, (.))
-- .> import Circuit.Category (Category (..), Discrete (..), (.>))
-- .> import Data.Profunctor
-- .> import Circuit.Channel (Traced (..))
-- .> import Circuit.Loop (Loop (..))
-- .> import Circuit.Layer (run)
-- .> let h = lift (+1) :: Hyper Int Int
-- .> let f1 = (*2) :: Int -> Int
-- .> let g1 = (+10) :: Int -> Int
-- .> let f2 = (+3) :: Int -> Int
-- .> let g2 = (*100) :: Int -> Int

-- | A hyperfunction from @a@ to @b@.
--
-- A 'Hyper' is completely determined by its dual. To get a @b@ you must
-- provide a continuation that can itself produce an @a@.
--
-- Two small examples:
--
-- .> observe (lift (+1)) 41
-- 42
--
-- .> runHyper (Hyper $ \k -> invoke k (Hyper $ \_ -> 0) + 1)
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
-- .> observe (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- | Extract a plain function from a hyperfunction.
--
-- Supplies the hyperfunction with a constant continuation
-- (@invoke h (Hyper (const a))@), asking: "what output do you produce
-- when the feedback channel feeds back the input @a@?"
--
-- .> observe (lift reverse) "hello"
-- "olleh"
observe :: Hyper a b -> (a -> b)
observe h a = invoke h (Hyper (const a))

-- | Ignores the input and returns a constant value.
--
-- .> observe (base 42) undefined
-- 42
base :: a -> Hyper b a
base a = Hyper (const a)

-- | Push a plain function onto a hyperfunction.
--
-- The function @f@ is applied to whatever value the hyperfunction
-- eventually produces. This threads @f@ through the continuation,
-- enabling feedback-aware composition.
--
-- .> observe (push (+1) (lift (*2))) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = Hyper (\k -> f (invoke k h))

-- | Close the self-referential loop.
--
-- @runHyper h@ feeds the hyperfunction back into itself, tying the knot.
-- This is the fundamental way to eliminate a 'Hyper'.
--
-- .> runHyper (Hyper $ \_ -> 42 :: Int)
-- 42
--
-- .> runHyper (Hyper $ \h -> invoke h (Hyper $ \_ -> 0) + 1) :: Int
-- 1
runHyper :: Hyper a a -> a
runHyper h = invoke h (Hyper runHyper)

-- * Properties

-- Faithful embedding: observation recovers the original arrow.
--
-- prop> \x -> observe (lift (+1)) (x :: Int) == x + 1

-- Functoriality: lift respects composition.
--
-- prop> \x -> observe (lift (*2) . lift (+1)) (x :: Int) == (x + 1) * 2

-- * Loop

-- | 'Loop' instance for 'Hyper' with the @(,)@ tensor.
--
-- Routes the self-reference through explicit 'Hyper' values:
--
--   1. @invoke body cont@ calls the body, which will eventually ask @cont@
--      for an @(a, b)@ — the feedback pair.
--   2. @cont@ captures @a@ from @body@'s output (@fst pair@) and feeds it
--      back as the first component of its return. This is the knot: @a@
--      cycles through @body → pair → cont → body@.
--   3. @invoke k (Hyper (const (snd pair)))@ converts the output @c@ to a
--      @b@ for @cont@'s return type — purely type plumbing.
--
-- .> import Circuit.Channel (Traced (..))
-- .> let body = lift (\(xs, ()) -> (0:xs, take 3 xs))
-- .> observe (trace body) ()
-- [0,0,0]
instance Channel (,) Hyper where
  assoc = lift $ \((a, b), c) -> (a, (b, c))
  assoc' = lift $ \(a, (b, c)) -> ((a, b), c)
  slide = lift $ \(a, (b, c)) -> (b, (a, c))

instance Strength (,) Hyper where
  strength h = lift (\p -> (fst p, observe h (snd p)))

instance Traced (,) Hyper where
  trace body = Hyper $ \k ->
    let pair = invoke body cont
        cont = Hyper $ \_ ->
          let a_val = invoke k (Hyper (const (snd pair)))
           in (fst pair, a_val)
     in snd pair

-- * Encoding Loop into Hyper

-- | Encode a Free into a Hyper.
--
-- The lift of the canonical fold 'run' into the final encoding.
--
-- Law: @'observe' . 'encodeFree' = 'run'@ — the two interpreters
-- from Free agree.
--
-- .> import Circuit.Free qualified as F
-- .> observe (encodeFree (F.Lift (+1))) 5
-- 6
encodeFree :: F.Free (->) a b -> Hyper a b
encodeFree (F.Lift f) = lift f
encodeFree (F.Compose f g) = encodeFree f . encodeFree g

-- | Encode a Loop into a Hyper.
--
-- This is the unique traced functor from the initial object ('Loop')
-- to the final object ('Hyper'), satisfying the commuting triangle
-- @'observe' . 'encode' = 'run'@.
--
-- 'Lift' constructors embed directly via 'lift'; 'Knot' constructors
-- become 'trace' over a hyperfunction.
--
-- .> import Circuit.Layer (run)
-- .> import Circuit.Loop (Loop (..))
-- .> observe (encode (Lift (+1) :: Loop (,) (->) Int Int)) 5
-- 6
encode :: Loop (,) (->) a b -> Hyper a b
encode (Lift f) = lift f
encode (Knot f) = trace (lift f)

-- | Encode an Either-loop as a self-referential Hyper.
--
-- Whereas 'encode' handles the @(,)@ tensor using Hyper's own Loop
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
-- 'encodeEither' embeds the Either state machine into Hyper, @runHyper@ ties
-- the self-referential knot, and @Right b@ injects the initial state.
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

-- | Flatten a Hyper to a Loop by observing it.
--
-- This is the forgetful map from the final encoding to the initial encoding.
-- All feedback structure is lost; only the observable behaviour remains.
--
-- .> let h = lift (+ 1)
-- .> run (flatten h) 5
-- 6
--
-- Flatten then encode is not identity — the feedback structure is gone:
--
-- .> let h = lift (+ 1)
-- .> observe (encode (flatten h)) 5
-- 6
flatten :: Hyper a b -> Loop (,) (->) a b
flatten h = Lift (observe h)

-- * Instances

instance Category Hyper where
  type Ob Hyper a = ()
  id = lift id
  f . g = Hyper $ \h -> invoke f (g . h)

-- | 'Profunctor' instance for 'Hyper'.
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
