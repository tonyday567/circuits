{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hyperfunctions: an encoding of traced monoidal categories.
-- 🟣 This is a mess for being our primary statement on hyperfunctions.
-- 
-- A Hyper is a Church encoding of a Circuit. The feedback channel is
-- structural in the type rather than explicit, so the sliding axiom
-- is inherent to composition rather than enforced by pattern matching.
--
-- Each named function is paired with its symbolic form immediately
-- below, so the haddock serves as a key between the two APIs.
module Circuit.Hyper
  ( -- * Hyper 🟣 not sure if this works better, but a Hyper is not just a Type.
    -- 🟣 refactor body to get the same order as this list.
    Hyper (..),
    type (↬),
    (⇸),
    (⊙),

    -- * Operators 🟣 not too happy with operators either, but we need one word.
    lift,
    (↑),
    lower,
    (↓),
    base,
    (○),
    push,
    (⊲),
    run,
    (⥁),

    -- * Encoding
    encode,
    (⇨),
    encodeEither,
    runEither,
    flatten,
  )
where

-- 🟣 check if we have to do the id, (.) hiding still. I like this version - importing all of Control.CAtegory and hiding the minimum of Prelude, but are there other name clashes being introduced?
import Control.Category
import Data.Profunctor
import Prelude hiding (id, (.))
-- 🟣 single-block import list
import Circuit.Traced (Trace (..))
import Circuit.Circuit (Circuit (..))

-- 🟣 It could be nice to have an example Hyper that we put in setup and is used to illustrate how to practically think about a Hyper.
-- $setup
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category
-- >>> import Circuit.Traced (Trace (..))
-- >>> import Circuit.Circuit (Circuit (..))

-- | Hyper a b is a hyperfunction from a to b.
--
-- Hyper is a newtype wrapper around a function (invoke) that takes an opposite Hyper needed to produce a 'b'.
-- 🟣 canonical Hyper example showing a low level Hyper computation engaging with covariant and contravariant position.
newtype Hyper a b = Hyper {invoke :: Hyper b a -> b}

-- | Type synonym for 'Hyper'.
--
type (↬) = Hyper

-- | Invoke a hyperfunction with a continuation.
--
-- >>> ((+1) ↑) ⇸ (0 ○)
-- 1
infixr 0 ⇸

(⇸) :: Hyper a b -> Hyper b a -> b
(⇸) = invoke

-- * Construction and elimination

-- | Ignores the input and return a constant value.
-- 🟣 Haskell forces us to have at least a single commentary line and I really like having the functions and operators together visually. I vote for repetition. We could leave it blank as the other alternative. But putting random other token stuff to explain what is exactly the same thing is baddoc. As is explaining technicals eg this is a postfix. 
-- >>> lower (base 42) undefined
-- 42
base :: a -> Hyper b a
base a = Hyper (const a)

-- | Ignores the input and return a constant value.
--
-- >>> (42 ○) ↓ undefined
-- 42
infixl 9 ○
-- 🟣 why cant we do infixr here?

(○) :: a -> Hyper b a
(○) = base

-- | Push a plain function onto a hyperfunction.
--
-- The function @f@ is applied to the result produced by invoking the
-- continuation on @h@. In this way @f@ is threaded through the continuation, allowing feedback-aware 🟣 composition.
--
-- >>> lower ((+1) ⊲ lift (*2)) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = Hyper (\k -> f (invoke k h))

-- | Push a plain function onto a hyperfunction.
-- 
--
-- >>> ((*2) ⊲ ((+1) ↑)) ↓ 5
-- 10
infixr 8 ⊲

(⊲) :: (a -> b) -> Hyper a b -> Hyper a b
(⊲) = push

-- | Sequential composition. Alias for '(.)'.
compose :: Hyper b c -> Hyper a b -> Hyper a c
compose = (.)

-- | Sequential composition. Alias for '(.)'.
infixr 9 ⊙

(⊙) :: Hyper b c -> Hyper a b -> Hyper a c
(⊙) = compose

-- | Embed a plain function into a hyperfunction.
--
-- @lift f@ prepends @f@ to itself recursively, so the function can be
-- applied arbitrarily many times as the continuation chain unwinds.
--
-- >>> lower (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- | Embed a plain function into a hyperfunction.
--
-- >>> ((+1) ↑) ↓ 5
-- 6
infixr 9 ↑

(↑) :: (a -> b) -> Hyper a b
(↑) = lift

-- | Extract a plain function from a hyperfunction.
--
-- Supplies the hyperfunction with a constant continuation
-- (@invoke h (Hyper (const a))@), asking: \"what output do you produce
-- when the feedback channel feeds back the input @a@?\"
--
-- >>> lower (lift reverse) "hello"
-- "olleh"
lower :: Hyper a b -> (a -> b)
lower h a = invoke h (Hyper (const a))

-- | Postfix lower. Operator form of 'lower'.
--
-- Because 'lower' returns a plain function, the postfix form
-- chains naturally via function application:
--
-- >>> ((+1) ↑) ↓ 5
-- 6
--
-- >>> ((*2) ↑) ↓ 5 + 10
-- 20
infixl 9 ↓

(↓) :: Hyper a b -> (a -> b)
(↓) = lower

-- | Close the self-referential loop. Applies a hyperfunction to its
-- own dual: @run h = invoke h (Hyper run)@.
--
-- For a hyperfunction @h :: a ↬ a@, @run h@ resolves the fixed point
-- by feeding the hyperfunction's dual back into itself. The recursive
-- knot ties the forward and backward directions into a single value.
-- 🟣 is forwards and backwards a very close synonym for contrvariant and covariant? Sounds a bit magical.
--
-- >>> run (Hyper $ \_ -> 42 :: Int)
-- 42
--
-- >>> run (Hyper $ \h -> invoke h (Hyper $ \_ -> 0) + 1) :: Int
-- 1
run :: Hyper a a -> a
run h = invoke h (Hyper run)

-- | Close the loop. Operator form of 'run'.
(⥁) :: Hyper a a -> a
(⥁) = run

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
-- Law: @lower (trace (lift f)) x = trace \@(->) f x@
--
-- >>> import Circuit.Traced (Trace (..))
-- >>> let body = lift (\(xs, ()) -> (0:xs, take 3 xs)) in lower (trace body) ()
-- [0,0,0]
instance Trace Hyper (,) where
  -- 🟣 the h usage is not needed - check for that pattern
  -- 🟣 the code below will simplify I am guessing. 
  trace body = h
    where
      h = Hyper $ \k ->
        let pair = invoke body cont
            cont = Hyper $ \_ ->
              let a_val = invoke k (Hyper (const (snd pair)))
              in (fst pair, a_val)
        in snd pair
  untrace = lift . fmap . lower

-- * Encoding Circuit into Hyper

-- | Encode a Circuit into a Hyper. Symbol: @(⇨)@.
--
-- This is the unique traced functor from the initial object (Circuit)
-- to the final object (Hyper). The triangle @lower . encode = lower@ holds,
-- making this the map that respects the adjunction.
--
-- The @Knot@ case uses Hyper's own @Trace (,)@ instance — a coinductive
-- lazy knot that preserves the feedback structure inside Hyper.
-- For an Either-loop encoding, see 'encodeEither'.
--
-- >>> import Circuit.Circuit (Circuit (..))
-- >>> lower (encode (Lift (+1) :: Circuit (->) (,) Int Int)) 5
-- 6
encode :: Circuit (->) (,) a b -> Hyper a b
encode (Lift f) = lift f
encode (Compose f g) = encode f . encode g
encode (Knot f) = trace (lift f)

-- | Synonym for 'encode'. Encode a Circuit into a Hyper.
infixr 9 ⇨

(⇨) :: Circuit (->) (,) a b -> Hyper a b
(⇨) = encode

-- | Encode an Either-loop as a self-referential Hyper.
--
-- Whereas 'encode' handles the @(,)@ tensor using Hyper's own Trace
-- instance, this preserves the Either-loop state in the function domain.
-- @Left a@ feeds back; @Right c@ terminates with output.
--
-- >>> runEither (\case Right n | n < 3 -> Left (n+1); Right n -> Right n; Left n | n < 3 -> Left (n+1); Left n -> Right n) (0 :: Int)
-- 3
encodeEither :: (Either a b -> Either a c) -> Hyper (Either a b -> c) (Either a b -> c)
encodeEither f = h
  where
    h = Hyper \k s ->
      case f s of
        Right c -> c
        Left a -> invoke k h (Left a)

-- | Run an 'encodeEither'-encoded circuit from initial input @b@.
--
-- @runEither@ is to @encodeEither@ what @run . lift@ is to plain functions:
-- 'encodeEither' embeds the Either state machine into Hyper, @run@ ties the
-- self-referential knot, and @Right b@ injects the initial state.
--
-- >>> runEither (\case Right n | n < 3 -> Left (n+1); Right n -> Right n; Left n | n < 3 -> Left (n+1); Left n -> Right n) (0 :: Int)
-- 3
runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = run (encodeEither f) (Right b)

-- | Flatten a Hyper to a Circuit by observing it.
--
-- This is the forgetful map from the final encoding to the initial encoding.
-- All feedback structure is lost; only the observable behaviour remains.
flatten :: Hyper a b -> Circuit (->) (,) a b
flatten h = Lift (lower h)

-- * Instances
-- 🟣 what instances are missing?
instance Category Hyper where
  id = lift id
  f . g = Hyper $ \h -> invoke f (g . h)

-- 🟣 what is rmap a composition of? push f?
instance Profunctor Hyper where
  dimap f g h = Hyper $ g . invoke h . dimap g f
  lmap f h = Hyper $ invoke h . rmap f
  rmap f h = Hyper $ f . invoke h . lmap f

instance Functor (Hyper a) where
  fmap = rmap

-- 🟣 can we do better than two lowers?
instance Applicative (Hyper a) where
  pure = base
  hf <*> ha = lift $ \a -> lower hf a (lower ha a)

-- 🟣 need to explain
instance Monad (Hyper a) where
  m >>= k = lift $ \a -> lower (k (lower m a)) a
