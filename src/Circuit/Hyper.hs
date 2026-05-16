{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Hyperfunctions: final encoding of traced monoidal categories.
--
-- A 'Hyper' is a Church encoding of a 'Circuit'. The feedback channel is
-- structural in the type rather than explicit, so the sliding axiom
-- is inherent to composition rather than enforced by pattern matching.
--
-- Each named function is paired with its symbolic form immediately
-- below, so the haddock serves as a key between the two APIs.
module Circuit.Hyper
  ( -- * Hyper
    Hyper (..),
    type (↬),
    (⇸),
    (⊙),

    -- * Construction and elimination
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
    (⇦),
  )
where

import Control.Category
import Data.Profunctor
import Prelude hiding (id, (.))
import Circuit.Traced (Trace (..))
import Circuit.Circuit (Circuit (..), reify)

-- $setup
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category
-- >>> import Circuit.Traced (Trace (..))
-- >>> import Circuit.Circuit (Circuit (..), reify)

-- | Hyper a b is a hyperfunction from @a@ to @b@.
--
-- A hyperfunction consumes a continuation ('Hyper' @b@ @a@) and produces
-- a value of type @b@. The continuation argument appears in contravariant
-- position; the result appears in covariant position.
--
-- >>> let ask = Hyper (\k -> invoke k (Hyper (\_ -> 0)) + 1) in ask ⇸ (○) 42
-- 43
newtype Hyper a b = Hyper {invoke :: Hyper b a -> b}

-- | Type synonym for 'Hyper'.
type (↬) = Hyper

-- | Invoke a hyperfunction with a continuation.
--
-- >>> ((+1) ↑) ⇸ (○) 0
-- 1
infixr 0 ⇸

(⇸) :: Hyper a b -> Hyper b a -> b
(⇸) = invoke

-- | Sequential composition. Alias for '(.)'.
compose :: Hyper b c -> Hyper a b -> Hyper a c
compose = (.)

-- | Sequential composition. Operator form of 'compose'.
--
-- >>> (((+1) ↑) ⊙ ((*2) ↑)) ↓ 5
-- 11
infixr 9 ⊙

(⊙) :: Hyper b c -> Hyper a b -> Hyper a c
(⊙) = compose

-- * Construction and elimination

-- | Embed a plain function into a hyperfunction.
--
-- @lift f@ prepends @f@ to itself recursively, so the function can be
-- applied arbitrarily many times as the continuation chain unwinds.
--
-- >>> lower (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift f = push f (lift f)

-- | Operator form of 'lift'.
--
-- >>> ((+1) ↑) ↓ 5
-- 6
infixr 9 ↑

(↑) :: (a -> b) -> Hyper a b
(↑) = lift

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

-- | Ignores the input and returns a constant value.
--
-- >>> lower (base 42) undefined
-- 42
base :: a -> Hyper b a
base a = Hyper (const a)

-- | Prefix constant. Operator form of 'base'.
--
-- >>> (○) 42 ↓ undefined
-- 42
infixl 9 ○

(○) :: a -> Hyper b a
(○) = base

-- | Push a plain function onto a hyperfunction.
--
-- The function @f@ is applied to the result produced by invoking the
-- continuation on @h@. In this way @f@ is threaded through the
-- continuation, enabling feedback-aware composition.
--
-- >>> lower ((+1) ⊲ lift (*2)) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push f h = Hyper (\k -> f (invoke k h))

-- | Operator form of 'push'.
--
-- >>> ((*2) ⊲ ((+1) ↑)) ↓ 5
-- 10
infixr 8 ⊲

(⊲) :: (a -> b) -> Hyper a b -> Hyper a b
(⊲) = push

-- | Close the self-referential loop. Applies a hyperfunction to its
-- own dual: @run h = invoke h (Hyper run)@.
--
-- For a hyperfunction @h :: a ↬ a@, @run h@ resolves the fixed point
-- by feeding the hyperfunction's dual back into itself. The recursive
-- knot ties the covariant output to the contravariant input.
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
-- >>> import Circuit.Traced (Trace (..))
-- >>> let body = lift (\(xs, ()) -> (0:xs, take 3 xs)) in lower (trace body) ()
-- [0,0,0]
instance Trace Hyper (,) where
  trace body = Hyper $ \k ->
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
-- >>> import Circuit.Circuit (Circuit (..), reify)
-- >>> lower (encode (Lift (+1) :: Circuit (->) (,) Int Int)) 5
-- 6
encode :: Circuit (->) (,) a b -> Hyper a b
encode (Lift f) = lift f
encode (Compose f g) = encode f . encode g
encode (Knot f) = trace (lift f)

-- | Synonym for 'encode'.
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
    h = Hyper (\k s ->
      case f s of
        Right c -> c
        Left a -> invoke k h (Left a))

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
--
-- >>> let h = lift (+ 1) in reify (flatten h) 5
-- 6
--
-- Flatten then encode is not identity — the feedback structure is gone:
--
-- >>> let h = lift (+ 1) in lower (encode (flatten h)) 5
-- 6
flatten :: Hyper a b -> Circuit (->) (,) a b
flatten h = Lift (lower h)

-- | Synonym for 'flatten'. Collapses Hyper to Circuit (lossy).
infixr 9 ⇦

(⇦) :: Hyper a b -> Circuit (->) (,) a b
(⇦) = flatten

-- * Instances

instance Category Hyper where
  id = lift id
  f . g = Hyper $ \h -> invoke f (g . h)

-- | 'Profunctor' instance for 'Hyper'.
--
-- 'rmap' is not a composition of 'push'; it acts directly on the
-- hyperfunction's output. 'dimap' routes both input and output
-- through the continuation structure.
instance Profunctor Hyper where
  dimap f g h = Hyper $ g . invoke h . dimap g f
  lmap f h = Hyper $ invoke h . rmap f
  rmap f h = Hyper $ f . invoke h . lmap f

instance Functor (Hyper a) where
  fmap = rmap

-- | 'Applicative' instance for 'Hyper'.
--
-- Two 'lower' calls are natural here: one extracts the function
-- @a -> b@, the other extracts the argument @a@. There is no
-- single-step alternative that preserves the hyperfunction structure.
instance Applicative (Hyper a) where
  pure = base
  hf <*> ha = lift $ \a -> lower hf a (lower ha a)

-- | 'Monad' instance for 'Hyper'.
--
-- @m >>= k@ extracts a value from @m@, feeds it to @k@ to obtain
-- a new hyperfunction, then extracts the final result. The pattern
-- is: lower to observe, lift to re-encode.
instance Monad (Hyper a) where
  m >>= k = lift $ \a -> lower (k (lower m a)) a
