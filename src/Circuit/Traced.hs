{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}
-- 🟣 check file pragmas versus GHC2025

-- | The trace: feedback in a monoidal category.
--
-- 🔴 "close a feedback loop" is a problematic meme. feedback is a continuous manifold concept in a step-by-step world of our yoneda-coyoneda two-step.
-- from our perspective, some ordinary functions do not slide. cannot slide.
-- They produce knots at boundaries where types change. Specifically where a portion of a type is eliminated via a forall. or representationally, so that fixpoint isomorphism cannot then occur. How do we summarise this?
--
-- 
-- 'Trace' generalises the ability to close a feedback loop. For each
-- tensor @t@, a 'Trace' instance specifies what \"feedback\" means:
--
--   * @(,)@ — lazy knot: output and feedback are produced simultaneously.
--     @trace f b = let (a, c) = f (a, b) in c@.
--
--   * @Either@ — iteration: @Left a@ feeds back (continue), @Right c@
--     terminates (exit). The loop runs until a 'Right' is produced.
--
-- Together these instances supply the 'Trace' constraints that
-- "Circuit.Circuit"'s @lower@ function dispatches on when it encounters a Knot, making 'Circuit' the free traced monoidal category over any base arrow with a tensor.
--
-- 🟣 = is baddoc
-- 🟣 This needs to be on the delcon instance
-- = Delimited continuations
--
-- The @Trace (Kleisli IO) Either@ instance uses GHC's delimited
-- continuation primops (@prompt#@ / @control0#@) to run IO loops in
-- constant stack space. Each iteration re-enters at the prompt boundary
-- rather than building up a call stack. See @examples/theory-delim.md@ 🟣 delink examples/ and haddocks.
-- for the correspondence:
--
-- @
--   Trace (Kleisli IO) Either   ≅   delimited continuations
--   Loop                        ≅   reset / prompt
--   feedback Left               ≅   shift / control0
--   exit Right                  ≅   return from reset
-- @
--
-- And @examples/resource-io.md@ for practical resource-handling loops
-- built on the same mechanism.
module Circuit.Traced
  ( Trace (..),
    (↪),
    (↩),
  )
where

-- 🟣 time to add explicit export lists back in for external imports.
import Control.Arrow
import GHC.Exts
import GHC.IO

-- $setup
-- 🟣 ??? an interesting pragma!
-- >>> :set -XNoRequiredTypeArguments
-- 🟣 is there an alternative source for Kleisli?
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Control.Category ((>>>))
-- >>> import Circuit.Traced

-- | A 🟣 Why past tense traced 🟣 arrow or morphism? over tensor @t@.
--
-- 🟣 repeating types in haddocks feels redundant.
-- @trace@ encodes the closing or annihilation of the tensor.
-- @untrace@ encodes the opening of the underlying morphism.
class Trace arr t where
  trace :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)

-- | Alias for 'trace'.
infixr 9 ↪

-- | Close a type tensored over a morphism.
(↪) :: (Trace arr t) => arr (t a b) (t a c) -> arr b c
(↪) = trace

-- | Symbolic alias for 'untrace'.
infixr 9 ↩

(↩) :: (Trace arr t) => arr b c -> arr (t a b) (t a c)
(↩) = untrace

-- 🟣 three words togther taht are all very loaded with meaning before we get to use them ourselves.
-- * (,) tensor — lazy knot

-- | The cartesian trace ties a lazy knot: the feedback value @a@ and
-- output @c@ are produced simultaneously. ie 🔴 magically, in other words.
--
-- >>> take 5 $ trace (\(fibs, ()) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs)) ()
-- [0,1,1,2,3]
-- 🟣 What is this overlapping with?
instance {-# OVERLAPPABLE #-} Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

-- * Either tensor — iteration

-- | The Either trace iterates: 'Left' feeds back (continue), 'Right'
-- terminates (exit).
-- 🟣 This is the least appreciated and most import unknown pattern in Haskell.
--
-- >>> trace (\x -> case x of Right n | n < 3 -> Left (n + 1); _ -> Right ()) (0 :: Int)
-- ()
--
-- >>> let step n = if n < 3 then Left (n + 1) else Right n in trace (either step step) (0 :: Int)
-- 3
instance {-# OVERLAPPING #-} Trace (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

-- 🟣 instance Trace (->) Maybe.
-- I think this looks a lot like loopIO 

-- * Kleisli IO Either — delimited continuations

-- | GHC delimited-continuation primops.

-- 🟣 review patterns here for good practice
data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag = IO \s ->
  case newPromptTag# s of
    (# s', t #) -> (# s', PromptTag t #)

prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

-- | Captures the continuation up to the nearest prompt with the matching tag.
control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

-- | Trace for 'Kleisli' 'IO' with 'Either' tensor.
--
-- Each iteration re-establishes the prompt boundary. When 'control0'
-- fires on @Left a@, it captures the continuation, wraps it around
-- the next loop step, and jumps back to the prompt — constant stack.
-- 🟣 This feels too messy for a doctest, and multi-lines are always garish. Are you sure there's not a one-liner that is a better illustration?
--
-- >>> :{
-- let stepK :: Either Int () -> IO (Either Int Int)
--     stepK (Right ()) = pure (Left 0)
--     stepK (Left n) | n < 3 = pure (Left (n + 1))
--     stepK (Left n) = pure (Right n)
-- in runKleisli (trace (Kleisli stepK)) ()
-- :}
-- 3
instance {-# OVERLAPPING #-} Trace (Kleisli IO) Either where
  trace (Kleisli body) = Kleisli \initial -> do
    tag <- newPromptTag
    let go x =
          prompt tag $
            -- 🟣 hard to read x >>= \case
            body x >>= \case
              Right c -> pure c
              Left a -> control0 tag \k -> k (go (Left a))
    go (Right initial)

  -- 🟣 How does Kleisli \case type check?
  untrace (Kleisli f) = Kleisli \case
    Left a -> pure (Left a)
    Right b -> Right <$> f b
