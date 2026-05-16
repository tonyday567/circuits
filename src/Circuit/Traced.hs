{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

-- | The trace: feedback in a monoidal category.
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
-- 'Circuit.Circuit''s @lower@ function dispatches on when it encounters
-- a 'Knot', making 'Circuit' the free traced monoidal category over any
-- base arrow with a tensor.
--
-- * Delimited continuations
--
-- The @Trace (Kleisli IO) Either@ instance uses GHC's delimited
-- continuation primops (@prompt#@ / @control0#@) to run IO loops in
-- constant stack space. Each iteration re-enters at the prompt boundary
-- rather than building up a call stack.
--
-- Correspondence with delimited continuation operators:
--
-- @
--   Trace (Kleisli IO) Either   ≅   delimited continuations
--   trace / reset               ≅   prompt
--   feedback Left               ≅   shift / control0
--   exit Right                  ≅   return from reset
-- @
module Circuit.Traced
  ( Trace (..),
    (↪),
    (↩),
  )
where


import Control.Arrow (Kleisli (..))
import GHC.Exts (PromptTag#, control0#, newPromptTag#, prompt#)
import GHC.IO (IO (..))

-- $setup
-- >>> import Control.Arrow (Kleisli (..))
-- >>> import Control.Category ((>>>))
-- >>> import Circuit.Traced

-- | A trace over a morphism @arr@ and tensor @t@.
--
-- @trace@ closes the feedback loop, eliminating the tensor channel.
-- @untrace@ opens the loop, lifting a plain morphism into the tensor.
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

-- * Cartesian tensor — lazy knot

-- | The cartesian trace ties a lazy knot: the feedback value @a@ and
-- output @c@ are produced simultaneously in a single recursive binding.
--
-- >>> take 5 (trace (\(fibs, ()) -> (0 : 1 : zipWith (+) fibs (drop 1 fibs), fibs)) () :: [Integer])
-- [0,1,1,2,3]

instance Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

-- * Either tensor — iteration

-- | The Either trace iterates: 'Left' feeds back (continue), 'Right'
-- terminates (exit). A compact, under-appreciated pattern for loops in Haskell.
--
-- >>> trace (\x -> case x of Right n | n < 3 -> Left (n + 1); _ -> Right ()) (0 :: Int)
-- ()
--
-- >>> let step n = if n < 3 then Left (n + 1) else Right n in trace (either step step) (0 :: Int)
-- 3
instance Trace (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

-- * Kleisli IO Either — delimited continuations

-- | GHC delimited-continuation primops.


data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag = IO (\s ->
  case newPromptTag# s of
    (# s', t #) -> (# s', PromptTag t #))

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
--
-- >>> runKleisli (trace (Kleisli $ \case Right () -> pure (Right (42 :: Int)))) ()
-- 42
instance Trace (Kleisli IO) Either where
  trace (Kleisli body) = Kleisli (\initial -> do
    tag <- newPromptTag
    let go x =
          prompt tag $
            body x >>= (\case
              Right c -> pure c
              Left a -> control0 tag (\k -> k (go (Left a))))
    go (Right initial))

  untrace (Kleisli f) = Kleisli (\case
    Left a -> pure (Left a)
    Right b -> Right <$> f b)
