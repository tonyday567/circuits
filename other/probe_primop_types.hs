{-# LANGUAGE MagicHash, UnboxedTuples, RankNTypes, BlockArguments, UnliftedNewtypes #-}
module ProbePrimopTypes where

import GHC.Exts
import GHC.IO (IO(..))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Unsafe.Coerce (unsafeCoerce)

-- Store the unlifted PromptTag# in an IORef via unsafeCoerce.
-- (In real code, use a more principled encoding.)
newtype TagRef a = TagRef (IORef ())

-- Create a fresh tag and store it
newTag' :: IO (TagRef a)
newTag' = IO \s0 -> case newPromptTag# s0 of
  (# s1, tag #) -> 
    -- Hack: use unsafeCoerce to store the unlifted tag in a lifted ref
    case unsafeIO (newIORef (unsafeCoerce tag)) of
      IO f -> case f s1 of
        (# s2, ref #) -> (# s2, TagRef ref #)

-- Unsafely run IO within primitive code
unsafeIO :: IO a -> (State# RealWorld -> (# State# RealWorld, a #))
unsafeIO (IO f) = f

-- prompt# wrapper
prompt' :: TagRef a -> IO a -> IO a
prompt' (TagRef ref) (IO m) = IO \s0 ->
  case unsafeIO (readIORef ref) s0 of
    (# s1, tagRaw #) ->
      let tag = unsafeCoerce tagRaw :: PromptTag# a
      in prompt# tag m s1

-- control0# wrapper
control0' :: TagRef a -> (((b -> IO a) -> IO a) -> IO a) -> IO b
control0' (TagRef ref) f = IO \s0 ->
  case unsafeIO (readIORef ref) s0 of
    (# s1, tagRaw #) ->
      let tag = unsafeCoerce tagRaw :: PromptTag# a
      in control0# tag f' s1
  where
    f' k = let kWrapped :: b -> IO a
               kWrapped x = IO (k (return x))
           in case f kWrapped of
             IO result -> result

-- Minimal test: prompt + control0, check it compiles.
testRoundtrip :: IO Int
testRoundtrip = do
  tag <- newTag'
  prompt' tag do
    x <- control0' tag \k -> do
      r <- k (return 42)
      return r
    return x
