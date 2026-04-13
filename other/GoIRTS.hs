{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}

-- | GoI with real RTS delimited continuations (GHC 9.6+)
--
-- Confirmed working wrapper (GHC 9.14.1):
--
--   control0 (PromptTag t) f = IO (control0# t arg)
--     where arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s
--
-- control0# semantics: −F− (Dybvig et al.)
--   prompt P (... control0 P \k -> body ...)
--   ≡ body [\x -> prompt P (k x)]
--
-- The prompt is REMOVED by control0, and k reinstalls it when called.
-- This means calling k returns to body's call site — body continues.
-- callCC must therefore use a second control0 to abort body after escape.

module GoIRTS
  ( PromptTag
  , newPromptTag
  , prompt
  , control0
  , callCC
  , throw
  , abort
  , Step (..)
  , principalCutIO
  , exampleCallCC
  , exampleMultiShot
  , exampleThrow
  , examplePrincipalCut
  ) where

import GHC.Exts (PromptTag#, newPromptTag#, prompt#, control0#, RealWorld, State#)
import GHC.IO   (IO (..))

-- ---------------------------------------------------------------------------
-- § 1. Tag
-- ---------------------------------------------------------------------------

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag = IO \s ->
  case newPromptTag# s of
    (# s', t #) -> (# s', PromptTag t #)

-- ---------------------------------------------------------------------------
-- § 2. Core primop wrappers
-- ---------------------------------------------------------------------------

prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

-- | Confirmed wrapper. control0# hands arg the captured continuation
--   f# :: IO# b -> IO# a. We wrap it as IO b -> IO a for the user.
--   Both f# and s must be explicit arguments (eta-expansion required).
control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

-- ---------------------------------------------------------------------------
-- § 3. Derived operations
-- ---------------------------------------------------------------------------

-- | throw: abort to the prompt boundary with a pure value.
--   Discards the captured continuation entirely.
throw :: forall a r. PromptTag r -> r -> IO a
throw tag r = control0 tag \_ -> return r

-- | abort: abort to the prompt boundary with an IO action.
abort :: forall a r. PromptTag r -> IO r -> IO a
abort tag m = control0 tag \_ -> m

-- | callCC: capture the current continuation as an escape function.
--
--   −F− semantics means calling k returns to body's call site.
--   To make escape truly abort body, we need two control0 calls:
--
--     control0 tag \k ->
--       prompt tag (body \a -> control0 tag \_ -> k (return a))
--
--   Normal path (escape not called):
--     body returns v → prompt tag sees v → result is v ✓
--
--   Escape path (escape a called):
--     inner control0 fires → discards body's remaining continuation
--     → calls k (return a) → k reinstalls prompt (−F−) → resumes
--     → continuation runs with x=a → delivers result to prompt → ✓
callCC :: forall a r. PromptTag r -> ((a -> IO r) -> IO r) -> IO a
callCC tag body = control0 tag \k ->
  prompt tag (body \a -> control0 tag \_ -> k (return a))

-- ---------------------------------------------------------------------------
-- § 4. Principal cut
-- ---------------------------------------------------------------------------

data Step a b = Yield a | Done b

-- | Two machines interact through a shared prompt tag.
--   The RTS stack carries machine state between yields — no explicit loop.
principalCutIO
  :: forall a b r.
     ((a -> IO (Step b r)) -> IO (Step a r))
  -> ((b -> IO (Step a r)) -> IO (Step b r))
  -> IO r
principalCutIO f g = do
  tag <- newPromptTag
  runF tag
  where
    -- control0 uses −F− semantics: it removes the prompt when it fires.
    -- So after each yield, the prompt is gone. We reinstall it before
    -- each kf call so f can yield again on the next turn.
    runF :: PromptTag r -> IO r
    runF tag = prompt tag $ do
      step <- f \a -> control0 tag \kf -> runG tag kf a
      case step of
        Done r  -> return r
        Yield _ -> error "principalCutIO: f yielded past prompt boundary"

    runG :: PromptTag r -> (IO (Step b r) -> IO r) -> a -> IO r
    runG tag kf a = do
      step <- g \b -> do
        r <- prompt tag $ kf (return (Yield b))
        return (Done r :: Step a r)
      case step of
        Done r  -> return r
        Yield _ -> error "principalCutIO: g returned Yield without using receive" 
-- ---------------------------------------------------------------------------
-- § 5. Examples
-- ---------------------------------------------------------------------------

-- | callCC escape. Expected:
--     [1] before escape
--     [2] x = 42
--     result = 43
exampleCallCC :: IO ()
exampleCallCC = do
  tag <- newPromptTag
  result <- prompt tag do
    x <- callCC tag \escape -> do
      putStrLn "  [1] before escape"
      escape (42 :: Int)
      putStrLn "  [!] never printed"
      return 0
    putStrLn $ "  [2] x = " ++ show x
    return (x + 1 :: Int)
  putStrLn $ "  result = " ++ show result

-- | Multi-shot: k called twice. Expected: [10,20]  (confirmed ✓)
exampleMultiShot :: IO ()
exampleMultiShot = do
  tag <- newPromptTag
  results <- prompt tag do
    x <- control0 tag \k -> do
      r1 <- k (return (1 :: Int))
      r2 <- k (return 2)
      return (r1 ++ r2)
    return [x * 10 :: Int]
  putStrLn $ "  multi-shot: " ++ show results

-- | throw abort. Expected:
--     [1] start
--     result = 99
exampleThrow :: IO ()
exampleThrow = do
  tag <- newPromptTag
  result <- prompt tag do
    putStrLn "  [1] start"
    _ <- throw tag (99 :: Int)
    putStrLn "  [!] never reached"
    return (0 :: Int)
  putStrLn $ "  result = " ++ show result

-- | Principal cut. Expected: principal cut sum = 6
examplePrincipalCut :: IO ()
examplePrincipalCut = do
  result <- principalCutIO producer consumer
  putStrLn $ "  principal cut sum = " ++ show result
  where
    producer yield = do
      _ <- yield (1 :: Int)
      _ <- yield 2
      _ <- yield 3
      return (Done (0 :: Int))
    consumer receive = do
      sa <- receive 0
      case sa of
        Done _  -> return (Done 0)
        Yield a -> do
          sb <- receive a
          case sb of
            Done _  -> return (Done a)
            Yield b -> do
              sc <- receive b
              case sc of
                Done _  -> return (Done (a + b))
                Yield c -> return (Done (a + b + c))
