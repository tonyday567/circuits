{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Effectful oracles over 'K IO' and 'FreeTrace (,) (K IO)': Central Sliding,
-- Step composition, and FreeTrace normal-form order preservation.
module Axioma.Effect
  ( effectTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV)
import Circuit.Category (K (..), id, runK, (.))
import Circuit.Machine qualified as Step
import Circuit.Syntax (Syntax (Lift))
import Circuit.Syntax qualified as Syn
import Circuit.Tensor (tensor)
import Circuit.Trace (FreeTrace)
import Circuit.Traced (trace)
import Control.Monad (when)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Prelude hiding (curry, id, uncurry, (.))

-- | Helper that fixes the cartesian tensor for 'trace' over 'K IO' arrows.
traceK :: K IO (s, a) (s, b) -> FreeTrace (,) (K IO) a b
traceK = trace . Lift

effectTopic :: Verbosity -> IO [Bool]
effectTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Effectful K IO and FreeTrace (,) (K IO) oracles"
  sequence
    [ -- Benton–Hyland Def 3.2: unrestricted sliding fails for non-central
      -- effectful morphisms. The witness uses two IO actions on a shared ref.
      checkIOV verbosity "unrestricted sliding fails for non-central K IO" $
        do
          ref <- newIORef (1 :: Int)
          let f = K $ \ ~((), ()) -> do
                v <- readIORef ref
                modifyIORef' ref (+ 1)
                pure ((), v)
              g = K $ \ ~() -> do
                modifyIORef' ref (* 2)
                pure ()
              post = trace (tensor @(,) @(K IO) g id . f)
              pre = trace (f . tensor @(,) @(K IO) g id)
          (l, r) <- (,) <$> runK post () <*> runK pre ()
          pure (l /= r),
      -- Step (,) (K IO) must compose as a category. This is the untested
      -- edge of parameterising Step over arr; Z2's FreeTrace-level witness
      -- stands on it. The steps touch a shared IORef to confirm
      -- composition threads state through the K base, not just the function
      -- base.
      checkIOV verbosity "Step (,) (K IO) composes as a category" $
        do
          ref <- newIORef (0 :: Int)
          let f = Step.Step $ K $ \((s, a) :: (Int, Int)) -> do
                writeIORef ref (s + 1)
                pure (s + 1, a + 1)
              g = Step.Step $ K $ \(s, b) -> do
                v <- readIORef ref
                pure (s + v, b * 2)
              gf = g . f
          (sOut, c) <- runK (Step.run gf) (0, 5)
          pure (sOut == 2 && c == 12),
      -- Benton-Hyland Def 3.2 at the FreeTrace level: FreeTrace's trace inherits the
      -- Central Sliding side-condition from its base. A non-central effectful
      -- morphism g slid past f give a different result depending on order.
      -- FreeTrace's 'trace' discharges into the base 'trace', so the same witness
      -- that fails for K IO directly also fails for FreeTrace (,) (K IO).
      checkIOV verbosity "FreeTrace trace requires centrality over K IO (Central Sliding)" $
        do
          ref <- newIORef 1
          let f = K $ \ ~((), ()) -> do
                v <- readIORef ref
                modifyIORef' ref (+ 1)
                pure ((), v) :: IO ((), Int)
              g = K $ \ ~() -> do
                modifyIORef' ref (* 2)
                pure ()
              post = trace (Lift f . Lift (tensor @(,) @(K IO) g id)) :: FreeTrace (,) (K IO) () Int
              pre = trace (Lift (tensor @(,) @(K IO) g id) . Lift f) :: FreeTrace (,) (K IO) () Int
          l <- runK (Syn.eval post) ()
          writeIORef ref 1
          r <- runK (Syn.eval pre) ()
          pure (l /= r),
      -- FreeTrace (.) preserves the semantic order of composed trace bodies over
      -- an effectful base. This is not a centrality claim; it just checks
      -- that FreeTrace's normal form agrees with a hand-built body that threads
      -- state in the same order.
      checkIOV verbosity "FreeTrace (.) preserves semantic order of composed trace bodies" $
        do
          ref <- newIORef 1
          let g = K $ \ ~(s, a) -> do
                v <- readIORef ref
                writeIORef ref (v + 1)
                pure (s, v + a)
              f = K $ \ ~(s, b) -> do
                v <- readIORef ref
                writeIORef ref (v * 2)
                pure (s, v * b)
              loopFG = traceK f . traceK g :: FreeTrace (,) (K IO) Int Int
              -- Same threading as FreeTrace's (.) normal form: g's state wire first.
              handBuiltFG =
                traceK
                  ( K $
                      \ ~((s1, s2), a) -> do
                        (s1', b) <- runK g (s1, a)
                        (s2', c) <- runK f (s2, b)
                        pure ((s1', s2'), c)
                  )
          r1 <- runK (Syn.eval loopFG) 5
          writeIORef ref 1
          r2 <- runK (Syn.eval handBuiltFG) 5
          pure (r1 == r2)
    ]
