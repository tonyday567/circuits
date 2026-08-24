{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Effectful oracles over 'K IO' and 'Trace (,) (K IO)': Central Sliding,
-- Body composition, and Trace normal-form order preservation.
module Axioma.Effect
  ( effectTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV)
import Circuit.Body (Body (..), morphism)
import Circuit.Body qualified as Body
import Circuit.Category (K (..), id, runK, (.))
import Circuit.Channel (trace)
import Circuit.Process (Process (..))
import Circuit.Syntax qualified as Syn
import Circuit.Tensor (tensor)
import Circuit.Trace (Trace, base, yank)
import Control.Monad (when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Prelude hiding (curry, id, uncurry, (.))

effectTopic :: Verbosity -> IO [Bool]
effectTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Effectful K IO and Trace (,) (K IO) oracles"
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
      -- Body (,) (K IO) must compose as a category. This is the untested
      -- edge of parameterising Body over arr; Z2's Trace-level witness stands
      -- on it. The bodies touch a shared IORef to confirm composition threads
      -- state through the K base, not just the function base.
      checkIOV verbosity "Body (,) (K IO) composes as a category" $
        do
          ref <- newIORef (0 :: Int)
          let f = Body.Body $ K $ \((s, a) :: (Int, Int)) -> do
                writeIORef ref (s + 1)
                pure (s + 1, a + 1)
              g = Body.Body $ K $ \(s, b) -> do
                v <- readIORef ref
                pure (s + v, b * 2)
              gf = g . f
          (sOut, c) <- runK (Body.morphism gf) (0, 5)
          pure (sOut == 2 && c == 12),
      -- Benton-Hyland Def 3.2 at the Trace level: Trace's trace inherits the
      -- Central Sliding side-condition from its base. A non-central effectful
      -- morphism g slid past f give a different result depending on order.
      -- Trace's 'trace' discharges into the base 'trace', so the same witness
      -- that fails for K IO directly also fails for Trace (,) (K IO).
      checkIOV verbosity "Trace trace requires centrality over K IO (Central Sliding)" $
        do
          ref <- newIORef 1
          let f = K $ \ ~((), ()) -> do
                v <- readIORef ref
                modifyIORef' ref (+ 1)
                pure ((), v) :: IO ((), Int)
              g = K $ \ ~() -> do
                modifyIORef' ref (* 2)
                pure ()
              post = trace (base f . base (tensor @(,) @(K IO) g id)) :: Trace (,) (K IO) () Int
              pre = trace (base (tensor @(,) @(K IO) g id) . base f) :: Trace (,) (K IO) () Int
          l <- runK (Syn.eval post) ()
          writeIORef ref 1
          r <- runK (Syn.eval pre) ()
          pure (l /= r),
      -- Trace (.) preserves the semantic order of composed yank bodies over
      -- an effectful base. This is not a centrality claim; it just checks
      -- that Trace's normal form agrees with a hand-built body that threads
      -- state in the same order.
      checkIOV verbosity "Trace (.) preserves semantic order of composed yank bodies" $
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
              loopFG = yank (base f) . yank (base g) :: Trace (,) (K IO) Int Int
              -- Same threading as Trace's (.) normal form: g's state wire first.
              handBuiltFG =
                yank
                  ( base
                      ( K $
                          \ ~((s1, s2), a) -> do
                            (s1', b) <- runK g (s1, a)
                            (s2', c) <- runK f (s2, b)
                            pure ((s1', s2'), c)
                      )
                  )
          r1 <- runK (Syn.eval loopFG) 5
          writeIORef ref 1
          r2 <- runK (Syn.eval handBuiltFG) 5
          pure (r1 == r2)
    ]
