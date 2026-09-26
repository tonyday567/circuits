{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Axioma.Effect
  ( effectTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV)
import Circuit.Category (K (..), id, runK, (.))
import Circuit.GMachine qualified as Stratum
import Circuit.Syntax (Syntax (Lift))
import Circuit.Syntax qualified as Syn
import Circuit.Tensor (tensor)
import Circuit.Trace (Trace)
import Circuit.Traced (yank)
import Control.Monad (when)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Prelude hiding (curry, id, uncurry, (.))

yankK :: K IO (s, a) (s, b) -> Trace (,) (K IO) a b
yankK = yank . Lift

effectTopic :: Verbosity -> IO [Bool]
effectTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Effectful K IO and Trace (,) (K IO) oracles"
  sequence
    [ checkIOV verbosity "unrestricted sliding fails for non-central K IO" $
        do
          ref <- newIORef (1 :: Int)
          let f = K $ \ ~((), ()) -> do
                v <- readIORef ref
                modifyIORef' ref (+ 1)
                pure ((), v)
              g = K $ \ ~() -> do
                modifyIORef' ref (* 2)
                pure ()
              post = yank (tensor @(,) @(K IO) g id . f)
              pre = yank (f . tensor @(,) @(K IO) g id)
          (l, r) <- (,) <$> runK post () <*> runK pre ()
          pure (l /= r),
      checkIOV verbosity "Stratum (,) (K IO) composes as a category" $
        do
          ref <- newIORef (0 :: Int)
          let f = Stratum.Stratum $ K $ \((s, a) :: (Int, Int)) -> do
                writeIORef ref (s + 1)
                pure (s + 1, a + 1)
              g = Stratum.Stratum $ K $ \(s, b) -> do
                v <- readIORef ref
                pure (s + v, b * 2)
              gf = g . f
          (sOut, c) <- runK (Stratum.morphism gf) (0, 5)
          pure (sOut == 2 && c == 12),
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
              post = yank (Lift f . Lift (tensor @(,) @(K IO) g id)) :: Trace (,) (K IO) () Int
              pre = yank (Lift (tensor @(,) @(K IO) g id) . Lift f) :: Trace (,) (K IO) () Int
          l <- runK (Syn.eval post) ()
          writeIORef ref 1
          r <- runK (Syn.eval pre) ()
          pure (l /= r),
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
              loopFG = yankK f . yankK g :: Trace (,) (K IO) Int Int

              handBuiltFG =
                yankK
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
