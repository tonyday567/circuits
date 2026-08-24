{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Poles, Additive Poles, Stamped, Boundary, and markSystem oracles.
module Axioma.Poles
  ( polesTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Category (K (..), id, runK, (.))
import Circuit.Dagger (Dagger (..), transpose)
import Circuit.Poles
  ( Bias (..),
    HasDual (..),
    In (..),
    Out (..),
    Poles (..),
    box,
    close,
    copycat,
    poles,
    poles0,
    polesK,
    prefixIn,
    splay,
    splay0,
    suffixOut,
    (>:>),
  )
import Circuit.Poles qualified as Poles
import Circuit.Poly (Mono)
import Circuit.Process (Boundary (..), fold, isMark, isPayload, markSystem, scan, systemToProcess)
import Circuit.Stamped (Stamped (..), stamp, stamped)
import Circuit.System (System, mooreSystem)
import Control.Monad (when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Maybe (isNothing)
import Prelude hiding (curry, id, uncurry, (.))

polesTopic :: Verbosity -> IO [Bool]
polesTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Poles, Stamped, Boundary, and markSystem oracles"
  sequence
    [ -- Poles oracles
      checkV verbosity "O9 poles . splay == id" $
        let e :: Poles (->) () Int
            e = poles0 (const ()) (const 42)
            (write', receive') = splay0 e
            e' = poles0 write' receive'
         in box @() e' () == 42 && box @() e () == 42,
      checkV verbosity "annihilation: close on non-copycat end violates yanking" $
        let e :: Poles (->) Int Int
            e = poles0 (const ()) (const 42)
         in close (conjoint e) (companion e) 0 == 42
              && close (conjoint e) (companion e) 7 == 42,
      checkIOV verbosity "residual observed: sequential boxes agree but residual is exposed" $ do
        ref <- newIORef (0 :: Int)
        let e1 :: Poles (K IO) Int Int
            e1 = polesK (\x -> modifyIORef' ref (+ x)) (pure 0)
            e2 :: Poles (K IO) Int Int
            e2 = polesK (\_ -> pure ()) (pure 1)
        r1 <- runK (box @() (Poles.compose0 e1 e2)) 5
        residual1 <- readIORef ref
        writeIORef ref 0
        r2 <- runK (box @() e2 . box @() e1) 5
        residual2 <- readIORef ref
        pure (r1 == r2 && r1 == 1 && residual1 == 5 && residual2 == 5),
      checkV verbosity "Bool as a non-terminal 'Poles' pole composes write then read" $
        let e :: Poles (->) Int Int
            e = poles @(->) @Int @Int @Bool (const False) (\b -> if b then 1 :: Int else 0)
            (w, r) = splay @(->) @Int @Int @Bool e
         in not (w 42) && r False == 0 && close (conjoint e) (companion e) 42 == 0,
      checkV verbosity "Bool copycat is not identity (Bool is not terminal)" $
        let e :: Poles (->) Bool Bool
            e = copycat @(->) @Bool
         in not (close (conjoint e) (companion e) True)
              && not (close (conjoint e) (companion e) False),
      -- Additive Poles oracles
      checkV verbosity "Additive Poles.pair pairs outputs" $
        let e1 :: Poles (->) () Int
            e1 = poles0 (const ()) (const 1)
            e2 :: Poles (->) () Int
            e2 = poles0 (const ()) (const 2)
         in box @() (Poles.pair e1 e2) () == (1, 2),
      checkV verbosity "Poles.race LeftFirst picks left when both speak" $
        let eL :: Poles (->) () (Maybe Int)
            eL = poles0 (const ()) (const (Just 1))
            eR :: Poles (->) () (Maybe Int)
            eR = poles0 (const ()) (const (Just 2))
         in box @() (Poles.race isNothing LeftFirst eL eR) () == Just 1,
      checkV verbosity "Poles.race RightFirst picks right when both speak" $
        let eL :: Poles (->) () (Maybe Int)
            eL = poles0 (const ()) (const (Just 1))
            eR :: Poles (->) () (Maybe Int)
            eR = poles0 (const ()) (const (Just 2))
         in box @() (Poles.race isNothing RightFirst eL eR) () == Just 2,
      checkV verbosity "Poles.race falls back when left is silent" $
        let eL :: Poles (->) () (Maybe Int)
            eL = poles0 (const ()) (const Nothing)
            eR :: Poles (->) () (Maybe Int)
            eR = poles0 (const ()) (const (Just 2))
         in box @() (Poles.race isNothing LeftFirst eL eR) () == Just 2
              && box @() (Poles.race isNothing RightFirst eL eR) () == Just 2,
      -- Stamped oracles
      checkV verbosity "Stamped fmap preserves stamp (Int token)" $
        let s = Stamped 7 ("hello" :: String)
         in stamp (fmap reverse s) == (7 :: Int) && stamped (fmap reverse s) == "olleh",
      checkV verbosity "Stamped fmap preserves stamp (Bool token)" $
        let s = Stamped True (10 :: Int)
         in stamp (fmap (+ 1) s) && stamped (fmap (+ 1) s) == 11,
      -- Boundary oracles
      checkV verbosity "Boundary fmap preserves Mark tag" $
        isMark (fmap length (Mark "halt" :: Boundary String String)),
      checkV verbosity "Boundary fmap acts on Payload" $
        let p = fmap length (Payload "hi" :: Boundary String String)
         in isPayload p && p == Payload 2,
      -- Mark system (circuits-residual §7)
      checkV verbosity "markSystem steps payloads through the inner system" $
        let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
            sys = markSystem (== "HALT") id innerSys
            p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
         in scan p (map Payload [1, 2, 3]) == [Just 1, Just 3, Just 6],
      checkV verbosity "markSystem halts on a halt mark and emits Nothing thereafter" $
        let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
            sys = markSystem (== "HALT") id innerSys
            p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
         in scan p [Payload 1, Payload 2, Mark "HALT", Payload 3] == [Just 1, Just 3, Nothing, Nothing],
      checkV verbosity "markSystem treats non-halt marks as no-ops" $
        let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
            sys = markSystem (== "HALT") id innerSys
            p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
         in scan p [Payload 1, Mark "NOOP", Payload 2] == [Just 1, Just 1, Just 3],
      checkV verbosity "markSystem halts immediately when the first input is a halt mark" $
        let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
            sys = markSystem (== "HALT") id innerSys
            p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
         in scan p [Mark "HALT", Payload 1] == [Nothing, Nothing],
      checkV verbosity "markSystem round-trips through systemToProcess" $
        let innerSys = mooreSystem (+) id :: System (->) Int (Mono Int Int)
            sys = markSystem (== "HALT") id innerSys
            p = systemToProcess (Left 0) (\case Left s -> Just s; Right _ -> Nothing) sys
         in scan p [] == [] && fold p [Payload 1, Payload 2, Mark "HALT"] == Just Nothing
    ]
