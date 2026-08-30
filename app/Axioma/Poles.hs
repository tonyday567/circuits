{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Poles, Additive Poles, Stamped, Boundary, and markMoore oracles.
module Axioma.Poles
  ( polesTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Body (Body (..))
import Circuit.Category (K (..), id, runK, (.))
import Circuit.Dagger (Dagger (..), transpose)
import Circuit.Moore (Boundary (..), Moore, isMark, isPayload, markMoore, mooreMachine)
import Circuit.Poles
  ( HasDual (..),
    In (..),
    Out (..),
    Poles (..),
    box,
    close,
    companionTight,
    compose,
    compose0,
    conjointTight,
    copycat,
    open,
    plug,
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
import Circuit.Process (fold, mooreAsProcess, scan)
import Circuit.Stamped (Stamped (..), stamp, stamped)
import Circuit.Tensor (Bias (..))
import Control.Monad (when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Maybe (isNothing)
import Data.Void (Void)
import Prelude hiding (curry, id, uncurry, (.))

polesTopic :: Verbosity -> IO [Bool]
polesTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Poles, Stamped, Boundary, and markMoore oracles"
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
      checkV verbosity "markMoore steps payloads through the inner system" $
        let innerSys = mooreMachine (+) id :: Moore (,) Int (->) (Mono Int Int)
            sys = markMoore (== "HALT") id innerSys
            p = mooreAsProcess sys (Left 0)
         in scan p (map Payload [1, 2, 3]) == [Just 1, Just 3, Just 6],
      checkV verbosity "markMoore halts on a halt mark and emits Nothing thereafter" $
        let innerSys = mooreMachine (+) id :: Moore (,) Int (->) (Mono Int Int)
            sys = markMoore (== "HALT") id innerSys
            p = mooreAsProcess sys (Left 0)
         in scan p [Payload 1, Payload 2, Mark "HALT", Payload 3] == [Just 1, Just 3, Nothing, Nothing],
      checkV verbosity "markMoore treats non-halt marks as no-ops" $
        let innerSys = mooreMachine (+) id :: Moore (,) Int (->) (Mono Int Int)
            sys = markMoore (== "HALT") id innerSys
            p = mooreAsProcess sys (Left 0)
         in scan p [Payload 1, Mark "NOOP", Payload 2] == [Just 1, Just 1, Just 3],
      checkV verbosity "markMoore halts immediately when the first input is a halt mark" $
        let innerSys = mooreMachine (+) id :: Moore (,) Int (->) (Mono Int Int)
            sys = markMoore (== "HALT") id innerSys
            p = mooreAsProcess sys (Left 0)
         in scan p [Mark "HALT", Payload 1] == [Nothing, Nothing],
      checkV verbosity "markMoore round-trips through mooreToProcess" $
        let innerSys = mooreMachine (+) id :: Moore (,) Int (->) (Mono Int Int)
            sys = markMoore (== "HALT") id innerSys
            p = mooreAsProcess sys (Left 0)
         in null (scan p []) && fold p [Payload 1, Payload 2, Mark "HALT"] == Just Nothing,
      -- equipment-law oracles
      checkV verbosity "box is a homomorphism for stateful Poles over Body" $
        let w1 = Body (\(s, x) -> (s + x, ())) :: Body (,) Int (->) Int ()
            r1 = Body (\(s, ()) -> (s, s)) :: Body (,) Int (->) () Int
            p1 = poles0 w1 r1 :: Poles (Body (,) Int (->)) Int Int
            w2 = Body (\(s, x) -> (s * x, ())) :: Body (,) Int (->) Int ()
            r2 = Body (\(s, ()) -> (s, s + 1)) :: Body (,) Int (->) () Int
            p2 = poles0 w2 r2 :: Poles (Body (,) Int (->)) Int Int
            lhs = box @() (compose @_ @_ @_ @_ @() p1 p2) :: Body (,) Int (->) Int Int
            rhs = box @() p2 . box @() p1
         in morphism lhs (2, 3) == morphism rhs (2, 3)
              && morphism lhs (1, 4) == morphism rhs (1, 4),
      checkV verbosity "open is the identity for Poles composition at terminal unit" $
        let p = poles0 (const ()) (const 42 :: () -> Int) :: Poles (->) () Int
            o = open :: Poles (->) () ()
            (wL, rL) = splay0 (compose0 o p)
            (w, r) = splay0 p
         in wL () == w () && rL () == r () && box @() (compose0 o p) () == box @() p (),
      checkV verbosity "Body (,) HasDual yanking closes unit poles to identity" $
        let b = box @() (open :: Poles (Body (,) Int (->)) () ()) :: Body (,) Int (->) () ()
         in morphism b (42, ()) == (42, ()) && morphism b (0, ()) == (0, ()),
      checkV verbosity "Body Either HasDual yanking closes unit poles to identity" $
        let b = box @Void (open :: Poles (Body Either [Int] (->)) Void Void) :: Body Either [Int] (->) Void Void
         in morphism b (Left [1, 2, 3]) == Left [1, 2, 3],
      -- Tight-arrow companion / conjoint oracles
      checkV verbosity "plug generalises close on same-type poles" $
        let p = open :: Poles (->) () ()
         in close (conjoint p) (companion p) () == plug (conjoint p) (companion p) (),
      checkV verbosity "companionTight posts a unit-incident arrow to Out" $
        let f = const 42 :: () -> Int
            o = companionTight f :: Out (->) Int
         in emit o (conjoint (open :: Poles (->) () ())) () == 42,
      checkV verbosity "conjointTight pres a unit-incident arrow to In" $
        let f = const () :: Int -> ()
            i = conjointTight f :: In (->) Int
         in commit i (companion (open :: Poles (->) () ())) 7 == (),
      checkV verbosity "plugging companionTight and conjointTight recovers composition" $
        let f = const () :: Int -> ()
            g = const 42 :: () -> Int
         in plug (conjointTight f) (companionTight g) 7 == 42,
      checkV verbosity "plugging companionTight and conjointTight agrees with f .> g" $
        let f = const () :: Int -> ()
            g = const 42 :: () -> Int
         in plug (conjointTight f) (companionTight g) 5 == (g . f) 5
    ]
