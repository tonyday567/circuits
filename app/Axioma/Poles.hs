-- | Poles oracles: the write legs, closing, and leg-mapping at '(->)'.
module Axioma.Poles
  ( polesTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Category (K (..), runK)
import Circuit.Machine
  ( Poles (..),
    close,
    compose,
    iomap,
    polesK,
    unclose,
  )
import Control.Monad (when)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Prelude hiding (init, (.))

polesTopic :: Verbosity -> IO [Bool]
polesTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Poles oracles"
  sequence
    [ checkV verbosity "close . unclose recovers the morphism" $
        let f :: Int -> Int
            f = (+ 1)
         in close (unclose f) 5 == f 5,
      checkV verbosity "the Poles legs at the unit carrier" $
        let p :: Poles () (->) Int Int
            p = Poles (const ()) (const ()) (const 42)
         in case p of
              Poles j k o -> j 7 == () && k 7 == () && o () == 42 && close p 7 == 42,
      checkV verbosity "compose pipes the read leg into the next write leg" $
        let p1 :: Poles Int (->) Int Int
            p1 = Poles (+ 1) (+ 1) (* 2)
            p2 :: Poles Int (->) Int Int
            p2 = Poles (+ 10) (+ 10) (subtract 3)
         in close (compose p1 p2) 5 == close p2 (close p1 5)
              && close (compose p1 p2) 5 == 19,
      checkV verbosity "iomap f id precomposes the write legs" $
        let p :: Poles Int (->) Int Int
            p = Poles (+ 1) (+ 1) (* 2)
         in close (iomap (* 10) (id :: Int -> Int) p) 5 == close p 50,
      checkV verbosity "iomap id g postcomposes the read leg" $
        let p :: Poles Int (->) Int Int
            p = Poles (+ 1) (+ 1) (* 2)
         in close (iomap (id :: Int -> Int) (+ 100) p) 5 == close p 5 + 100,
      checkV verbosity "iomap f g is iomap f id together with iomap id g" $
        let p :: Poles Int (->) Int Int
            p = Poles (+ 1) (+ 1) (* 2)
         in close (iomap (* 10) (+ 100) p) 5
              == close (iomap (id :: Int -> Int) (+ 100) (iomap (* 10) (id :: Int -> Int) p)) 5,
      checkIOV verbosity "polesK runs the write effect before the read" $ do
        ref <- newIORef (0 :: Int)
        let p :: Poles () (K IO) Int Int
            p = polesK (\x -> modifyIORef' ref (+ x)) (pure 42)
        r <- runK (close p) 5
        residual <- readIORef ref
        pure (r == 42 && residual == 5)
    ]
