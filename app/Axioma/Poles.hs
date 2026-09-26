-- | Poles oracles: write/read legs, closing, and leg-mapping at '(->)'.
module Axioma.Poles
  ( polesTopic,
  )
where

import Axioma.Common (Verbosity (..), checkIOV, checkV)
import Circuit.Category (K (..), runK)
import Circuit.GMachine
  ( Cap (..),
    Point (..),
    Poles (..),
    close,
    compose,
    copycat,
    imap,
    iomap,
    omap,
    poles0,
    polesK,
    splay0,
    unclose,
  )
import Circuit.Tensor (Unit)
import Control.Monad (when)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Prelude hiding (read, (.))

polesTopic :: Verbosity -> IO [Bool]
polesTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Poles oracles"
  sequence
    [ checkV verbosity "close . copycat is the identity at any carrier" $
        close (copycat :: Poles Int (->) Int Int) 5 == (5 :: Int)
          && close (copycat :: Poles Bool (->) Bool Bool) True
          && not (close (copycat :: Poles Bool (->) Bool Bool) False),
      checkV verbosity "close . unclose recovers the morphism" $
        let f :: Int -> Int
            f = (+ 1)
         in close (unclose f) 5 == f 5,
      checkV verbosity "write and read are the poles0 legs" $
        let p :: Poles () (->) Int Int
            p = poles0 (const ()) (const 42)
         in write p 7 == () && read p () == 42 && close p 7 == 42,
      checkV verbosity "splay0 and poles0 are inverse" $
        let p :: Poles () (->) Int Int
            p = poles0 (const ()) (const 42)
            (w, r) = splay0 p
            p' = poles0 w r
         in w 7 == write p 7 && r () == read p () && write p' 3 == w 3 && read p' () == r (),
      checkV verbosity "compose pipes the read leg into the next write leg" $
        let p1 :: Poles Int (->) Int Int
            p1 = Poles (+ 1) (* 2)
            p2 :: Poles Int (->) Int Int
            p2 = Poles (+ 10) (subtract 3)
         in close (compose p1 p2) 5 == close p2 (close p1 5)
              && close (compose p1 p2) 5 == 19,
      checkV verbosity "imap precomposes the write leg" $
        let p :: Poles Int (->) Int Int
            p = Poles (+ 1) (* 2)
         in close (imap (* 10) p) 5 == close p 50,
      checkV verbosity "omap postcomposes the read leg" $
        let p :: Poles Int (->) Int Int
            p = Poles (+ 1) (* 2)
         in close (omap (+ 100) p) 5 == close p 5 + 100,
      checkV verbosity "iomap f g is imap f together with omap g" $
        let p :: Poles Int (->) Int Int
            p = Poles (+ 1) (* 2)
         in close (iomap (* 10) (+ 100) p) 5 == close (omap (+ 100) (imap (* 10) p)) 5,
      checkIOV verbosity "polesK runs the write effect before the read" $ do
        ref <- newIORef (0 :: Int)
        let p :: Poles () (K IO) Int Int
            p = polesK (\x -> modifyIORef' ref (+ x)) (pure 42)
        r <- runK (close p) 5
        residual <- readIORef ref
        pure (r == 42 && residual == 5),
      checkV verbosity "Point and Cap plug into the poles legs at unit" $
        let pt :: Point (,) (->) Int
            pt = Point (const 7)
            cap :: Cap (,) (->) Int
            cap = Cap (const ())
         in close (Poles (runPoint pt) (id :: Int -> Int)) () == 7
              && close (Poles (id :: Int -> Int) (runCap cap)) 7 == ()
    ]
