{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

-- | Box spec via Producer/Consumer hyperfunctions (Kidney & Wu, POPL 2026).
--
--   Producer m a = (m → a) ↬ a     — produces m messages, result a
--   Consumer m a = a ↬ (m → a)     — consumes m messages, result a
--   𝜄 :: Producer m a → Consumer m a → a  — run in lockstep

import Circuit.Hyper
  ( Hyper (..),
    run,
    base,
    lift,
    lower,
    ana,
    (⇸),
    (⊲),
    (↓),
    (⥁),
  )
import Prelude hiding (id, (.))
import Control.Category ((.), id)

-- ---------------------------------------------------------------------------
-- Producer/Consumer types
-- ---------------------------------------------------------------------------

type Producer o a = Hyper (o -> a) a
type Consumer i a = Hyper a (i -> a)

-- prod :: o → Producer o a → Producer o a
-- 𝜄 (prod o p) q = 𝜄 q p o
prod :: o -> Producer o a -> Producer o a
prod o p = Hyper $ \q -> invoke q p o

-- cons :: (i → a → a) → Consumer i a → Consumer i a
-- 𝜄 (cons f p) q i = f i (𝜄 q p)
cons :: (i -> a -> a) -> Consumer i a -> Consumer i a
cons f p = Hyper $ \q i -> f i (invoke q p)

-- Base cases: producer/consumer that just return the accumulator
yield :: a -> Producer o a
yield a = Hyper $ \_ -> a

accept :: a -> Consumer i a
accept a = Hyper $ \_ _ -> a

-- Run a producer and consumer together
(glue) :: Producer m a -> Consumer m a -> a
(glue) = invoke

-- ---------------------------------------------------------------------------
-- emitSingles — builds a Producer from a list
-- ---------------------------------------------------------------------------

-- | Produce each element as Just, then Nothing to signal end.
emitSingles :: [a] -> Producer (Maybe a) [a]
emitSingles = foldr (\x p -> prod (Just x) p) (prod Nothing (yield []))

-- ---------------------------------------------------------------------------
-- collectSingles — builds a Consumer (coinductive, infinite)
-- ---------------------------------------------------------------------------

-- | Consumer that collects Just values, stops on Nothing.
--   coinductive: h = cons step h — consumes any number of messages.
collectSingles :: Consumer (Maybe a) [a]
collectSingles = h
  where
    h = cons step h
    step mx acc = case mx of
      Just x  -> x : acc
      Nothing -> acc

-- ---------------------------------------------------------------------------
-- Two-component pipeline: emitSingles → collectSingles
-- ---------------------------------------------------------------------------

pipeline2 :: [a] -> [a]
pipeline2 xs = emitSingles xs glue collectSingles

-- >>> pipeline2 [1,2,3]
-- [1,2,3]
-- >>> pipeline2 []
-- []
-- >>> pipeline2 [1]
-- [1]

-- ---------------------------------------------------------------------------
-- circuitTake — count-limited Producer transformer
-- ---------------------------------------------------------------------------

-- | Wrap a Producer, stopping after n elements.
--   Can't do this as a Consumer modifier because Consumer is opaque.
--   Instead: build the Producer WITH the limit baked in.
takeP :: Int -> [a] -> Producer (Maybe a) [a]
takeP n xs = go n xs
  where
    go 0 _      = prod Nothing (yield [])
    go _ []     = prod Nothing (yield [])
    go k (x:rest) = prod (Just x) (go (k-1) rest)

-- ---------------------------------------------------------------------------
-- Three-component pipeline (monolithic)
-- ---------------------------------------------------------------------------

pipeline3 :: Int -> [a] -> [a]
pipeline3 n xs = takeP n xs glue collectSingles

-- >>> pipeline3 2 [1,2,3]
-- [1,2]
-- >>> pipeline3 0 [1,2,3]
-- []
-- >>> pipeline3 5 [1,2,3]
-- [1,2,3]

-- ---------------------------------------------------------------------------
-- circuitTake as a Channel (Kidney & Wu §5.1)
-- ---------------------------------------------------------------------------

-- | Channel r i o = (o → r) ↬ (i → r)
--   Consumes i, produces o, result r. Bidirectional: can both send and receive.
type Channel r i o = Hyper (o -> r) (i -> r)

-- | takeChannel: count messages, pass through up to N, then stop.
takeChannel :: forall a. Int -> Channel [a] (Maybe a) (Maybe a)
takeChannel n = go n
  where
    go :: Int -> Channel [a] (Maybe a) (Maybe a)
    go 0 = Hyper $ \_ i -> case i of { Nothing -> ([] :: [a]); Just _ -> ([] :: [a]) }
    go k = Hyper $ \out i ->
      case i of
        Nothing -> ([] :: [a])
        Just x  -> invoke out (go (k-1)) (Just x)

-- Compose Channel with Consumer (paper: Consumer o r ⊙ Channel r i o = Consumer i r):
--   (.) :: Hyper b c -> Hyper a b -> Hyper a c
--   takeChannel :: Hyper (o→r) (i→r)  = Hyper b c where b = o→r, c = i→r
--   collectSingles :: Hyper r (o→r)    = Hyper a b where a = r, b = o→r
--   takeChannel . collectSingles :: Hyper r (i→r) = Consumer i r  ✓
--
-- Then: emitSingles xs glue (takeChannel n . collectSingles) :: [a]

pipelineChannel :: Int -> [a] -> [a]
pipelineChannel n xs = emitSingles xs glue (takeChannel n . collectSingles)

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== pipeline2 (emit → collect) ==="
  print (pipeline2 [1,2,3 :: Int])
  print (pipeline2 ([] :: [Int]))
  putStrLn ""
  putStrLn "=== pipeline3 (emit → take 2 → collect, monolithic) ==="
  print (pipeline3 2 [1,2,3 :: Int])
  print (pipeline3 0 [1,2,3 :: Int])
  putStrLn ""
  putStrLn "=== pipelineChannel (emit → channel(take 2) → collect) ==="
  print (pipelineChannel 2 [1,2,3 :: Int])
  print (pipelineChannel 0 [1,2,3 :: Int])
  print (pipelineChannel 5 [1,2,3 :: Int])
