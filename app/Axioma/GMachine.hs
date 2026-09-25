{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | GMachine oracles.
module Axioma.GMachine
  ( gMachineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (id, (.))
import Circuit.GMachine (Cell (..), GMoore (..), GMooreT (..), TensorSchedule (..), cellAsLens, scanT)
import Circuit.Poly (applyLens)
import Circuit.Tensor (Tensor (..))
import Control.Monad (when)
import Data.These (These (..), these)
import Prelude hiding (id, (.))

-- Cell (,) as a lens, via the cellAsLens dictionary: a Cell (,) s (->) i o
-- is the data of Lens s s o i — get = observe, put = curry write. The laws,
-- in machine spelling:
--
--   GetPut: write (s, observe s) = s
--   PutGet: observe (write (s, i)) = i
--   PutPut: write (write (s, i), j) = write (s, j)

-- The fully lawful witness: the register. The channel holds nothing but
-- the last input, the observation is the identity.
regW :: Cell (,) Int (->) Int Int
regW = Cell snd id

-- GetPut counterexample: the accumulator remembers. Its channel carries
-- history the view never shows, so feeding the view back doubles.
accW :: Cell (,) Int (->) Int Int
accW = Cell (uncurry (+)) id

-- PutGet counterexample: the observation ignores the input entirely.
constW :: Cell (,) Int (->) Int Int
constW = Cell fst (const 0)

-- PutPut counterexample: the update depends on history. A write already
-- applied cannot be undone by the next input alone.
cntW :: Cell (,) Int (->) Int Int
cntW = Cell (\(s, _) -> s + 1) id

getPut :: (Eq ch) => Cell (,) ch (->) i i -> ch -> Bool
getPut (Cell w o) s = w (s, o s) == s

-- PutGet only typechecks at a homogeneous focus: observe (write (s, i))
-- has type o, and the law compares it against i.
putGet :: (Eq i) => Cell (,) ch (->) i i -> ch -> i -> Bool
putGet (Cell w o) s i = o (w (s, i)) == i

putPut :: (Eq ch) => Cell (,) ch (->) i o -> ch -> i -> i -> Bool
putPut (Cell w _) s i j = w (w (s, i), j) == w (s, j)

-- The dictionary round trip: applyLens (cellAsLens c) is (observe, curry
-- write) back again.
dictOk :: Bool
dictOk =
  all
    ( \(s, i) ->
        fst (applyLens (cellAsLens regW) s) == observe regW s
          && snd (applyLens (cellAsLens regW) s) i == write regW (s, i)
    )
    [(s, i) | s <- points, i <- points]
  where
    points = [-1, 0, 5] :: [Int]

-- Falsifiers (verify.md discipline): a stale-carrier composite feed breaks
-- the unit scans; a non-projection fold (e.g. a These-sum fold) breaks
-- naturality; naturality alone admits both projection folds, so the These
-- input-bias is pinned by the scanBoth unit witnesses — scanT's
-- That-injection never exercises the These clause.

sumG :: GMooreT (,) (->) Int Int
sumG = GMooreT (GMoore id (Cell (uncurry (+)) id))

prodG :: GMooreT (,) (->) Int Int
prodG = GMooreT (GMoore (* 10) (Cell (\(c, i) -> c * i) id))

countG :: GMooreT (,) (->) Int Int
countG = GMooreT (GMoore (const 100) (Cell (\(c, _) -> c + 1) id))

eitherG :: GMooreT Either (->) Int Int
eitherG = GMooreT (GMoore id (Cell (either id (+ 1)) (* 2)))

theseG :: GMooreT These (->) Int Int
theseG = GMooreT (GMoore id (Cell (these id (+ 1) (\c i -> c + i)) id))

xs :: [Int]
xs = [1, 2, 3, 4]

-- Input-list elimination at the inclusive tensor, full injection: every
-- step feeds These c i, where scanT's That-injection is memoryless on the
-- carrier. Modelled on scanT, pattern-matching These directly.
scanBoth :: GMooreT These (->) i o -> [i] -> [o]
scanBoth (GMooreT (GMoore j (Cell k e))) = \case
  [] -> []
  (i : is) -> let c = j i in e c : go c is
  where
    go _ [] = []
    go c (i : is) = let c' = k (These c i) in e c' : go c' is

-- echoFold naturality: echoFold . tensor f f == f . echoFold at f = (+ 1).
natPair :: Bool
natPair =
  all
    (\x -> echoFold (tensor f f x) == f (echoFold x))
    [(0, 5), (3, 7)]
  where
    f :: Int -> Int
    f = (+ 1)

natEither :: Bool
natEither =
  all
    (\x -> echoFold (tensor f f x) == f (echoFold x))
    [Left 0, Right 5]
  where
    f :: Int -> Int
    f = (+ 1)

natThese :: Bool
natThese =
  all
    (\x -> echoFold (tensor f f x) == f (echoFold x))
    [This 0, That 5, These 0 5]
  where
    f :: Int -> Int
    f = (+ 1)

gMachineTopic :: Verbosity -> IO [Bool]
gMachineTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "GMachine oracles"
  sequence
    [ checkV verbosity "cell lens dictionary: get = observe, put = curry write" dictOk,
      checkV verbosity "cell GetPut (register)" (all (getPut regW) points),
      checkV verbosity "cell GetPut catches the accumulator" (not (getPut accW 1)),
      checkV verbosity "cell PutGet (register)" (all (\s -> putGet regW s 3) points),
      checkV verbosity "cell PutGet catches the constant observation" (not (putGet constW 0 3)),
      checkV verbosity "cell PutPut (register)" (putPut regW 0 1 2),
      checkV verbosity "cell PutPut catches the counting machine" (not (putPut cntW 0 1 2)),
      checkV verbosity "gmoorT (,) scan anchor" (scanT sumG xs == [1, 3, 6, 10]),
      checkV verbosity "gmoorT Either scan anchor" (scanT eitherG xs == [2, 6, 8, 10]),
      checkV verbosity "gmoorT These scan anchor (That-injection)" (scanT theseG xs == [1, 3, 4, 5]),
      checkV verbosity "gmoorT These scanBoth anchor (full injection)" (scanBoth theseG xs == [1, 3, 6, 10]),
      checkV verbosity "echoFold naturality at (,)" natPair,
      checkV verbosity "echoFold naturality at Either" natEither,
      checkV verbosity "echoFold naturality at These" natThese,
      checkV verbosity "gmoorT unit L at (,): scanT (id . m) == scanT m" (scanT (id . sumG) xs == scanT sumG xs),
      checkV verbosity "gmoorT unit R at (,): scanT (m . id) == scanT m" (scanT (sumG . id) xs == scanT sumG xs),
      checkV verbosity "gmoorT unit L at Either" (scanT (id . eitherG) xs == scanT eitherG xs),
      checkV verbosity "gmoorT unit R at Either" (scanT (eitherG . id) xs == scanT eitherG xs),
      checkV verbosity "gmoorT unit L at These" (scanT (id . theseG) xs == scanT theseG xs),
      checkV verbosity "gmoorT unit R at These" (scanT (theseG . id) xs == scanT theseG xs),
      checkV verbosity "gmoorT unit L at These, full injection" (scanBoth (id . theseG) xs == scanBoth theseG xs),
      checkV verbosity "gmoorT unit R at These, full injection" (scanBoth (theseG . id) xs == scanBoth theseG xs),
      checkV verbosity "gmoorT associativity on a three-machine chain" (scanT ((countG . prodG) . sumG) xs == scanT (countG . (prodG . sumG)) xs)
    ]
  where
    points = [-1, 0, 5] :: [Int]
