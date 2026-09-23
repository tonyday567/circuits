{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | GMachine oracles.
module Axioma.GMachine
  ( gMachineTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (id)
import Circuit.GMachine (Cell (..), cellAsLens)
import Circuit.Poly (applyLens)
import Control.Monad (when)
import Prelude hiding (id)

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
      checkV verbosity "cell PutPut catches the counting machine" (not (putPut cntW 0 1 2))
    ]
  where
    points = [-1, 0, 5] :: [Int]
