{-# LANGUAGE BlockArguments #-}

-- | Bimonoid net oracles — the claim example 1 rests on, as a law.
--
-- Example 1 of the circuit-examples wave counts a corpus three ways and shows
-- the three transcripts agree. That is a fact about one corpus. This topic
-- states the law underneath it ⟜ the fan-in / fan-out shape of a bimonoid net
-- cannot change its result, because 'SigMerge' is commutative and associative
-- and 'SigCopy' with 'SigDiscard' is the identity.
--
-- The channel is 'Integer' under @(+)@, which the menu carries; the example's
-- keyed map is the example's complication, not the law's subject.
--
-- Mutation note ⟜ row 5 is the falsifier. A merge that keeps its left operand
-- (a left-biased union, the example's named counterexample) has the same channel
-- type but is not a commutative bimonoid and disagrees by value, so a green
-- suite here is a green suite that could have been red.
module Axioma.BimonoidNet
  ( bimonoidNetTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Bimonoid (Copy, Discard, SigCopy (..), SigDiscard (..), SigMerge (..), SigZero (..))
import Circuit.Category ((.>))
import Circuit.Net (Net, SigPar (..))
import Circuit.Syntax (Syntax (..), run, (:+:) (..))
import Control.Category (id)
import Control.Monad (when)
import Data.List (foldl')
import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- the rows, as the library spells them
-- ---------------------------------------------------------------------------

-- | @SigCompose :+: SigPar :+: SigSwap :+: SigCopy :+: SigDiscard :+: SigMerge
-- :+: SigZero@ — a row is an 'Oper' at a fixed injection depth.
copyRow :: (Copy (->) a) => Net (,) (->) a (a, a)
copyRow = Oper (R (R (R (L SigCopy))))

discardRow :: (Discard (->) a) => Net (,) (->) a ()
discardRow = Oper (R (R (R (R (L SigDiscard)))))

mergeRow :: Net (,) (->) (Integer, Integer) Integer
mergeRow = Oper (R (R (R (R (R (L SigMerge))))))

zeroRow :: Net (,) (->) () Integer
zeroRow = Oper (R (R (R (R (R (R SigZero))))))

-- | Parallel composition on 'Net' is the 'SigPar' row; there is no
-- @Tensor (,) (Net …)@ instance to call.
parNet :: Net (,) (->) a b -> Net (,) (->) c d -> Net (,) (->) (a, c) (b, d)
parNet f g = Oper (R (L (SigPar f g)))

-- | Copy, keep one copy, discard the other: the composite the shard shape
-- leans on when it says a token belongs to exactly one shard.
keepLeft :: Net (,) (->) Integer Integer
keepLeft = copyRow .> parNet (Lift id) discardRow .> Lift fst

keepRight :: Net (,) (->) Integer Integer
keepRight = copyRow .> parNet discardRow (Lift id) .> Lift snd

-- ---------------------------------------------------------------------------
-- the three shapes
-- ---------------------------------------------------------------------------

leftShape :: [Integer] -> Integer
leftShape = foldl' (\acc x -> run mergeRow (acc, x)) 0

treeShape :: [Integer] -> Integer
treeShape = rounds
  where
    rounds [] = 0
    rounds [x] = x
    rounds xs = rounds (pairs xs)
    pairs (a : b : rest) = run mergeRow (a, b) : pairs rest
    pairs rest = rest

shardShape :: [Integer] -> Integer
shardShape xs =
  let (as, bs) = splitAt (length xs `div` 2) xs
      a = foldl' (\acc x -> run mergeRow (acc, x)) 0 as
      b = foldl' (\acc x -> run mergeRow (acc, x)) 0 bs
   in run mergeRow (a, b)

-- | The mutant: keep the left operand instead of adding. Same type, same
-- channel, different value — the shape of every counterexample in this library.
leftBiased :: [Integer] -> Integer
leftBiased = foldl' (\acc x -> if acc == 0 then x else acc) 0

-- ---------------------------------------------------------------------------
-- the rows
-- ---------------------------------------------------------------------------

corpus :: [Integer]
corpus = [1 .. 64]

shapesAgreeOk :: Bool
shapesAgreeOk = and [leftShape xs == treeShape xs | xs <- prefixes]
  where
    prefixes = [take n corpus | n <- [0 .. length corpus]]

shardAgreesOk :: Bool
shardAgreesOk = and [shardShape xs == leftShape xs | xs <- [corpus, take 7 corpus, [3], []]]

copyDiscardOk :: Bool
copyDiscardOk = and [run keepLeft x == x && run keepRight x == x | x <- corpus]

zeroOk :: Bool
zeroOk = run zeroRow () == 0 && leftShape [] == 0 && treeShape [] == 0

mutantDisagreesOk :: Bool
mutantDisagreesOk = leftBiased [1, 2, 3] /= treeShape [1, 2, 3] && leftBiased [1, 2, 3] == 1

-- | Regrouping the fan-in is the associativity half of the same claim.
regroupOk :: Bool
regroupOk = and [treeShape (a <> b <> c) == run mergeRow (run mergeRow (treeShape a, treeShape b), treeShape c) | (a, b, c) <- splits]
  where
    splits = [(take i corpus, take j (drop i corpus), drop (i + j) corpus) | i <- [0, 16, 32], j <- [16, 32, 48], i + j <= length corpus]

bimonoidNetTopic :: Verbosity -> IO [Bool]
bimonoidNetTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Bimonoid net oracles"
  sequence
    [ checkV verbosity "left fold and balanced tree agree on every prefix of 1..64" shapesAgreeOk,
      checkV verbosity "sharded fan-out agrees with the fold" shardAgreesOk,
      checkV verbosity "copy then discard is the identity on either wire" copyDiscardOk,
      checkV verbosity "zero is the empty sum for every shape" zeroOk,
      checkV verbosity "the left-biased merge disagrees (the oracle has teeth)" mutantDisagreesOk,
      checkV verbosity "regrouping the fan-in does not change the result" regroupOk
    ]
