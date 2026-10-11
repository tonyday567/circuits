module Axioma.BiK
  ( biKTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Category (BiK (..), Dist (..), K (..), id, (.))
import Circuit.Machine (Body (..), bodyBiK)
import Circuit.Traced (Strength (..))
import Control.Monad (when)
import Prelude hiding (id, (.))

grid :: [(Int, Int)]
grid = [(s, a) | s <- [1, 2, 3], a <- [0, 7]]

stageFRaw :: (Int, Int) -> [Int]
stageFRaw (s, a) = [a + s, a - s]

stageGRaw :: (Int, Int) -> [Int]
stageGRaw (s, a) = [a * s, a + s + 1]

stageHRaw :: (Int, Int) -> [Int]
stageHRaw (s, a) = [s - a, a * s]

stageF :: BiK ((,) Int) [] Int Int
stageF = BiK stageFRaw

stageG :: BiK ((,) Int) [] Int Int
stageG = BiK stageGRaw

stageH :: BiK ((,) Int) [] Int Int
stageH = BiK stageHRaw

stageBlind :: BiK ((,) Int) [] Int Int
stageBlind = BiK (\(_, a) -> [a + 1, a + 2])

rightIdentityOk :: Bool
rightIdentityOk = all (\sa -> runBiK (stageF . id) sa == runBiK stageF sa) grid

rightIdentitySmellOk :: Bool
rightIdentitySmellOk = all (\sa -> runBiK (stageBlind . id) sa == runBiK stageBlind sa) grid

leftIdentityOk :: Bool
leftIdentityOk = all (\sa -> runBiK (id . stageF) sa == runBiK stageF sa) grid

associativityOk :: Bool
associativityOk =
  all (\sa -> runBiK ((stageH . stageG) . stageF) sa == runBiK (stageH . (stageG . stageF)) sa) grid

composeWith ::
  ((Int, [Int]) -> [(Int, Int)]) ->
  ((Int, Int) -> [Int]) ->
  ((Int, Int) -> [Int]) ->
  (Int, Int) ->
  [Int]
composeWith d g f (s, a) =
  let mws = d (s, f (s, a))
   in concatMap (\(s', y) -> g (s', y)) mws

leftIdentityMutationRed :: Bool
leftIdentityMutationRed =
  let rev (s, xs) = [(s, x) | x <- reverse xs]
      lhs = composeWith rev (\(_, b) -> [b]) stageFRaw
      rhs = stageFRaw
   in any (\sa -> lhs sa /= rhs sa) grid

associativityMutationRed :: Bool
associativityMutationRed =
  let rev (s, xs) = [(s, x) | x <- reverse xs]
      lhs = composeWith rev (composeWith rev stageHRaw stageGRaw) stageFRaw
      rhs = composeWith rev stageHRaw (composeWith rev stageGRaw stageFRaw)
   in any (\sa -> lhs sa /= rhs sa) grid

spendMaybeOk :: Bool
spendMaybeOk =
  all (\(s, ma) -> dist (s, ma) == runK (strength (K id)) (s, ma)) space
  where
    space :: [(Int, Maybe Int)]
    space = [(s, ma) | s <- [0, 2], ma <- [Nothing, Just 4, Just 9]]

spendListOk :: Bool
spendListOk =
  all (\(s, ma) -> dist (s, ma) == runK (strength (K id)) (s, ma)) space
  where
    space :: [(Int, [Int])]
    space = [(s, ma) | s <- [0, 2], ma <- [[], [4], [4, 9 :: Int]]]

jermaineEitherOk :: Bool
jermaineEitherOk =
  runBiK (stageTwo . stageOne) (5, 0) == Left 6
  where
    -- init is dead weight here: the BiK arrow sees only commit and emit.
    stageOne =
      bodyBiK
        ( Body
            id
            (\(s, _) -> s + 1)
            (\s -> Left s) ::
            Body (,) Either Int Int (->) Int Int
        )
    stageTwo = bodyBiK (Body id (\(s, _) -> s * 2) (\s -> Right (s + 100)))

biKTopic :: Verbosity -> IO [Bool]
biKTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "BiK oracles"
  sequence
    [ checkV verbosity "right identity: a state-reading stage at three states; a state-blind dist routes every read to 0 and fails this clause" rightIdentityOk,
      checkV verbosity "right identity smell: a state-blind stage passes here and is the defined-to-pass shape the main clause must not stand alone" rightIdentitySmellOk,
      checkV verbosity "left identity: an order-permuting dist reverses the stage list and fails this clause" leftIdentityOk,
      checkV verbosity "left identity mutation: the order-reversing dist goes red on this witness" leftIdentityMutationRed,
      checkV verbosity "associativity: two branches per stage, every stage reading s, over lists" associativityOk,
      checkV verbosity "associativity mutation: the order-reversing dist goes red on this witness" associativityMutationRed,
      checkV verbosity "spend: dist == strength (K id) at Maybe, over Nothing and two Justs" spendMaybeOk,
      checkV verbosity "spend: dist == strength (K id) at lists, over the empty list and two nonempties" spendListOk,
      checkV verbosity "jermaine row at Either: stage one's Left short-circuits the composite; a fall-through reaches stage two and fails this clause" jermaineEitherOk
    ]
