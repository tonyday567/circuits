{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Axioma.Shared
  ( sharedTopic,
  )
where

import Axioma.Common
  ( Verbosity (..),
    checkV,
  )
import Circuit.Category (id, (.), (.>))
import Circuit.Shared (AlgShared, Pick (..), Schedule (..), SigShared (..), Stamped (..), sharedBy, transcriptSharedBy)
import Circuit.Shared qualified as Shared
import Circuit.Syntax (Syntax (..), eval, (:+:) (..))
import Circuit.Syntax qualified as Syn
import Circuit.Tensor (Bias (..), SemiTensor (..), Tensor, superpose)
import Circuit.Trace (SigYank (..), Trace)
import Circuit.Traced (assoc, assoc', slide, yank)
import Control.Monad (when)
import Data.List (sort)
import Data.These (These (..), these)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

yankFun :: ((s, a) -> (s, b)) -> Trace (,) (->) a b
yankFun = yank . Lift

markerBody :: Int -> ([Int], ()) -> ([Int], [Int])
markerBody n (ns, ()) = (n : ns, take 3 ns)

pureLeft :: Schedule [Int]
pureLeft = Schedule (,Both LeftFirst)

pureRight :: Schedule [Int]
pureRight = Schedule (,Both RightFirst)

leftFirst :: Schedule [Int]
leftFirst = Schedule $ \s -> (0 : s, Both LeftFirst)

rightFirst :: Schedule [Int]
rightFirst = Schedule $ \s -> (0 : s, Both RightFirst)

sharedAddF :: (Int, Int) -> (Int, Int)
sharedAddF (s, a) = let s' = s + a in (s', s')

sharedDoubleF :: (Int, Int) -> (Int, Int)
sharedDoubleF (s, _c) = let s' = s * 2 in (s', s')

bodyIdF :: (Int, Int) -> (Int, Int)
bodyIdF (s, a) = (s, a)

bodyIncF :: (Int, Int) -> (Int, Int)
bodyIncF (s, c) = (s, c + 1)

bodyParL :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, These b d))
bodyParL f g (s, (a, c)) =
  let (s', b) = f (s, a)
      (s'', d) = g (s', c)
   in (s'', These b d)

bodyParR :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, These b d))
bodyParR f g (s, (a, c)) =
  let (s', d) = g (s, c)
      (s'', b) = f (s', a)
   in (s'', These b d)

bodyCentral :: (Eq s, Eq b, Eq d) => ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> (s, (a, c)) -> Bool
bodyCentral f g input = bodyParL f g input == bodyParR f g input

whiskerL :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, (b, d)))
whiskerL f g =
  assoc' @(,) @(->)
    .> tensor @(,) @(->) f id
    .> assoc @(,) @(->)
    .> slide @(,) @(->)
    .> tensor @(,) @(->) id g
    .> slide @(,) @(->)

whiskerR :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, (b, d)))
whiskerR f g =
  slide @(,) @(->)
    .> tensor @(,) @(->) id g
    .> slide @(,) @(->)
    .> assoc' @(,) @(->)
    .> tensor @(,) @(->) f id
    .> assoc @(,) @(->)

liftBody :: (a -> b) -> (s, a) -> (s, b)
liftBody f (s, a) = (s, f a)

sharedAddFPair :: (Int, (Int, Int)) -> (Int, (Int, Int))
sharedAddFPair (s, (a, b)) = let s' = s + a + b in (s', (s', s'))

sharedTopic :: Verbosity -> IO [Bool]
sharedTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Shared-medium scheduling, centrality, and receipt oracles"
  sequence
    [ checkV verbosity "pure order braid is invisible at the shared channel (sliding axiom)" $
        let k1 = markerBody 1
            k2 = markerBody 2
         in Syn.eval (yankFun (sharedBy pureLeft k1 k2)) ((), ())
              == Syn.eval (yankFun (sharedBy pureRight k1 k2)) ((), ()),
      checkV verbosity "sharedBy differs from superpose (shared vs independent feedback)" $
        let k1 = markerBody 1
            k2 = markerBody 2
            theseToPair (This a) = (a, [])
            theseToPair (That b) = ([], b)
            theseToPair (These a b) = (a, b)
         in Syn.eval (superpose (yankFun k1) (yankFun k2)) ((), ())
              /= theseToPair (Syn.eval (yankFun (sharedBy leftFirst k1 k2)) ((), ())),
      checkV verbosity "sharedBy schedule changes observable interleaving" $
        let k1 = markerBody 1
            k2 = markerBody 2
         in Syn.eval (yankFun (sharedBy rightFirst k1 k2)) ((), ())
              /= Syn.eval (yankFun (sharedBy leftFirst k1 k2)) ((), ()),
      checkV verbosity "sharedBy Both LeftFirst equals premonoidal left-first product" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
         in sharedBy (Schedule (,Both LeftFirst) :: Schedule [Int]) k1 k2 input == bodyParL k1 k2 input,
      checkV verbosity "sharedBy Both RightFirst equals premonoidal right-first product" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
         in sharedBy (Schedule (,Both RightFirst) :: Schedule [Int]) k1 k2 input == bodyParR k1 k2 input,
      checkV verbosity "bodyParL equals sharedBy under pureLeft" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
         in bodyParL k1 k2 input == sharedBy pureLeft k1 k2 input,
      checkV verbosity "bodyParR equals sharedBy under pureRight" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
         in bodyParR k1 k2 input == sharedBy pureRight k1 k2 input,
      checkV verbosity "left-first whiskering equals bodyParL" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
            (s, (b, d)) = whiskerL k1 k2 input
         in (s, These b d) == bodyParL k1 k2 input,
      checkV verbosity "right-first whiskering equals bodyParR" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
            (s, (b, d)) = whiskerR k1 k2 input
         in (s, These b d) == bodyParR k1 k2 input,
      checkV verbosity "state-agnostic bodies witness centrality at a point" $
        let input = (0, (1, 2)) :: (Int, (Int, Int))
         in bodyCentral bodyIdF bodyIncF input,
      checkV verbosity "state-touching bodies witness non-centrality at a point" $
        let input = (1, (2, 3)) :: (Int, (Int, Int))
         in not (bodyCentral sharedAddF sharedDoubleF input),
      checkV verbosity "marker bodies have equal trace under left-first and right-first threading (not centrality)" $
        let k1 = markerBody 1
            k2 = markerBody 2
         in Syn.eval (yankFun (bodyParL k1 k2)) ((), ())
              == Syn.eval (yankFun (bodyParR k1 k2)) ((), ()),
      checkV verbosity "copy witnesses centrality wrt state-touching body at a point" $
        let input = (0, (1, 2)) :: (Int, (Int, Int))
         in bodyCentral (liftBody (\x -> (x, x))) sharedAddF input,
      checkV verbosity "discard witnesses centrality wrt state-touching body at a point" $
        let input = (0, (1, 2)) :: (Int, (Int, Int))
         in bodyCentral (liftBody (const ())) sharedAddF input,
      checkV verbosity "plus witnesses centrality wrt state-touching body at a point" $
        let input = (0, ((1, 2), 3)) :: (Int, ((Int, Int), Int))
         in bodyCentral (liftBody (Pre.uncurry (+))) sharedAddF input,
      checkV verbosity "zero witnesses centrality wrt state-touching body at a point" $
        let input = (0, ((), 3)) :: (Int, ((), Int))
         in bodyCentral (liftBody (const (0 :: Int))) sharedAddF input,
      checkV verbosity "braid witnesses centrality wrt state-touching body at a point" $
        let input = (0, ((1, 2), (3, 4))) :: (Int, ((Int, Int), (Int, Int)))
         in bodyCentral (liftBody (\(a, b) -> (b, a))) sharedAddFPair input,
      checkV verbosity "commuting channel-touching bodies are order-invisible under sharedBy (discriminator)" $
        let addF :: (Int, Int) -> (Int, Int)
            addF (s, a) = (s + a, a)
            addG :: (Int, Int) -> (Int, Int)
            addG (s, c) = (s + c, c)
            input = (0, (3, 5)) :: (Int, (Int, Int))
         in sharedBy (Schedule (,Both LeftFirst) :: Schedule Int) addF addG input
              == sharedBy (Schedule (,Both RightFirst) :: Schedule Int) addF addG input,
      checkV verbosity "sharedBy L gates right body (output is This only)" $
        let k1 = markerBody 1
            k2 = markerBody 2
            leftOnly = Schedule (,Shared.PickL) :: Schedule [Int]
         in Syn.eval (yankFun (sharedBy leftOnly k1 k2)) ((), ()) == This [1, 1, 1],
      checkV verbosity "sharedBy R gates left body (output is That only)" $
        let k1 = markerBody 1
            k2 = markerBody 2
            rightOnly = Schedule (,Shared.PickR) :: Schedule [Int]
         in Syn.eval (yankFun (sharedBy rightOnly k1 k2)) ((), ()) == That [2, 2, 2],
      checkV verbosity "sharedBy left-first and right-first both agree on body sets" $
        let k1 = markerBody 1
            k2 = markerBody 2
            leftResult = Syn.eval (yankFun (sharedBy leftFirst k1 k2)) ((), ())
            rightResult = Syn.eval (yankFun (sharedBy rightFirst k1 k2)) ((), ())
            bodySet = sort . these id id (++)
         in bodySet leftResult == [0, 0, 1, 1, 2, 2]
              && bodySet rightResult == [0, 0, 1, 1, 2, 2],
      checkV verbosity "AlgShared Syn.eval agrees with sharedBy" $
        let k1 = markerBody 1
            k2 = markerBody 2
            term :: AlgShared (,) (->) ((), ()) (These [Int] [Int])
            term =
              Oper
                ( Syn.R
                    ( Syn.R
                        ( YankBody
                            ( Oper
                                ( Syn.R
                                    (Syn.L (SigShared pureLeft (Lift k1) (Lift k2)))
                                )
                            )
                        )
                    )
                )
         in eval term ((), ()) == Syn.eval (yankFun (sharedBy pureLeft k1 k2)) ((), ()),
      checkV verbosity "AlgShared L schedule gates right body" $
        let k1 = markerBody 1
            k2 = markerBody 2
            leftOnly = Schedule (,Shared.PickL) :: Schedule [Int]
            term :: AlgShared (,) (->) ((), ()) (These [Int] [Int])
            term =
              Oper
                ( Syn.R
                    ( Syn.R
                        ( YankBody
                            ( Oper
                                ( Syn.R
                                    (Syn.L (SigShared leftOnly (Lift k1) (Lift k2)))
                                )
                            )
                        )
                    )
                )
         in eval term ((), ()) == This [1, 1, 1],
      checkV verbosity "AlgShared R schedule gates left body" $
        let k1 = markerBody 1
            k2 = markerBody 2
            rightOnly = Schedule (,Shared.PickR) :: Schedule [Int]
            term :: AlgShared (,) (->) ((), ()) (These [Int] [Int])
            term =
              Oper
                ( Syn.R
                    ( Syn.R
                        ( YankBody
                            ( Oper
                                ( Syn.R
                                    (Syn.L (SigShared rightOnly (Lift k1) (Lift k2)))
                                )
                            )
                        )
                    )
                )
         in eval term ((), ()) == That [2, 2, 2],
      checkV verbosity "transcript stamps are the schedule's picks at the pre-step states" $
        let alt = Schedule (\s -> (s + 1, if odd s then PickL else PickR)) :: Schedule Int
            f :: (Int, Int) -> (Int, Int)
            f (s, a) = (s, a + 100)
            g :: (Int, Int) -> (Int, Int)
            g (s, c) = (s, c * 2)
            ts = transcriptSharedBy alt f g 0 (replicate 4 (1, 1))
            preStates = take 5 (iterate (fst . chooseS alt) 0)
            picks = map (snd . chooseS alt) preStates
         in map stamp ts == take 4 picks,
      checkV verbosity "transcript payloads are the solo runs (state-independent bodies, Both schedule)" $
        let bothFirst = Schedule (\s -> (s, Both LeftFirst)) :: Schedule Int
            f :: (Int, Int) -> (Int, Int)
            f (s, a) = (s, a + 100)
            g :: (Int, Int) -> (Int, Int)
            g (s, c) = (s, c * 2)
            ts = transcriptSharedBy bothFirst f g 0 [(1, 10), (2, 20), (3, 30)]
            solo :: ((s, a) -> (s, b)) -> s -> [a] -> [b]
            solo _ _ [] = []
            solo h s (x : xs) = let (s', y) = h (s, x) in y : solo h s' xs
         in map stamp ts == [Both LeftFirst, Both LeftFirst, Both LeftFirst]
              && map stamped ts
                == zipWith These (solo f 0 [1, 2, 3]) (solo g 0 [10, 20, 30]),
      checkV verbosity "the seed is the first stamp: seed difference shows from tick 0" $
        let alt = Schedule (\s -> (s + 1, if odd s then PickL else PickR)) :: Schedule Int
            f :: (Int, Int) -> (Int, Int)
            f (s, a) = (s, a + 100)
            g :: (Int, Int) -> (Int, Int)
            g (s, c) = (s, c * 2)
            ts0 = transcriptSharedBy alt f g 0 (replicate 2 (1, 1))
            ts1 = transcriptSharedBy alt f g 1 (replicate 2 (1, 1))
         in map stamp ts0 == [PickR, PickL]
              && map stamp ts1 == [PickL, PickR]
              && ts0 /= ts1,
      checkV verbosity "Stamped fmap preserves stamp (Int token)" $
        let s = Stamped 7 ("hello" :: String)
         in stamp (fmap reverse s) == (7 :: Int) && stamped (fmap reverse s) == "olleh",
      checkV verbosity "Stamped fmap preserves stamp (Bool token)" $
        let s = Stamped True (10 :: Int)
         in stamp (fmap (+ 1) s) && stamped (fmap (+ 1) s) == 11
    ]
