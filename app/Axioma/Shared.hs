{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Shared-medium scheduling, premonoidal centrality, whiskering, and the
-- impossibility of a canonical 'Traced These' instance.
module Axioma.Shared
  ( sharedTopic,
  )
where

import Axioma.Common
  ( checkIO,
    sharedAddP,
    sharedDoubleP,
  )
import Circuit.Category (id, (.), (.>))
import Circuit.Channel (assoc, assoc', slide)
import Circuit.Process (Process (..))
import Circuit.Shared (AlgShared, Pick (Both), Schedule (..), SigShared (..), sharedBy)
import Circuit.Shared qualified as Shared
import Circuit.Syntax (Syntax (..), eval)
import Circuit.Syntax qualified as Syn
import Circuit.Tensor (Tensor (..), superpose)
import Circuit.Tools.Test (check)
import Circuit.Trace (SigYank (..), Trace, base, yank)
import Data.List (sort)
import Data.These (These (..), these)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

-- | Body that prepends a marker to the shared feedback list and emits the
-- first three elements.  Used to make the shared-medium interleaving observable.
markerBody :: Int -> ([Int], ()) -> ([Int], [Int])
markerBody n (ns, ()) = (n : ns, take 3 ns)

-- | Schedule that always runs the left body first without modifying the shared
-- state.  A pure order braid is invisible to the trace — this is the sliding
-- axiom of the traced category observed at the shared channel.
pureLeft :: Schedule [Int]
pureLeft = Schedule (,Both Shared.LeftFirst)

-- | Schedule that always runs the right body first without modifying the shared
-- state.
pureRight :: Schedule [Int]
pureRight = Schedule (,Both Shared.RightFirst)

-- | Schedule that always runs the left body first, leaving a neutral schedule
-- token in the shared state so the interleaving is observable.
leftFirst :: Schedule [Int]
leftFirst = Schedule $ \s -> (0 : s, Both Shared.LeftFirst)

-- | Schedule that always runs the right body first, leaving the same neutral
-- schedule token so the two orderings remain comparable on body sets.
rightFirst :: Schedule [Int]
rightFirst = Schedule $ \s -> (0 : s, Both Shared.RightFirst)

-- | Function counterpart of 'sharedAddP' for premonoidal centrality tests.
sharedAddF :: (Int, Int) -> (Int, Int)
sharedAddF (s, a) = let s' = s + a in (s', s')

-- | Function counterpart of 'sharedDoubleP' for premonoidal centrality tests.
sharedDoubleF :: (Int, Int) -> (Int, Int)
sharedDoubleF (s, _c) = let s' = s * 2 in (s', s')

-- | State-agnostic body: passes payload through unchanged.
bodyIdF :: (Int, Int) -> (Int, Int)
bodyIdF (s, a) = (s, a)

-- | State-agnostic body: increments the right payload, leaves state alone.
bodyIncF :: (Int, Int) -> (Int, Int)
bodyIncF (s, c) = (s, c + 1)

-- | Premonoidal left-first product of two knot bodies.
--
-- This is the composite @(f ⊗ id) ; (id ⊗ g)@ in the category of knot bodies
-- @Body (,) s (->)@.  It threads the shared state through @f@ first, then @g@.
bodyParL :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, These b d))
bodyParL f g (s, (a, c)) =
  let (s', b) = f (s, a)
      (s'', d) = g (s', c)
   in (s'', These b d)

-- | Premonoidal right-first product of two knot bodies.
--
-- This is the composite @(id ⊗ g) ; (f ⊗ id)@.  It threads the shared state
-- through @g@ first, then @f@.
bodyParR :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, These b d))
bodyParR f g (s, (a, c)) =
  let (s', d) = g (s, c)
      (s'', b) = f (s', a)
   in (s'', These b d)

-- | Centrality of two knot bodies at a chosen input.
--
-- Two bodies are central when the premonoidal left-first and right-first
-- products agree.  For the cartesian instance @Body (,) s (->)@ this is the
-- statement that order of state threading is invisible.
bodyCentral :: (Eq s, Eq b, Eq d) => ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> (s, (a, c)) -> Bool
bodyCentral f g input = bodyParL f g input == bodyParR f g input

-- | Premonoidal left-first whiskering built from assoc / slide / first.
--
-- This is the composite @(f ⊗ id) ; (id ⊗ g)@ expressed with the cartesian
-- structural maps.  It threads state through @f@ first, then @g@.
whiskerL :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, (b, d)))
whiskerL f g =
  assoc' @(,) @(->)
    .> tensor @(,) @(->) f id
    .> assoc @(,) @(->)
    .> slide @(,) @(->)
    .> tensor @(,) @(->) id g
    .> slide @(,) @(->)

-- | Premonoidal right-first whiskering built from assoc / slide / first.
--
-- This is the composite @(id ⊗ g) ; (f ⊗ id)@.
whiskerR :: ((s, a) -> (s, b)) -> ((s, c) -> (s, d)) -> ((s, (a, c)) -> (s, (b, d)))
whiskerR f g =
  slide @(,) @(->)
    .> tensor @(,) @(->) id g
    .> slide @(,) @(->)
    .> assoc' @(,) @(->)
    .> tensor @(,) @(->) f id
    .> assoc @(,) @(->)

-- | Lift a payload map to a body that leaves shared state alone.
--
-- Such bodies are exactly the structural maps of the underlying category
-- threaded through the ambient state wire.
liftBody :: (a -> b) -> (s, a) -> (s, b)
liftBody f (s, a) = (s, f a)

-- | State-touching body with a pair payload: adds both components to state.
sharedAddFPair :: (Int, (Int, Int)) -> (Int, (Int, Int))
sharedAddFPair (s, (a, b)) = let s' = s + a + b in (s', (s', s'))

sharedTopic :: IO [Bool]
sharedTopic = do
  putStrLn "Shared-medium, centrality, and Channel These oracles"
  sequence
    [ -- Channel These presence-preserving slide
      check "Channel These slide preserves presence on all 7 cases" $
        let presenceInput :: These Char (These Char Char) -> (Bool, Bool, Bool)
            presenceInput = \case
              This _ -> (True, False, False)
              That (This _) -> (False, True, False)
              That (That _) -> (False, False, True)
              That (These _ _) -> (False, True, True)
              These _ (This _) -> (True, True, False)
              These _ (That _) -> (True, False, True)
              These _ (These _ _) -> (True, True, True)
            presenceOutput :: These Char (These Char Char) -> (Bool, Bool, Bool)
            presenceOutput = \case
              This _ -> (False, True, False)
              That (This _) -> (True, False, False)
              That (That _) -> (False, False, True)
              That (These _ _) -> (True, False, True)
              These _ (This _) -> (True, True, False)
              These _ (That _) -> (False, True, True)
              These _ (These _ _) -> (True, True, True)
            cases :: [These Char (These Char Char)]
            cases =
              [ This 'a',
                That (This 'b'),
                That (That 'c'),
                That (These 'b' 'c'),
                These 'a' (This 'b'),
                These 'a' (That 'c'),
                These 'a' (These 'b' 'c')
              ]
         in all (\x -> presenceInput x == presenceOutput (slide x)) cases,
      check "Channel These slide . slide == id where types permit" $
        let x = These 'a' (These 'b' 'c' :: These Char Char)
         in (slide . slide) x == (x :: These Char (These Char Char)),
      -- Traced These falsifier: the both-branch forces a discard.
      --
      -- A candidate trace for These must choose, in the These a c case,
      -- whether to emit c (discarding a) or loop on a (discarding c).
      -- Two equally natural biased traces disagree, so no canonical trace
      -- exists; any fixed bias breaks sliding/dinaturality under composition.
      check "Traced These is impossible: biased traces disagree in the both-branch" $
        let traceTheseEmit f b = go (f (That b))
              where
                go (That c) = c
                go (This a) = go (f (This a))
                go (These _ c) = c
            traceTheseLoop f b = go (f (That b))
              where
                go (That c) = c
                go (This a) = go (f (This a))
                go (These a _) = go (f (This a))
            step :: These Int Int -> These Int Int
            step (That n) = These 1 n
            step (This 0) = That 0
            step (This n) = This (n - 1)
            step (These m n) = These (m + 1) n
         in traceTheseEmit step 5 /= traceTheseLoop step 5,
      -- tensor/par probe: sharedBy vs superpose
      check "pure order braid is invisible at the shared channel (sliding axiom)" $
        let k1 = markerBody 1
            k2 = markerBody 2
         in Syn.eval (yank (base (sharedBy pureLeft k1 k2))) ((), ())
              == Syn.eval (yank (base (sharedBy pureRight k1 k2))) ((), ()),
      check "sharedBy differs from superpose (shared vs independent feedback)" $
        let k1 = markerBody 1
            k2 = markerBody 2
            theseToPair (This a) = (a, [])
            theseToPair (That b) = ([], b)
            theseToPair (These a b) = (a, b)
         in Syn.eval (superpose (yank (base k1)) (yank (base k2))) ((), ())
              /= theseToPair (Syn.eval (yank (base (sharedBy leftFirst k1 k2))) ((), ())),
      check "sharedBy schedule changes observable interleaving" $
        let k1 = markerBody 1
            k2 = markerBody 2
         in Syn.eval (yank (base (sharedBy rightFirst k1 k2))) ((), ())
              /= Syn.eval (yank (base (sharedBy leftFirst k1 k2))) ((), ()),
      check "sharedBy Both LeftFirst equals premonoidal left-first product" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
         in sharedBy (Schedule (,Both Shared.LeftFirst) :: Schedule [Int]) k1 k2 input == bodyParL k1 k2 input,
      check "sharedBy Both RightFirst equals premonoidal right-first product" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
         in sharedBy (Schedule (,Both Shared.RightFirst) :: Schedule [Int]) k1 k2 input == bodyParR k1 k2 input,
      -- Gate: Bias = f⋉g / f⋊g means the hand-written products agree with
      -- sharedBy under the constant schedules pureLeft / pureRight.
      check "bodyParL equals sharedBy under pureLeft" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
         in bodyParL k1 k2 input == sharedBy pureLeft k1 k2 input,
      check "bodyParR equals sharedBy under pureRight" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
         in bodyParR k1 k2 input == sharedBy pureRight k1 k2 input,
      -- Gate: Bias is the premonoidal ordering iff the whiskerings agree.
      check "left-first whiskering equals bodyParL" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
            (s, (b, d)) = whiskerL k1 k2 input
         in (s, These b d) == bodyParL k1 k2 input,
      check "right-first whiskering equals bodyParR" $
        let k1 = markerBody 1
            k2 = markerBody 2
            input = ([], ((), ())) :: ([Int], ((), ()))
            (s, (b, d)) = whiskerR k1 k2 input
         in (s, These b d) == bodyParR k1 k2 input,
      -- Centrality oracles: the tensor/par distinction is exactly premonoidal centrality
      -- Centrality witnesses: bodyCentral is a predicate at one input against
      -- one partner. These are existence witnesses, not proofs of ∀g.
      check "state-agnostic bodies witness centrality at a point" $
        let input = (0, (1, 2)) :: (Int, (Int, Int))
         in bodyCentral bodyIdF bodyIncF input,
      check "state-touching bodies witness non-centrality at a point" $
        let input = (1, (2, 3)) :: (Int, (Int, Int))
         in not (bodyCentral sharedAddF sharedDoubleF input),
      -- markerBody writes to the shared state, so these bodies are NOT central.
      -- What this oracle observes: after feedback closure, the two threading
      -- orders produce the same observable output (here, the same rotation of
      -- markers). This is a coincidence of the example, not Benton–Hyland
      -- centrality and not Centre Preservation (Def 3.2 runs the other way).
      check "marker bodies have equal trace under left-first and right-first threading (not centrality)" $
        let k1 = markerBody 1
            k2 = markerBody 2
         in Syn.eval (yank (base (bodyParL k1 k2))) ((), ())
              == Syn.eval (yank (base (bodyParR k1 k2))) ((), ()),
      -- Structural maps are central: they do not touch the shared state,
      -- so order of threading is invisible (Benton–Hyland centrality).
      check "copy witnesses centrality wrt state-touching body at a point" $
        let input = (0, (1, 2)) :: (Int, (Int, Int))
         in bodyCentral (liftBody (\x -> (x, x))) sharedAddF input,
      check "discard witnesses centrality wrt state-touching body at a point" $
        let input = (0, (1, 2)) :: (Int, (Int, Int))
         in bodyCentral (liftBody (const ())) sharedAddF input,
      check "plus witnesses centrality wrt state-touching body at a point" $
        let input = (0, ((1, 2), 3)) :: (Int, ((Int, Int), Int))
         in bodyCentral (liftBody (Pre.uncurry (+))) sharedAddF input,
      check "zero witnesses centrality wrt state-touching body at a point" $
        let input = (0, ((), 3)) :: (Int, ((), Int))
         in bodyCentral (liftBody (const (0 :: Int))) sharedAddF input,
      check "braid witnesses centrality wrt state-touching body at a point" $
        let input = (0, ((1, 2), (3, 4))) :: (Int, ((Int, Int), (Int, Int)))
         in bodyCentral (liftBody (\(a, b) -> (b, a))) sharedAddFPair input,
      check "sharedBy L gates right body (output is This only)" $
        let k1 = markerBody 1
            k2 = markerBody 2
            leftOnly = Schedule (,Shared.L) :: Schedule [Int]
         in Syn.eval (yank (base (sharedBy leftOnly k1 k2))) ((), ()) == This [1, 1, 1],
      check "sharedBy R gates left body (output is That only)" $
        let k1 = markerBody 1
            k2 = markerBody 2
            rightOnly = Schedule (,Shared.R) :: Schedule [Int]
         in Syn.eval (yank (base (sharedBy rightOnly k1 k2))) ((), ()) == That [2, 2, 2],
      check "sharedBy left-first and right-first both agree on body sets" $
        let k1 = markerBody 1
            k2 = markerBody 2
            leftResult = Syn.eval (yank (base (sharedBy leftFirst k1 k2))) ((), ())
            rightResult = Syn.eval (yank (base (sharedBy rightFirst k1 k2))) ((), ())
            bodySet = sort . these id id (++)
         in bodySet leftResult == [0, 0, 1, 1, 2, 2]
              && bodySet rightResult == [0, 0, 1, 1, 2, 2],
      -- Free-syntax bridge: AlgShared is the algebraic par connective
      check "AlgShared Syn.eval agrees with sharedBy" $
        let k1 = markerBody 1
            k2 = markerBody 2
            term :: AlgShared (,) (->) ((), ()) (These [Int] [Int])
            term =
              Op
                ( Syn.R
                    ( Syn.R
                        ( Yank
                            ( Op
                                ( Syn.R
                                    (Syn.L (SigShared pureLeft (Lift k1) (Lift k2)))
                                )
                            )
                        )
                    )
                )
         in eval term ((), ()) == Syn.eval (yank (base (sharedBy pureLeft k1 k2))) ((), ()),
      check "AlgShared L schedule gates right body" $
        let k1 = markerBody 1
            k2 = markerBody 2
            leftOnly = Schedule (,Shared.L) :: Schedule [Int]
            term :: AlgShared (,) (->) ((), ()) (These [Int] [Int])
            term =
              Op
                ( Syn.R
                    ( Syn.R
                        ( Yank
                            ( Op
                                ( Syn.R
                                    (Syn.L (SigShared leftOnly (Lift k1) (Lift k2)))
                                )
                            )
                        )
                    )
                )
         in eval term ((), ()) == This [1, 1, 1],
      check "AlgShared R schedule gates left body" $
        let k1 = markerBody 1
            k2 = markerBody 2
            rightOnly = Schedule (,Shared.R) :: Schedule [Int]
            term :: AlgShared (,) (->) ((), ()) (These [Int] [Int])
            term =
              Op
                ( Syn.R
                    ( Syn.R
                        ( Yank
                            ( Op
                                ( Syn.R
                                    (Syn.L (SigShared rightOnly (Lift k1) (Lift k2)))
                                )
                            )
                        )
                    )
                )
         in eval term ((), ()) == That [2, 2, 2]
    ]
