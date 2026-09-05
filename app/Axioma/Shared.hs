{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | Shared-medium scheduling, premonoidal centrality, whiskering, and the
-- impossibility of a canonical 'Yank These' instance.
module Axioma.Shared
  ( sharedTopic,
  )
where

import Axioma.Common
  ( Verbosity (..),
    checkIOV,
    checkV,
    sharedAddP,
    sharedDoubleP,
  )
import Circuit.Category (id, (.), (.>))
import Circuit.Equip (Stamped (..))
import Circuit.Process (Process (..), scanProcessP, scheduleAsProcessP)
import Circuit.Shared (AlgShared, Pick (..), Schedule (..), SigShared (..), sharedBy, transcriptSharedBy)
import Circuit.Shared qualified as Shared
import Circuit.Syntax (Syntax (..), eval)
import Circuit.Syntax qualified as Syn
import Circuit.Tensor (Bias (..), Tensor (..), superpose)
import Circuit.Trace (SigYank (..), Trace, base)
import Circuit.Traced (assoc, assoc', slide, strength, yank)
import Control.Monad (when)
import Data.List (sort)
import Data.These (These (..), these)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

-- | Helper that fixes the cartesian tensor for 'yank' over plain functions.
--
-- The class method needs the 'Trace' tensor to be inferable; this wrapper
-- pins it to @(,)@ via the argument shape.
yankFun :: ((s, a) -> (s, b)) -> Trace (,) (->) a b
yankFun = yank . base

-- | Body that prepends a marker to the shared feedback list and emits the
-- first three elements.  Used to make the shared-medium interleaving observable.
markerBody :: Int -> ([Int], ()) -> ([Int], [Int])
markerBody n (ns, ()) = (n : ns, take 3 ns)

-- | Schedule that always runs the left body first without modifying the shared
-- state.  A pure order braid is invisible to the trace — this is the sliding
-- axiom of the traced category observed at the shared channel.
pureLeft :: Schedule [Int]
pureLeft = Schedule (,Both LeftFirst)

-- | Schedule that always runs the right body first without modifying the shared
-- state.
pureRight :: Schedule [Int]
pureRight = Schedule (,Both RightFirst)

-- | Schedule that always runs the left body first, leaving a neutral schedule
-- token in the shared state so the interleaving is observable.
leftFirst :: Schedule [Int]
leftFirst = Schedule $ \s -> (0 : s, Both LeftFirst)

-- | Schedule that always runs the right body first, leaving the same neutral
-- schedule token so the two orderings remain comparable on body sets.
rightFirst :: Schedule [Int]
rightFirst = Schedule $ \s -> (0 : s, Both RightFirst)

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

sharedTopic :: Verbosity -> IO [Bool]
sharedTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "Shared-medium, centrality, and Channel These oracles"
  sequence
    [ -- Channel These presence-preserving slide
      checkV verbosity "Channel These slide preserves presence on all 7 cases" $
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
      checkV verbosity "Channel These slide . slide == id where types permit" $
        let x = These 'a' (These 'b' 'c' :: These Char Char)
         in (slide . slide) x == (x :: These Char (These Char Char)),
      -- Yank These falsifier: the both-branch forces a discard.
      --
      -- A candidate yank for These must choose, in the These a c case,
      -- whether to emit c (discarding a) or loop on a (discarding c).
      -- Two equally natural biased yanks disagree, so no canonical yank
      -- exists; any fixed bias breaks sliding/dinaturality under composition.
      checkV verbosity "Yank These is impossible: biased yanks disagree in the both-branch" $
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
      -- Free-strength slide placement (Circuit.Trace Strength t (Trace t arr),
      -- YankBody clause). The body is slid out, strengthened, and slid back:
      -- yank (base slide .> strength body .> base slide). The oracle pins the
      -- placement against evaluating first and strengthening at the base: the
      -- two slides sit outside the loop, so a dropped or duplicated slide wires
      -- the payload into the loop channel and the sides disagree. Bodies mix
      -- channel and payload so the placements genuinely differ.
      checkV verbosity "Trace (,) strength: eval-then-strengthen == strengthen-then-eval" $
        let f :: (Int, Int) -> (Int, Int)
            f (s, x) = (x, s + x)
            t :: Trace (,) (->) Int Int
            t = yank (base f)
            -- Mutation room: yank (strength body) without the slides gives
            -- (3,10) here against the true (7,6).
            input = (7, 3)
         in eval (strength t) input == strength (eval t) input,
      checkV verbosity "Trace Either strength: eval-then-strengthen == strengthen-then-eval" $
        let f :: Either Int Int -> Either Int Int
            f (Right n) = Left n
            f (Left 0) = Right 42
            f (Left n) = Left (n - 1)
            t :: Trace Either (->) Int Int
            t = yank (base f)
            -- Different tensor, different slide: the Either slide routes the
            -- outer value to the inner-left loop position. Mutation room:
            -- without the slides the loop below never exits.
            leftOnly = Left 5 :: Either Int Int
            payload = Right 3 :: Either Int Int
         in eval t 3 == 42
              && eval (strength t) leftOnly == strength (eval t) leftOnly
              && eval (strength t) payload == strength (eval t) payload,
      -- tensor/par probe: sharedBy vs superpose
      checkV verbosity "pure order braid is invisible at the shared channel (sliding axiom)" $
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
      -- Gate: Bias = f⋉g / f⋊g means the hand-written products agree with
      -- sharedBy under the constant schedules pureLeft / pureRight.
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
      -- Gate: Bias is the premonoidal ordering iff the whiskerings agree.
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
      -- Centrality oracles: the tensor/par distinction is exactly premonoidal centrality
      -- Centrality witnesses: bodyCentral is a predicate at one input against
      -- one partner. These are existence witnesses, not proofs of ∀g.
      checkV verbosity "state-agnostic bodies witness centrality at a point" $
        let input = (0, (1, 2)) :: (Int, (Int, Int))
         in bodyCentral bodyIdF bodyIncF input,
      checkV verbosity "state-touching bodies witness non-centrality at a point" $
        let input = (1, (2, 3)) :: (Int, (Int, Int))
         in not (bodyCentral sharedAddF sharedDoubleF input),
      -- markerBody writes to the shared state, so these bodies are NOT central.
      -- What this oracle observes: after feedback closure, the two threading
      -- orders produce the same observable output (here, the same rotation of
      -- markers). This is a coincidence of the example, not Benton–Hyland
      -- centrality and not Centre Preservation (Def 3.2 runs the other way).
      checkV verbosity "marker bodies have equal trace under left-first and right-first threading (not centrality)" $
        let k1 = markerBody 1
            k2 = markerBody 2
         in Syn.eval (yankFun (bodyParL k1 k2)) ((), ())
              == Syn.eval (yankFun (bodyParR k1 k2)) ((), ()),
      -- Structural maps are central: they do not touch the shared state,
      -- so order of threading is invisible (Benton–Hyland centrality).
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
      -- The discriminator for the two readings of schedule order-dependence.
      -- Both bodies below read and write the shared channel, yet the orders
      -- agree because the bodies commute.  A reading on which the order
      -- difference is intrinsic to the shared medium predicts disagreement
      -- here; the centrality reading predicts agreement.
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
      -- Free-syntax bridge: AlgShared is the algebraic par connective
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
      -- Receipt transcripts (equip-next phase 7): stamps are the schedule's
      -- picks, payloads are the bodies' outputs.  The stamp at tick i is the
      -- pick made at the pre-step state — the decision that caused the step.
      -- The standalone mark machine reports a state's pick only after
      -- stepping into it, so its stream is the transcript's stream shifted
      -- one tick; the agreement is modulo that phase.
      checkV verbosity "transcript stamps are the standalone pick stream (modulo the post-step phase)" $
        let alt = Schedule (\s -> (s + 1, if odd s then PickL else PickR)) :: Schedule Int
            f :: (Int, Int) -> (Int, Int)
            f (s, a) = (s, a + 100)
            g :: (Int, Int) -> (Int, Int)
            g (s, c) = (s, c * 2)
            ts = transcriptSharedBy alt f g 0 (replicate 4 (1, 1))
            pick0 = snd (chooseS alt 0)
            standalone = scanProcessP (scheduleAsProcessP 0 alt) (replicate 4 ())
         in map stamp ts == init (pick0 : standalone),
      -- The Both payloads are the bodies' solo runs only because these
      -- bodies are state-independent; a state-touching body couples its run
      -- to the shared channel (the centrality oracles above measure exactly
      -- that coupling).
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
      -- The pointing conjecture (equip-next phase 7): marks/stamps are the
      -- value-level shadow of unit cells, and the seeding crossing is the
      -- first stamp.  Witness: two transcripts of the same system differing
      -- only in the seed already differ in receipt at tick 0.
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
              && ts0 /= ts1
    ]
