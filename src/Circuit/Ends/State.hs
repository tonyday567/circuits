{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Pole-unfused mediators and polynomial machines as channel ends over 'SArr'.
--
-- This module is now a conversions layer over 'Circuit.Body': it takes the
-- cartesian ambient-state arrow 'SArr' and the 'Circuit.Ends' companion/conjoint
-- split, and exposes 'Med', 'System', and 'Machine' as different ways to write
-- the same stateful morphism.
--
-- The core knot-body category lives in 'Circuit.Body'.
module Circuit.Ends.State
  ( -- * Re-exports from 'Circuit.Body'
    SArr (..),
    SomeSArr (..),
    runSomeSArr,
    processToSomeSArr,
    Body (..),
    SomeBody (..),
    bodyToLoop,
    bodyToSArr,
    sArrToBody,
    processToBody,
    loopToSomeSArr,
    loopEitherToSomeSArr,

    -- * Pole-unfused mediator
    Med (..),
    medToEnds,
    medFromEnds,
    medStep,
    medStepDirect,
    runMed,

    -- * System / Machine as channel ends
    SomeEnds (..),
    runSomeEnds,
    systemToEnds,
    machineToEnds,

    -- * Mediate view
    mediatorToMed,
    medToMediator,

    -- * Reusable mediator configurations
    medLinear,
    medPairSum,
    medCount,

    -- * Re-exported residual types
    Mediate.PS (..),
  )
where

import Circuit.Body
  ( Body (..),
    SArr (..),
    SomeBody (..),
    SomeSArr (..),
    bodyToLoop,
    bodyToSArr,
    loopEitherToSomeSArr,
    loopToSomeSArr,
    runSomeSArr,
    sArrToBody,
  )
import Circuit.Category (Category (..), Discrete (..), (.>))
import Circuit.Ends (Ends (..), HasDual (..), In (..), Out (..), close, emit, ends0, splay0)
import Circuit.Mediate qualified as Mediate
import Circuit.Poly (Dir, Pos, System, SystemEval (..), runSystem, system)
import Circuit.Process (Machine (..), Process (..))
import Data.Maybe (catMaybes)
import Prelude hiding (id, (.))

-- | Unit ends for @SArr s@ at the unit object @()@.
--
-- The companion discards its input and returns @()@; the conjoint delegates
-- to the companion. Yanking recovers the identity on @()@.
--
-- This instance is technically orphan because 'SArr' now lives in
-- 'Circuit.Body', but keeping it here keeps the 'Ends' plumbing local to this
-- conversions module.
instance HasDual () (SArr s) where
  open =
    let outU = Out $ \_ -> SArr $ \(s, _) -> (s, ())
        inU = In $ \o -> emit o inU
     in Ends inU outU

-- | View a 'Process' as a knot body over the 'Either' tensor.
--
-- This is the same body used by 'Circuit.Process.encode', now exposed as a value
-- of @Body Either (->) s@. It confirms the Process / Loop Either round-trip
-- factors through the knot-body category.
processToBody :: Process a b -> SomeBody Either (->) [a] [b]
processToBody (Process inject step extract) =
  SomeBody (Nothing, [], []) $ Body $ \case
    Right [] -> Right []
    Right (a : as) ->
      let s0 = inject a
       in Left (Just s0, as, [extract s0])
    Left (_, [], bs) -> Right (reverse bs)
    Left (Just s, a : as, bs) ->
      let s' = step s a
       in Left (Just s', as, extract s' : bs)
    Left (Nothing, _, _) -> error "processToBody: feedback reached before first input"

-- | View a 'Process' as an existentially-quantified 'SArr'.
--
-- The process state is exposed as the ambient wire.  The initial state is
-- 'Nothing'; the first input is fed to 'inject' to create the real state, and
-- subsequent inputs use 'step'.  The output is always 'extract' of the current
-- state.
processToSomeSArr :: Process a b -> SomeSArr a b
processToSomeSArr (Process inject step extract) =
  SomeSArr Nothing $ SArr $ \case
    (Nothing, a) ->
      let s = inject a
       in (Just s, extract s)
    (Just s, a) ->
      let s' = step s a
       in (Just s', extract s')

-- | A pole-unfused mediator with residual state @s@, input @a@, output @b@.
--
-- * @medIn@ is the write pole: it consumes an input together with the current
--   residual and updates the residual.
-- * @medOut@ is the read pole: it observes the residual and may emit an output,
--   updating the residual again.
-- * @medStep@ is the sequential composition of the two poles, recovered as
--   'close' on the unit ends.
data Med s a b = Med
  { -- | Initial residual state.
    medSeed :: s,
    -- | Write pole: consume input, update residual.
    medIn :: (s, a) -> s,
    -- | Read pole: observe residual, optionally emit output.
    medOut :: s -> (s, Maybe b)
  }

-- | View a mediator as a matched pair of channel ends over @SArr s@.
--
-- The write pole becomes the conjoint @SArr s a ()@; the read pole becomes
-- the companion @SArr s () (Maybe b)@.
medToEnds :: Med s a b -> Ends (SArr s) a (Maybe b)
medToEnds med =
  ends0
    (SArr $ \(s, a) -> (medIn med (s, a), ()))
    (SArr $ \(s, ()) -> medOut med s)

-- | Recover a mediator from a pair of unit-split ends.
--
-- The seed is not present in the 'Ends' view; the caller must supply it.
medFromEnds :: s -> Ends (SArr s) a (Maybe b) -> Med s a b
medFromEnds s0 e =
  let (write, receive) = splay0 e
   in Med
        { medSeed = s0,
          medIn = \(s, a) -> fst (runSArr write (s, a)),
          medOut = \s -> runSArr receive (s, ())
        }

-- | The mediator step, recovered by closing the unit poles of 'medToEnds'.
--
-- The write and read poles are splayed out and composed forward: write the
-- input into the residual, then read whatever the residual is willing to emit.
medStep :: Med s a b -> s -> a -> (s, Maybe b)
medStep med s a =
  let (write, receive) = splay0 (medToEnds med)
   in runSArr (write .> receive) (s, a)

-- | Direct reference implementation of the mediator step.
--
-- Law: @medStep med s a == medStepDirect med s a@.
medStepDirect :: Med s a b -> s -> a -> (s, Maybe b)
medStepDirect med s a = medOut med (medIn med (s, a))

-- | Run a mediator over a list of inputs, collecting emitted outputs.
--
-- The seed is taken from 'medSeed'.
runMed :: Med s a b -> [a] -> [b]
runMed med xs =
  let (_, mys) = foldl (\(s, acc) a -> let (s', mb) = medStep med s a in (s', mb : acc)) (medSeed med, []) xs
   in reverse (catMaybes mys)

-- | An existentially-quantified pair of channel ends, carrying its seed.
data SomeEnds a b where
  SomeEnds :: s -> Ends (SArr s) a b -> SomeEnds a b

-- | Run an existentially-packed pair of ends over a list of inputs.
runSomeEnds :: SomeEnds a b -> [a] -> [b]
runSomeEnds (SomeEnds s0 ends) xs =
  let (write, receive) = splay0 ends
      SArr f = write .> receive
      (_, bs) = foldl (\(s, acc) a -> let (s', b) = f (s, a) in (s', b : acc)) (s0, []) xs
   in reverse bs

-- | Convert a '(->)' 'System' into companion/conjoint channel ends over @SArr@.
--
-- The write pole runs the step and discards the output position; the read pole
-- runs the step with the supplied probe direction and returns the position.
-- This is a lower-level split than 'Machine' provides: it does not assume a
-- separate observation map.
systemToEnds :: Dir p -> System (->) s p -> Ends (SArr s) (Dir p) (Pos p)
systemToEnds probe sys =
  ends0
    (SArr $ \(s, d) -> (fst (runSystem sys (s, d)), ()))
    (SArr $ \(s, ()) -> runSystem sys (s, probe))

-- | Convert a 'Machine' into companion/conjoint channel ends over @SArr@.
--
-- The state carrier is wrapped in 'Maybe' because the initial state is produced
-- by the injector only once a real direction is supplied.  The write pole
-- handles the first input via 'medInit' and subsequent inputs via the step
-- system; the read pole observes the current state without stepping.
machineToEnds :: Machine (->) p -> SomeEnds (Dir p) (Pos p)
machineToEnds (Machine i ex sys) =
  SomeEnds Nothing $
    ends0
      ( SArr $ \case
          (Nothing, d) -> (Just (i d), ())
          (Just s, d) -> (Just (fst (runSystem sys (s, d))), ())
      )
      ( SArr $ \case
          (Nothing, ()) -> error "machineToEnds: read before first input"
          (Just s, ()) -> (Just s, ex s)
      )

-- | Embed a Mealy-style 'Mediator' into a pole-unfused 'Med' over 'SArr'.
--
-- The residual is extended with a one-slot output buffer @Maybe (Maybe b)@:
-- the outer 'Maybe' is the buffer slot, the inner 'Maybe' is the mediator's
-- optional output.  The write pole runs the full mediator step and stores the
-- output; the read pole emits and clears the buffer.  This keeps same-tick
-- semantics: one input in, zero or one output out.
--
-- This is an embedding, not an isomorphism: the buffer slot is extra structure
-- that a natively-written 'Med' does not carry.  Behaviour is preserved:
-- @runMediator med xs == runMed (mediatorToMed med) xs@.
mediatorToMed :: Mediate.Mediator s a b -> Med (s, Maybe (Maybe b)) a b
mediatorToMed med =
  Med
    { medSeed = (Mediate.medInit med, Nothing),
      medIn = \((s, _), a) ->
        let (s', mb) = Mediate.medStep med s a
         in (s', Just mb),
      medOut = \case
        (s, Just mb) -> ((s, Nothing), mb)
        (s, Nothing) -> ((s, Nothing), Nothing)
    }

-- | View a pole-unfused 'Med' as a Mealy-style 'Mediator'.
--
-- The step is 'medStepDirect', i.e. write then read.  This is a left inverse
-- to 'mediatorToMed' up to behaviour: @runMediator (medToMediator (mediatorToMed m)) xs@
-- equals @runMediator m xs@.  It is not an isomorphism because the buffer slot
-- introduced by 'mediatorToMed' is discarded.
medToMediator :: Med s a b -> Mediate.Mediator s a b
medToMediator med = Mediate.Mediator (medSeed med) (medStepDirect med)

-- | Linear mediator: no residual, every input is forwarded immediately.
medLinear :: Med (Maybe a) a a
medLinear =
  Med
    { medSeed = Nothing,
      medIn = \(_, a) -> Just a,
      medOut = \case
        Just a -> (Nothing, Just a)
        Nothing -> (Nothing, Nothing)
    }

-- | Pair-sum mediator: buffers the first integer, emits the sum on the second.
--
-- State is 'Mediate.PS' extended with the output-buffer slot introduced by
-- 'mediatorToMed'.  'Held' carries a buffered value; 'Empty' cleanly represents
-- the absence of a residual, so zero is a valid input.
medPairSum :: Med (Mediate.PS, Maybe (Maybe Int)) Int Int
medPairSum = mediatorToMed Mediate.pairSum

-- | Count mediator: emits the number of inputs seen so far.
medCount :: Med Int () Int
medCount =
  Med
    { medSeed = 0,
      medIn = \case
        (n, ()) -> n + 1,
      medOut = \case
        n -> (n, Just n)
    }
