{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

-- | Stateful arrows and pole-unfused mediators as channel ends.
--
-- This is a spike for the 'Ends-state unification' thesis from
-- @loom/ends-state.md@: a stateful morphism @(s, a) -> (s, b)@ is a base arrow
-- in its own right, and a mediator is just a pair of channel ends over that
-- arrow split by the unit pole @()@.
--
-- @
--   SArr s a b  =  (s, a) -> (s, b)
--   Med  s a b  ≈  Ends (SArr s) a (Maybe b)
-- @
--
-- The @Med@ record keeps the seed and the two pole functions explicit. The
-- step function is recovered as 'close' on the unit ends, i.e. as sequential
-- composition of the write pole followed by the read pole.
module Circuit.Ends.State
  ( -- * Stateful arrow
    SArr (..),
    SomeSArr (..),
    runSomeSArr,
    processToSomeSArr,

    -- * Pole-unfused mediator
    Med (..),
    medToEnds,
    medFromEnds,
    medStep,
    medStepDirect,
    runMed,

    -- * Mediate view
    mediatorToMed,
    medToMediator,

    -- * Reusable mediator configurations
    medLinear,
    medPairSum,
    medCount,
  )
where

import Circuit.Category (Category (..), Discrete (..), (.>))
import Circuit.Ends (Ends (..), HasUnit (..), In (..), Out (..), close, emit, ends0, splay0)
import Circuit.Mediate qualified as Mediate
import Circuit.Process (Process (..))
import Data.Maybe (catMaybes)
import Prelude hiding (id, (.))

-- | The ambient-state arrow: a morphism that threads a state wire @s@.
--
-- This is the underlying category of the Ends-state unification. Composition
-- threads the state sequentially.
newtype SArr s a b = SArr {runSArr :: (s, a) -> (s, b)}

instance Category (SArr s) where
  type Ob (SArr s) a = ()

  id :: SArr s a a
  id = SArr id
  {-# INLINE id #-}

  (.) :: SArr s b c -> SArr s a b -> SArr s a c
  SArr g . SArr f = SArr $ \(s, a) ->
    let (s', b) = f (s, a)
     in g (s', b)
  {-# INLINE (.) #-}

-- | @SArr s@ has trivial object constraints, so it is discrete.
instance Discrete (SArr s) where
  withOb x = x

-- | Unit ends for @SArr s@ at the unit object @()@.
--
-- The companion discards its input and returns @()@; the conjoint delegates
-- to the companion. Yanking recovers the identity on @()@.
instance HasUnit () (SArr s) where
  open =
    let outU = Out $ \_ -> SArr $ \(s, _) -> (s, ())
        inU = In $ \o -> emit o inU
     in Ends inU outU

-- | An existentially-quantified ambient-state arrow.
--
-- This is the packing that lets us treat a 'Process' as a value of the form
-- @exists s. SArr s a b@.
data SomeSArr a b where
  SomeSArr :: s -> SArr s a b -> SomeSArr a b

-- | Run an existentially-packed stateful arrow over a list of inputs.
runSomeSArr :: SomeSArr a b -> [a] -> [b]
runSomeSArr (SomeSArr s0 (SArr f)) xs =
  let (_, bs) = foldl (\(s, acc) a -> let (s', b) = f (s, a) in (s', b : acc)) (s0, []) xs
   in reverse bs

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

-- | Recover a mediator (without its seed) from a pair of unit-split ends.
--
-- The seed is not present in the 'Ends' view; the caller must supply it.
medFromEnds :: Ends (SArr s) a (Maybe b) -> Med s a b
medFromEnds e =
  let (write, receive) = splay0 e
   in Med
        { medSeed = error "medFromEnds: seed is not stored in Ends",
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

-- | View a Mealy-style 'Mediator' as a pole-unfused 'Med' over 'SArr'.
--
-- The residual is extended with a one-slot output buffer @Maybe (Maybe b)@:
-- the outer 'Maybe' is the buffer slot, the inner 'Maybe' is the mediator's
-- optional output.  The write pole runs the full mediator step and stores the
-- output; the read pole emits and clears the buffer.  This keeps same-tick
-- semantics: one input in, zero or one output out.
--
-- Law: @runMediator med xs == runMed (mediatorToMed med) xs@.
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
-- This is the tautological reverse direction: the step is 'medStepDirect',
-- i.e. write then read.
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
-- State is @Either Int Int@.  'Left' carries a buffered value; 'Right' carries
-- a value ready for emission.  'Left 0' is used as the empty-buffer sentinel,
-- so this example assumes non-zero inputs.
medPairSum :: Med (Either Int Int) Int Int
medPairSum =
  Med
    { medSeed = Left 0,
      medIn = \case
        (Left 0, x) -> Left x
        (Left y, x) -> Right (x + y)
        (Right _, x) -> Left x,
      medOut = \case
        Left y -> (Left y, Nothing)
        Right z -> (Left 0, Just z)
    }

-- | Count mediator: emits the number of inputs seen so far.
medCount :: Med Int () Int
medCount =
  Med
    { medSeed = 0,
      medIn = \(n, ()) -> n + 1,
      medOut = \n -> (n, Just n)
    }
