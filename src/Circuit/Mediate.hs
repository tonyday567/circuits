-- | Mediator abstraction for Track B.
--
-- A mediator is a state machine with residual state @s@. It consumes inputs of
-- type @a@ and may produce outputs of type @b@. The residual state is what
-- persists between interactions; it is the locus of the "Ends-with-residual"
-- design.
--
-- The channel type itself carries no residual field. The residual is supplied
-- by a mediator value when two channels are composed.
--
-- Whether the mediator is best implemented as a plain state-passing record or
-- as a 'Circuit.Hyper.HyperF' is the deferred B1/B3 question. This module
-- starts with the record version because it is the minimal design that
-- reproduces the B0 oracles.
module Circuit.Mediate
  ( -- * Mediator state machine
    Mediator (..),
    runMediator,

    -- * Stream view
    mediateProcess,

    -- * Reusable mediator configurations
    linear,
    pairSum,
    count,
  )
where

import Circuit.Process (Process (..))

-- | A mediator with residual state @s@, input @a@, output @b@.
--
-- The step function consumes one input and updates the residual state. It may
-- emit zero or one output. A 'Nothing' output means the mediator is still
-- accumulating residual state.
--
-- This is the minimal strict-alternation model suggested by the B0 spike:
-- the mediator owns the buffer that the old @composeEnds@ flattened to @()@.
data Mediator s a b = Mediator
  { -- | Initial residual state.
    medInit :: s,
    -- | Consume one input, update residual state, optionally emit output.
    medStep :: s -> a -> (s, Maybe b)
  }

-- | Run a mediator over a list of inputs, collecting emitted outputs.
--
-- This is the reference semantics for the mediator: push inputs strictly and
-- pull whenever the mediator is willing to emit.
runMediator :: Mediator s a b -> [a] -> [b]
runMediator m = go (medInit m)
  where
    go _ [] = []
    go s (x : xs) =
      let (s', my) = medStep m s x
       in case my of
            Nothing -> go s' xs
            Just y -> y : go s' xs

-- | View a mediator as a 'Process' stream transformer.
--
-- A mediator step is Mealy-style: the output depends on the current state
-- /and/ input.  'Process' is Moore-style, so the output carrier is @Maybe b@
-- and the state remembers the output produced by the most recent step.  The
-- seed @s0@ is the initial residual, following the register pattern.
--
-- This is the honest stream cut: the residual state is carried by the
-- process's feedback wire, exactly as 'encode' carries it in a
-- @Loop Either (->) [a] [Maybe b]@.
mediateProcess :: Mediator s a b -> s -> Process a (Maybe b)
mediateProcess med s0 =
  Process
    (\a -> let (s', my) = medStep med s0 a in (s', my))
    (\(s, _) a -> let (s', my) = medStep med s a in (s', my))
    snd

-- | Linear mediator: no residual, every input is forwarded immediately.
--
-- The residual state is @()@, so 'close' on a linear composition is yanking
-- with an empty residual.
linear :: Mediator () a a
linear = Mediator () $ \() x -> ((), Just x)

-- | Pair-sum mediator: buffers the first integer, emits the sum on the second.
--
-- Residual state is 'Maybe Int'. This reproduces the B0 @pairSum@ oracle
-- without an external 'TQueue'.
pairSum :: Mediator (Maybe Int) Int Int
pairSum =
  Mediator Nothing $ \s x -> case s of
    Nothing -> (Just x, Nothing)
    Just y -> (Nothing, Just (x + y))

-- | Count mediator: emits the number of inputs seen so far.
--
-- A simple non-linear mediator with accumulating residual state.
count :: Mediator Int a Int
count = Mediator 0 $ \n _ -> let n' = n + 1 in (n', Just n')
