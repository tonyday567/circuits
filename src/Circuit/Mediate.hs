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
    runMediatorState,

    -- * Close certification
    LinearResidual (..),
    LinearityViolation (..),
    closeCertified,

    -- * ?-comonoid structure
    medCounit,
    medComult,

    -- * Stream view
    mediateProcess,

    -- * Reusable mediator configurations
    linear,
    pairSum,
    count,
  )
where

import Circuit.Process (Process (..))
import Data.List (mapAccumL)
import Data.Maybe (catMaybes)

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

-- | Run a mediator over a list of inputs, collecting both the emitted outputs
-- and the final residual state.
runMediatorState :: Mediator s a b -> s -> [a] -> (s, [b])
runMediatorState m s0 xs =
  let (sFinal, mys) = mapAccumL (medStep m) s0 xs
   in (sFinal, catMaybes mys)

-- | Run a mediator over a list of inputs, collecting emitted outputs.
--
-- This is the reference semantics for the mediator: push inputs strictly and
-- pull whenever the mediator is willing to emit.
runMediator :: Mediator s a b -> [a] -> [b]
runMediator m = snd . runMediatorState m (medInit m)

-- | Types whose residual state has a canonical empty value. A 'closeCertified'
-- run asserts that the mediator's residual has returned to this value.
class LinearResidual s where
  -- | The canonical empty residual state.
  emptyResidual :: s

instance LinearResidual () where
  emptyResidual = ()

instance LinearResidual (Maybe a) where
  emptyResidual = Nothing

instance LinearResidual [a] where
  emptyResidual = []

-- | @Int@ is treated as a count residual; the empty value is @0@.
instance LinearResidual Int where
  emptyResidual = 0

-- | A violation reported when a certified close finds the residual state is not
-- empty.
newtype LinearityViolation = LinearityViolation String
  deriving (Eq, Show)

-- | Run a mediator over a stream and certify that the residual is empty at
-- close.
--
-- If the final residual state equals 'emptyResidual', return the emitted
-- outputs. Otherwise report a 'LinearityViolation' carrying the offending
-- residual.
closeCertified :: (LinearResidual s, Eq s, Show s) => Mediator s a b -> s -> [a] -> Either LinearityViolation [b]
closeCertified m s0 as =
  let (sFinal, bs) = runMediatorState m s0 as
   in if sFinal == emptyResidual
        then Right bs
        else Left (LinearityViolation ("close: residual not empty: " ++ show sFinal))

-- | Counit of the @?@-comonoid.
--
-- Closing a mediator with no further inputs is allowed only when the residual
-- state is already empty.  This is the discard law for the exponential:
-- a buffered channel cannot be silently dropped.
medCounit ::
  (LinearResidual s, Eq s, Show s) =>
  Mediator s a b ->
  s ->
  Either LinearityViolation [b]
medCounit m s0 = closeCertified m s0 []

-- | Comultiplication of the @?@-comonoid.
--
-- A mediator policy can be duplicated into two independent consumers.  Each
-- copy starts from the same initial residual state, so the duplication is
-- performed on an empty buffer.
medComult :: Mediator s a b -> (Mediator s a b, Mediator s a b)
medComult m = (m, m)

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
