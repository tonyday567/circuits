{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}

-- | Stateful arrows, knot bodies, and pole-unfused mediators as channel ends.
--
-- This is a spike for the 'Ends-state unification' thesis from
-- @loom/ends-state.md@ and the 'Body-loop' thesis from @loom/body-loop.md@:
-- a stateful morphism @(s, a) -> (s, b)@ is a base arrow in its own right,
-- 'Body t arr s' generalises that to any tensor @t@ and base arrow @arr@,
-- and a mediator is just a pair of channel ends over the cartesian instance
-- split by the unit pole @()@.
--
-- @
--   Body t arr s a b  =  arr (t s a) (t s b)
--   SArr s a b        =  Body (,) (->) s a b
--   Med  s a b        ≅  (s, Ends (SArr s) a (Maybe b))
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

    -- * Knot-body category
    Body (..),
    SomeBody (..),
    bodyToLoop,
    bodyToSArr,
    sArrToBody,
    processToBody,

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

    -- * Loop as ambient-state arrow
    loopToSomeSArr,
    loopEitherToSomeSArr,

    -- * Mediate view
    mediatorToMed,
    medToMediator,

    -- * Reusable mediator configurations
    medLinear,
    PS (..),
    medPairSum,
    medCount,
  )
where

import Circuit.Category (Category (..), Discrete (..), (.>))
import Circuit.Ends (Ends (..), HasUnit (..), In (..), Out (..), close, emit, ends0, splay0)
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Circuit.Mediate qualified as Mediate
import Circuit.Poly (Dir, Pos, System (..), SystemEval (..))
import Circuit.Process (Machine (..), Process (..))
import Data.Bifunctor (second)
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

-- | The knot-body category: morphisms @arr (t s a) (t s b)@ for a fixed
-- feedback/state type @s@, base arrow @arr@, and tensor @t@.
--
-- Composition is just @arr@ composition; no @Channel@, @Strength@, or @Traced@
-- structure is required. This is the category Loop's 'Knot' hides before tracing.
--
-- @SArr s = Body (,) (->) s@ is the cartesian instance.
newtype Body t arr s a b = Body {runBody :: arr (t s a) (t s b)}

instance (Category arr) => Category (Body t arr s) where
  type Ob (Body t arr s) a = Ob arr (t s a)

  id :: forall a. (Ob arr (t s a)) => Body t arr s a a
  id = Body id
  {-# INLINE id #-}

  (.) :: forall a b c. (Ob arr (t s a), Ob arr (t s b), Ob arr (t s c)) => Body t arr s b c -> Body t arr s a b -> Body t arr s a c
  Body g . Body f = Body (g . f)
  {-# INLINE (.) #-}

-- | @Body t arr s@ has the same discreteness as its base arrow.
instance (Discrete arr) => Discrete (Body t arr s) where
  withOb @a = withOb @arr @(t s a)

-- | Cartesian instance: @SArr s@ is exactly @Body (,) (->) s@.
sArrToBody :: SArr s a b -> Body (,) (->) s a b
sArrToBody (SArr f) = Body f

bodyToSArr :: Body (,) (->) s a b -> SArr s a b
bodyToSArr (Body f) = SArr f

-- | A 'Body' with its state type hidden, for the same reason 'SomeSArr' exists.
data SomeBody t arr a b where
  SomeBody :: s -> Body t arr s a b -> SomeBody t arr a b

-- | Lift a knot body into a 'Loop' by hiding the state wire.
bodyToLoop ::
  (Ob arr s, Ob arr (t s a), Ob arr (t s b)) =>
  Body t arr s a b ->
  Loop t arr a b
bodyToLoop (Body f) = Knot f

-- | View a 'Process' as a knot body over the 'Either' tensor.
--
-- This is the same body used by 'Circuit.Process.encode', now exposed as a value
-- of 'Body Either (->) s'. It confirms the Process / Loop Either round-trip
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

-- | View a 'Loop (,) (->)' as an existentially-quantified 'SArr'.
--
-- The hidden feedback channel of the loop becomes the ambient unit state of the
-- 'SArr'; the runner is just 'run' on the underlying traced category.
loopToSomeSArr :: Loop (,) (->) a b -> SomeSArr a b
loopToSomeSArr loop = SomeSArr () $ SArr $ second (run loop)

-- | View a 'Loop Either (->)' as an existentially-quantified 'SArr'.
--
-- Same idea as 'loopToSomeSArr' for the iteration tensor: the loop is
-- interpreted into functions, then wrapped in a trivial ambient state.
loopEitherToSomeSArr :: Loop Either (->) a b -> SomeSArr a b
loopEitherToSomeSArr loop = SomeSArr () $ SArr $ second (run loop)

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
systemToEnds probe (System sys) =
  ends0
    (SArr $ \(s, d) -> (fst (sys (s, d)), ()))
    (SArr $ \(s, ()) -> sys (s, probe))

-- | Convert a 'Machine' into companion/conjoint channel ends over @SArr@.
--
-- The state carrier is wrapped in 'Maybe' because the initial state is produced
-- by the injector only once a real direction is supplied.  The write pole
-- handles the first input via 'medInit' and subsequent inputs via the step
-- system; the read pole observes the current state without stepping.
machineToEnds :: Machine (->) p -> SomeEnds (Dir p) (Pos p)
machineToEnds (Machine i ex (System sys)) =
  SomeEnds Nothing $
    ends0
      ( SArr $ \case
          (Nothing, d) -> (Just (i d), ())
          (Just s, d) -> (Just (fst (sys (s, d))), ())
      )
      ( SArr $ \case
          (Nothing, ()) -> error "machineToEnds: read before first input"
          (Just s, ()) -> (Just s, ex s)
      )

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

-- | Three-state residual for pair summation.
--
-- * 'Empty'  : no buffered value.
-- * 'Held'   : one value buffered, not yet ready.
-- * 'Ready'  : a sum is ready for emission.
data PS = Empty | Held Int | Ready Int
  deriving (Eq, Show)

instance Mediate.LinearResidual PS where
  emptyResidual = Empty

-- | Pair-sum mediator: buffers the first integer, emits the sum on the second.
--
-- State is 'PS'.  'Held' carries a buffered value; 'Ready' carries a value
-- ready for emission.  'Empty' cleanly represents the absence of a residual,
-- so zero is a valid input.
medPairSum :: Med PS Int Int
medPairSum =
  Med
    { medSeed = Empty,
      medIn = \case
        (Empty, x) -> Held x
        (Held y, x) -> Ready (x + y)
        (Ready _, x) -> Held x,
      medOut = \case
        Empty -> (Empty, Nothing)
        Held y -> (Held y, Nothing)
        Ready z -> (Empty, Just z)
    }

-- | Count mediator: emits the number of inputs seen so far.
medCount :: Med Int () Int
medCount =
  Med
    { medSeed = 0,
      medIn = \(n, ()) -> n + 1,
      medOut = \n -> (n, Just n)
    }
