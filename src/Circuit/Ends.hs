{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Free channel ends over a base arrow, plus concrete box helpers.
--
-- A channel has exactly two ends:
--
--   * @Out@ — the companion (read / emit end), covariant in the payload.
--   * @In@  — the conjoint (write / commit end), contravariant in the payload.
--
-- @Ends@ is the record that pairs one @In@ with one @Out@.  The ends are
-- defined purely in terms of the base arrow @arr@.
--
-- 'open' produces a matched pair; 'close' plugs the pair back together by
-- feeding the @Out@ into the @In@.
--
-- A /symmetric/ end @Ends arr a a@ with @close (conjoint e) (companion e) = id@
-- is the copycat strategy for the multiplicative excluded middle @A ⅋ A⊥@:
-- it routes traffic between the two poles without ever deciding which side is
-- true.  For the unit object use 'open' (also exported as 'copycat').
--
-- == Relationship to 'Circuit.ChannelPoly'
--
-- @Ends@ is the bi-polar / effectful API: it is the right tool for
-- @K IO/STM@ process plumbing where the channel is a write end paired
-- with a read end.  For pure @(->)@ Moore-style channels indexed by a
-- polynomial, prefer 'Circuit.ChannelPoly.Channel'.
--
-- There is no deprecation shim yet: the relationship between the bi-polar
-- and polynomial views is still being settled.  This module stays unchanged
-- until 'Channel' gains 'K' evaluation or an equivalent effectful
-- story.
--
-- Effectful queue-based constructors ('openSTM', 'openIO') live in
-- @Circuit.Agent.Ends@ so that the core library does not depend on @stm@.
module Circuit.Ends
  ( -- * Channel ends (bi-polar contract)
    Out (..),
    In (..),

    -- * Matched pair
    Ends (..),

    -- * Counit
    close,

    -- * Prefixing an action to an @In@
    prefixIn,

    -- * Suffixing an action to an @Out@
    suffixOut,

    -- * Build an @Ends@ from primitive actions
    ends,
    ends0,
    endsK,

    -- * Extract primitive actions from an @Ends@
    splay,
    splay0,

    -- * Sequential composition
    composeEnds,
    composeEnds0,
    (>:>),

    -- * Parallel composition
    parEnds,

    -- * Profunctor structure (morphism-level)
    dimapEnds,
    lmapEnds,
    rmapEnds,

    -- * Dualising object / unit ends (requires constant morphisms)
    HasDual (..),

    -- * Copycat / multiplicative excluded middle
    copycat,

    -- * Boxes
    box,
    boxAsymmetric,

    -- * Additive connectives
    pairEnds,
    Bias (..),
    IsSilent (..),
    HasSilent (..),
    raceEnds,
    raceMediator,

    -- * Stateful conversions over 'SArr'
    SArr (..),
    SomeSArr (..),
    runSomeSArr,
    Body (..),
    SomeBody (..),
    bodyToLoop,
    bodyToSArr,
    sArrToBody,
    processToBody,
    processToSomeSArr,
    loopToSomeSArr,
    loopEitherToSomeSArr,

    -- * Pole-unfused mediator
    Med (..),
    medToEnds,
    medFromEnds,
    medStep,
    medStepDirect,
    runMed,

    -- * System as channel ends
    SomeEnds (..),
    runSomeEnds,
    systemToEnds,
    systemWithSeedToEnds,

    -- * Mediate view
    mediatorToMed,
    medToMediator,
    medToMediatorBuffered,

    -- * Reusable mediator configurations
    medLinear,
    medPairSum,
    medCount,

    -- * Pair-sum residual
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
import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Dagger (Copy (copy), Discard (discard))
import Circuit.Loop (Loop (..))
import Circuit.Mediate qualified as Mediate
import Circuit.Poly (Dir, Pos, System, SystemEval (..), runSystem, system)
import Circuit.Process (Process (..))
import Circuit.Tensor (Action (..), Bias (..), Tensor (..), Unit)
import Data.Maybe (catMaybes, isJust, isNothing)
import Data.Void (Void)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Category ((.>))
-- >>> import Circuit.Ends
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Category (K(..), runK)

-- ---------------------------------------------------------------------------
-- Channel ends — the companion and conjoint of the identity functor.
-- ---------------------------------------------------------------------------

-- | @Out@ is the companion of the identity functor.  Covariant in @a@
-- (sits in the output position).
newtype Out arr a = Out
  { -- | Emit through the companion, supplying the other end.
    emit :: forall x. In arr x -> arr x a
  }

-- | @In@ is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
newtype In arr a = In
  { -- | Commit through the conjoint, supplying the other end.
    commit :: forall x. Out arr x -> arr a x
  }

-- | A matched pair of channel ends: one @In@ and one @Out@.
--
-- This is the bi-polar communication contract.  The conjoint (@In@)
-- consumes payloads of type @a@; the companion (@Out@) produces payloads
-- of type @b@.  For symmetric channels such as queues @a = b@.
--
-- Together with 'prefixIn' and 'suffixOut', @Ends@ carries an /enriched/
-- profunctor structure over the base category @arr@: 'prefixIn' is the
-- left action of @arr@ on @In@ ends, and 'suffixOut' is the right action
-- of @arr@ on @Out@ ends.
data Ends arr a b = Ends
  { -- | Write end (producer), the conjoint.
    conjoint :: In arr a,
    -- | Read end  (consumer), the companion.
    companion :: Out arr b
  }

-- | Plug an @In@ and an @Out@ of the same payload type together.
--
-- 'close' feeds the @Out@ into the @In@ end, producing a morphism
-- @arr a a@ from the paired payload type.
--
-- Yanking: for the unit ends from 'open',
-- @close (conjoint ends) (companion ends) = id@.
close :: In arr a -> Out arr a -> arr a a
close contra = commit contra

-- | Precompose an @arr@-morphism with an @In@ end.
--
-- Given @f :: arr a b@ and an @In@ end at type @b@, produce an @In@ end
-- at type @a@.  Running the resulting end first executes @f@ and then
-- commits through the original end.
--
-- This is the left (contravariant) action of the base category on @In@
-- ends.  Specialised to unit ends it is the canonical way to build
-- effectful write ends.
--
-- >>> let endsU = open :: Ends (->) () ()
-- >>> let inA = prefixIn (const ()) (conjoint endsU) :: In (->) Int
-- >>> commit inA (companion endsU) 42
-- ()
prefixIn :: forall arr a b. (Category arr) => arr a b -> In arr b -> In arr a
prefixIn f i = In $ \(o :: Out arr x) -> f .> commit i o

-- | Postcompose an @arr@-morphism with an @Out@ end.
--
-- Given an @Out@ end at type @a@ and @g :: arr a b@, produce an @Out@
-- end at type @b@.  Running the resulting end first emits through the
-- original end and then executes @g@ on the emitted value.
--
-- This is the right (covariant) action of the base category on @Out@
-- ends.  Specialised to unit ends it is the canonical way to build
-- effectful read ends.
--
-- >>> let endsU = open :: Ends (->) () ()
-- >>> let outA = suffixOut (companion endsU) (const 42) :: Out (->) Int
-- >>> emit outA (conjoint endsU) ()
-- 42
suffixOut :: forall arr a b. (Category arr) => Out arr a -> arr a b -> Out arr b
suffixOut o g = Out $ \(i :: In arr x) -> emit o i .> g

-- ---------------------------------------------------------------------------
-- Dualising object / unit ends
-- ---------------------------------------------------------------------------

-- | Arrows that have channel ends for a given dualising object @bot@.
--
-- The dualising object is the target of the Chu pairing and the object
-- through which the two poles of an 'Ends' are plugged together.  In the
-- cartesian case it is the monoidal unit @()@; for halt-mark / delivery
-- pairings it can be 'Bool'.
--
-- The ends are the identity-on-@bot@ morphism split into its two polar
-- halves.  The companion is constant; the conjoint delegates to the
-- opposing companion.
--
-- These ends require the base arrow to support constant morphisms, so
-- they are captured by this class rather than being definable for all
-- arrows.
class (Category arr) => HasDual bot arr where
  -- | The dualising object as channel ends.
  --
  -- === Yank
  --
  -- >>> let ends = open :: Ends (->) () ()
  -- >>> close (conjoint ends) (companion ends) ()
  -- ()
  --
  -- === Plug
  --
  -- >>> let endsA = open :: Ends (->) () ()
  -- >>> let endsU = open :: Ends (->) () ()
  -- >>> commit (conjoint endsA) (companion endsU) ()
  -- ()
  -- >>> emit (companion endsA) (conjoint endsU) ()
  -- ()
  open :: Ends arr bot bot

-- | The copycat strategy at the dualising object @bot@.
--
-- This is the multiplicative excluded middle @bot ⅋ bot⊥@ for arrows that
-- have ends at @bot@: a self-dual channel whose 'close' is the identity on
-- @bot@.  It routes between the two poles without ever deciding which one
-- holds.
--
-- The additive excluded middle @bot ⊕ bot⊥@ — a verdict, now — is /not/
-- supported; there is no @decide :: Either bot bot@ here, because only the
-- routing witness is provable.
copycat :: forall arr bot. (HasDual bot arr) => Ends arr bot bot
copycat = open
{-# INLINE copycat #-}

-- | Build an @Ends@ from a write morphism and a read morphism.
--
-- @write :: arr a bot@ consumes the input payload and produces the dualising
-- object; @read :: arr bot b@ consumes the dualising object and produces the
-- output payload.  The dualising-object ends wire the two halves together.
--
-- This is the canonical way to turn a pair of primitive channel actions
-- into a matched pair of @In@ and @Out@ ends.
--
-- Compositional spelling:
--
-- @
-- ends write receive =
--   Ends (prefixIn write (conjoint open)) (suffixOut (companion open) receive)
-- @
ends ::
  forall arr a b bot.
  (HasDual bot arr) =>
  arr a bot ->
  arr bot b ->
  Ends arr a b
ends write receive =
  Ends
    (prefixIn write (conjoint open))
    (suffixOut (companion open) receive)

-- | Convenience version of 'ends' when the dualising object is @()@.
ends0 ::
  (HasDual () arr) =>
  arr a () ->
  arr () b ->
  Ends arr a b
ends0 = ends @_ @_ @_ @()
{-# INLINE ends0 #-}

-- | Specialization of 'ends' for @K@ actions.
--
-- @write :: a -> m ()@ consumes the input payload; @receive :: m b@
-- produces the output payload. The dualising-object handling is hidden
-- inside the @K@ wrappers.
endsK ::
  forall m a b.
  (Monad m) =>
  (a -> m ()) ->
  m b ->
  Ends (K m) a b
endsK write receive = ends (K write) (K $ const receive)

-- | Extract the primitive write and read actions from an @Ends@ by
-- plugging each end with the dualising-object ends.
--
-- For an @Ends@ built with 'ends', this recovers the original
-- @write :: arr a bot@ and @receive :: arr bot b@.
--
-- >>> let e = ends0 (\() -> ()) (const (42 :: Int)) :: Ends (->) () Int
-- >>> let (write, receive) = splay0 e
-- >>> (write (), receive ())
-- ((),42)
splay ::
  forall arr a b bot.
  (HasDual bot arr) =>
  Ends arr a b ->
  (arr a bot, arr bot b)
splay e =
  ( commit (conjoint e) (companion (open :: Ends arr bot bot)),
    emit (companion e) (conjoint (open :: Ends arr bot bot))
  )

-- | Convenience version of 'splay' when the dualising object is @()@.
splay0 ::
  (HasDual () arr) =>
  Ends arr a b ->
  (arr a (), arr () b)
splay0 = splay @_ @_ @_ @()
{-# INLINE splay0 #-}

-- ---------------------------------------------------------------------------
-- Composition
-- ---------------------------------------------------------------------------

-- | Sequential composition of @Ends@.
--
-- Given @e1 :: Ends arr a b@ and @e2 :: Ends arr b c@, produce an
-- @Ends arr a c@ by connecting the @b@ end of @e1@ to the @b@ end of
-- @e2@.  The primitive actions are extracted via 'splay' and reassembled
-- with 'ends', so 'box' preserves the composition:
--
-- @box (composeEnds e1 e2) = box e2 . box e1@
--
-- Identity exists at the chosen unit type: @open :: Ends arr u u@ is
-- the identity for composition.
--
-- >>> let e1 = ends0 (const ()) (const 1 :: () -> Int) :: Ends (->) () Int
-- >>> let e2 = ends0 (const ()) (const 2 :: () -> Int) :: Ends (->) Int Int
-- >>> run (box @(,) (composeEnds0 e1 e2)) ()
-- 2
composeEnds ::
  forall arr a b c bot.
  (HasDual bot arr) =>
  Ends arr a b ->
  Ends arr b c ->
  Ends arr a c
composeEnds e1 e2 =
  let (write1, read1) = splay e1 :: (arr a bot, arr bot b)
      (write2, read2) = splay e2 :: (arr b bot, arr bot c)
   in ends write1 (read1 .> write2 .> read2)

-- | Convenience version of 'composeEnds' when the dualising object is @()@.
composeEnds0 ::
  (HasDual () arr) =>
  Ends arr a b ->
  Ends arr b c ->
  Ends arr a c
composeEnds0 = composeEnds @_ @_ @_ @_ @()
{-# INLINE composeEnds0 #-}

-- | Forward-composition operator for @Ends@.  @e1 >:> e2 = composeEnds e1 e2@.
(>:>) ::
  forall arr a b c bot.
  (HasDual bot arr) =>
  Ends arr a b ->
  Ends arr b c ->
  Ends arr a c
e1 >:> e2 = composeEnds @arr @a @b @c @bot e1 e2

infixr 1 >:>

-- | Parallel composition of @Ends@.
--
-- Pair two @Ends@ side by side on the tensor @t@.  The primitive
-- actions are tensored and then collapsed to and from the dualising object
-- with the tensor unitors.  This requires the tensor unit to coincide with
-- the dualising object @bot@; in practice this is the cartesian @(,)@ tensor
-- with @bot = ()@.
--
-- >>> let e1 = ends0 (const ()) (const 1 :: () -> Int) :: Ends (->) () Int
-- >>> let e2 = ends0 (const ()) (const 2 :: () -> Int) :: Ends (->) () Int
-- >>> run (box @(,) (parEnds e1 e2)) ((), ())
-- (1,2)
parEnds ::
  forall t arr a b c d bot.
  (Tensor t arr, HasDual bot arr, Unit t ~ bot) =>
  Ends arr a b ->
  Ends arr c d ->
  Ends arr (t a c) (t b d)
parEnds e1 e2 =
  let (write1, read1) = splay e1 :: (arr a bot, arr bot b)
      (write2, read2) = splay e2 :: (arr c bot, arr bot d)
      write = par write1 write2 .> (unitr :: arr (t bot bot) bot)
      readEnds = (unitl' :: arr bot (t bot bot)) .> par read1 read2
   in ends write readEnds

-- | Precompose the input and postcompose the output of an @Ends@.
--
-- This is the morphism-level profunctor action: @f :: arr a' a@ shapes
-- what the conjoint sees, and @g :: arr b b'@ shapes what the companion
-- emits.
--
-- >>> let e = ends0 (const ()) (const 42 :: () -> Int) :: Ends (->) () Int
-- >>> let e' = dimapEnds (const ()) ((+1) :: Int -> Int) e :: Ends (->) () Int
-- >>> run (box @(,) e') ()
-- 43
dimapEnds ::
  forall arr a a' b b'.
  (Category arr) =>
  arr a' a ->
  arr b b' ->
  Ends arr a b ->
  Ends arr a' b'
dimapEnds f g (Ends i o) = Ends (prefixIn f i) (suffixOut o g)

-- | Precompose the input of an @Ends@.
lmapEnds ::
  forall arr a a' b.
  (Category arr) =>
  arr a' a ->
  Ends arr a b ->
  Ends arr a' b
lmapEnds f (Ends i o) = Ends (prefixIn f i) o

-- | Postcompose the output of an @Ends@.
rmapEnds ::
  forall arr a b b'.
  (Category arr) =>
  arr b b' ->
  Ends arr a b ->
  Ends arr a b'
rmapEnds g (Ends i o) = Ends i (suffixOut o g)

-- | Dualising object @()@ for @(->)@.
--
-- The companion is the constant function returning @()@; the conjoint
-- recursively emits through the supplied companion.
instance HasDual () (->) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> const ()
      inU = In $ \o -> emit o inU

-- | Dualising object @()@ for @K@ @m@.
--
-- Same shape as the @(->)@ instance, but the constant companion returns
-- @()@ in the monad.
instance (Monad m) => HasDual () (K m) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> K $ \_ -> pure ()
      inU = In $ \o -> emit o inU

-- === Notes on the dualising object
--
-- The class parameter @bot@ is the object through which the two poles of an
-- 'Ends' are plugged.  For the cartesian @(,)@ tensor this is the monoidal
-- unit @()@, which is terminal.  'copycat' yanks to the identity on @bot@
-- exactly when @bot@ is terminal; for non-terminal objects such as 'Bool'
-- the same 'open' still typechecks but 'copycat' becomes a constant
-- endomorphism rather than the identity.
--
-- The unification with halt-mark / delivery 'Bool' pairings therefore lives
-- partly in the Chu construction: a 'Bool'-valued pairing @arr (a, b) Bool@
-- can be supplied to 'endsAsChu' as the dualising object, while 'HasDual'
-- governs the object used for unit plumbing.  The 'Bool' instances below
-- make that plumbing explicit.

-- | Dualising object 'Bool' for @(->)@.
--
-- The companion is the constant function returning 'False'; the conjoint
-- recursively emits through the supplied companion.  Because 'Bool' is not
-- terminal, 'copycat' at 'Bool' is the constant function, not the identity.
instance HasDual Bool (->) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> const False
      inU = In $ \o -> emit o inU

-- | Dualising object 'Bool' for @K@ @m@.
--
-- Same shape as the @(->)@ instance, but the constant companion returns
-- 'False' in the monad.
instance (Monad m) => HasDual Bool (K m) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> K $ \_ -> pure False
      inU = In $ \o -> emit o inU

-- ---------------------------------------------------------------------------
-- Boxes
-- ---------------------------------------------------------------------------

-- | String-diagram boxes from channel ends.
--
-- A matched pair of free ends (@Ends@) is a box with one input wire and
-- one output wire.  The helpers below embed that box into a traced
-- monoidal category by unit-plugging the remaining two slots.

-- | Embed an @Ends@ into a plain @Loop t arr a b@.
--
-- Connects the two channel ends through the unit object, giving a plain
-- @Loop t arr a b@. This is the version most users expect: input on the
-- left, output on the right, with the unit plumbing hidden.
--
-- >>> let e = ends0 (const ()) (const 42) :: Ends (->) () Int
-- >>> run (box @(,) e) ()
-- 42
box ::
  forall t arr a b.
  (HasDual (Unit t) arr) =>
  Ends arr a b ->
  Loop t arr a b
box ends' =
  Lift $
    commit (conjoint ends') (companion (open :: Ends arr (Unit t) (Unit t)))
      .> emit (companion ends') (conjoint (open :: Ends arr (Unit t) (Unit t)))

-- | Asymmetric box with the dualising object exposed on opposite sides.
--
-- Uses 'par' at the base arrow level and lifts the result with 'Lift'.
-- The input carries the dualising object on the right and the output carries
-- it on the left; most users will prefer the dualising-object-normalised
-- 'box'.
--
-- >>> let e = ends0 (const ()) (const 42) :: Ends (->) () Int
-- >>> run (boxAsymmetric @(,) e) ((), ())
-- ((),42)
boxAsymmetric ::
  forall t arr a b.
  (HasDual (Unit t) arr, Tensor t arr) =>
  Ends arr a b ->
  Loop t arr (t a (Unit t)) (t (Unit t) b)
boxAsymmetric ends' =
  Lift $
    par
      (commit (conjoint ends') (companion open))
      (emit (companion ends') (conjoint open))

-- $setup
-- >>> import Circuit.Ends
-- >>> import Circuit.Layer (run)

-- | Parallel product of two morphisms on a pair.
--
-- This is the cartesian product, renamed from 'Par' to avoid collision with
-- the multiplicative disjunction 'Circuit.Tensor.Par'.
class CartesianPar arr where
  parP :: arr a b -> arr c d -> arr (a, c) (b, d)

instance CartesianPar (->) where
  parP f g (x, y) = (f x, g y)

instance (Monad m) => CartesianPar (K m) where
  parP (K f) (K g) = K $ \(x, y) -> (,) <$> f x <*> g y

-- | Values that can be tested for silence.
class IsSilent b where
  -- | True iff the value is silent.
  isSilent :: b -> Bool

instance IsSilent [a] where
  isSilent = null

instance IsSilent (Maybe a) where
  isSilent = isNothing

instance IsSilent Void where
  isSilent = const True

-- | Values that carry a canonical silent value.
class (IsSilent b) => HasSilent b where
  -- | The canonical silent value.
  silent :: b

instance HasSilent [a] where
  silent = []

instance HasSilent (Maybe a) where
  silent = Nothing

-- | Additive conjunction: both sub-ends receive the same input and their
-- outputs are paired.
--
-- This is the @&@ connective / 'await' fragment: every branch sees the
-- input, and the composite emits all of their results.
--
-- >>> let e1 = ends0 (const ()) (const 1 :: () -> Int) :: Ends (->) () Int
-- >>> let e2 = ends0 (const ()) (const 2 :: () -> Int) :: Ends (->) () Int
-- >>> run (box @(,) (pairEnds e1 e2)) ()
-- (1,2)
pairEnds ::
  (Copy (->) a) =>
  Ends (->) a b ->
  Ends (->) a c ->
  Ends (->) a (b, c)
pairEnds e1 e2 =
  let (w1, r1) = splay0 e1
      (w2, r2) = splay0 e2
      w = discard . parP w1 w2 . copy
      r = parP r1 r2 . copy
   in ends0 w r

-- | Additive disjunction / race: both sub-ends receive the same input, but
-- only the first non-silent output (according to the bias) is emitted.
--
-- The bias is explicit in the term rather than silently left-biased.  The
-- picking logic is the additive disjunction mediator: a state machine whose
-- residual is the first non-silent value it has seen.
--
-- >>> let eL = ends0 (const ()) (const (Just 1)) :: Ends (->) () (Maybe Int)
-- >>> let eR = ends0 (const ()) (const (Just 2)) :: Ends (->) () (Maybe Int)
-- >>> run (box @(,) (raceEnds LeftFirst eL eR)) ()
-- Just 1
-- >>> run (box @(,) (raceEnds RightFirst eL eR)) ()
-- Just 2
raceEnds ::
  (Copy (->) a, IsSilent b) =>
  Bias ->
  Ends (->) a b ->
  Ends (->) a b ->
  Ends (->) a b
raceEnds bias e1 e2 =
  let (w1, r1) = splay0 e1
      (w2, r2) = splay0 e2
      w = discard . parP w1 w2 . copy
      r = pick bias . parP r1 r2 . copy
   in ends0 w r
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y

-- | Additive disjunction as a mediator.
--
-- The residual is the first non-silent value seen.  Once set, every further
-- input is ignored and the chosen value is emitted repeatedly.  This is the
-- same picking logic as 'raceEnds', expressed in the @?@-policy vocabulary.
raceMediator :: (IsSilent b) => Bias -> Mediate.Mediator (Maybe b) (b, b) b
raceMediator bias =
  Mediate.Mediator
    Nothing
    ( \s (x, y) -> case s of
        Just z -> (Just z, Just z)
        Nothing ->
          let z = pick bias (x, y)
           in (Just z, Just z)
    )
    (const False)
    (\_ _ -> Nothing)
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y

-- ---------------------------------------------------------------------------
-- Stateful conversions over 'SArr'
-- ---------------------------------------------------------------------------

-- | Unit ends for @SArr s@ at the unit object @()@.
--
-- The companion discards its input and returns @()@; the conjoint delegates
-- to the companion. Yanking recovers the identity on @()@.
--
-- This instance is technically orphan because 'SArr' now lives in
-- 'Circuit.Body', but keeping it here keeps the 'Ends' plumbing local to the
-- conversions section.
instance HasDual () (SArr s) where
  open =
    let outU = Out $ \_ -> SArr $ \(s, _) -> (s, ())
        inU = In $ \o -> emit o inU
     in Ends inU outU

-- | Dualising object @()@ for @Body (,) (K m) s@.
--
-- Same shape as the 'SArr' instance, but the companion returns @()@ in the
-- monad and threads the ambient state through unchanged.
instance (Monad m) => HasDual () (Body (,) (K m) s) where
  open =
    let outU = Out $ \_ -> Body $ K $ \(s, _) -> pure (s, ())
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

-- | A pole-unfused mediator with state @s@, input @a@, output @b@.
--
-- * @medIn@ is the write pole: it consumes an input together with the current
--   state and updates the state.
-- * @medOut@ is the read pole: it observes the state and may emit an output,
--   updating the state again.
-- * @medOwed@ selects which states carry resource debt for close certification.
-- * @medDraw@ checks for overdraw on shared-medium transitions.
-- * @medStep@ is the sequential composition of the two poles, recovered as
--   'close' on the unit ends.
data Med s a b = Med
  { -- | Initial state.
    medSeed :: s,
    -- | Write pole: consume input, update state.
    medIn :: (s, a) -> s,
    -- | Read pole: observe state, optionally emit output.
    medOut :: s -> (s, Maybe b),
    -- | Predicate selecting states that are owed / residual at close time.
    medOwed :: s -> Bool,
    -- | Overdraw check for shared-medium transitions.
    medDraw :: s -> s -> Maybe Int
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
-- The seed, owed predicate, and draw predicate are not present in the 'Ends'
-- view; the caller must supply them.
medFromEnds :: s -> (s -> Bool) -> (s -> s -> Maybe Int) -> Ends (SArr s) a (Maybe b) -> Med s a b
medFromEnds s0 owed draw e =
  let (write, receive) = splay0 e
   in Med
        { medSeed = s0,
          medIn = \(s, a) -> fst (runSArr write (s, a)),
          medOut = \s -> runSArr receive (s, ()),
          medOwed = owed,
          medDraw = draw
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
runSomeEnds (SomeEnds s0 e) xs =
  let (write, receive) = splay0 e
      SArr f = write .> receive
      (_, bs) = foldl (\(s, acc) a -> let (s', b) = f (s, a) in (s', b : acc)) (s0, []) xs
   in reverse bs

-- | Convert a '(->)' 'System' into companion/conjoint channel ends over @SArr@.
--
-- The write pole runs the step and discards the output position; the read pole
-- runs the step with the supplied probe direction and returns the position.
-- This is a lower-level split than a pointed Moore machine: it does not assume
-- a separate observation map.
systemToEnds :: Dir p -> System (->) s p -> Ends (SArr s) (Dir p) (Pos p)
systemToEnds probe sys =
  ends0
    (SArr $ \(s, d) -> (fst (runSystem sys (s, d)), ()))
    (SArr $ \(s, ()) -> runSystem sys (s, probe))

-- | Convert a pointed 'System' into companion/conjoint channel ends over @SArr@.
--
-- The state carrier is the system's state @s@ and the seed @s0@ is carried by
-- 'SomeEnds'.  The write pole steps with the supplied direction; the read pole
-- observes the current state without stepping, using the supplied observation
-- function.
systemWithSeedToEnds :: s -> (s -> Pos p) -> System (->) s p -> SomeEnds (Dir p) (Pos p)
systemWithSeedToEnds s0 ex sys =
  SomeEnds s0 $
    ends0
      (SArr $ \(s, d) -> (fst (runSystem sys (s, d)), ()))
      (SArr $ \(s, ()) -> (s, ex s))

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
--
-- For close certification use 'medToMediatorBuffered', which projects away the
-- output-buffer slot so that 'closeCertified' inspects only the original
-- residual @s@.
mediatorToMed :: Mediate.Mediator s a b -> Med (s, Maybe (Maybe b)) a b
mediatorToMed med =
  Med
    { medSeed = (Mediate.medInit med, Nothing),
      medIn = \((s, _), a) ->
        let (s', mb) = Mediate.medStep med s a
         in (s', Just mb),
      medOut = \case
        (s, Just mb) -> ((s, Nothing), mb)
        (s, Nothing) -> ((s, Nothing), Nothing),
      medOwed = \(s, _) -> Mediate.medOwed med s,
      medDraw = \(s, _) (s', _) -> Mediate.medDraw med s s'
    }

-- | View a pole-unfused 'Med' as a Mealy-style 'Mediator'.
--
-- The step is 'medStepDirect', i.e. write then read.  This is a left inverse
-- to 'mediatorToMed' up to behaviour: @runMediator (medToMediator (mediatorToMed m)) xs@
-- equals @runMediator m xs@.  It is not an isomorphism because the buffer slot
-- introduced by 'mediatorToMed' is discarded.
medToMediator :: Med s a b -> Mediate.Mediator s a b
medToMediator med = Mediate.Mediator (medSeed med) (medStepDirect med) (medOwed med) (medDraw med)

-- | View a buffered 'Med' (produced by 'mediatorToMed') as a 'Mediator' over
-- the original residual @s@, discarding the output-buffer slot.
--
-- 'mediatorToMed' adds @(Maybe (Maybe b))@ to the residual so the two poles
-- can be scheduled independently.  That slot is an output register, not part
-- of the linear residual, so it must not be inspected by 'closeCertified'.
-- This function projects it away: each step starts with an empty buffer, runs
-- the full write-then-read step, and returns only the original residual.
medToMediatorBuffered :: Med (s, Maybe (Maybe b)) a b -> Mediate.Mediator s a b
medToMediatorBuffered med =
  Mediate.Mediator
    { Mediate.medInit = fst (medSeed med),
      Mediate.medStep = \s a ->
        let ((s', _), mb) = medStepDirect med (s, Nothing) a
         in (s', mb),
      Mediate.medOwed = \s -> medOwed med (s, Nothing),
      Mediate.medDraw = \s s' -> medDraw med (s, Nothing) (s', Nothing)
    }

-- | Linear mediator: no state is owed, every input is forwarded immediately.
--
-- A held value is pending output, so it is owed until emitted.
medLinear :: Med (Maybe a) a a
medLinear =
  Med
    { medSeed = Nothing,
      medIn = \(_, a) -> Just a,
      medOut = \case
        Just a -> (Nothing, Just a)
        Nothing -> (Nothing, Nothing),
      medOwed = isJust,
      medDraw = \_ _ -> Nothing
    }

-- | Pair-sum mediator: buffers the first integer, emits the sum on the second.
--
-- State is 'Mediate.PS' extended with the output-buffer slot introduced by
-- 'mediatorToMed'.  Only the 'Mediate.PS' component is owed; the buffer slot
-- is an output register.
medPairSum :: Med (Mediate.PS, Maybe (Maybe Int)) Int Int
medPairSum = mediatorToMed Mediate.pairSum

-- | Count mediator: emits the number of inputs seen so far.
--
-- The counter is state, not residual: nothing is owed at close.
medCount :: Med Int () Int
medCount =
  Med
    { medSeed = 0,
      medIn = \case
        (n, ()) -> n + 1,
      medOut = \case
        n -> (n, Just n),
      medOwed = const False,
      medDraw = Mediate.debtDraw
    }
