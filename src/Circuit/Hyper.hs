{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

-- | Hyperfunctions: the final encoding of traced monoidal categories.
--
-- A @Hyper@ is completely determined by its dual. To get a @b@ you must
-- provide a continuation that can itself produce an @a@.
--
-- The underlying construction is parameterised by a base category @arr@;
-- @Hyper@ itself is the function-category specialisation:
--
-- @
-- type Hyper = HyperF (->)
-- @
--
-- The two named targets are:
--
-- * @Hyper@ — arrows run in 'Data.Functor.Identity.Identity' and knots tie
--   by Haskell laziness.
-- * @'HyperF' ('K' m)@ — arrows run in @m@ and knots tie
--   with 'mfix'.
--
-- @HyperF@ lives in the same module so the function API is literally a
-- specialisation of the generic one.
--
-- === stateful arrows
--
-- A stateful function @(s, a) -> (s, b)@ is isomorphic to a K arrow
-- @a -> State s b@. 'stateK' records that isomorphism; it is the bridge
-- between 'Circuit.Body.Body' (the cartesian knot body) and the state
-- monad. The same isomorphism justifies 'Circuit.Body.Body' for general
-- tensors: a knot body @arr (t s a) (t s b)@ is stateful over the
-- tensor-paired carrier @t s -@.
--
-- === doctests
--
-- >>> import Circuit.Hyper
-- >>> import Circuit.Channel (trace)
-- >>> import Circuit.Layer (Free (..), run)
-- >>> import Circuit.Loop (Loop (..))
-- >>> import qualified Circuit.Loop as Loop
-- >>> import Circuit.Category (K (..))
-- >>> import Data.Functor.Identity (Identity (..))
-- >>> import Data.Profunctor (dimap)
--
-- >>> let body = liftH (K (\(xs, ()) -> Identity (0 : xs, take 3 xs)) :: K Identity ([Int], ()) ([Int], [Int]))
-- >>> runIdentity (observeH (trace body) ())
-- [0,0,0]
module Circuit.Hyper
  ( -- * Parameterised hyperfunctions
    HyperF (..),
    Hyper,
    pattern Hyper,

    -- * Base-category structure
    HyperBase (..),

    -- * Generic constructors and eliminators
    liftH,
    observeH,
    baseH,
    pushH,
    runHyperH,

    -- * Function-category hyperfunctions
    lift,
    observe,
    base,
    push,
    runHyper,

    -- * Either-loop state machine
    encodeEither,
    runEither,

    -- * K aliases
    liftArr,
    observeArr,
    baseArr,
    pushArr,
    runHyperArr,

    -- * Bridges from initial syntax
    encode,
    encodeFree,
    flatten,

    -- * Shared-medium composition via base change
    StateT (..),
    stateK,
    runSharedHyperH,
    sharedHyperBy,
  )
where

import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Layer (Free (..), freeze, run)
import Circuit.Loop qualified as Loop
import Circuit.Tensor (Schedule (..), Shared (..), sharedBy)
import Control.Monad.Fix (MonadFix, mfix)
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.Profunctor
import Data.These (These)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Prelude
-- >>> import Data.Profunctor
-- >>> import Circuit.Channel (Traced (..))
-- >>> import Circuit.Hyper (observe, lift, runHyper, Hyper (..), invoke)
-- >>> import Circuit.Layer (Free (..), run)
-- >>> import qualified Circuit.Loop as Loop
-- >>> let h = lift (+1) :: Hyper Int Int
-- >>> let f1 = (*2) :: Int -> Int
-- >>> let g1 = (+10) :: Int -> Int
-- >>> let f2 = (+3) :: Int -> Int
-- >>> let g2 = (*100) :: Int -> Int

-- ---------------------------------------------------------------------------
-- Local lazy state transformer
--
-- We keep this local to avoid a dependency on the @transformers@ package.
-- The implementation matches the standard lazy state transformer; the lazy
-- 'MonadFix' instance is the part we need, because 'trace' on
-- @HyperF (K (StateT s m))@ ties its knot with 'mfix'.
-- ---------------------------------------------------------------------------

-- | A lazy state monad transformer.
newtype StateT s m a = StateT {runStateT :: s -> m (a, s)}

instance (Functor m) => Functor (StateT s m) where
  fmap f m = StateT $ \s ->
    fmap (\ ~(a, s') -> (f a, s')) (runStateT m s)

instance (Functor m, Monad m) => Applicative (StateT s m) where
  pure a = StateT $ \s -> return (a, s)
  StateT mf <*> StateT mx = StateT $ \s -> do
    ~(f, s') <- mf s
    ~(x, s'') <- mx s'
    return (f x, s'')

instance (Monad m) => Monad (StateT s m) where
  m >>= k = StateT $ \s -> do
    ~(a, s') <- runStateT m s
    runStateT (k a) s'

instance (MonadFix m) => MonadFix (StateT s m) where
  mfix f = StateT $ \s -> mfix $ \ ~(a, _) -> runStateT (f a) s

-- ---------------------------------------------------------------------------
-- Hyperfunctions
-- ---------------------------------------------------------------------------

-- | A hyperfunction from @a@ to @b@ over the base category @arr@.
newtype HyperF arr a b = HyperF
  { -- | Feed a continuation into the hyperfunction.
    invoke :: arr (HyperF arr b a) b
  }

-- | The function-category hyperfunction.
type Hyper = HyperF (->)

-- | Bidirectional pattern for the function-category hyperfunction.
pattern Hyper :: (HyperF (->) b a -> b) -> Hyper a b
pattern Hyper f = HyperF f

{-# COMPLETE Hyper :: Hyper #-}

-- ---------------------------------------------------------------------------
-- Base-category structure
-- ---------------------------------------------------------------------------

-- | Enough structure on a base category @arr@ to give 'HyperF arr' a
-- traced monoidal category structure.
--
-- * 'Run' is the underlying functor in which arrows are evaluated.
-- * 'runArr' / 'mkArr' witness that @arr@ is concretely represented by
--   functions into 'Run'.
-- * 'fixRun' ties the recursive knot used by the trace.
class (Category arr, Monad (Run arr)) => HyperBase arr where
  -- | Underlying effect functor for evaluating arrows.
  type Run arr :: Type -> Type

  -- | Evaluate an arrow at a value.
  runArr :: arr a b -> a -> Run arr b

  -- | Build an arrow from a function into 'Run'.
  mkArr :: (a -> Run arr b) -> arr a b

  -- | Fixed-point operator for 'Run'.
  fixRun :: (a -> Run arr a) -> Run arr a

-- | Function category: arrows run in the identity monad and knots tie
-- by Haskell laziness.
instance HyperBase (->) where
  type Run (->) = Identity
  runArr f a = Identity (f a)
  mkArr f = runIdentity . f
  fixRun f = let x = f (runIdentity x) in x

-- | K arrows: arrows run in the monad and knots tie with 'mfix'.
instance {-# INCOHERENT #-} (MonadFix m) => HyperBase (K m) where
  type Run (K m) = m
  runArr = runK
  mkArr = K
  fixRun = mfix

-- | State-enriched K arrows: the medium enters as a base change.
--
-- Lazy 'StateT' is required so that 'mfix' can tie the recursive knot used by
-- 'trace'.  Strict 'StateT' lacks a general 'MonadFix' instance and would
-- force an explicit seed, repeating the B0 register-pattern lesson.
instance {-# OVERLAPPING #-} (MonadFix m) => HyperBase (K (StateT s m)) where
  type Run (K (StateT s m)) = StateT s m
  runArr = runK
  mkArr = K
  fixRun = mfix

-- ---------------------------------------------------------------------------
-- Generic constructors and eliminators
-- ---------------------------------------------------------------------------

-- | Push a base morphism onto a hyperfunction.
pushH ::
  (HyperBase arr) =>
  arr a b ->
  HyperF arr a b ->
  HyperF arr a b
pushH f h = HyperF $ mkArr $ \k -> do
  a_val <- runArr (invoke k) h
  runArr f a_val

-- | Embed a base morphism into a hyperfunction.
--
-- This is the coinductive character of the construction: the morphism is
-- pushed onto every future continuation.
liftH :: (HyperBase arr) => arr a b -> HyperF arr a b
liftH f = pushH f (liftH f)

-- | A constant hyperfunction.
baseH :: (HyperBase arr) => b -> HyperF arr a b
baseH b = HyperF $ mkArr $ \_ -> pure b

-- | Extract the underlying arrow as a function into 'Run'.
observeH :: (HyperBase arr) => HyperF arr a b -> a -> Run arr b
observeH h a = runArr (invoke h) (baseH a)

-- | Close the self-referential loop.
runHyperH ::
  forall arr a.
  (HyperBase arr) =>
  HyperF arr a a ->
  Run arr a
runHyperH h = fixRun @arr $ \a -> runArr (invoke h) (baseH a)

-- ---------------------------------------------------------------------------
-- Generic instances
-- ---------------------------------------------------------------------------

instance (HyperBase arr) => Category (HyperF arr) where
  id = liftH id
  f . g = HyperF $ mkArr $ \k -> runArr (invoke f) (g . k)

instance (HyperBase arr, Channel (,) arr) => Channel (,) (HyperF arr) where
  assoc = liftH assoc
  assoc' = liftH assoc'
  slide = liftH slide

instance (HyperBase arr, Strength (,) arr) => Strength (,) (HyperF arr) where
  strength h = liftH $ mkArr $ \(a, b) -> (a,) <$> observeH h b

instance
  ( HyperBase arr,
    Strength (,) arr
  ) =>
  Traced (,) (HyperF arr)
  where
  trace = traceHyper
    where
      traceHyper ::
        forall a b c.
        HyperF arr (a, b) (a, c) ->
        HyperF arr b c
      traceHyper body =
        HyperF $
          mkArr $ \k ->
            snd
              <$> fixRun @arr
                ( \pair -> do
                    let cont =
                          HyperF $
                            mkArr $ \_ -> do
                              a_val <- observeH k (snd pair)
                              pure (fst pair, a_val)
                    runArr (invoke body) cont
                )

-- ---------------------------------------------------------------------------
-- Function-category hyperfunctions
-- ---------------------------------------------------------------------------

-- | Embed a plain function into a hyperfunction.
--
-- >>> observe (lift (+1)) 5
-- 6
lift :: (a -> b) -> Hyper a b
lift = liftH

-- | Extract a plain function from a hyperfunction.
--
-- >>> observe (lift reverse) "hello"
-- "olleh"
observe :: Hyper a b -> (a -> b)
observe h = runIdentity . observeH h

-- | Ignores the input and returns a constant value.
--
-- >>> observe (base 42) undefined
-- 42
base :: a -> Hyper b a
base = baseH

-- | Push a plain function onto a hyperfunction.
--
-- >>> observe (push (+1) (lift (*2))) 5
-- 6
push :: (a -> b) -> Hyper a b -> Hyper a b
push = pushH

-- | Close the self-referential loop.
--
-- >>> runHyper (Hyper $ \_ -> 42 :: Int)
-- 42
runHyper :: Hyper a a -> a
runHyper = runIdentity . runHyperH

-- | Encode an Either-loop as a self-referential 'Hyper'.
--
-- Whereas 'encode' handles the @(,)@ tensor using 'Hyper''s own 'Traced'
-- instance, this preserves the Either-loop state in the function domain.
-- @Left a@ feeds back; @Right c@ terminates with output.
--
-- >>> :{
-- let step = \case
--       Right n | n < 3 -> Left (n + 1)
--       Right n         -> Right n
--       Left n  | n < 3 -> Left (n + 1)
--       Left n          -> Right n
-- :}
--
-- >>> runEither step (0 :: Int)
-- 3
encodeEither ::
  (Either a b -> Either a c) ->
  Hyper (Either a b -> c) (Either a b -> c)
encodeEither f = h
  where
    h =
      Hyper
        ( \k s ->
            case f s of
              Right c -> c
              Left a -> invoke k h (Left a)
        )

-- | Run an 'encodeEither'-encoded circuit from initial input @b@.
--
-- 'encodeEither' embeds the Either state machine into 'Hyper', 'runHyper'
-- ties the self-referential knot, and @Right b@ injects the initial state.
--
-- >>> :{
-- let step = \case
--       Right n | n < 3 -> Left (n + 1)
--       Right n         -> Right n
--       Left n  | n < 3 -> Left (n - 1)
--       Left n          -> Right n
-- :}
--
-- FIXME: the doctest for @runEither step (0 :: Int)@ used to hang forever
-- because the step function above loops between Left 0 and Left 1.
-- It has been removed until the example is fixed.
runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = runHyper (encodeEither f) (Right b)

-- * Instances

-- | 'Traced' instance for @Hyper@ with the @(,)@ tensor.
--
-- Routes the self-reference through explicit @Hyper@ values:
--
--   1. @invoke body cont@ calls the body, which will eventually ask @cont@
--      for an @(a, b)@ — the feedback pair.
--   2. @cont@ captures @a@ from @body@'s output (@fst pair@) and feeds it
--      back as the first component of its return. This is the knot: @a@
--      cycles through @body -> pair -> cont -> body@.
--   3. @invoke k (Hyper (const (snd pair)))@ converts the output @c@ to a
--      @b@ for @cont@'s return type — purely type plumbing.
--
-- >>> let body = lift (\(xs, ()) -> (0:xs, take 3 xs))
-- >>> observe (trace body) ()
-- [0,0,0]

-- | 'Profunctor' instance for @Hyper@.
--
-- 'dimap' routes both input and output through the continuation
-- structure.
instance Profunctor Hyper where
  dimap f g h = Hyper $ g . invoke h . dimap g f
  lmap f h = Hyper $ invoke h . rmap f
  rmap f h = Hyper $ f . invoke h . lmap f

-- Profunctor identity: dimap id id = id
--
-- >>> observe (dimap id id h) 5
-- 6
--
-- Profunctor composition: dimap f g . dimap f' g' = dimap (f' . f) (g . g')
--
-- >>> observe (dimap f1 g1 (dimap f2 g2 h)) 5
-- 1410
-- >>> observe (dimap (f2 . f1) (g1 . g2) h) 5
-- 1410
--
-- lmap f = dimap f id
--
-- >>> observe (lmap ((*2) :: Int -> Int) h) 5
-- 11
-- >>> observe (dimap ((*2) :: Int -> Int) id h) 5
-- 11
--
-- rmap g = dimap id g
--
-- >>> observe (rmap ((*2) :: Int -> Int) h) 5
-- 12
-- >>> observe (dimap id ((*2) :: Int -> Int) h) 5
-- 12

instance Functor (Hyper a) where
  fmap = rmap

-- ---------------------------------------------------------------------------
-- K aliases
-- ---------------------------------------------------------------------------

-- | Alias for 'pushH' on @K m@.
pushArr ::
  (MonadFix m) =>
  K m a b ->
  HyperF (K m) a b ->
  HyperF (K m) a b
pushArr = pushH

-- | Alias for 'liftH' on @K m@.
liftArr :: (MonadFix m) => K m a b -> HyperF (K m) a b
liftArr = liftH

-- | Alias for 'baseH' on @K m@.
baseArr :: (MonadFix m) => b -> HyperF (K m) a b
baseArr = baseH

-- | Alias for 'observeH' on @K m@.
observeArr ::
  (MonadFix m) =>
  HyperF (K m) a b ->
  a ->
  m b
observeArr = observeH

-- | Alias for 'runHyperH' on @K m@.
runHyperArr ::
  (MonadFix m) =>
  HyperF (K m) a a ->
  m a
runHyperArr = runHyperH

-- ---------------------------------------------------------------------------
-- Bridges from initial syntax
-- ---------------------------------------------------------------------------

-- | Encode a 'Free' category into a 'HyperF'.
--
-- The lift of the canonical fold 'run' into the final encoding.
--
-- Law: @'observe' . 'encodeFree' = 'run'@ — the two interpreters
-- from Free agree.
--
-- >>> observe (encodeFree (Lift (+1))) 5
-- 6
encodeFree ::
  (HyperBase arr) =>
  Free arr a b ->
  HyperF arr a b
encodeFree (Lift f) = liftH f
encodeFree (Compose f g) = encodeFree f . encodeFree g

-- | Encode a 'Loop' into a 'HyperF'.
--
-- This is the unique traced functor from the initial object ('Loop')
-- to the final object ('HyperF'), satisfying the commuting triangle
-- @'observe' . 'encode' = 'run'@.
--
-- 'Lift' constructors embed directly via 'liftH'; 'Knot' constructors
-- become 'trace' over a hyperfunction.
--
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Loop (Loop (..))
-- >>> observe (encode (Loop.Lift (+1) :: Loop (,) (->) Int Int)) 5
-- 6
encode ::
  ( HyperBase arr,
    Strength (,) arr
  ) =>
  Loop.Loop (,) arr a b ->
  HyperF arr a b
encode (Loop.Lift f) = liftH f
encode (Loop.Knot f) = trace (liftH f)

-- | Flatten a 'HyperF' to a 'Loop' by observing it.
--
-- This is the forgetful map from the final encoding to the initial encoding.
-- All feedback structure is lost; only the observable behaviour remains.
--
-- >>> let h = Circuit.Hyper.lift (+ 1)
-- >>> run (flatten h) 5
-- 6
--
-- Flatten then encode is not identity — the feedback structure is gone:
--
-- >>> let h = Circuit.Hyper.lift (+ 1)
-- >>> Circuit.Hyper.observe (encode (flatten h)) 5
-- 6
flatten ::
  (HyperBase arr) =>
  HyperF arr a b ->
  Loop.Loop (,) arr a b
flatten h = Loop.Lift (mkArr (observeH h))

-- ---------------------------------------------------------------------------
-- Shared-medium composition (the bridge square)
-- ---------------------------------------------------------------------------

-- | Lift a stateful function into the state-enriched K base.
--
-- This is the base change that makes the medium explicit: a body
-- @arr (s, a) (s, b)@ becomes a K arrow @a -> StateT s m b@.
stateK ::
  (Monad m) =>
  ((s, a) -> (s, b)) ->
  K (StateT s m) a b
stateK f = K $ \a -> StateT $ \s -> let (s', b) = f (s, a) in pure (b, s')

-- | Run a shared-state hyperfunction from an initial medium state.
runSharedHyperH ::
  (MonadFix m) =>
  s ->
  HyperF (K (StateT s m)) a b ->
  a ->
  m (b, s)
runSharedHyperH s0 h a = runStateT (observeH h a) s0

-- | Shared-medium fusion in the final encoding.
--
-- Two hyperfunctions whose inputs/outputs carry the medium state are fused
-- along that medium using the schedule.  This is the right-hand side of
-- the bridge square:
--
-- @
--   encode (sharedKnotBy sched k1 k2)  ≅  sharedHyperBy sched (encode (Lift k1)) (encode (Lift k2))
-- @
--
-- The implementation extracts the underlying arrows via 'observeH'/'mkArr',
-- composes them with the schedule-driven 'sharedBy', and re-encodes via
-- 'trace'/'liftH'.  The state-enriched base (@K (StateT s m)@) provides
-- the conceptual home for the medium; this combinator is its value-level
-- presentation.
sharedHyperBy ::
  forall arr s a b c d.
  ( HyperBase arr,
    Strength (,) arr,
    Shared (,) arr
  ) =>
  Schedule s ->
  HyperF arr (s, a) (s, b) ->
  HyperF arr (s, c) (s, d) ->
  HyperF arr (a, c) (These b d)
sharedHyperBy sched f g = trace (liftH (sharedBy sched f' g'))
  where
    f' = mkArr (observeH f)
    g' = mkArr (observeH g)
