{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Channels, transitions, Moore runners, and neutral token streams.
--
-- 'Channel' keeps commit and emit legs independent. 'Body' identifies their
-- open-transition boundary, 'Moore' is the recurrent bare-output corner, and
-- 'Step' is one fused transition. The canonical seeded 'scanM' and 'foldM'
-- observe initial and final channels without imposing that schedule on every
-- Channel. 'Uncons', 'Cons', and 'Snoc' are the neutral stream interfaces.
module Circuit.Channel
  ( -- * Channels and transitions
    Channel (..),
    Body,
    Moore,
    MooreP,
    Step (..),
    fuse,

    -- * Canonical Moore runners
    scanM,
    foldM,

    -- * Body factorisations
    Poles (..),
    FoldBody (..),
    TheseBody (..),
    EitherBody (..),
    LensBody (..),
    OpticBody (..),
    ProfunctorBody (..),

    -- * Body assemblies and conversions
    close,
    unclose,
    polesK,
    pipe,
    iomap,
    fuseFoldBody,
    fuseTheseBody,
    fuseEitherBody,
    fuseLensBody,
    fuseOpticBody,
    fuseProfunctorBody,
    unfuseEitherBody,
    unfuseTheseBody,
    bodyBiK,
    bodyAsLens,
    lensAsBody,
    lensBodyAsLens,
    lensAsLensBody,
    lensBodyToOptic,
    opticToLensBody,
    lensAsOptic,
    opticAsLens,
    closedToGenerator,

    -- * Streams
    These (..),
    Uncons (..),
    Cons (..),
    Snoc (..),
  )
where

import Circuit.Bimonoid (Copy (..))
import Circuit.Category (BiK (..), Category (..), K (..), StateX, (.>))
import Circuit.Poly (Dir, Lens, Poly, Pos, applyLens, lens)
import Circuit.Tensor (Cocartesian (..), Const (..), ConstInject (..), SemiTensor (..), Symmetric (..), Tensor, TheseElim (..), Unit, Unital (..), innerSwap, unConst, unitl)
import Circuit.Traced (OuterSwap (..))
import Data.List (foldl', scanl)
import Data.These (These (..), these)
import Prelude hiding (id, init, (.))

-- $setup
-- >>> import Circuit.Channel
-- >>> import Circuit.Poly (applyLens)
-- >>> import Circuit.Tensor (Const (..), unConst)
-- >>> import Circuit.Traced (trace)
-- >>> import Data.These (These (..), these)

-- | A neutral two-lane morphism, with semantics supplied by its packagings
-- and runners.
--
-- Start with:
--
-- @
-- arr (t x y) (t' x' y')
-- @
--
-- At the pair/function corner this is one morphism @(x, y) -> (x', y')@,
-- not independent arrows @x -> x'@ and @y -> y'@. Either result may depend
-- on either source. Currying and braiding give two State readings,
-- @y -> StateX x x' y'@ and @x -> StateX y y' x'@. The bare arrow chooses
-- neither; 'StateX' is a view, not Step's intrinsic semantics.
--
-- The library parameters @ch ch'@ and @i o@ preserve the channel and
-- interface conventions used by machine composition. They do not remove
-- the underlying symmetry. A body or runner decides which lane is seeded,
-- threaded, observed, hidden, or eliminated.
--
-- The two lanes package the same morphism differently:
--
-- * "Circuit.Channel" — 'Circuit.Channel.Channel' keeps commit and emit independent;
--   'Circuit.Channel.Body' identifies their boundary so 'Circuit.Channel.fuse' can
--   land one open transition back here.
-- * "Circuit.Trace" — 'Circuit.Trace.Knot' hides the channel
--   existentially, and its one run is 'Circuit.Traced.trace'.
--
-- 'Circuit.Traced.trace' ties the channel as a fixpoint — lazily at @(,)@,
-- by closed iteration at 'Either' — while 'Circuit.Channel.scanM' and
-- 'Circuit.Channel.foldM' iterate over a tape from a supplied channel.
-- The runner is the semantics. Which steps fit which runs:
--
-- * Every step can be paired with a seed; that asks nothing of the
--   underlying morphism.
-- * A step fuses from a 'Circuit.Channel.Body' iff it is
--   Moore-disciplined: the output reads the fresh channel only, so the
--   step factors as @f x = (k x, e (k x))@. The shift register
--   @\\(s, i) -> (i, s)@ fails here — its output reads the stale
--   channel.
-- * A step traces at @(,)@ iff it is productive: the fresh channel's
--   constructor is produced before the stale channel is demanded. The
--   accumulator @\\(n, i) -> (n + i, n + i)@ fails here — the knot is
--   circular. At 'Either' the trace iterates strictly and productivity is
--   free.
--
-- == A worked example
--
-- The recent-window step is both Moore-disciplined (the window reads the
-- fresh channel) and productive (the channel's constructor is immediate):
--
-- >>> :{
-- let win :: ([Int], Int) -> ([Int], [Int])
--     win (ns, i) = (i : ns, take 3 (i : ns))
-- :}
--
-- As a visible-channel Moore machine over a tape, run by 'scanM':
--
-- >>> let m = Channel (\(ns, i) -> i : ns) (\ns -> ((), take 3 ns)) :: Moore (,) [Int] (->) Int [Int]
-- >>> scanM [] m [1,2,3,4]
-- [[],[1],[2,1],[3,2,1],[4,3,2]]
--
-- As a knot, run by 'Circuit.Traced.trace' (the 'Circuit.Trace.Knot'
-- packaging folds to exactly this): the channel ties to a constant
-- stream and the window is constant — no tape exists in a knot:
--
-- >>> trace win 7
-- [7,7,7]
--
-- Same step, two runs, different answers: the runner is the semantics.

-- | Package one two-lane morphism. The channel and interface names follow
-- the library convention; the underlying arrow remains runnerless and
-- unsealed. Category composition uses the diagonal channel and tensor, so
-- consecutive Steps compose through the same interface @arr i o@.
newtype Step t t' ch ch' arr i o = Step {step :: arr (t ch i) (t' ch' o)}

instance (Category arr) => Category (Step t t ch ch arr) where
  id :: forall a. Step t t ch ch arr a a
  id = Step id
  {-# INLINE id #-}

  (.) :: forall a b c. Step t t ch ch arr b c -> Step t t ch ch arr a b -> Step t t ch ch arr a c
  Step g . Step f = Step (g . f)
  {-# INLINE (.) #-}

-- | A commit leg and an emit leg with independent channel positions.
-- Composition is available only when an explicit link connects @posti@ to
-- @preo@; neither leg is an obligatory schedule for the other.
data Channel t t' prei posti preo posto arr i o = Channel
  { commit :: arr (t prei i) posti,
    emit :: arr preo (t' posto o)
  }

-- | The diagonal commit/emit channel used for one open transition.
type Body t t' old new arr i o = Channel t t' old new new new arr i o

-- | A recurrent Moore machine. Commit produces the channel observed by emit;
-- emit returns no continuing channel. Initialisation belongs to the runner or
-- an upstream channel, not to this recurrent value.
type Moore t ch arr i o = Channel t (,) ch ch ch () arr i o

-- | Compose a body's commit and emit into one open transition. This fusion
-- chooses @posti ~ preo@ and does not give arbitrary 'Step's a factorisation.
fuse :: (Category arr) => Body t t' old new arr i o -> Step t t' old new arr i o
fuse (Channel k p) = Step (p . k)

-- | The memoryless body at the @(Const, Const)@ corner. 'init' and 'commit'
-- share a type but not a job; no previous channel enters the operation.
data Poles ch arr i o = Poles
  { init :: arr i ch,
    commit :: arr i ch,
    emit :: arr ch o
  }

-- | Fire the initial write and then read.
close :: (Category arr) => Poles ch arr i o -> arr i o
close (Poles j _ o) = j .> o

-- | Lift a plain arrow as 'Poles'.
unclose :: (Category arr) => arr i o -> Poles o arr i o
unclose f = Poles f f id

-- | 'Poles' over a Kleisli arrow: the write effect, then the read.
polesK :: (a -> m ()) -> m b -> Poles () (K m) a b
polesK write receive = Poles (K write) (K write) (K $ const receive)

-- | One-shot pipeline: the first read crosses into the second write.
pipe :: (Category arr) => Poles ch1 arr a b -> Poles ch2 arr b c -> Poles ch1 arr a c
pipe (Poles j1 k1 o1) (Poles j2 _ o2) = Poles j1 k1 (o1 .> j2 .> o2)

-- | Precompose both write legs and postcompose the read leg.
iomap :: (Category arr) => arr i' i -> arr o o' -> Poles ch arr i o -> Poles ch arr i' o'
iomap f g (Poles j k o) = Poles (f .> j) (f .> k) (o .> g)

-- | A unit seed, a diagonal transition, and a bare extract.
data FoldBody t ch arr i o = FoldBody
  { begin :: arr (Unit t) ch,
    step :: arr (t ch i) ch,
    extract :: arr ch o
  }

-- | One leg for each 'These' source-presence pattern.
data TheseBody t' ch ch' arr i o = TheseBody
  { chLeg :: arr ch (t' ch' o),
    iLeg :: arr i (t' ch' o),
    bothLeg :: arr (ch, i) (t' ch' o)
  }

-- | An 'Either' source-split with an explicit collapse.
data EitherBody t t' ch ch' arr i o = EitherBody
  { chLeg :: arr ch (t' ch' o),
    iLeg :: arr i (t' ch' o),
    collapse :: arr (t ch i) (Either ch i)
  }

-- | Parallel update and pre-set observation legs.
data LensBody t ch ch' arr i o = LensBody
  { set :: arr (t ch i) ch',
    view :: arr ch o
  }

-- | A residual-mediated factorisation. The residual is existential, so
-- bodies related by sliding an arrow across it have the same fused arrow.
data OpticBody t ch ch' arr i o
  = forall r. OpticBody (arr ch (t r o)) (arr (t r i) ch')

-- | Serial pre-compose, navigation, and post-compose legs.
data ProfunctorBody t ch ch' arr i o = ProfunctorBody
  { pre :: arr (t ch i) ch,
    pmap :: arr ch ch',
    post :: arr ch' o
  }

-- | Commit and extract at the pair target, copying the fresh channel.
--
-- >>> let sb = FoldBody (const 0) (\(c, i) -> c + i) (* 2) :: FoldBody (,) Int (->) Int Int
-- >>> case fuseFoldBody sb of Step f -> f (3, 4 :: Int)
-- (7,14)
fuseFoldBody :: (Tensor (,) arr, Copy arr ch) => FoldBody t ch arr i o -> Step t (,) ch ch arr i o
fuseFoldBody (FoldBody _ k e) = Step (k .> copy .> tensor id e)

-- | The 'These' eliminator as a transition.
--
-- >>> let tb = TheseBody Left Right (\(c, i) -> Right (c + i)) :: TheseBody Either Int Int (->) Int Int
-- >>> let Step f = fuseTheseBody tb
-- >>> [f (This 5), f (That 5), f (These 3 4)]
-- [Left 5,Right 5,Right 7]
fuseTheseBody :: (TheseElim arr) => TheseBody t' ch ch' arr i o -> Step These t' ch ch' arr i o
fuseTheseBody (TheseBody ch i b) = Step (theseElim ch i b)

-- | Collapse to 'Either', then split the source legs.
--
-- >>> let sb = EitherBody (Left . (* 10)) (Right . (+ 1)) id :: EitherBody Either Either Int Int (->) Int Int
-- >>> let Step f = fuseEitherBody sb
-- >>> [f (Left 5), f (Right 5)]
-- [Left 50,Right 6]
fuseEitherBody :: (Cocartesian Either arr) => EitherBody Either t' ch ch' arr i o -> Step Either t' ch ch' arr i o
fuseEitherBody (EitherBody ch i c) = Step (c .> elim ch i)

-- | Fuse parallel lens legs through the residual representation.
--
-- >>> let lb = LensBody (\(c, i) -> c + i) (* 2) :: LensBody (,) Int Int (->) Int Int
-- >>> case fuseLensBody lb of Step f -> f (3, 4 :: Int)
-- (7,6)
fuseLensBody :: (Symmetric (,) arr, OuterSwap (,) arr, Copy arr ch) => LensBody (,) ch ch' arr i o -> Step (,) (,) ch ch' arr i o
fuseLensBody = fuseOpticBody . lensBodyToOptic

-- | Focus, swap the output past the input, and rebuild.
--
-- >>> let ob = OpticBody (\c -> (c, c * 2)) (\(c, i) -> c + i) :: OpticBody (,) Int Int (->) Int Int
-- >>> case fuseOpticBody ob of Step f -> f (3, 4 :: Int)
-- (7,6)
-- >>> let pr = OpticBody (\c -> if c > 0 then Right (c * 10) else Left c) (either id negate) :: OpticBody Either Int Int (->) Int Int
-- >>> case fuseOpticBody pr of Step f -> [f (Left 3), f (Left (-2)), f (Right 5)]
-- [Right 30,Left (-2),Left (-5)]
fuseOpticBody :: (Symmetric t arr, OuterSwap t arr) => OpticBody t ch ch' arr i o -> Step t t ch ch' arr i o
fuseOpticBody (OpticBody f b) = Step (tensor f id .> innerSwap .> tensor b id)

-- | Pre-compose, navigate, post-compose, and inject the 'Const' target.
--
-- >>> let pb = ProfunctorBody (\(c, i) -> c + i) (* 10) (+ 1) :: ProfunctorBody (,) Int Int (->) Int Int
-- >>> case fuseProfunctorBody pb of Step f -> unConst (f (3, 4 :: Int))
-- 71
fuseProfunctorBody :: (ConstInject arr) => ProfunctorBody t ch ch' arr i o -> Step t Const ch ch' arr i o
fuseProfunctorBody (ProfunctorBody a n o) = Step (a .> n .> o .> constIn)

-- | Every arrow out of 'Either' is uniquely its two source legs.
--
-- >>> let g = either (Left . (* 2)) (Right . (+ 1)) :: Either Int Int -> Either Int Int
-- >>> let Step h = fuseEitherBody (unfuseEitherBody (Step g))
-- >>> [h (Left 3), h (Right 3)] == [g (Left 3), g (Right 3)]
-- True
unfuseEitherBody :: Step Either t' ch ch' (->) i o -> EitherBody Either t' ch ch' (->) i o
unfuseEitherBody (Step f) = EitherBody (f . Left) (f . Right) id

-- | Every arrow out of 'These' is uniquely its three source legs.
--
-- >>> let g = these Left Right (\c i -> Right (c + i)) :: These Int Int -> Either Int Int
-- >>> let Step h = fuseTheseBody (unfuseTheseBody (Step g))
-- >>> [h (This 3), h (That 3), h (These 3 4)] == [g (This 3), g (That 3), g (These 3 4)]
-- True
unfuseTheseBody :: Step These t' ch ch' (->) i o -> TheseBody t' ch ch' (->) i o
unfuseTheseBody (Step f) = TheseBody (f . This) (f . That) (f . uncurry These)

-- | A body's commit/emit legs as one 'BiK' arrow.
bodyBiK :: Body (,) t' s s (->) i o -> BiK ((,) s) (t' s) i o
bodyBiK (Channel k p) = BiK (p . k)

-- | A diagonal body's commit/emit legs as a lens.
bodyAsLens :: Body (,) Const ch ch (->) i o -> Lens ch ch o i
bodyAsLens (Channel k e) = lens (unConst . e) (curry k)

-- | A lens as a diagonal commit/emit body.
lensAsBody :: Lens ch ch o i -> Body (,) Const ch ch (->) i o
lensAsBody m = Channel (\(s, i) -> snd (applyLens m s) i) (Const . fst . applyLens m)

-- | The parallel-legs body as a lens.
--
-- >>> let lb = LensBody (\(c, i) -> c + i) (* 2) :: LensBody (,) Int Int (->) Int Int
-- >>> let (v, put) = applyLens (lensBodyAsLens lb) 3 in (v, put 4)
-- (6,7)
lensBodyAsLens :: LensBody (,) ch ch' (->) i o -> Lens ch ch' o i
lensBodyAsLens (LensBody s v) = lens v (curry s)

-- | A lens as a parallel-legs body.
lensAsLensBody :: Lens ch ch' o i -> LensBody (,) ch ch' (->) i o
lensAsLensBody m = LensBody (\(s, i) -> snd (applyLens m s) i) (fst . applyLens m)

-- | Getter/putter into residual form, with the whole channel as residual.
lensBodyToOptic :: (Tensor (,) arr, Copy arr ch) => LensBody (,) ch ch' arr i o -> OpticBody (,) ch ch' arr i o
lensBodyToOptic (LensBody s v) = OpticBody (copy .> tensor id v) s

-- | Residual form back to getter/putter at the function corner.
opticToLensBody :: OpticBody (,) ch ch' (->) i o -> LensBody (,) ch ch' (->) i o
opticToLensBody (OpticBody f b) = LensBody (\(c, i) -> b (fst (f c), i)) (snd . f)

-- | A lens with the canonical update-function residual.
lensAsOptic :: Lens ch ch' o i -> OpticBody (,) ch ch' (->) i o
lensAsOptic m = OpticBody (\c -> let (o, k) = applyLens m c in (k, o)) (\(k, i) -> k i)

-- | Residual form back to a 'Lens'.
opticAsLens :: OpticBody (,) ch ch' (->) i o -> Lens ch ch' o i
opticAsLens (OpticBody f b) = lens (snd . f) (\c i -> b (fst (f c), i))

-- | Close the input at the tensor's unit and chain commit into emit.
closedToGenerator :: (Tensor t arr) => Body t t ch ch arr (Unit t) b -> arr ch (t ch b)
closedToGenerator (Channel k p) = unitr' .> k .> p

-- | A Moore machine on a polynomial interface.
type MooreP t ch arr (p :: Poly) = Moore t ch arr (Dir p) (Pos p)

-- | Observe the supplied channel before consuming input, then run every input
-- through ordinary commit and observe the fresh channel. Only commit-produced
-- channels feed later inputs. Empty input performs no commit and returns the
-- singleton initial observation; outputs remain incremental on infinite input.
--
-- >>> let sumM = Channel (uncurry (+)) ((),) :: Moore (,) Int (->) Int Int
-- >>> scanM 0 sumM [1,2,3,4]
-- [0,1,3,6,10]
-- >>> scanM 0 sumM []
-- [0]
scanM :: ch -> Moore (,) ch (->) i o -> [i] -> [o]
scanM ch0 (Channel c e) =
  fmap (e .> unitl) . scanl (curry c) ch0

-- | Fold inputs through ordinary commit from the supplied channel and observe
-- the final channel. Empty input performs no commit and emits the supplied
-- channel. The strict left fold forces each intermediate channel to weak-head
-- normal form.
--
-- >>> let sumM = Channel (uncurry (+)) ((),) :: Moore (,) Int (->) Int Int
-- >>> foldM 0 sumM [1,2,3,4]
-- 10
-- >>> foldM 0 sumM []
-- 0
foldM :: ch -> Moore (,) ch (->) i o -> [i] -> o
foldM ch0 (Channel c e) =
  unitl . e . foldl' (curry c) ch0

instance Uncons [a] a where
  uncons [] = That []
  uncons (x : xs) = These x xs
  nil = []

instance Cons [a] a where
  cons = (:)
  consNil = []

instance Snoc [a] a where
  snoc xs x = xs ++ [x]
  snocNil = []

-- | Stream coalgebra with explicit boundary.
--
-- @This x@ announces the final element when the representation knows that
-- boundary. Lazy lists instead use @These x xs@ for every nonempty input,
-- leaving exhaustion to the next step rather than demanding the tail early.
-- The 'nil' value is the stream-specific empty used to continue after a
-- 'This' result.
--
-- >>> uncons ([] :: [Int]) :: These Int [Int]
-- That []
-- >>> uncons ([1] :: [Int]) :: These Int [Int]
-- These 1 []
-- >>> uncons ([1,2,3] :: [Int]) :: These Int [Int]
-- These 1 [2,3]
class Uncons f s where
  uncons :: f -> These s f
  nil :: f

-- | Stream algebra: construct a stream by prepending one token on the left.
--
-- This is the construction dual of 'Uncons'.  Together they let code move
-- back and forth between tokens and streams using the same coalgebra.
class Cons f s where
  -- | Prepend one token to the left of a stream.
  cons :: s -> f -> f

  -- | The empty stream.
  consNil :: f

-- | Stream algebra: construct a stream by appending one token on the right.
--
-- This is the right-handed dual of 'Uncons'.
class Snoc f s where
  -- | Append one token to the right of a stream.
  snoc :: f -> s -> f

  -- | The empty stream.
  snocNil :: f
