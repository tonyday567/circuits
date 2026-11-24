{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Factorisations of a two-lane 'Step' into independently usable legs.
--
-- Each body chooses a different cut. 'Body' keeps serial commit/emit;
-- 'LensBody' keeps parallel view/set; 'OpticBody' exposes an existential
-- residual; 'ProfunctorBody' keeps serial pre/navigation/post legs;
-- 'FoldBody' has a unit seed and bare extract; 'EitherBody' and 'TheseBody'
-- split by source presence; 'Poles' is the memoryless corner. Fusion closes
-- a chosen route through these legs. Initialisation and seeding remain
-- outside the transition unless a body supplies them explicitly.
module Circuit.Body
  ( Body (..),
    Poles (..),
    FoldBody (..),
    TheseBody (..),
    EitherBody (..),
    LensBody (..),
    OpticBody (..),
    ProfunctorBody (..),
    fuse,
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
  )
where

import Circuit.Bimonoid (Copy (..))
import Circuit.Category (BiK (..), Category (..), K (..), (.>))
import Circuit.Poly (Lens, applyLens, lens)
import Circuit.Step (Step (..))
import Circuit.Tensor (Cocartesian (..), Const (..), ConstInject (..), SemiTensor (..), Symmetric (..), Tensor, TheseElim (..), Unit, Unital (..), innerSwap, unConst)
import Circuit.Traced (OuterSwap (..))
import Data.These (These (..), these)
import Prelude hiding (id, init, (.))

-- $setup
-- >>> import Circuit.Body
-- >>> import Circuit.Tensor (Const (..), unConst)
-- >>> import Data.These (These (..), these)

-- | First-input initialisation, commit, and post-commit emission.
data Body t t' ch ch' arr i o = Body
  { init :: arr i ch,
    commit :: arr (t ch i) ch',
    emit :: arr ch' (t' ch' o)
  }

-- | Compose commit and emit into one transition. 'init' is not part of the
-- transition and remains with the body and its runner.
fuse :: (Category arr) => Body t t' ch ch' arr i o -> Step t t' ch ch' arr i o
fuse (Body _ k p) = Step (p . k)

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

-- | A body's commit/emit legs as one 'BiK' arrow. 'init' is outside it.
bodyBiK :: Body (,) t' s s (->) i o -> BiK ((,) s) (t' s) i o
bodyBiK (Body _ k p) = BiK (p . k)

-- | A diagonal body's commit/emit legs as a lens.
bodyAsLens :: Body (,) Const ch ch (->) i o -> Lens ch ch o i
bodyAsLens (Body _ k e) = lens (unConst . e) (curry k)

-- | Supply input initialisation to a lens-derived body.
lensAsBody :: (i -> ch) -> Lens ch ch o i -> Body (,) Const ch ch (->) i o
lensAsBody j m = Body j (\(s, i) -> snd (applyLens m s) i) (Const . fst . applyLens m)

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
closedToGenerator (Body _ k p) = unitr' .> k .> p
