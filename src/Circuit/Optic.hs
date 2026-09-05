-- | Mixed optics as residual maps.
--
-- In the equipment-optics story an optic between two spans with common
-- boundaries is a globular 2-cell between the corresponding loose arrows.  In
-- @Prof@ that unwinds to the mixed-optic coend
--
-- @
--   Optic_M((S,R),(A,B)) = ∫^M C(S, M ⊙ A) × D(M ⊙ B, R)
-- @
--
-- where @⊙@ is a monoidal action.  In @circuits@ the action is the tensor @t@
-- itself.  'Optic' is the /integrand/ of that coend: the residual @ch@ sits in
-- the type, so this is the residual-remembering form.  The coend quotient
-- itself is never taken here — it is witnessed observationally, by the
-- lens round-trip oracles in @Axioma.Optic@.
--
-- == Relationship to the rest of the library
--
-- 'Optic' is the curried form of 'Circuit.Equip.iomap': a pointed optic is
-- exactly a pair of actions on channel poles, 'opticForward' precomposing the
-- conjoint and 'opticBackward' postcomposing the companion.  'opticPoles' is
-- that identification, and it costs nothing to state.
--
-- The objects of the optic category are boundary /pairs/, which the local
-- 'Circuit.Category.Category' class cannot index directly.  "Circuit.Poly"
-- already solves that problem: @'Circuit.Poly.Mono' i o@ packages a boundary
-- pair as a single @Poly@, and @instance Category Morphism@ is the wiki's
-- "category for free".  So this module does not duplicate that instance; it
-- maps into it, with 'opticAsLens' and 'lensAsOptic'.
--
-- == Constraints
--
-- Only 'identityOptic' needs 'Unital', for the unitors.  Composition and the
-- update action need nothing beyond 'Strength', because
-- @'strength' f == 'Circuit.Tensor.tensor' 'Circuit.Category.id' f@ — a
-- coherence the Axioma oracles check at @(,)@, 'Either' and 'These'.
-- This matters for base arrows that are premonoidal and therefore have
-- 'Strength' but deliberately no 'Tensor' instance, such as @Circuit.Prob@.
module Circuit.Optic
  ( -- * Mixed optic
    Optic (..),

    -- * Composition
    identityOptic,
    composeOptic,

    -- * Action on morphisms
    opticUpdate,

    -- * Action on channel poles
    opticPoles,

    -- * Bridge to the polynomial lens
    opticAsLens,
    lensAsOptic,

    -- * Bridge to pointed processes
    processAsLens,
    lensAsProcess,
  )
where

import Circuit.Category (Category, (.>), (<.))
import Circuit.Equip (Poles, iomap)
import Circuit.Poly (Lens, applyLens, lens)
import Circuit.Process (Process (..))
import Circuit.Tensor (Unit, Unital (..))
import Circuit.Traced (Assoc (..), Strength (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Optic
-- >>> import Circuit.Equip (Poles (..))
-- >>> import Circuit.Poly (applyLens)
-- >>> import Prelude hiding (id, (.))
-- >>> :{
-- let firstLens :: Optic (,) String (->) Int Int (Int, String) (Int, String)
--     firstLens = Optic (\(n, s) -> (s, n)) (\(s, n) -> (n, s))
--     outer :: Optic (,) String (->) (Int, Bool) (Int, Bool) ((Int, Bool), String) ((Int, Bool), String)
--     outer = Optic (\(p, s) -> (s, p)) (\(s, p) -> (p, s))
--     inner :: Optic (,) Bool (->) Int Int (Int, Bool) (Int, Bool)
--     inner = Optic (\(n, b) -> (b, n)) (\(b, n) -> (n, b))
--     prismLeft :: Optic Either String (->) Int Int (Either Int String) (Either Int String)
--     prismLeft =
--       Optic
--         (\case { Left n -> Right n; Right s -> Left s })
--         (\case { Left s -> Right s; Right n -> Left n })
-- :}

-- | A mixed optic from @(s,r)@ to @(a,b)@ with residual @ch@.
--
-- * @opticForward :: arr s (t ch a)@ splits the domain left boundary into the
--   residual and the codomain left boundary.
-- * @opticBackward :: arr (t ch b) r@ recombines the residual with the
--   codomain right boundary.
--
-- For @t = (,)@ and @arr = (->)@ this is the concrete lens pair
-- @s -> (ch, a)@ and @(ch, b) -> r@.  For @t = 'Either'@ it is a prism: the
-- residual is the branch that did not match.  The residual is produced by the
-- forward leg and consumed by the backward leg, never stored — so the
-- identity exists even at tensors with an uninhabited unit, where a
-- body-based existential has no inhabitant.  'identityOptic' exists at
-- 'Either', where @'Circuit.Tensor.Unit' 'Either' = 'Data.Void.Void'@.
data Optic t ch arr a b s r = Optic
  { -- | Forward direction: introduce the residual and the codomain left boundary.
    opticForward :: arr s (t ch a),
    -- | Backward direction: consume the residual and the codomain right boundary.
    opticBackward :: arr (t ch b) r
  }

-- | Identity optic at the boundary pair @(a,b)@.  The residual is the
-- tensor unit.
--
-- This is the only operation in the module that needs 'Unital' rather than
-- 'Strength', and it needs only the unitors.
identityOptic :: (Unital t arr) => Optic t (Unit t) arr a b a b
identityOptic = Optic unitl' unitl
{-# INLINE identityOptic #-}

-- | Vertical composition of mixed optics.
--
-- Given @opt1@ from @(s,r)@ to @(a,b)@ with residual @ch1@ and @opt2@ from
-- @(a,b)@ to @(u,v)@ with residual @ch2@, the composite has residual
-- @t ch1 ch2@ — the tensoring of residuals in the coend formula.  The
-- residual order matches 'Circuit.Body.seqCompose': first-applied on the
-- left.
--
-- Note what is /absent/: composition reassociates and applies 'strength', but
-- never 'Circuit.Traced.slide'.  'Circuit.Body.seqCompose' needs two slides,
-- because a single 'Circuit.Body.Body' must push one carrier past the payload
-- so that one arrow sees both.  A pointed optic keeps its two residuals on the
-- same side throughout.  That is the precise sense in which body composition
-- is the fused case of optic composition.
--
-- Unit and associativity hold only up to the residual unitor and associator,
-- exactly as for the squares in "Circuit.Equip"; the observational statements
-- are in @Axioma.Optic@.
--
-- >>> opticUpdate (composeOptic inner outer) (+ 1) ((3, True), "hi")
-- ((4,True),"hi")
--
-- The same result by nesting the updates — functoriality of 'opticUpdate':
--
-- >>> opticUpdate outer (opticUpdate inner (+ 1)) ((3, True), "hi")
-- ((4,True),"hi")
composeOptic ::
  (Strength t arr) =>
  Optic t ch2 arr u v a b ->
  Optic t ch1 arr a b s r ->
  Optic t (t ch1 ch2) arr u v s r
composeOptic (Optic f2 b2) (Optic f1 b1) =
  Optic
    (f1 .> strength f2 .> assoc')
    (assoc .> strength b2 .> b1)
{-# INLINE composeOptic #-}

-- | Apply an optic to a plain base-arrow morphism.
--
-- A lens turns a focus-update into a whole-update; a prism turns a
-- branch-update into a sum-update.
--
-- >>> opticUpdate firstLens (+ 1) (3, "hello")
-- (4,"hello")
--
-- >>> (opticUpdate prismLeft (+ 1) (Left 3), opticUpdate prismLeft (+ 1) (Right "hi"))
-- (Left 4,Right "hi")
--
-- Lawfulness is not enforced.  @'opticUpdate' o 'Circuit.Category.id' ==
-- 'Circuit.Category.id'@ is the round-trip condition, and a well-typed optic
-- can fail it; @Axioma.Optic@ carries a witness that it can.
opticUpdate ::
  (Strength t arr) =>
  Optic t ch arr a b s r ->
  arr a b ->
  arr s r
opticUpdate (Optic f b) m = f .> strength m .> b
{-# INLINE opticUpdate #-}

-- | The action of an optic on channel poles.
--
-- This is 'Circuit.Equip.iomap' with its two arguments read as the legs of an
-- optic: 'opticForward' precomposes the conjoint, 'opticBackward'
-- postcomposes the companion.  A pointed optic /is/ a morphism of that
-- enriched profunctor.
--
-- >>> let p = Poles fst (\ch -> (ch, 7)) :: Poles String String (->) (->) (String, Int) (String, Int)
-- >>> companion (opticPoles firstLens p) "hi"
-- (7,"hi")
opticPoles ::
  (Category arr) =>
  Optic t ch arr a b s r ->
  Poles ch ch arr arr (t ch a) (t ch b) ->
  Poles ch ch arr arr s r
opticPoles (Optic f b) = iomap f b
{-# INLINE opticPoles #-}

-- | A cartesian optic as a polynomial lens.
--
-- Currying the residual away turns the pair @s -> (ch, a)@, @(ch, b) -> r@
-- into @s -> (a, b -> r)@, which is exactly
-- @'Circuit.Poly.applyLens' :: 'Morphism' ('Mono' r s) ('Mono' b a) -> s -> (a, b -> r)@.
--
-- >>> let (a, put) = applyLens (opticAsLens firstLens) (3, "hello") in (a, put 9)
-- (3,(9,"hello"))
opticAsLens :: Optic (,) ch (->) a b s r -> Lens s r a b
opticAsLens (Optic f g) =
  lens (\s -> snd (f s)) (\s b -> g (fst (f s), b))

-- | A polynomial lens as a cartesian optic.
--
-- The residual is reconstructed as the continuation type @b -> r@ — the
-- classical "existential is a function" encoding.  So @'lensAsOptic'
-- . 'opticAsLens'@ changes the residual and is only an identity after the
-- coend quotient; @Axioma.Optic@ checks that it is an identity
-- observationally, which is that quotient in action.
lensAsOptic :: Lens s r a b -> Optic (,) (b -> r) (->) a b s r
lensAsOptic m =
  Optic
    (\s -> let (a, k) = applyLens m s in (k, a))
    (\(k, b) -> k b)

-- | A pointed monomial process as a polynomial lens.
processAsLens :: Process s i o -> Lens s s o i
processAsLens pp = lens get put
  where
    get s = processExtract pp s
    put s = processStep pp s

-- | Build a pointed process from a polynomial lens and a seed.
lensAsProcess :: Lens s s o i -> s -> Process s i o
lensAsProcess m s0 =
  Process
    s0
    (\s i -> snd (applyLens m s) i)
    (\s -> fst (applyLens m s))
