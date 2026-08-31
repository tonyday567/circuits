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
-- itself.  'Optic' is the /integrand/ — the residual @ch@ is in the type, so
-- this is the residual-remembering rung.  'SomeOptic' hides it, which is the
-- coend without the quotient.
--
-- == Relationship to the rest of the library
--
-- 'Optic' is the curried form of 'Circuit.Poles.iomap': an optic is exactly a
-- pair of actions on channel poles, 'Circuit.Poles.prefixIn' on the conjoint
-- and 'Circuit.Poles.suffixOut' on the companion.  'opticPoles' is that
-- identification, and it costs nothing to state.
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
-- coherence the @Axioma.Circ@ oracles check at @(,)@, 'Either' and 'These'.
-- This matters for base arrows that are premonoidal and therefore have
-- 'Strength' but deliberately no 'Tensor' instance, such as @Circuit.Prob@.
module Circuit.Optic
  ( -- * Mixed optic
    Optic (..),
    SomeOptic (..),
    withSomeOptic,

    -- * Composition
    identityOptic,
    composeOptic,
    identitySomeOptic,
    composeSomeOptic,

    -- * Action on morphisms
    opticUpdate,
    someOpticUpdate,

    -- * Action on channel poles
    opticPoles,

    -- * Bridge to the polynomial lens
    opticAsLens,
    lensAsOptic,
  )
where

import Circuit.Category (Category, (.>))
import Circuit.Poles (Poles, iomap)
import Circuit.Poly (Mono, Morphism, applyLens, lens)
import Circuit.Tensor (Unit, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Optic
-- >>> import Circuit.Poles (Poles, poles0, splay0)
-- >>> import Circuit.Poly (applyLens)
-- >>> import Prelude hiding (id, (.))
-- >>> :{
-- let firstLens :: Optic (,) (->) String Int Int (Int, String) (Int, String)
--     firstLens = Optic (\(n, s) -> (s, n)) (\(s, n) -> (n, s))
--     outer :: Optic (,) (->) String (Int, Bool) (Int, Bool) ((Int, Bool), String) ((Int, Bool), String)
--     outer = Optic (\(p, s) -> (s, p)) (\(s, p) -> (p, s))
--     inner :: Optic (,) (->) Bool Int Int (Int, Bool) (Int, Bool)
--     inner = Optic (\(n, b) -> (b, n)) (\(b, n) -> (n, b))
--     prismLeft :: Optic Either (->) String Int Int (Either Int String) (Either Int String)
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
-- residual is the branch that did not match.
data Optic t arr ch a b s r = Optic
  { -- | Forward direction: introduce the residual and the codomain left boundary.
    opticForward :: arr s (t ch a),
    -- | Backward direction: consume the residual and the codomain right boundary.
    opticBackward :: arr (t ch b) r
  }

-- | A mixed optic with the residual existentially hidden.
--
-- There is no residual /value/ here, only a residual type: the forward leg
-- produces the residual and the backward leg consumes it.  This is why
-- 'SomeOptic' is cheaper than an existential body wrapper, which would have
-- to store a seed and therefore has no inhabitant at tensors with an
-- uninhabited unit.  'identitySomeOptic' exists at 'Either', where
-- @'Circuit.Tensor.Unit' 'Either' = 'Data.Void.Void'@ and the corresponding
-- pointed-body identity does not.
data SomeOptic t arr a b s r where
  SomeOptic :: Optic t arr ch a b s r -> SomeOptic t arr a b s r

-- | Eliminator for the existential residual type.
withSomeOptic ::
  SomeOptic t arr a b s r ->
  (forall ch. Optic t arr ch a b s r -> x) ->
  x
withSomeOptic (SomeOptic o) k = k o

-- | Identity optic at the boundary pair @(a,b)@.  The residual is the tensor
-- unit.
--
-- This is the only operation in the module that needs 'Unital' rather than
-- 'Strength', and it needs only the unitors.
identityOptic :: (Unital t arr) => Optic t arr (Unit t) a b a b
identityOptic = Optic unitl' unitl
{-# INLINE identityOptic #-}

-- | Vertical composition of mixed optics.
--
-- Given @opt1@ from @(s,r)@ to @(a,b)@ with residual @ch1@ and @opt2@ from
-- @(a,b)@ to @(u,v)@ with residual @ch2@, the composite has residual
-- @t ch1 ch2@ — the tensoring of residuals in the coend formula.  The
-- residual order matches 'Circuit.Body.mergeChannel': first-applied on the
-- left.
--
-- Note what is /absent/: composition reassociates and applies 'strength', but
-- never 'Circuit.Traced.slide'.  'Circuit.Body.mergeChannel' needs two slides,
-- because a single 'Circuit.Body.Body' must push one carrier past the payload
-- so that one arrow sees both.  An optic keeps its two residuals on the same
-- side throughout.  That is the precise sense in which body composition is the
-- fused case of optic composition.
--
-- Unit and associativity hold only up to the residual unitor and associator,
-- exactly as for 'Circuit.Circ.Circ'; the observational statements are in
-- @Axioma.Optic@.
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
  Optic t arr ch2 u v a b ->
  Optic t arr ch1 a b s r ->
  Optic t arr (t ch1 ch2) u v s r
composeOptic (Optic f2 b2) (Optic f1 b1) =
  Optic
    (f1 .> strength f2 .> assoc')
    (assoc .> strength b2 .> b1)
{-# INLINE composeOptic #-}

-- | 'identityOptic' with the residual hidden.
identitySomeOptic :: (Unital t arr) => SomeOptic t arr a b a b
identitySomeOptic = SomeOptic identityOptic
{-# INLINE identitySomeOptic #-}

-- | 'composeOptic' with the residuals hidden.  Once hidden, the bracketing
-- that makes 'composeOptic' associative only up to the associator is no longer
-- observable in the type.
composeSomeOptic ::
  (Strength t arr) =>
  SomeOptic t arr u v a b ->
  SomeOptic t arr a b s r ->
  SomeOptic t arr u v s r
composeSomeOptic (SomeOptic o2) (SomeOptic o1) = SomeOptic (composeOptic o2 o1)
{-# INLINE composeSomeOptic #-}

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
  Optic t arr ch a b s r ->
  arr a b ->
  arr s r
opticUpdate (Optic f b) m = f .> strength m .> b
{-# INLINE opticUpdate #-}

-- | 'opticUpdate' through the existential.
someOpticUpdate ::
  (Strength t arr) =>
  SomeOptic t arr a b s r ->
  arr a b ->
  arr s r
someOpticUpdate (SomeOptic o) = opticUpdate o
{-# INLINE someOpticUpdate #-}

-- | The action of an optic on channel poles.
--
-- This is 'Circuit.Poles.iomap' with its two arguments read as the legs of an
-- optic: 'opticForward' prefixes the conjoint, 'opticBackward' suffixes the
-- companion.  Since "Circuit.Poles" already describes that pair as "the left
-- action of @arr@ on @In@ poles" and "the right action of @arr@ on @Out@
-- poles", an optic /is/ a morphism of that enriched profunctor.
--
-- >>> let p = poles0 (const ()) (const ("hi", 7)) :: Poles (->) (String, Int) (String, Int)
-- >>> snd (splay0 (opticPoles firstLens p)) ()
-- (7,"hi")
opticPoles ::
  (Category arr) =>
  Optic t arr ch a b s r ->
  Poles arr (t ch a) (t ch b) ->
  Poles arr s r
opticPoles (Optic f b) = iomap f b
{-# INLINE opticPoles #-}

-- | A cartesian optic as a polynomial lens.
--
-- Currying the residual away turns the pair @s -> (ch, a)@, @(ch, b) -> r@
-- into @s -> (a, b -> r)@, which is exactly
-- @'Circuit.Poly.applyLens' :: 'Morphism' ('Mono' r s) ('Mono' b a) -> s -> (a, b -> r)@.
--
-- >>> let (a, put) = applyLens (opticAsLens (SomeOptic firstLens)) (3, "hello") in (a, put 9)
-- (3,(9,"hello"))
opticAsLens :: SomeOptic (,) (->) a b s r -> Morphism (Mono r s) (Mono b a)
opticAsLens (SomeOptic (Optic f g)) =
  lens (\s -> snd (f s)) (\s b -> g (fst (f s), b))

-- | A polynomial lens as a cartesian optic.
--
-- The residual is reconstructed as the continuation type @b -> r@ — the
-- classical "existential is a function" encoding.  So @'lensAsOptic'
-- . 'opticAsLens'@ changes the residual and is only an identity after the
-- coend quotient; @Axioma.Optic@ checks that it is an identity
-- observationally, which is that quotient in action.
lensAsOptic :: Morphism (Mono r s) (Mono b a) -> Optic (,) (->) (b -> r) a b s r
lensAsOptic m =
  Optic
    (\s -> let (a, k) = applyLens m s in (k, a))
    (\(k, b) -> k b)
