-- | Finite relations as an explicit reference semantics.
--
-- Unlike 'Circuit.FinRel', which fixes the value set to @GF(2)@ and encodes
-- morphisms as linear subspaces, 'Rel' works with any type equipped with an
-- explicit finite listing of inhabitants.  Composition requires 'Eq' on the
-- middle type so that relational composition can be implemented by list
-- comprehension.
--
-- This module is intentionally not an instance of the unconstrained
-- 'Circuit.Category.Category' tower: 'relComp' needs an 'Eq' constraint on the
-- intermediate type, and the monoidal unitors / associators need explicit
-- 'Fin' evidence.  Use the named combinators directly when working with finite
-- relations.
module Circuit.Rel
  ( -- * Objects
    Fin (..),

    -- * Morphisms
    Rel (..),

    -- * Category structure
    relId,
    relComp,

    -- * Monoidal structure
    relPar,
    relSwap,
    relAssoc,
    relAssoc',
    relUnitl,
    relUnitl',
    relUnitr,
    relUnitr',

    -- * Bimonoid generators (require explicit finite set)
    relCopy,
    relDiscard,
    relPlus,
    relZero,

    -- * Convenience
    Finite (..),
  )
where

-- | Explicit finite set of values.
newtype Fin a = Fin {inhabitants :: [a]}

-- | A relation from @a@ to @b@, represented as a list of pairs.
newtype Rel a b = Rel {pairs :: [(a, b)]}
  deriving (Eq, Show)

-- | Identity relation on a finite set.
relId :: Fin a -> Rel a a
relId (Fin as) = Rel [(a, a) | a <- as]

-- | Relational composition: @R ; S@ contains @(a, c)@ whenever there exists a
-- @b@ with @(a, b) ∈ R@ and @(b, c) ∈ S@.
relComp :: (Eq b) => Rel b c -> Rel a b -> Rel a c
relComp (Rel r2) (Rel r1) =
  Rel [(a, c) | (a, b1) <- r1, (b2, c) <- r2, b1 == b2]

-- | Parallel (monoidal) product of relations.
relPar :: Rel a b -> Rel c d -> Rel (a, c) (b, d)
relPar (Rel r1) (Rel r2) =
  Rel [((a, c), (b, d)) | (a, b) <- r1, (c, d) <- r2]

-- | Swap the two components of a product.
relSwap :: Fin a -> Fin b -> Rel (a, b) (b, a)
relSwap (Fin as) (Fin bs) =
  Rel [((a, b), (b, a)) | a <- as, b <- bs]

-- | Associator @((a, b), c) -> (a, (b, c))@.
relAssoc :: Fin a -> Fin b -> Fin c -> Rel ((a, b), c) (a, (b, c))
relAssoc (Fin as) (Fin bs) (Fin cs) =
  Rel [(((a, b), c), (a, (b, c))) | a <- as, b <- bs, c <- cs]

-- | Inverse associator @(a, (b, c)) -> ((a, b), c)@.
relAssoc' :: Fin a -> Fin b -> Fin c -> Rel (a, (b, c)) ((a, b), c)
relAssoc' (Fin as) (Fin bs) (Fin cs) =
  Rel [((a, (b, c)), ((a, b), c)) | a <- as, b <- bs, c <- cs]

-- | Left unitor @((), a) -> a@.
relUnitl :: Fin a -> Rel ((), a) a
relUnitl (Fin as) = Rel [(((), a), a) | a <- as]

-- | Inverse left unitor @a -> ((), a)@.
relUnitl' :: Fin a -> Rel a ((), a)
relUnitl' (Fin as) = Rel [(a, ((), a)) | a <- as]

-- | Right unitor @(a, ()) -> a@.
relUnitr :: Fin a -> Rel (a, ()) a
relUnitr (Fin as) = Rel [((a, ()), a) | a <- as]

-- | Inverse right unitor @a -> (a, ())@.
relUnitr' :: Fin a -> Rel a (a, ())
relUnitr' (Fin as) = Rel [(a, (a, ())) | a <- as]

-- | Copy relation: @a ↦ (a, a)@.
relCopy :: Fin a -> Rel a (a, a)
relCopy (Fin as) = Rel [(a, (a, a)) | a <- as]

-- | Discard relation: @a ↦ ()@ for every inhabitant.
relDiscard :: Fin a -> Rel a ()
relDiscard (Fin as) = Rel [(a, ()) | a <- as]

-- | Merge relation for a finite magma: @((x, y), x `add` y)@ when the result
-- is an inhabitant of the finite set.
relPlus :: (Eq a) => Fin a -> (a -> a -> a) -> Rel (a, a) a
relPlus (Fin as) add =
  Rel [((x, y), z) | x <- as, y <- as, let z = add x y, z `elem` as]

-- | Point relation: the unit for 'relPlus' at a chosen element.
relZero :: a -> Rel () a
relZero a = Rel [((), a)]

-- | Types with a canonical finite enumeration.
class Finite a where
  finite :: Fin a

instance Finite () where
  finite = Fin [()]

instance Finite Bool where
  finite = Fin [False, True]

instance (Finite a, Finite b) => Finite (a, b) where
  finite = Fin [(a, b) | a <- inhabitants finite, b <- inhabitants finite]
