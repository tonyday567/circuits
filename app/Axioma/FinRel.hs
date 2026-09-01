{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | FinRel oracles: bimonoid laws, dagger collapse, and traced structure over
-- finite GF(2) linear relations.
module Axioma.FinRel
  ( finRelTopic,
  )
where

import Axioma.Common (Verbosity (..), checkV)
import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), Zero (..))
import Circuit.Category (id)
import Circuit.Dagger (Dagger (..), transpose)
import Circuit.FinRel
import Control.Monad (when)
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (id, (.))

type N1 = FinObj 1

type N2 = FinObj 2

-- | Swap the second and third @n@-wire blocks of @((a,b),(c,d))@.
swapBlocks ::
  forall n.
  (KnownNat n) =>
  FinRel ((FinObj n, FinObj n), (FinObj n, FinObj n)) ((FinObj n, FinObj n), (FinObj n, FinObj n))
swapBlocks = wiring perm
  where
    n = fromIntegral (natVal (Proxy @n))
    perm i
      | i < n = i
      | i < 2 * n = i + n
      | i < 3 * n = i - n
      | otherwise = i

swapMiddle :: FinRel ((N1, N1), (N1, N1)) ((N1, N1), (N1, N1))
swapMiddle = swapBlocks @1

swapMiddle2 :: FinRel ((N2, N2), (N2, N2)) ((N2, N2), (N2, N2))
swapMiddle2 = swapBlocks @2

id1 :: FinRel N1 N1
id1 = finId

id2 :: FinRel N2 N2
id2 = finId

copy1 :: FinRel N1 (N1, N1)
copy1 = copy

copy2 :: FinRel N2 (N2, N2)
copy2 = copy

discard1 :: FinRel N1 ()
discard1 = discard

discard2 :: FinRel N2 ()
discard2 = discard

plus1 :: FinRel (N1, N1) N1
plus1 = plus

plus2 :: FinRel (N2, N2) N2
plus2 = plus

zero1 :: FinRel () N1
zero1 = zero

zero2 :: FinRel () N2
zero2 = zero

unitl1' :: FinRel N1 ((), N1)
unitl1' = wiring id

unitr1' :: FinRel N1 (N1, ())
unitr1' = wiring id

unitl2' :: FinRel N2 ((), N2)
unitl2' = wiring id

unitr2' :: FinRel N2 (N2, ())
unitr2' = wiring id

unitr0 :: FinRel ((), ()) ()
unitr0 = wiring id

discard0 :: FinRel () ()
discard0 = discard

zero0 :: FinRel () ()
zero0 = zero

-- | Swap the two @n@-wire blocks of @(n, n)@.
swapFinRel ::
  forall n.
  (KnownNat n) =>
  FinRel (FinObj n, FinObj n) (FinObj n, FinObj n)
swapFinRel = wiring $ \i ->
  let n = fromIntegral (natVal (Proxy @n))
   in if i < n then n + i else i - n

assocFinRel ::
  forall n.
  (KnownNat n) =>
  FinRel ((FinObj n, FinObj n), FinObj n) (FinObj n, (FinObj n, FinObj n))
assocFinRel = wiring id

assoc'FinRel ::
  forall n.
  (KnownNat n) =>
  FinRel (FinObj n, (FinObj n, FinObj n)) ((FinObj n, FinObj n), FinObj n)
assoc'FinRel = wiring id

-- | Dagger(FinRel) collapse witness: 'Copy' on the dagger requires
-- 'Merge' on the base, so the back of @copy@ is @plus@.  The
-- constructors are pinned by type signatures so the instance method
-- resolves unambiguously.
daggerCopy1 :: Dagger FinRel N1 (N1, N1)
daggerCopy1 = copy

daggerDiscard1 :: Dagger FinRel N1 ()
daggerDiscard1 = discard

finRelTopic :: Verbosity -> IO [Bool]
finRelTopic verbosity = do
  when (verbosity == Axioms) $ putStrLn "FinRel bimonoid, dagger, and trace oracles"
  sequence
    [ -- copy/discard comonoid laws
      checkV verbosity "copy coassociative (n=1)" $
        parFinRel copy1 id1 `compFinRel` copy1 == assoc'FinRel `compFinRel` parFinRel id1 copy1 `compFinRel` copy1,
      checkV verbosity "copy coassociative (n=2)" $
        parFinRel copy2 id2 `compFinRel` copy2 == assoc'FinRel `compFinRel` parFinRel id2 copy2 `compFinRel` copy2,
      checkV verbosity "copy left counit (n=1)" $
        parFinRel discard1 id1 `compFinRel` copy1 == unitl1',
      checkV verbosity "copy left counit (n=2)" $
        parFinRel discard2 id2 `compFinRel` copy2 == unitl2',
      checkV verbosity "copy right counit (n=1)" $
        parFinRel id1 discard1 `compFinRel` copy1 == unitr1',
      checkV verbosity "copy right counit (n=2)" $
        parFinRel id2 discard2 `compFinRel` copy2 == unitr2',
      checkV verbosity "copy cocommutative (n=1)" $
        swapFinRel `compFinRel` copy1 == copy1,
      checkV verbosity "copy cocommutative (n=2)" $
        swapFinRel `compFinRel` copy2 == copy2,
      -- plus/zero monoid laws
      checkV verbosity "plus associative (n=1)" $
        plus1 `compFinRel` parFinRel plus1 id1 == plus1 `compFinRel` parFinRel id1 plus1 `compFinRel` assocFinRel,
      checkV verbosity "plus associative (n=2)" $
        plus2 `compFinRel` parFinRel plus2 id2 == plus2 `compFinRel` parFinRel id2 plus2 `compFinRel` assocFinRel,
      checkV verbosity "plus left unit (n=1)" $
        plus1 `compFinRel` parFinRel zero1 id1 `compFinRel` unitl1' == id1,
      checkV verbosity "plus left unit (n=2)" $
        plus2 `compFinRel` parFinRel zero2 id2 `compFinRel` unitl2' == id2,
      checkV verbosity "plus right unit (n=1)" $
        plus1 `compFinRel` parFinRel id1 zero1 `compFinRel` unitr1' == id1,
      checkV verbosity "plus right unit (n=2)" $
        plus2 `compFinRel` parFinRel id2 zero2 `compFinRel` unitr2' == id2,
      checkV verbosity "plus commutative (n=1)" $
        plus1 `compFinRel` swapFinRel == plus1,
      checkV verbosity "plus commutative (n=2)" $
        plus2 `compFinRel` swapFinRel == plus2,
      -- bialgebra laws
      checkV verbosity "bialgebra copy-plus (n=1)" $
        copy1 `compFinRel` plus1 == parFinRel plus1 plus1 `compFinRel` swapMiddle `compFinRel` parFinRel copy1 copy1,
      checkV verbosity "bialgebra copy-plus (n=2)" $
        copy2 `compFinRel` plus2 == parFinRel plus2 plus2 `compFinRel` swapMiddle2 `compFinRel` parFinRel copy2 copy2,
      checkV verbosity "bialgebra discard-plus (n=1)" $
        discard1 `compFinRel` plus1 == unitr0 `compFinRel` parFinRel discard1 discard1,
      checkV verbosity "bialgebra discard-plus (n=2)" $
        discard2 `compFinRel` plus2 == unitr0 `compFinRel` parFinRel discard2 discard2,
      checkV verbosity "bialgebra zero-copy (n=1)" $
        copy1 `compFinRel` zero1 == parFinRel zero1 zero1 `compFinRel` (wiring id :: FinRel () ((), ())),
      checkV verbosity "bialgebra zero-copy (n=2)" $
        copy2 `compFinRel` zero2 == parFinRel zero2 zero2 `compFinRel` (wiring id :: FinRel () ((), ())),
      checkV verbosity "bialgebra discard-zero" $
        compFinRel discard0 zero0 == (finId :: FinRel () ()),
      -- scalar arithmetic over GF(2)
      checkV verbosity "scalar True is identity" $
        finScalar True == id1,
      checkV verbosity "scalar False is idempotent" $
        compFinRel (finScalar False :: FinRel N1 N1) (finScalar False) == finScalar False,
      checkV verbosity "scalar False absorbs scalar True" $
        compFinRel (finScalar False :: FinRel N1 N1) (finScalar True) == finScalar False,
      checkV verbosity "scalar True after scalar False" $
        compFinRel (finScalar True :: FinRel N1 N1) (finScalar False) == finScalar False,
      -- Dagger(FinRel k) collapse: the dagger instances interlock the
      -- tensor-comonoid and the par-monoid in a single construction.
      checkV verbosity "Dagger(FinRel) copy front is FinRel copy" $
        front daggerCopy1 == copy1,
      checkV verbosity "Dagger(FinRel) copy back is FinRel plus" $
        back daggerCopy1 == plus1,
      checkV verbosity "Dagger(FinRel) discard front is FinRel discard" $
        front daggerDiscard1 == discard1,
      checkV verbosity "Dagger(FinRel) discard back is FinRel zero" $
        back daggerDiscard1 == zero1,
      checkV verbosity "Dagger(FinRel) transpose copy has plus in front" $
        front (transpose daggerCopy1) == plus1,
      -- traced structure
      checkV verbosity "trace yanking (n=1)" $
        traceFinRel (swapFinRel :: FinRel (N1, N1) (N1, N1)) == id1,
      checkV verbosity "trace of identity pair" $
        traceFinRel (parFinRel id1 id1 :: FinRel (N1, N1) (N1, N1)) == id1
    ]
