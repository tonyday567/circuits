{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | FinRel oracles: bimonoid laws, dagger collapse, and traced structure over
-- finite GF(2) linear relations.
module Axioma.FinRel
  ( finRelTopic,
  )
where

import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), Zero (..))
import Circuit.Category (id)
import Circuit.Dagger (Dagger (..), transpose)
import Circuit.FinRel
import Circuit.Tools.Test (check)
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
unitl1' = unitl'FinRel

unitr1' :: FinRel N1 (N1, ())
unitr1' = unitr'FinRel

unitl2' :: FinRel N2 ((), N2)
unitl2' = unitl'FinRel

unitr2' :: FinRel N2 (N2, ())
unitr2' = unitr'FinRel

unitr0 :: FinRel ((), ()) ()
unitr0 = unitrFinRel

discard0 :: FinRel () ()
discard0 = discard

zero0 :: FinRel () ()
zero0 = zero

-- | Dagger(FinRel) collapse witness: 'Copy' on the dagger requires
-- 'Merge' on the base, so the back of @copy@ is @plus@.  The
-- constructors are pinned by type signatures so the instance method
-- resolves unambiguously.
daggerCopy1 :: Dagger FinRel N1 (N1, N1)
daggerCopy1 = copy

daggerDiscard1 :: Dagger FinRel N1 ()
daggerDiscard1 = discard

finRelTopic :: IO [Bool]
finRelTopic = do
  putStrLn "FinRel bimonoid, dagger, and trace oracles"
  sequence
    [ -- copy/discard comonoid laws
      check "copy coassociative (n=1)" $
        parFinRel copy1 id1 `compFinRel` copy1 == assoc'FinRel `compFinRel` parFinRel id1 copy1 `compFinRel` copy1,
      check "copy coassociative (n=2)" $
        parFinRel copy2 id2 `compFinRel` copy2 == assoc'FinRel `compFinRel` parFinRel id2 copy2 `compFinRel` copy2,
      check "copy left counit (n=1)" $
        parFinRel discard1 id1 `compFinRel` copy1 == unitl1',
      check "copy left counit (n=2)" $
        parFinRel discard2 id2 `compFinRel` copy2 == unitl2',
      check "copy right counit (n=1)" $
        parFinRel id1 discard1 `compFinRel` copy1 == unitr1',
      check "copy right counit (n=2)" $
        parFinRel id2 discard2 `compFinRel` copy2 == unitr2',
      check "copy cocommutative (n=1)" $
        swapFinRel `compFinRel` copy1 == copy1,
      check "copy cocommutative (n=2)" $
        swapFinRel `compFinRel` copy2 == copy2,
      -- plus/zero monoid laws
      check "plus associative (n=1)" $
        plus1 `compFinRel` parFinRel plus1 id1 == plus1 `compFinRel` parFinRel id1 plus1 `compFinRel` assocFinRel,
      check "plus associative (n=2)" $
        plus2 `compFinRel` parFinRel plus2 id2 == plus2 `compFinRel` parFinRel id2 plus2 `compFinRel` assocFinRel,
      check "plus left unit (n=1)" $
        plus1 `compFinRel` parFinRel zero1 id1 `compFinRel` unitl1' == id1,
      check "plus left unit (n=2)" $
        plus2 `compFinRel` parFinRel zero2 id2 `compFinRel` unitl2' == id2,
      check "plus right unit (n=1)" $
        plus1 `compFinRel` parFinRel id1 zero1 `compFinRel` unitr1' == id1,
      check "plus right unit (n=2)" $
        plus2 `compFinRel` parFinRel id2 zero2 `compFinRel` unitr2' == id2,
      check "plus commutative (n=1)" $
        plus1 `compFinRel` swapFinRel == plus1,
      check "plus commutative (n=2)" $
        plus2 `compFinRel` swapFinRel == plus2,
      -- bialgebra laws
      check "bialgebra copy-plus (n=1)" $
        copy1 `compFinRel` plus1 == parFinRel plus1 plus1 `compFinRel` swapMiddle `compFinRel` parFinRel copy1 copy1,
      check "bialgebra copy-plus (n=2)" $
        copy2 `compFinRel` plus2 == parFinRel plus2 plus2 `compFinRel` swapMiddle2 `compFinRel` parFinRel copy2 copy2,
      check "bialgebra discard-plus (n=1)" $
        discard1 `compFinRel` plus1 == unitr0 `compFinRel` parFinRel discard1 discard1,
      check "bialgebra discard-plus (n=2)" $
        discard2 `compFinRel` plus2 == unitr0 `compFinRel` parFinRel discard2 discard2,
      check "bialgebra zero-copy (n=1)" $
        copy1 `compFinRel` zero1 == parFinRel zero1 zero1 `compFinRel` unitr'FinRel,
      check "bialgebra zero-copy (n=2)" $
        copy2 `compFinRel` zero2 == parFinRel zero2 zero2 `compFinRel` unitr'FinRel,
      check "bialgebra discard-zero" $
        compFinRel discard0 zero0 == (finId :: FinRel () ()),
      -- scalar arithmetic over GF(2)
      check "scalar True is identity" $
        finScalar True == id1,
      check "scalar False is idempotent" $
        compFinRel (finScalar False :: FinRel N1 N1) (finScalar False) == finScalar False,
      check "scalar False absorbs scalar True" $
        compFinRel (finScalar False :: FinRel N1 N1) (finScalar True) == finScalar False,
      check "scalar True after scalar False" $
        compFinRel (finScalar True :: FinRel N1 N1) (finScalar False) == finScalar False,
      -- Dagger(FinRel k) collapse: the dagger instances interlock the
      -- tensor-comonoid and the par-monoid in a single construction.
      check "Dagger(FinRel) copy front is FinRel copy" $
        front daggerCopy1 == copy1,
      check "Dagger(FinRel) copy back is FinRel plus" $
        back daggerCopy1 == plus1,
      check "Dagger(FinRel) discard front is FinRel discard" $
        front daggerDiscard1 == discard1,
      check "Dagger(FinRel) discard back is FinRel zero" $
        back daggerDiscard1 == zero1,
      check "Dagger(FinRel) transpose copy has plus in front" $
        front (transpose daggerCopy1) == plus1,
      -- traced structure
      check "trace yanking (n=1)" $
        traceFinRel (swapFinRel :: FinRel (N1, N1) (N1, N1)) == id1,
      check "trace of identity pair" $
        traceFinRel (parFinRel id1 id1 :: FinRel (N1, N1) (N1, N1)) == id1
    ]
