{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Circuit.Category (id, (.), (.>))
import Circuit.Channel (assoc, assoc', trace)
import Circuit.Dagger (CopyDiscard (..), MergeZero (..))
import Circuit.FinRel
import Circuit.Tensor (Action (..), Tensor (..))
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (id, (.))

type F = Bool

type N1 = FinObj 1

type N2 = FinObj 2

-- | Swap the second and third @n@-wire blocks of @((a,b),(c,d))@.
swapBlocks ::
  forall n.
  (KnownNat n) =>
  FinRel F ((FinObj n, FinObj n), (FinObj n, FinObj n)) ((FinObj n, FinObj n), (FinObj n, FinObj n))
swapBlocks = wiring perm
  where
    n = fromIntegral (natVal (Proxy @n))
    perm i
      | i < n = i
      | i < 2 * n = i + n
      | i < 3 * n = i - n
      | otherwise = i

swapMiddle :: FinRel F ((N1, N1), (N1, N1)) ((N1, N1), (N1, N1))
swapMiddle = swapBlocks @1

swapMiddle2 :: FinRel F ((N2, N2), (N2, N2)) ((N2, N2), (N2, N2))
swapMiddle2 = swapBlocks @2

-- | Annotated helpers to avoid ambiguous overloads.
id1 :: FinRel F N1 N1
id1 = id

id2 :: FinRel F N2 N2
id2 = id

copy1 :: FinRel F N1 (N1, N1)
copy1 = copy

copy2 :: FinRel F N2 (N2, N2)
copy2 = copy

discard1 :: FinRel F N1 ()
discard1 = discard

discard2 :: FinRel F N2 ()
discard2 = discard

plus1 :: FinRel F (N1, N1) N1
plus1 = plus

plus2 :: FinRel F (N2, N2) N2
plus2 = plus

zero1 :: FinRel F () N1
zero1 = zero

zero2 :: FinRel F () N2
zero2 = zero

unitl1' :: FinRel F N1 ((), N1)
unitl1' = unitl'

unitr1' :: FinRel F N1 (N1, ())
unitr1' = unitr'

unitl2' :: FinRel F N2 ((), N2)
unitl2' = unitl'

unitr2' :: FinRel F N2 (N2, ())
unitr2' = unitr'

unitr0 :: FinRel F ((), ()) ()
unitr0 = unitr

discard0 :: FinRel F () ()
discard0 = discard

zero0 :: FinRel F () ()
zero0 = zero

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

main :: IO ()
main = do
  results <-
    sequence
      [ -- copy/discard comonoid laws
        check "copy coassociative (n=1)" $
          par copy1 id1 . copy1 == assoc' . par id1 copy1 . copy1,
        check "copy coassociative (n=2)" $
          par copy2 id2 . copy2 == assoc' . par id2 copy2 . copy2,
        check "copy left counit (n=1)" $
          par discard1 id1 . copy1 == unitl1',
        check "copy left counit (n=2)" $
          par discard2 id2 . copy2 == unitl2',
        check "copy right counit (n=1)" $
          par id1 discard1 . copy1 == unitr1',
        check "copy right counit (n=2)" $
          par id2 discard2 . copy2 == unitr2',
        check "copy cocommutative (n=1)" $
          swap . copy1 == copy1,
        check "copy cocommutative (n=2)" $
          swap . copy2 == copy2,

        -- plus/zero monoid laws
        check "plus associative (n=1)" $
          plus1 . par plus1 id1 == plus1 . par id1 plus1 . assoc,
        check "plus associative (n=2)" $
          plus2 . par plus2 id2 == plus2 . par id2 plus2 . assoc,
        check "plus left unit (n=1)" $
          plus1 . par zero1 id1 . unitl1' == id1,
        check "plus left unit (n=2)" $
          plus2 . par zero2 id2 . unitl2' == id2,
        check "plus right unit (n=1)" $
          plus1 . par id1 zero1 . unitr1' == id1,
        check "plus right unit (n=2)" $
          plus2 . par id2 zero2 . unitr2' == id2,
        check "plus commutative (n=1)" $
          plus1 . swap == plus1,
        check "plus commutative (n=2)" $
          plus2 . swap == plus2,

        -- bialgebra laws
        check "bialgebra copy-plus (n=1)" $
          copy1 . plus1 == par plus1 plus1 . swapMiddle . par copy1 copy1,
        check "bialgebra copy-plus (n=2)" $
          copy2 . plus2 == par plus2 plus2 . swapMiddle2 . par copy2 copy2,
        check "bialgebra discard-plus (n=1)" $
          discard1 . plus1 == unitr0 . par discard1 discard1,
        check "bialgebra discard-plus (n=2)" $
          discard2 . plus2 == unitr0 . par discard2 discard2,
        check "bialgebra zero-copy (n=1)" $
          copy1 . zero1 == par zero1 zero1 . unitr',
        check "bialgebra zero-copy (n=2)" $
          copy2 . zero2 == par zero2 zero2 . unitr',
        check "bialgebra discard-zero" $
          discard0 . zero0 == (id :: FinRel F () ()),

        -- scalar arithmetic over GF(2)
        check "scalar True is identity" $
          finScalar True == id1,
        check "scalar False is idempotent" $
          (finScalar False :: FinRel F N1 N1) . finScalar False == finScalar False,
        check "scalar False absorbs scalar True" $
          (finScalar False :: FinRel F N1 N1) . finScalar True == finScalar False,
        check "scalar True after scalar False" $
          (finScalar True :: FinRel F N1 N1) . finScalar False == finScalar False,

        -- traced structure
        check "trace yanking (n=1)" $
          trace (swap :: FinRel F (N1, N1) (N1, N1)) == id1,
        check "trace of identity pair" $
          trace (par id1 id1 :: FinRel F (N1, N1) (N1, N1)) == id1
      ]
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."
