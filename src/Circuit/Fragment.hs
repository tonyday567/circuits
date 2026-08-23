{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Re-export hub for modular circuit syntax.
--
-- The individual signatures now live in their natural modules:
--
-- * 'Circuit.Syntax' — 'SigCompose', the generic 'Syntax' substrate, and the
--   'Algebra' / 'eval' machinery.
-- * 'Circuit.Trace' — 'SigYank', the free traced category.
-- * 'Circuit.SMC' — 'SigPar' and 'SigSwap', the free symmetric monoidal
--   category.
-- * 'Circuit.Bimonoid' — 'SigCopy', 'SigDiscard', 'SigPlus', 'SigZero', the
--   bimonoid structural rows.
-- * 'Circuit.Shared' — 'SigShared', shared-medium fusion.
-- * 'Circuit.Net' — the composite aliases built from SMC + bimonoid.
--
-- This module remains as a compatibility convenience: importing
-- 'Circuit.Fragment' brings in the whole lattice of syntax combinations.
module Circuit.Fragment
  ( -- * Core syntax (re-exported from "Circuit.Syntax" and "Circuit.Trace")
    Sig,
    (:+:) (..),
    Syntax (..),
    Algebra (..),
    eval,
    evalInto,
    SigCompose (..),
    AlgCat,
    SigYank (..),
    Trace,
    base,
    yank,

    -- * SMC signatures (re-exported from "Circuit.SMC")
    SigPar (..),
    SigSwap (..),

    -- * Bimonoid signatures (re-exported from "Circuit.Bimonoid")
    SigCopy (..),
    SigDiscard (..),
    SigCopyDiscard,
    SigPlus (..),
    SigZero (..),
    SigMergeZero,

    -- * Shared-medium fusion signature (re-exported from "Circuit.Shared")
    SigShared (..),

    -- * Common syntax combinations (re-exported from "Circuit.Net" and

    -- "Circuit.Shared")
    AlgShared,
    AlgRelevant,
    AlgAffine,
    AlgCartesian,
    AlgCoRelevant,
    AlgCoAffine,
    AlgCocartesian,
    AlgBimonoidal,
    AlgNet,
  )
where

import Circuit.Bimonoid
  ( SigCopy (..),
    SigCopyDiscard,
    SigDiscard (..),
    SigMergeZero,
    SigPlus (..),
    SigZero (..),
  )
import Circuit.Net
  ( AlgAffine,
    AlgBimonoidal,
    AlgCartesian,
    AlgCoAffine,
    AlgCoRelevant,
    AlgCocartesian,
    AlgNet,
    AlgRelevant,
  )
import Circuit.SMC (SigPar (..), SigSwap (..))
import Circuit.Shared (AlgShared, SigShared (..))
import Circuit.Syntax
  ( AlgCat,
    Algebra (..),
    Sig,
    SigCompose (..),
    Syntax (..),
    eval,
    evalInto,
    (:+:) (..),
  )
import Circuit.Trace (SigYank (..), Trace, base, yank)
