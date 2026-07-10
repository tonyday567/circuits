---
title: "circuits — imports and pragmas"
category: core
status: stable
tags: ["imports", "setup", "minimal"]
---

# circuits — imports and pragmas

Imports for using circuits.  The umbrella module `Circuit` re-exports everything.

```haskell
import Circuit
```

That's it.  `Circuit` brings in `Trace(..)`, `Traced`, `Co(..)`, `Contra(..)`, `close`, `trace`, `untrace`, `Free`, `Layer(..)`, `Cat2`, `NT`, `HNT`, `(:~>)`, `(:~~>)`, `lower`, `run`, `hmap`, `join`, `Monoid(..)`, `Comonoid(..)`, `Dagger(..)`, `Bimonoid`, `transpose`, `Mon`, `Net`, `enrich`, `melt`, `Hyper(..)`, `lift`, `observe`, `base`, `push`, `runHyper`, `encode`, `encodeEither`, `encodeFree`, `runEither`, `flatten`, `Braided(..)`, `ambient`, `assoc`, `assoc'`, `seed`, `absorb`, `release`, `coassoc`, `coassoc'`, `coseed`, `coabsorbL`, `coabsorbR`, `coreleaseL`, `coreleaseR`, `ambientBy`, `Action(..)`.

LANGUAGE pragmas used internally: `CPP`, `RankNTypes`, `UndecidableInstances`, `ConstraintKinds`, `GADTs`, `FlexibleInstances`.

For user code: `GHC2021` covers most, add `BlockArguments` if you want `\\case` style.  `Prelude hiding (Monoid)` if you bring in `Circuit` unqualified.

`>>>` and `Kleisli` come from `Control.Arrow` and `Control.Category` — not re-exported by Circuit.

## two tags

`Arr` embeds a base arrow. `Knot` introduces a feedback channel. Sequential composition is `(.)` or `(>>>)`.

The tensor choice lives in the type argument: `(,)` for lazy coinductive sharing, `Either` for iteration (`Left` = continue, `Right` = exit).

## minimal example

```haskell
import Circuit
import Control.Arrow (Kleisli(..), runKleisli)
import Control.Category ((>>>))
import Data.Bool (bool)
import System.IO (Handle, IOMode(ReadMode), hClose, hGetLine, hIsEOF, openFile)

openf :: Trace t (Kleisli IO) FilePath Handle
openf = Arr (Kleisli (\fp -> openFile fp ReadMode))

countLines :: Trace Either (Kleisli IO) Handle (Handle, Int)
countLines = Knot (Kleisli step)
  where
    step (Left (h, n)) =
      hIsEOF h >>= bool
        (hGetLine h >> pure (Left (h, n + 1)))
        (pure (Right (h, n)))
    step (Right h) = pure (Left (h, 0))

pipeline :: Trace Either (Kleisli IO) FilePath Int
pipeline = openf >>> countLines >>> Arr (Kleisli (\(h, n) -> hClose h >> pure n))

-- paste into ghci:
-- runKleisli (run pipeline) "readme.md"
```
