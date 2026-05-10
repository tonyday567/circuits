# Circuit Parsing

Parser combinators on Circuit. A parser consumes elements from a stream,
producing a result with remaining input, or signalling progress-aware
failure. The actual module is `Circuit.Parser` in `src/`.

## Parser type

```haskell
newtype Parser s a = Parser
  { unParser :: Circuit (->) Either [s] (These a [s])
  }
```

**Tensor: `Either`.** The `Either` tensor provides `<|>` — genuine
two-phase alternation. Try `p1`; if it fails without consuming (`That`),
try `p2`. This is the tensor's natural use for backtracking choice.

**Output: `These`.** `These a [s]` splits parser outcomes into three
cases:

| case        | meaning                           |
|-------------|-----------------------------------|
| `These a s` | consumed some, result + remainder |
| `This a`    | consumed everything, final result |
| `That s`    | no progress, stream intact        |

`That s` is the key innovation over `Maybe (a, s)` — it explicitly
signals "touched nothing, safe to backtrack" vs "consumed and failed"
(which `Maybe` can't express). The mtok refactor confirmed this:
`tokenizeKnot` uses all three arms naturally.

`These(..)` is re-exported from the module so consumers don't need
a direct `these` dependency.

## Running

```haskell
runParser :: Parser s a -> [s] -> These a [s]
runParser = reify . unParser
```

## Primitives via Lift

`Lift` embeds a function into Circuit. Character-level primitives:

```haskell
-- | Consume one element satisfying a predicate.
satisfy :: (s -> Bool) -> Parser s s
satisfy p = Parser $ Lift $ \case
  (x : []) | p x -> This x
  (x : xs) | p x -> These x xs
  xs              -> That xs

-- | Match a specific element.
char :: Eq s => s -> Parser s s
char c = satisfy (== c)

-- | Match a sequence.
string :: Eq s => [s] -> Parser s [s]
string = traverse char

-- | Consume any single element.
anyToken :: Parser s s
anyToken = Parser $ Lift $ \case
  (x : []) -> This x
  (x : xs) -> These x xs
  []       -> That []
```

## Stream decomposition: Uncons

`uncons` is the coinductive primitive — the input-side mirror of
`These` output. It's a pure function, not a Parser:

```haskell
uncons :: [s] -> These s [s]
uncons []     = That []
uncons (x:xs) = These x xs
```

Where parser output is `These result remainder`, `uncons` is
`These element remainder` — it peels one element off the front.
Every successful parse reduces to some number of `uncons` calls.

## Repetition: many / some

The mtok refactor established: `many` is `Lift` + plain recursion,
not `Knot`. Three pattern matches on `These` are sufficient:

```haskell
many :: Parser s a -> Parser s [a]
many p = Parser $ Lift $ \s -> go s []
  where
    go s acc = case runParser p s of
      This a     -> This (reverse (a : acc))
      These a s' -> go s' (a : acc)
      That s'    -> These (reverse acc) s'

some :: Parser s a -> Parser s [a]
some p = (:) <$> p <*> many p
```

`Knot` is for choice (below), not repetition. The `These` pattern
match carries all the control flow `many` needs — accumulate on
`These`, finalise on `This`, stop on `That`.

## Choice via Either tensor + Knot

`<|>` is where `Knot` pulls its weight. The `Either` tensor's two
phases map to the two branches of alternation:

```haskell
(<|>) :: Parser s a -> Parser s a -> Parser s a
Parser p1 <|> Parser p2 = Parser $ Knot body
  where
    body (Right s) = case reify p1 s of
      This a     -> Right (This a)      -- p1 consumed all, done
      That s'    -> Left s'             -- p1 failed, try p2
      These a s' -> Right (These a s')  -- p1 succeeded, done
    body (Left s) = case reify p2 s of
      result -> Right result            -- p2 result, win or lose
```

The `Knot` defunctionalises the two-phase alternation: `Right`
= try p1, `Left` = try p2. The `Either` tensor provides the
feedback channel that switches phases.

## mtok port (worked example)

mtok's tokenizer was ported from `regex-applicative` to
`Circuit.Parser`. The mapping:

| regex-applicative     | Circuit.Parser       |
|-----------------------|----------------------|
| `RE Char a`           | `Parser Char a`      |
| `sym 'a'`             | `char 'a'`           |
| `foldr1 (<|>) (map sym ['a'..'z'])` | `satisfy isAsciiLower` |
| `some`                | `some`               |
| `pure <$> p`          | `fmap (:[]) p`       |
| `findFirstPrefix p s` | `runParser p s`      |

The tokenizer loop changed from `Maybe (tok, rest)` to a three-arm
`These` match:

```haskell
tokenizeKnot s acc = case runParser token s of
  These tok rest -> tokenizeKnot rest (tok : acc)  -- got one, continue
  This tok       -> reverse (tok : acc)             -- final token
  That _         -> case s of (_:rest) -> tokenizeKnot rest acc  -- skip char
```

The `This` arm was new — the original `findFirstPrefix` never
returned end-of-stream. The `That` arm replaced the `Nothing` case
with explicit "no progress" semantics.

30 lines changed, build clean, all edge cases correct.

## These semantics

The mtok port validated the three-way `These` output in practice.
Each constructor has a clear role in the tokenizer:

| arm          | tokenizer meaning          | `<|>` behaviour   |
|-------------|----------------------------|--------------------|
| `These a s` | got token, keep going      | success, stop      |
| `This a`    | got final token, done      | success, EOF       |
| `That s`    | no match here, skip char   | try next alternative |

`That s` is the missing case in `Maybe (a, s)` — the signal that
says "I touched nothing, backtrack to the next branch." With
`Maybe`, `<|>` can't distinguish "failed without consuming" from
"failed after consuming, can't backtrack." `These` makes this
structural.

## Territory coverage

| library        | approach                  | status                                    |
|---------------|--------------------------|-------------------------------------------|
| `mtok`        | regex-applicative `RE s a`| 🟢 ported to Circuit.Parser             |
| `huihua`      | `Parser e a`, `Result e a`| `These` + error channel                  |
| `dotparse`    | FlatParse.Basic + TH      | same shape as huihua                     |
| `markup-parse`| tokenize → gather pipeline| Circuit tokenizer feeds Circuit builder  |

## regex-applicative bridge

The `RE s a` GADT maps to Circuit constructors. The mtok port
validated this mapping:

| `RE s a` constructor       | Circuit equivalent            | status    |
|---------------------------|------------------------------|-----------|
| `Symbol i (s -> Maybe a)` | `Lift` (satisfy/char)        | 🟢 tested |
| `Alt a b`                 | `Either` tensor (`<|>`)      | 🟢 tested |
| `App a b`                 | `Compose` (Applicative `*>`) | 🟢 tested |
| `Rep greed f b a`         | `many`/`some` (Lift+recursion)| 🟢 tested |
| `Fmap f a`                | `fmap`                       | 🟢 tested |
| `Fail`                    | `empty`                      | 🟢        |
| `Eps`                     | `pure`                       | 🟢        |

The regex engine's `findFirstPrefixWithUncons` — which takes an
`uncons` parameter — is now recognised as the `Uncons`/`These`
pattern: `uncons :: ss -> These s ss` feeds the engine, which
returns `These ss a` (remainder + result).

## Tensor summary

| tensor   | use in parsers            | semantic                      |
|---------|--------------------------|-------------------------------|
| `Either`| `<|>`, backtracking     | two-phase alternation via Knot|
| `These` | output, uncons           | progress-aware result/input   |

The `(,)` tensor from earlier sketches was replaced by `Either` —
the choice/backtracking use of `Either` is genuine alternation,
not the degenerate `either step step` pattern from I/O loops.

## What's next

- `Trace arr These` instance — native three-way control flow
- `choice :: [Parser s a] -> Parser s a` — generalised `<|>`
- huihua port — absorbed (Huihua.Parse.Parser replaced with circuits-parser)
