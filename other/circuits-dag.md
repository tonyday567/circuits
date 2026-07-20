# circuits — API structure

```mermaid
graph LR
  Category["Category"]
  Channel["Channel"]
  Strength["Strength"]
  Traced["Traced"]
  Tensor["Tensor"]
  Action["Action"]

  Free["Free"]
  Sym["Sym"]
  Net["Net"]
  Loop["Loop"]

  Category -.-> Free
  Strength -.-> Loop
  Traced -.-> Loop
  Tensor -.-> Sym
  Action -.-> Sym
  Tensor -.-> Loop
  Action -.-> Loop
  Tensor -.-> Net
  Action -.-> Net
  Traced -.-> Net

  Category --> Channel --> Strength --> Traced
  Category --> Tensor --> Action
  Free --> Sym --> Net
  Loop --> Net
```

**Solid arrows** show enrichment:
- Structural semantics: `Category → Channel → Strength → Traced`
- Functorial semantics: `Category → Tensor → Action`
- Syntax: `Free → Sym → Net` with `Loop` enriching to `Net`

**Thick magenta dashed arrows** are the `Layer` Laws — the constraints the type
family attaches to each syntax constructor:
- `Law Free = Discrete`
- `Law Sym = Action (,) + Discrete`
- `Law (Loop t) = Traced t + Discrete`
- `Law (Net t) = Traced t + Action (,) + Discrete`

**Other dashed arrows** are conceptual consumption / free construction:
`Category → Free`, `Strength → Loop`, and `Tensor → Sym/Loop/Net`.

`Loop → Net` is `enrich` — embedding the normal form into inspectable wiring.
`melt` (the forgetful fold `Net → Loop`) is one of many folds and is not drawn.

`Ends`, `Box`/`Queue`, `Hyper`, and `Dagger` are deliberately omitted from this
core structure diagram.
