# circuits — API structure

## class relationships

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
  Action -.-> Sym
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
`Category → Free` and `Strength → Loop`.

`Loop → Net` is `enrich` — embedding the normal form into inspectable wiring.
`melt` (the forgetful fold `Net → Loop`) is one of many folds and is not drawn.

`Ends` (including boxes and queues), `Hyper`, and `Dagger` are deliberately
omitted from this core structure diagram.

## semantic and syntax streams

Same structure with the Law/construction dashed lines removed:

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

  Category --> Channel --> Strength --> Traced
  Category --> Tensor --> Action
  Free --> Sym --> Net
  Loop --> Net
```

## module view

Transparent boxes group the two enrichment zones by module:

```mermaid
graph LR
  CategoryMod["Circuit.Category<br/>Category"]

  subgraph ChannelMod ["Circuit.Channel"]
    Channel["Channel"]
    Strength["Strength"]
    Traced["Traced"]
  end

  subgraph TensorMod ["Circuit.Tensor"]
    Tensor["Tensor"]
    Action["Action"]
  end

  FreeMod["Circuit.Free<br/>Free"]
  SymMod["Circuit.Sym<br/>Sym"]
  NetMod["Circuit.Net<br/>Net"]
  LoopMod["Circuit.Loop<br/>Loop"]

  CategoryMod --> Channel --> Strength --> Traced
  CategoryMod --> Tensor --> Action
  FreeMod --> SymMod --> NetMod
  LoopMod --> NetMod
```
