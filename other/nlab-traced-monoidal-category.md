# Traced Monoidal Category (from nlab)

**Source:** https://ncatlab.org/nlab/show/traced+monoidal+category

---

## Idea

The concept of _traced monoidal category_ axiomatizes the structure on a monoidal category for it to have a sensible notion of (partial) trace the way it exists canonically in compact closed categories. Traced monoidal categories sometimes only have _right_ or _left_ traces, and are referred to as _right traced_ or _left traced_ respectively. A category with compatible right and left traces is called a planar traced category. If the right and left traces agree, then we call a planar traced category _spherical_.

Graphically, the trace of an endomorphism f:A→A is represented by the closed loop.

The ambiguity in whether to close the loop to the right or to the left is codified in the difference between left and right traced categories. Every pivotal category can be canonically made into a planar traced category by using its implicit distinguished morphisms to close loops. Pivotal categories which induce spherical traced structures are known as spherical categories. In this way, traced monoidal categories generalize the trace operation to categories which do not necessarily have duals.

In denotational semantics of programming languages, the trace is used to model recursion, though if the language is not substructural, then this can be simplified to a fixed point operator.

---

## Definition

A monoidal category 𝒞 is said to be _right traced_ if it is equipped with family of maps

```
tr^X_R : Hom(A ⊗ X, B ⊗ X) ⟶ Hom(A, B)
```

for all A, B, X ∈ 𝒞, satisfying the following four axioms:

### 1. Tightening (naturality in A, B)

For all A, B, C, D, X ∈ 𝒞, h : A → B, f : B ⊗ X → C ⊗ X, g : C → D:

```
tr^X_R((g ⊗ id_X) ∘ f ∘ (h ⊗ id_X)) = g ∘ tr^X_R(f) ∘ h
```

### 2. Sliding (naturality in X)

For all A, B, X, Y ∈ 𝒞, f : A ⊗ X → B ⊗ Y, g : Y → X:

```
tr^X_R((id_B ⊗ g) ∘ f) = tr^Y_R(f ∘ (id_A ⊗ g))
```

### 3. Vanishing

For all A, B, X, Y ∈ 𝒞:

```
tr^1_R(f) = f,  ∀ f : A → B
```

and

```
tr^{X⊗Y}_R(f) = tr^X_R(tr^Y_R(f))
```

for all f : A ⊗ X ⊗ Y → B ⊗ X ⊗ Y.

### 4. Strength

For all A, B, C, D, X ∈ 𝒞, f : C ⊗ X → D ⊗ X, g : A → B:

```
tr^X_R(g ⊗ f) = g ⊗ tr^X_R(f)
```

### 5. Yanking (in braided categories)

In the presence of a braiding (such as in a symmetric monoidal category), we additionally require:

```
Tr^X(β_{X,X}) = id_X
```

for all X ∈ 𝒞, where β : X ⊗ X → X ⊗ X is the braiding.

---

## Left Traced Category

A left traced category is defined similarly, with a family of morphisms

```
tr^X_L : Hom(X ⊗ A, X ⊗ B) → Hom(A, B)
```

satisfying symmetric axioms (X on the left).

---

## Planar and Spherical Traced Categories

A planar traced category is a monoidal category 𝒞 which is simultaneously left and right traced, such that the following axioms are satisfied:

### Interchange

For all A, B, X, Y ∈ 𝒞, f : Y ⊗ A ⊗ X → Y ⊗ B ⊗ X:

```
tr^X_R(tr^Y_L(f)) = tr^Y_L(tr^X_R(f))
```

### Left Pivoting

For all A, B ∈ 𝒞, f : 1 → A ⊗ B:

```
tr^B_R(id_B ⊗ f) = tr^A_L(f ⊗ id_A)
```

### Right Pivoting

For all A, B ∈ 𝒞, f : A ⊗ B → 1:

```
tr^B_R(id_B ⊗ f) = tr^A_L(f ⊗ id_A)
```

---

A spherical trace category is a planar traced category in which the left and right partial traces agree. That is, for any endomorphism f : A → A in 𝒞 we have:

```
tr^A_R(f) = tr^A_L(f)
```

---

## Examples

1. **Finite-dimensional vector spaces:** The category of finite-dimensional vector spaces is traced monoidal, with trace as a generalization of matrix trace.

2. **Profunctors:** The category of profunctors is compact closed, hence traced monoidal.

3. **Sets and partial functions:** The category of sets and partial functions with coproduct monoidal structure is traced, modeling "while loops" in programming.

4. **Pointed cpos:** The category of pointed complete partial orders and continuous functions is traced. In Haskell notation:
   ```
   Tr_{A,B}^X(f)(a) = let (b, x) = f(a, x) in b
   ```
   This is a parameterized fixed point operator.

5. **Monoids with divisibility:** For a cancellative commutative monoid M with divisibility relation, (M, |) with monoidal product is traced monoidal.

---

## Properties

### Relation to Compact Closed Categories

Every compact closed category is equipped with a canonical trace. Conversely, given a traced monoidal category 𝒞, there is a free construction completion to a compact closed category Int(𝒞) (Joyal-Street-Verity).

The objects of Int(𝒞) are pairs (A⁺, A⁻) of objects of 𝒞. A morphism (A⁺, A⁻) → (B⁺, B⁻) is given by A⁺ ⊗ B⁻ → A⁻ ⊗ B⁺ in 𝒞.

### In Cartesian Monoidal Categories

For a cartesian monoidal category, the existence of a trace operator is equivalent to the existence of a parameterized fixed point operator satisfying certain properties (Hasegawa 1997).

### Categorical Semantics

Traced monoidal categories serve as an "operational" categorical semantics for linear logic, known as Geometry of Interactions. The free compact closure Int(𝒞) is sometimes called the Geometry of Interaction construction.

---

## References

- Joyal, Street, Verity (1996). Traced monoidal categories. Math. Proc. Camb. Phil. Soc. 119, 447-468.
- Selinger (2011). A survey of graphical languages for monoidal categories.
- Hasegawa (1997). Recursion from Cyclic Sharing: Traced Monoidal Categories and Models of Cyclic Lambda Calculi.
- Abramsky, Haghverdi, Scott (2002). Geometry of Interaction and Linear Combinatory Algebras.
