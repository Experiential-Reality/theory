---
status: DERIVED
depends_on:
  - factorization-calculus.md
  - ../lie-theory/lie-correspondence.md
  - ../derived/manifold-foundations.md
---

# Structural Cost Conservation

> **Status**: Derived — Cost is conserved under factorization.

This document proves that **structural cost is conserved** during refactoring (factorization). Factorization reveals hidden cost — it doesn't reduce total cost.

---

## Quick Summary (D≈7 Human Traversal)

**Cost conservation in 7 steps:**

1. **C : S → ℝ⁺** — cost function on structures
2. **C(b), C(l), C(d)** — primitive costs (proven exact formulas)
3. **C_total = C_visible + C_hidden** — decomposition into explicit + implicit
4. **Conservation: C(S) = C(FACTOR(S))** — total cost unchanged
5. **FACTOR: C_hidden → C_visible** — factorization reveals hidden cost
6. **Explicitness(S) = C_visible/C_total** — fraction of cost that's explicit
7. **Monotonic: FACTOR increases explicitness** — approaches 1 at normal form

| Quantity | Definition | FACTOR Effect |
|----------|------------|---------------|
| C_visible | Cost of explicit BLD | Increases |
| C_hidden | Cost of implicit structure | Decreases |
| C_total | C_visible + C_hidden | **Conserved** |
| Explicitness | C_visible / C_total | Increases → 1 |

**Key insight**: Refactoring doesn't make code simpler — it makes complexity explicit and auditable.

---

## BLD Cost Flow Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                    COST CONSERVATION UNDER FACTORIZATION                  │
│                                                                           │
│                      C_total(S) = C_total(FACTOR(S))                      │
└───────────────────────────────────────────────────────────────────────────┘

                         BEFORE FACTORIZATION
┌───────────────────────────────────────────────────────────────────────────┐
│                           STRUCTURE S                                     │
│                                                                           │
│     ┌─────────────────────────┐  ┌─────────────────────────┐              │
│     │      C_visible          │  │       C_hidden          │              │
│     │    (explicit BLD)       │  │    (implicit BLD)       │              │
│     │                         │  │                         │              │
│     │  ████████               │  │  ████████████████████   │              │
│     │  (small)                │  │  (large)                │              │
│     └─────────────────────────┘  └─────────────────────────┘              │
│                                                                           │
│     Explicitness = C_visible/C_total ≈ 0.25                               │
│                                                                           │
│     C_total = ██████████████████████████████████ (CONSERVED)              │
└───────────────────────────────────────────────────────────────────────────┘
                                    │
                              FACTOR │
                                    ▼
                          AFTER FACTORIZATION
┌───────────────────────────────────────────────────────────────────────────┐
│                           STRUCTURE S*                                    │
│                                                                           │
│     ┌─────────────────────────┐  ┌─────────────────────────┐              │
│     │      C_visible          │  │       C_hidden          │              │
│     │    (explicit BLD)       │  │    (implicit BLD)       │              │
│     │                         │  │                         │              │
│     │  ████████████████████   │  │  ████                   │              │
│     │  (large)                │  │  (small)                │              │
│     └─────────────────────────┘  └─────────────────────────┘              │
│                                                                           │
│     Explicitness = C_visible/C_total ≈ 0.85                               │
│                                                                           │
│     C_total = ██████████████████████████████████ (SAME!)                  │
└───────────────────────────────────────────────────────────────────────────┘

COST PRIMITIVE BREAKDOWN:

┌───────────────────┐  ┌───────────────────┐  ┌───────────────────┐
│    C(B)           │  │    C(L)           │  │    C(D)           │
│    Boundary       │  │    Link           │  │    Dimension      │
│                   │  │                   │  │                   │
│ ½log(1+d²_Mahal)  │  │ -½ln(1-ρ²)        │  │ n × C(element)    │
│                   │  │                   │  │                   │
│ Partition cost:   │  │ Connection cost:  │  │ Repetition cost:  │
│ How different     │  │ How correlated    │  │ How many          │
│ are cases?        │  │ are components?   │  │ instances?        │
└───────────────────┘  └───────────────────┘  └───────────────────┘
         │                     │                     │
         └─────────────────────┼─────────────────────┘
                               │
                               ▼
                    C_total = C(B) + C(L) + C(D)
                    (for fully factored structure)

FACTORIZATION REVEALS HIDDEN COST:

  Implicit                    Explicit
  ┌─────────────────┐        ┌─────────────────┐
  │ scattered if    │   B    │ Sum type        │
  │ statements      │ ────→  │ (EventType)     │
  │                 │        │                 │
  │ C_hidden: high  │        │ C_visible: same │
  └─────────────────┘        └─────────────────┘

  ┌─────────────────┐        ┌─────────────────┐
  │ cyclic deps     │   L    │ Shared state +  │
  │ A→B→C→A         │ ────→  │ DAG             │
  │                 │        │                 │
  │ C_hidden: high  │        │ C_visible: same │
  └─────────────────┘        └─────────────────┘

  ┌─────────────────┐        ┌─────────────────┐
  │ mixed loop      │   D    │ Separate        │
  │ (types tangled) │ ────→  │ homogeneous     │
  │                 │        │ loops           │
  │ C_hidden: high  │        │ C_visible: same │
  └─────────────────┘        └─────────────────┘
```

---

## 1. The Cost Function

### 1.1 Definition

The **structural cost function** C assigns a non-negative real cost to each structure:

```
C : Structure → ℝ⁺
```

Cost measures the **information content** of structure — how much a traverser must process.

### 1.2 Primitive Costs (Proven)

From the manifold foundations ([manifold-foundations.md](../derived/manifold-foundations.md)), the costs of irreducible primitives are:

**Boundary Cost** (B):
```
C(b) = ½ log(1 + d²_Mahal)

Where d²_Mahal = squared Mahalanobis distance between cases

Simplified (valid for sep ∈ [1.5, 5.0]):
C(b) ≈ a × sep² × g(ρ,θ)^α(ρ)
```

**Link Cost** (L) — **EXACT THEOREM**:
```
C(l) = -½ ln(1 - ρ²)

Where ρ = correlation coefficient (dependency strength)
```

**Dimension Cost** (D):
```
C(d) = n × C(element)

Where n = extent (repetition count)
```

### 1.3 Composite Costs

For composite structures:

```
C(s₁ × s₂) = C(s₁) + C(s₂)      [product: additive]
C(s₁ + s₂) = C(s₁) ⊕ C(s₂)      [sum: choice-weighted]
C(s₁ → s₂) = C(s₁) + C(s₂)      [function: domain + codomain]
```

The **sum cost** uses choice-weighted addition:
```
C(s₁) ⊕ C(s₂) = p₁·C(s₁) + p₂·C(s₂)

Where p₁, p₂ are choice probabilities (p₁ + p₂ = 1)
```

---

## 2. Cost Decomposition

### 2.1 Visible and Hidden Cost

Every structure S has cost that decomposes into:

```
C_total(S) = C_visible(S) + C_hidden(S)
```

**C_visible**: Cost of structure that's explicit (named types, defined interfaces, clear dependencies)

**C_hidden**: Cost of structure that's implicit (scattered conditionals, hidden cycles, mixed dimensions)

### 2.2 Examples

**Scattered Conditionals** (hidden B):
```python
# Hidden cost: The boundary is implicit
if x == 1: do_a()
elif x == 2: do_b()
elif x == 3: do_c()
```
- C_visible ≈ 0 (no explicit boundary type)
- C_hidden = C(b) where b = case over {1, 2, 3}

**Explicit Sum Type** (visible B):
```python
class State(Enum):
    ONE = 1
    TWO = 2
    THREE = 3

# Visible cost: The boundary is explicit
match state:
    case State.ONE: do_a()
    case State.TWO: do_b()
    case State.THREE: do_c()
```
- C_visible = C(b) (explicit boundary type)
- C_hidden = 0 (boundary fully factored)

### 2.3 Total Cost is Fixed

The **total cost is an intrinsic property** of what the code computes, not how it's written:

```
C_total(S) = fixed for given functionality
```

Refactoring changes the visible/hidden ratio, not the total.

---

## 3. The Conservation Theorem

### 3.1 Statement

**Theorem (Cost Conservation)**: Factorization preserves total cost.

```
C(S) = C(FACTOR(S)) = Σᵢ C(Sᵢ)
```

### 3.2 Proof

**Lemma**: Each factorization rule preserves total cost.

**B-Factor**:
```
S[if x==c₁:e₁ | ... | if x==cₙ:eₙ]  →  B(x) × Dispatch(e₁,...,eₙ)

C(left) = C(implicit boundary) + C(e₁) + ... + C(eₙ)
C(right) = C(B(x)) + C(Dispatch)

Since B(x) IS the implicit boundary and Dispatch contains e₁,...,eₙ:
C(left) = C(right) ✓
```

**L-Factor**:
```
S[A→B→C→A]  →  Shared × (A→S) × (B→S) × (C→S)

C(left) = C(A→B) + C(B→C) + C(C→A)    [cycle cost]
C(right) = C(Shared) + C(A→S) + C(B→S) + C(C→S)    [DAG cost]

The cycle ENCODES shared state with cost = C(Shared).
Therefore C(left) = C(right) ✓
```

**D-Factor**:
```
S[D(mixed items)]  →  D_A(items_A) × D_B(items_B)

C(left) = Σᵢ C(itemᵢ) + C(mixed overhead)
C(right) = Σ_A C(itemₐ) + Σ_B C(itemᵦ) + 0    [no mixed overhead]

The mixed overhead IS the cost of implicit boundary between types.
Therefore C(left) = C(right) ✓
```

**Main theorem**: By induction on factorization steps:
- Base case: Identity (no factorization) trivially preserves cost
- Inductive step: Each rule preserves cost (lemma above)
- Conclusion: Any sequence of factorizations preserves cost

∎

### 3.3 Corollary: Cost is Redistributed

Factorization **redistributes** cost from implicit to explicit:

```
FACTOR: C_hidden → C_visible
        C_total unchanged
```

---

## 4. The Explicitness Metric

### 4.1 Definition

The **explicitness** of a structure measures how much of its cost is explicit:

```
Explicitness : Structure → [0, 1]

Explicitness(S) := C_visible(S) / C_total(S)
```

**Interpretation**:
- Explicitness = 0: All structure is hidden (maximally implicit)
- Explicitness = 1: All structure is explicit (normal form)

### 4.2 Component Indicators

For practical measurement:

```
Explicit_B(S) = 1  iff  all boundaries factored to sum types
Explicit_L(S) = 1  iff  all dependencies factored to DAG
Explicit_D(S) = 1  iff  all dimensions factored to homogeneous

Explicitness(S) ≈ (Explicit_B + Explicit_L + Explicit_D) / 3
```

### 4.3 Monotonicity

**Theorem (Monotonic Explicitness)**: Factorization increases explicitness.

```
S →_FACTOR S'  implies  Explicitness(S') > Explicitness(S)
```

**Proof**:
1. FACTOR moves cost from C_hidden to C_visible
2. C_total is conserved
3. C_visible increases while C_total stays constant
4. Therefore C_visible/C_total increases

∎

### 4.4 Termination at Full Explicitness

**Corollary**: Factorization terminates when Explicitness(S*) = 1.

At the fixed point S*:
```
C_hidden(S*) = 0
C_visible(S*) = C_total(S*)
Explicitness(S*) = 1
```

All structure is explicit as irreducible BLD primitives.

---

## 5. Connection to Physics

### 5.1 Observer Correction

From the structural-observer framework: implicit structure has **hidden cost that multiplies**.

```
Perceived_complexity(S) = C_visible(S) × (1 + C_hidden(S)/C_visible(S))
                        = C_visible(S) + C_hidden(S)
                        = C_total(S)
```

But the **experience** of implicit structure is worse than explicit:
- Hidden cycles: debugging feels exponentially harder
- Scattered conditionals: maintenance requires global search
- Mixed dimensions: reasoning requires type tracking

### 5.2 Alignment Cost as Structural Cost

In the manifold ([manifold-applications.md](../derived/manifold-applications.md)), cost is alignment cost:

```
φ_T(S) = cost(S, T)    [potential function]
```

The cost algebra here is compatible: C(S) = φ_T(S) for appropriate traverser T.

### 5.3 Conservation as Noether

From BLD conservation ([bld-conservation.md](../bld-conservation.md)):

```
BLD conservation ←→ Noether's theorem

Cost conservation ←→ Structural symmetry
```

The invariance of C_total under factorization is a **structural symmetry** — factorization is a transformation that doesn't change the "energy" (cost) of the system.

---

## 6. Practical Implications

### 6.1 Refactoring Doesn't Reduce Complexity

A common misconception: "refactoring makes code simpler."

**Truth**: Refactoring makes complexity **visible**. Total complexity is conserved.

```
Before refactoring: Low C_visible, high C_hidden, hard to audit
After refactoring:  High C_visible, low C_hidden, easy to audit
```

### 6.2 The Value of Explicitness

Why prefer explicit structure?

| Property | Implicit | Explicit |
|----------|----------|----------|
| Debugging | Hard (where is it?) | Easy (it's named) |
| Maintenance | Risky (side effects?) | Safe (clear boundaries) |
| Testing | Incomplete (hidden paths) | Thorough (all paths visible) |
| Documentation | Requires archaeology | Self-documenting |

### 6.3 Cost Budgeting

Knowing that cost is conserved enables **cost budgeting**:

```
C_total(feature) = fixed by requirements
C_visible_target = C_total    (fully explicit)

Refactoring progress = C_visible / C_total → 1
```

Track explicitness as a code quality metric.

---

## 7. Notation Summary

| Symbol | Meaning |
|--------|---------|
| C(S) | Total structural cost |
| C_visible(S) | Cost of explicit structure |
| C_hidden(S) | Cost of implicit structure |
| C(b), C(l), C(d) | Primitive costs |
| Explicitness(S) | C_visible/C_total |
| ⊕ | Choice-weighted cost addition |

---

## 8. Open Questions

1. **Measurement**: How to precisely measure C_hidden in practice? (Currently requires factorization to discover)

2. **Optimal explicit form**: Given multiple normal forms, which has lowest **cognitive cost**?

3. **Partial factorization value**: At what explicitness threshold do benefits plateau?

4. **Cross-language comparison**: Is C_total comparable across programming languages?

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Factorization Calculus](./factorization-calculus.md) — The FACTOR operation
- [Manifold Foundations](../derived/manifold-foundations.md) — Primitive cost formulas
- [BLD Conservation](../bld-conservation.md) — Physical conservation laws
- [Manifold Applications](../derived/manifold-applications.md) — Alignment cost interpretation
