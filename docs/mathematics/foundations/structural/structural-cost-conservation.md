---
status: DERIVED
layer: 1
depends_on:
  - factorization-calculus.md
  - ../../lie-theory/lie-correspondence.md
  - ../../geometry/manifold-foundations.md
used_by:
  - factorization-calculus.md
  - ../machine/universal-machine.md
  - ../../relativity/special-relativity.md
  - ../../relativity/general-relativity.md
  - ../../../applications/code/refactoring.md
  - ../machine/integer-factorization.md
---

# Structural Cost Conservation

## Summary

**Cost is conserved under factorization:**

1. Conservation theorem: C(S) = C(FACTOR(S)) — cost redistributes, doesn't disappear — [The Conservation Theorem](#3-the-conservation-theorem)
2. Decomposition: C_total = C_visible + C_hidden — structure is either explicit or implicit — [Cost Decomposition](#2-cost-decomposition)
3. Primitive costs: C(B)=½log(1+d²), C(L)=-½ln(1-ρ²), C(D)=n×C(element) — [Primitive Costs](#12-primitive-costs-proven)
4. Explicitness = C_visible/C_total monotonically increases toward 1 — [The Explicitness Metric](#4-the-explicitness-metric)
5. Refactoring makes complexity visible, not simpler — [Practical Implications](#6-practical-implications)
6. Cost conservation ↔ structural symmetry (Noether) — [Connection to Physics](#5-connection-to-physics)

| State | C_visible | C_hidden | Audit |
|-------|-----------|----------|-------|
| Before factoring | Low | High | Hard |
| After factoring | High | Low | Easy |
| Normal form | C_total | 0 | Complete |

---

## Abstract

We establish that structural cost is conserved under factorization: C(S) = C(FACTOR(S)). While factorization may appear to simplify structure, it actually transfers cost from hidden (implicit) to visible (explicit) components. The decomposition C_total = C_visible + C_hidden is invariant, with factorization monotonically increasing the explicitness ratio C_visible/C_total toward 1. We provide exact formulas for primitive costs: C(B) = ½log(1+d²_Mahal) for boundaries, C(L) = -½ln(1-ρ²) for links, and C(D) = n × C(element) for dimensions. This principle connects refactoring practices to BLD theory and explains why "simpler" code isn't necessarily lower cost—it's more explicit about its inherent complexity.

## 1. Introduction

The intuition that refactoring "simplifies" code is misleading. Complexity doesn't disappear—it becomes explicit. This document formalizes structural cost conservation and its implications.

**Main Claim.** Structural cost is conserved under factorization: FACTOR reveals hidden cost but doesn't reduce total cost.

**Key Results:**
- Exact primitive cost formulas for B, L, D
- Conservation law: C(S) = C(FACTOR(S))
- Monotonic increase in explicitness

**Outline.** Section 2 presents primitive cost formulas. Section 3 defines the cost function. Section 4 proves the conservation law. Section 5 introduces the explicitness metric.

## 2. Primitive Cost Formulas

| Primitive | Formula | Meaning |
|-----------|---------|---------|
| C(B) | ½log(1+d²_Mahal) | Partition cost: how different are cases? |
| C(L) | -½ln(1-ρ²) | Connection cost: how correlated are components? |
| C(D) | n × C(element) | Repetition cost: how many instances? |

**Conservation**: C_total = C(B) + C(L) + C(D) is conserved under FACTOR.

---

## 1. The Cost Function

### 1.1 Definition

The **structural cost function** C assigns a non-negative real cost to each structure:

```
C : Structure → ℝ⁺
```

Cost measures the **information content** of structure — how much a traverser must process.

### 1.2 Primitive Costs (Proven)

From the manifold foundations ([manifold-foundations.md](../../geometry/manifold-foundations.md)), the costs of irreducible primitives are:

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

### 3.4 Quantitative Verification: Integer Factoring

The conservation theorem receives its first quantitative verification outside code refactoring through integer factoring. For a k-bit semiprime N = pq, the total information cost to determine a factor is C_total = k/2 bits (the Shannon entropy of the answer). Three algorithms with radically different strategies all obey this budget:

```
Algorithm        C_visible    C_hidden     C_total
─────────────    ─────────    ─────────    ───────
Trial division   k/2          0            k/2
Pollard rho      k/4          k/4          k/2
GNFS             sub-exp      exp          k/2
```

Each algorithm redistributes cost between visible probes and hidden structural pre-computation, but C_total = k/2 is invariant. GPU confirmation across bit sizes k = 20 to k = 44 shows each coprime probe contributes exactly 1 bit (K/X = 1), and k/2 probes always suffice.

See [Integer Factorization: Cost Conservation](../machine/integer-factorization.md#cost-conservation-c-total--k2) for derivation and experimental data.

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

In the manifold ([manifold-applications.md](../../geometry/manifold-applications.md)), cost is alignment cost:

```
φ_T(S) = cost(S, T)    [potential function]
```

The cost algebra here is compatible: C(S) = φ_T(S) for appropriate traverser T.

### 5.3 Conservation as Noether

From BLD conservation ([bld-conservation.md](bld-conservation.md)):

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

## 8. Research Questions

**Application Questions** (for practitioners):

1. **Measurement**: How to precisely measure C_hidden in practice? (Currently requires factorization to discover)

   *Partial answer*: For integer factoring, C_hidden = C_total − C_visible, where C_total = k/2 is known a priori (Shannon entropy) and C_visible is directly measurable as the number of explicit probes. Different algorithms make different fractions visible: trial division achieves full explicitness (C_hidden = 0), while GNFS hides exponential structure in the factor base. See [Integer Factorization](../machine/integer-factorization.md#cost-conservation-c-total--k2).

2. **Partial factorization value**: At what explicitness threshold do benefits plateau?

3. **Cross-language comparison**: Is C_total comparable across programming languages?

**Outside BLD Scope**:

4. **Optimal explicit form**: Given multiple normal forms, which has lowest *cognitive cost*? (Cognitive cost is a separate domain from structural cost.)

---

## See Also

- [Glossary](../../../glossary.md) — Central definitions
- [Factorization Calculus](./factorization-calculus.md) — The FACTOR operation
- [Manifold Foundations](../../geometry/manifold-foundations.md) — Primitive cost formulas
- [BLD Conservation](bld-conservation.md) — Physical conservation laws
- [Manifold Applications](../../geometry/manifold-applications.md) — Alignment cost interpretation
