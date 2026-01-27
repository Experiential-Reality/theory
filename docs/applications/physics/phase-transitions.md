---
status: DERIVED
layer: application
depends_on:
  - thermodynamics-validation.md
  - ../../mathematics/derived/thermodynamics.md
  - ../../mathematics/foundations/structural/compensation-principle.md
  - ../../mathematics/quantum/entanglement-entropy.md
used_by:
  - fluids.md
---

# BLD for Phase Transitions

> **Status**: Derived — follows from [Thermodynamics](../../mathematics/derived/thermodynamics.md) (VALIDATED, 10-test suite) and [Compensation Principle](../../mathematics/foundations/structural/compensation-principle.md) (PROVEN).

## Summary

**Phase Transitions as BLD Structure Reorganization:**

1. Phase transitions are where B changes — [Q1](#q1-where-does-behavior-partition-finding-b)
2. Correlation length ξ is fundamental L, diverges at T_c — [Q2](#q2-what-connects-finding-l)
3. System size is D, determines finite-size effects — [Q3](#q3-what-repeats-finding-d)
4. Critical exponents satisfy D×L scaling relations — [D×L Scaling](#dl-scaling-and-critical-exponents)
5. Universality from same (d, n, symmetry) — [Universality Classes](#universality-classes)
6. At T_c, B is undefined — fluctuations at all scales — [Where B Changes](#where-b-changes-the-critical-point)
7. RG describes B/L/D flow under scale change — [Renormalization Group](#renormalization-group-bld-flow)

| Component | BLD | Description |
|-----------|-----|-------------|
| Phase boundary T_c | B | Topological threshold — partitions ordered/disordered |
| Correlation length ξ | L | Connection strength — diverges at T_c |
| System size / lattice sites | D | Repetition — determines finite-size effects |

Phase transitions are where **B changes** — the critical gap in current BLD physics coverage, which mostly addresses equilibrium structure.

---

## Conclusion

| Finding | Status | Evidence |
|---------|--------|----------|
| Second law derived | **VALIDATED** | [Thermodynamics](../../mathematics/derived/thermodynamics.md) — 10-test suite |
| Phase boundary as B | DERIVED | Partitions ordered/disordered |
| Correlation length as L | DERIVED | Diverges at criticality |
| L = -½ ln(1-ρ²) applies | DERIVED | Same formula as entanglement |
| L ~ ν ln(ξ) | DERIVED | Logarithmic divergence |
| System size as D | DERIVED | D×L scaling predicts finite-size effects |
| Critical exponents | DERIVED | Follow D×L scaling |

### Key Insight

Phase transitions are where BLD structure **reorganizes** — not just where cost is computed, but where the primitives themselves transform.

---

## The Three Questions Applied to Phase Transitions

### Q1: Where Does Behavior Partition? (Finding B)

| Boundary | Discriminator | Regions | Critical Point |
|----------|--------------|---------|----------------|
| **Solid/Liquid** | Temperature | Ordered / Disordered | T_m (melting) |
| **Liquid/Gas** | T, P | Dense / Sparse | Critical point |
| **Magnetic** | Temperature | Ferromagnetic / Paramagnetic | T_c (Curie) |
| **Superconducting** | Temperature | SC / Normal | T_c |
| **Symmetry** | Order parameter | Broken / Unbroken | T_c |

**The Fundamental Observation**

At a phase transition, **B itself changes**:

```
T < T_c: System has boundary B₁ (ordered, broken symmetry)
T > T_c: System has boundary B₂ (disordered, full symmetry)

At T = T_c: B is undefined (critical point)
```

This is different from circuits or thermodynamics, where B is fixed and we compute alignment cost. Here B **transforms**.

### Q2: What Connects? (Finding L)

| Link | Meaning | Behavior at T_c |
|------|---------|-----------------|
| **Correlation length ξ** | How far order propagates | ξ → ∞ |
| **Susceptibility χ** | Response to perturbation | χ → ∞ |
| **Specific heat C** | Thermal fluctuations | May diverge |

**L1: Correlation Length**

The correlation function measures how connected sites are:

```
G(r) = ⟨s(0)s(r)⟩ - ⟨s⟩²

At large r:
  T ≠ T_c: G(r) ~ exp(-r/ξ)      (finite L)
  T = T_c: G(r) ~ r^(-(d-2+η))   (infinite L, power law)
```

**Critical Divergence**: As T → T_c:
```
ξ ~ |T - T_c|^(-ν)
```

The exponent ν is **universal** — depends only on symmetry and dimension, not microscopic details.

**BLD Interpretation**: At criticality, L becomes infinite. The system is maximally connected.

### L Formula at Criticality

From [Entanglement Entropy](../../mathematics/quantum/entanglement-entropy.md):

```
L = -½ ln(1 - ρ²)
```

where ρ is the correlation coefficient. At a phase transition:

```
ρ → 1  (long-range correlations)
L → ∞  (link cost diverges)
```

**Connection to critical exponents:**
```
If ξ ~ |T - T_c|^(-ν), then:
  ρ² ~ 1 - |T - T_c|^(2ν)
  L ~ -½ ln(|T - T_c|^(2ν))
  L ~ ν × ln(ξ)
```

**Key result**: Link cost grows logarithmically with correlation length: **L ~ ν ln(ξ)**.

This connects the BLD link formula to statistical mechanics. The same L = -½ ln(1 - ρ²) governs:
- Quantum entanglement (ρ = C/√2)
- Phase transitions (ρ → 1 at T_c)

### Q3: What Repeats? (Finding D)

| Dimension | Meaning | Effect on Transition |
|-----------|---------|---------------------|
| **System size L** | Physical extent | Finite-size rounding |
| **Spatial dimension d** | Embedding space | Determines universality class |
| **Order parameter dimension n** | Components of φ | Affects exponents |

**D×L Scaling at Criticality**

At T = T_c with infinite system (D → ∞), L diverges.

For finite systems:
```
ξ_eff = min(ξ_bulk, L)

When ξ_bulk > L: Finite-size effects dominate
```

This is **D×L interplay** — system size D cuts off the diverging L.

---

## D×L Scaling and Critical Exponents

### The Scaling Hypothesis

Near T_c, thermodynamic quantities follow power laws:

| Quantity | Symbol | Exponent | Scaling |
|----------|--------|----------|---------|
| Correlation length | ξ | ν | ξ ~ t^(-ν) |
| Order parameter | φ | β | φ ~ t^β |
| Susceptibility | χ | γ | χ ~ t^(-γ) |
| Specific heat | C | α | C ~ t^(-α) |

Where t = (T - T_c)/T_c is reduced temperature.

### Scaling Relations

The exponents are not independent — they satisfy **scaling relations**:

```
α + 2β + γ = 2        (Rushbrooke)
γ = ν(2 - η)          (Fisher)
β = ν(d - 2 + η)/2    (Josephson)
```

**BLD Interpretation**: These relations encode how D×L scaling constrains the transition.

### Universality Classes

Different systems share the same exponents if they have the same:
- **d**: Spatial dimension (D structure)
- **n**: Order parameter dimension (internal D)
- **Symmetry**: What B is preserved

| Universality Class | d | n | Examples |
|-------------------|---|---|----------|
| Ising | 3 | 1 | Uniaxial magnets, binary alloys |
| XY | 3 | 2 | Superfluids, superconductors |
| Heisenberg | 3 | 3 | Isotropic magnets |
| Mean-field | >4 | any | Long-range interactions |

**BLD Insight**: Universality means the same (B, L, D) structure produces the same critical behavior, regardless of microscopic details.

---

## Where B Changes: The Critical Point

### B Transformation

Below T_c:
```
B = symmetry-broken boundary
  - Order parameter φ ≠ 0
  - System partitions into domains
  - Boundary between domains costs energy
```

Above T_c:
```
B = symmetric boundary (or no effective boundary)
  - Order parameter φ = 0
  - No domains
  - System homogeneous
```

At T_c:
```
B is critical
  - Fluctuations at all scales
  - Domains of all sizes (fractal)
  - Self-similarity (scale invariance)
```

### Why This Is Different

In circuits:
- V_th is fixed (B invariant)
- We compute alignment cost against fixed B

In phase transitions:
- B itself is the order parameter
- The transition IS B changing

**This requires extending BLD**: We need a theory of B dynamics, not just B evaluation.

---

## Ising Model: Concrete Example

### Setup

```
H = -J Σ_{⟨i,j⟩} s_i s_j - h Σ_i s_i

Where:
  s_i = ±1 (spin at site i)
  J = coupling strength
  h = external field
  ⟨i,j⟩ = nearest neighbors
```

### BLD Decomposition

| Primitive | Ising Model | Value |
|-----------|-------------|-------|
| **B** | Domain walls (s_i ≠ s_j boundaries) | E_wall = 2J per bond |
| **L** | Spin-spin coupling | L = J |
| **D** | Lattice size | N = L^d sites |

### D×L Scaling

**Total coupling energy** (fully aligned):
```
E_ground = -J × D × z/2

Where:
  D = N = L^d (site count)
  z = coordination number
  L = J (coupling strength)
```

This is D×L scaling — energy scales as (number of sites) × (coupling per site).

### Finite-Size Scaling

For finite systems of size L:

```
ξ(T, L) = L × f(L/ξ_∞)

Where:
  ξ_∞ = ξ(T, ∞) ~ t^(-ν)  (infinite system)
  f(x) = universal scaling function
```

**Predictions**:
- Peak in susceptibility: χ_max ~ L^(γ/ν)
- Order parameter at T_c: φ ~ L^(-β/ν)
- Pseudo-critical temperature: T_c(L) - T_c(∞) ~ L^(-1/ν)

All testable via D×L scaling.

---

## Compensation Principle at Phase Transitions

### L Compensates for B Deficiency?

At T > T_c, the symmetry-breaking B is absent (deficient). Can L compensate?

**Test**: Apply external field h (adds explicit B)

```
With h ≠ 0:
  - Sharp boundary restored even above T_c
  - φ ≠ 0 for all T
  - No true phase transition (crossover only)
```

**Interpretation**: External field (explicit B) removes the transition. The system with weak B (h → 0) shows the full critical behavior. This is consistent with compensation principle operating — weak B allows L to dominate near T_c.

### Correlation as L

Near T_c, correlation length (L) diverges while explicit boundaries (B) vanish:
```
ξ → ∞  (L → ∞)
h → 0  (B → 0)
```

The diverging L "compensates" for the vanishing B — the system maintains structure through long-range correlation rather than explicit boundaries.

---

## Renormalization Group: B/L/D Flow

### The RG Perspective

Renormalization group (RG) describes how B, L, D transform under scale change:

```
Scale transformation: L → L' = L/b

Under RG:
  D → D' = D × b^d        (block spins)
  L → L' = L(ξ/ξ')        (coupling renormalization)
  B → B' = B × b^(d-y_h)  (boundary scaling)
```

### Fixed Points

Fixed points of RG flow are where B, L, D are scale-invariant:
- **Trivial fixed point** (T = ∞): No correlations
- **Critical fixed point** (T = T_c): Scale invariance
- **Ordered fixed point** (T = 0): Full order

**BLD Insight**: Critical point is where RG flow reaches a fixed point — the (B, L, D) structure is self-similar.

---

## Symmetry Breaking and B

### Order Parameter as B

The order parameter φ encodes which B the system chooses:

```
Z₂ symmetry (Ising):
  φ = +1: "Up" phase
  φ = -1: "Down" phase
  φ = 0: Symmetric (no B chosen)

O(n) symmetry:
  φ = vector in Rⁿ
  Direction of φ = chosen B
  |φ| = 0: Symmetric
```

### Spontaneous vs Explicit

| Type | Definition | B Status |
|------|-----------|----------|
| **Explicit breaking** | h ≠ 0 (external field) | B imposed from outside |
| **Spontaneous breaking** | T < T_c, h = 0 | System chooses B |

Spontaneous symmetry breaking is where B **emerges** from L structure (fluctuations select a direction).

---

## What BLD Does NOT Explain

### 1. Specific Critical Temperatures

BLD framework doesn't predict T_c from first principles:
```
T_c(Ising, 2D) = 2J / ln(1 + √2) ≈ 2.27 J
```

The value comes from solving the model, not from BLD structure.

### 2. Dynamical Critical Exponent

The framework addresses equilibrium structure. Dynamic critical slowing:
```
τ ~ ξ^z  (relaxation time)
```

has dynamical exponent z not directly predicted.

### 3. Non-Equilibrium Transitions

Phase transitions far from equilibrium (driven systems, absorbing states) require extending BLD beyond the current equilibrium framework.

### 4. Quantum Phase Transitions

Transitions at T = 0 driven by quantum fluctuations involve (d+1)-dimensional scaling. BLD mapping to QPTs is not yet developed.

---

## Falsifiable Predictions

| Prediction | Test | Falsification Criterion |
|------------|------|------------------------|
| D×L finite-size scaling | Monte Carlo, vary L | Scaling collapses fail |
| ξ → ∞ as L | Measure correlation near T_c | Correlation stays finite |
| Universality from (d, n, symmetry) | Compare different models | Same structure, different exponents |
| B vanishes at T_c | Order parameter measurement | φ ≠ 0 at T_c (first-order) |

---

## Connection to Thermodynamics

The thermodynamics validation (10/10 tests) uses:
```
dS/dt = k_B T ∫ P |∇ ln P + ∇E/k_B T|² dμ ≥ 0
```

At phase transitions:
- **Second-order**: dS/dt continuous, entropy continuous
- **First-order**: Latent heat, entropy jumps

BLD connection: Phase transitions are where the energy landscape E(σ) topology changes — the B structure reorganizes.

---

## Proposed Validation Tests

### Test 1: Ising D×L Scaling

```python
# Monte Carlo simulation
for L in [8, 16, 32, 64, 128]:
    for T in temperatures_near_Tc:
        φ, χ, ξ = simulate_ising(L, T)
        # Record for scaling collapse

# Verify:
# χ × L^(-γ/ν) vs (T-Tc) × L^(1/ν) collapses to single curve
# Using known ν = 1.0, γ = 1.75 for 2D Ising
```

### Test 2: Correlation Length Divergence

```python
# Measure correlation function G(r)
# Fit to G(r) ~ exp(-r/ξ)
# Plot ξ vs |T - Tc|

# Prediction: ξ ~ |T - Tc|^(-ν)
# 2D Ising: ν = 1.0
# 3D Ising: ν ≈ 0.63
```

### Test 3: Universality Class Matching

Compare systems with same (d, n) but different microscopic details:
- Ising model on square vs triangular lattice
- Should have identical critical exponents

---

## See Also

- [Thermodynamics](thermodynamics-validation.md) — Entropy dynamics
- [Thermodynamics (Math)](../../mathematics/derived/thermodynamics.md) — Energy landscape
- [Physics Traverser](../../examples/physics-traverser.md) — Symmetry breaking (P11, P16)
- [Compensation Principle](../../mathematics/foundations/structural/compensation-principle.md) — L→B compensation
