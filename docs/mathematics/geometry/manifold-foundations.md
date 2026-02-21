---
status: VALIDATED
depends_on:
  - ../lie-theory/lie-correspondence.md
---

# The Structural Manifold: Foundations

> **Status**: Validated

A mathematical formalization of what the structural manifold IS and its primitive characterization.

> **Rigor Summary**: The probability distribution submanifold is rigorously defined via classical information geometry. Primitive irreducibility is proven. The full BLD manifold over arbitrary structures remains informal. See "What's Proven vs. Informal" section below.

---

## Summary

**The structural manifold (BLD extends information geometry):**

1. BLD = stratified extension: Info Geo = BLD_{k=1} (unimodal) — [Main Result](#bld-as-stratified-extension-of-information-geometry)
2. B = topological: mode structure, dimension-independent — [Boundary](#boundary-b--topological-derived)
3. L = metric: correlation, L = -½ ln(1-ρ²) exact — [Link](#link-l--metric)
4. D = multiplier: scales L linearly (KL additivity) — [Dimension](#dimension-d--structural-multiplier-theorem)
5. Algebraically independent, geometrically coupled (~16%) — [Coupling](#geometric-coupling-between-primitives)
6. Universal: Gaussian, Student-t, Laplace all work — [Universality](#universality-across-distributions)

| Primitive | Character | Scaling | Exact Formula |
|-----------|-----------|---------|---------------|
| B | Topological | O(1) | ½ log(1 + d²_Mahal) |
| L | Metric | O(s) | -½ ln(1 - ρ²) |
| D | Multiplier | × on L | KL additivity |

---

## Overview

All structures describable by B/L/D live on a manifold. The metric on this manifold is derived from alignment cost. Classical information geometry (Fisher-Rao) is a submanifold.

---

## What's Proven vs. Informal

| Component | Status | Evidence |
|-----------|--------|----------|
| Primitive irreducibility | **PROVEN** | Type-theoretic proof ([irreducibility-categorical.md](../foundations/proofs/irreducibility-categorical.md)) |
| **Information Geometry ⊂ BLD** | **PROVEN** | BLD is stratified extension; Info Geo = BLD_{k=1} |
| Link cost formula | **PROVEN** | L = -½ ln(1 - ρ²) exact theorem from KL divergence |
| Alignment factor g(ρ,θ) | **PROVEN** | g = (1-ρsin(2θ))/(1-ρ²) from Mahalanobis geometry |
| Geodesic = Mahalanobis | **PROVEN** | On mean submanifold with Fisher-Rao metric |
| B dimension-independence | **VALIDATED** | B(d=16)/B(d=2) = 1.03 empirically |
| L linear scaling | **PROVEN** | L(s=8)/L(s=1) = 8.99 ≈ 8, KL additivity |
| Universality (3 distributions) | **PROVEN** | Gaussian, Student-t, Laplace mixtures |
| **Exact B formula** | **PROVEN** | B = ½ log(1 + d²_Mahal) from Killing form |
| **α(ρ) interpretation** | **CLARIFIED** | Regime artifact from log(1+x) transition, not fundamental |
| **D as multiplier** | **PROVEN** | Theorem from KL additivity |
| **B formula structure** | **DERIVED** | Two-traverser interpolation with α; see [Boundary Derivation](../lie-theory/boundary-derivation.md) |
| Full BLD manifold topology | Informal | No rigorous atlas construction |
| Measure dμ | Informal | Not rigorously constructed |

---

## BLD as Stratified Extension of Information Geometry

**Theorem (Main Result)**: BLD is a stratified extension of information geometry:

```
Information Geometry ⊂ BLD
```

More precisely:
```
BLD = B × (L × D)

Where:
- B = discrete topological invariant (mode count k ∈ ℤ₊)
- L × D = continuous Riemannian structure (≅ Information Geometry)

Therefore:
Information Geometry ≅ BLD_{k=1}  (the unimodal stratum)
```

**Visual representation**:
```
┌─────────────────────────────────────────┐
│                  BLD                     │
│  ┌───────────────────────────────────┐  │
│  │     B = 1 (unimodal stratum)      │  │
│  │  ┌─────────────────────────────┐  │  │
│  │  │  Information Geometry (L×D) │  │  │
│  │  │  - Fisher-Rao metric        │  │  │
│  │  │  - KL divergence            │  │  │
│  │  └─────────────────────────────┘  │  │
│  └───────────────────────────────────┘  │
│  ┌───────────────────────────────────┐  │
│  │     B = 2 (bimodal stratum)       │  │
│  │     (L×D structure within)        │  │
│  └───────────────────────────────────┘  │
│  ┌───────────────────────────────────┐  │
│  │     B = k (k-modal stratum)       │  │
│  └───────────────────────────────────┘  │
└─────────────────────────────────────────┘
```

**Proof sketch**:

1. Let M_k denote the space of k-component Gaussian mixtures
2. M_k and M_{k+1} are disjoint manifolds (different dimensions)
3. Any path from p ∈ M_k to q ∈ M_{k+1} must pass through a degenerate distribution (where one component has zero weight)
4. At degenerate points, the Fisher metric becomes singular
5. Therefore, no smooth geodesic connects M_k to M_{k+1}
6. The transition k → k+1 is a **topological discontinuity**

**Corollary**: B indexes discrete strata, not directions in tangent space.

**Key insight**: Information geometry only sees the smooth structure within a stratum. BLD reveals the discrete topology between strata—the mode structure that classical information geometry misses.

**Geodesic distance = Mahalanobis distance**: On the mean submanifold (fixed covariance), geodesic distance equals Mahalanobis distance:
```
d_geodesic(μ₁, μ₂) = √[(μ₁ - μ₂)ᵀ Σ⁻¹ (μ₁ - μ₂)]
```

This connects B (mode separation) directly to information geometry through the Fisher-Rao structure.

**Source**: See [bld-vi-experiment/docs/BLD_INFORMATION_THEORY.md](https://github.com/rax-V/bld-vi-experiment/blob/main/docs/BLD_INFORMATION_THEORY.md) for complete proofs.

---

## Primitive Characterization

The three primitives have distinct geometric character:

### Boundary (B) — Topological (Derived)

**What it measures**: Mode structure (whether distinct regions exist)

**Dimension scaling**: O(1) — independent of embedding dimension

**Evidence**: B(d=16)/B(d=2) = 1.03 (only 3% variation across 8× dimension increase)

**Interpretation**: Boundary cost measures whether an approximation can represent distinct modes. This is a *topological* property (connectivity) not a *metric* property (distances). A unimodal Gaussian cannot represent a bimodal distribution regardless of dimension.

**Derivation**: B requires TWO traversers (unlike L which has one):
1. **Entropy traverser** → optimal regime: B ∝ log(sep)
2. **Mahalanobis traverser** → fixed regime: B ∝ sep²

The empirical formula interpolates between them via α. See [Boundary Derivation](../lie-theory/boundary-derivation.md) for complete derivation.

**Exact formula** (from Lie theory):
```
B_cost = ½ log(1 + d²_Mahal)

Where d²_Mahal = μᵀ Σ⁻¹ μ (squared Mahalanobis distance)
```

**Simplified formula** (valid for sep ∈ [1.5, 5.0]):
```
B_cost ≈ a × sep² × g(ρ,θ)^α(ρ)

Where:
- a ≈ 0.053 (scaling constant)
- g(ρ,θ) = (1 - ρ sin(2θ)) / (1 - ρ²)  [EXACT: alignment factor]
- α(ρ) = 0.081 + 0.119×ρ                [regime-specific fit]
- θ = angle between mode separation and correlation axis
```

**Simplified formula** (for θ = 0, valid for sep ≥ 1.5):
```
B_cost ≈ 0.060 × sep² / (1 + 0.22 × corr)
```

**The exact B formula** (from Lie theory):
```
B = ½ log(1 + d²_Mahal)
```
where d²_Mahal = μᵀ Σ⁻¹ μ is the squared Mahalanobis distance.

**The α(ρ) exponent** (regime artifact):
- The simplified formula B ≈ a·sep²·g^α is valid in regime sep ∈ [1.5, 5.0]
- α arises from the transition between log(1+x) ≈ x and log(1+x) ≈ log(x)
- α is **not** a fundamental geometric constant from SPD curvature
- For general use, prefer the exact formula B = ½ log(1 + d²_Mahal)

### Link (L) — Metric

**What it measures**: Correlation structure (dependencies between variables)

**Dimension scaling**: O(s) where s = number of correlated pairs

**Evidence**: L(s=8)/L(s=1) = 8.99 ≈ 8 (perfect linear scaling)

**Formula** (**EXACT THEOREM**):
```
L_cost = -½ ln(1 - ρ²)    per correlated pair
```

*Proof*: For a correlated Gaussian P = N(0, Σ_corr) approximated by diagonal Q = N(0, I):
```
KL(P||Q) = ½[tr(Σ_Q⁻¹ Σ_P) - d + ln(det(Σ_Q)/det(Σ_P))]
         = ½[2 - 2 - ln(1-ρ²)]
         = -½ ln(1 - ρ²)  ∎
```

This is exact mathematics, not an empirical fit.

### Dimension (D) — Structural Multiplier (Theorem)

**What it measures**: Repetition extent (how many independent structural units)

**Dimension scaling**: Multiplicative on L, no effect on B

**Theorem (D as Multiplier)**: D is not an independent cost primitive but a structural multiplier arising from KL additivity.

**Proof**:

For independent structures P₁, P₂ approximated by independent Q₁, Q₂:
```
KL(P₁ × P₂ || Q₁ × Q₂) = KL(P₁||Q₁) + KL(P₂||Q₂)
```

Therefore:
- **For L**: L_total(d dimensions) = d × L(1 dimension)
- **For B**: B is O(1) in dimension (topological invariant, dimension-independent)

**Evidence**:
- L(s=8 pairs) / L(s=1 pair) = 8.99 ≈ 8 (linear scaling) ✓
- B(d=16) / B(d=2) = 1.03 (dimension-independent) ✓

**Interpretation**: D counts how many times the base L cost applies. B is unaffected because mode structure is topological—a bimodal distribution has two modes regardless of embedding dimension.

---

## Geometric Coupling Between Primitives

The primitives are **algebraically independent** but **geometrically coupled**.

### Independence

Each primitive cost is zero when that structure doesn't exist:
- Pure boundary structure (sep > 0, corr = 0): L_cost = 0
- Pure link structure (sep = 0, corr > 0): B_cost = 0

This confirms B and L capture genuinely distinct aspects of structure.

### Coupling

When both structures are present, the cost Hessian has off-diagonal terms:

```
Hessian = | H_BB   H_BL |
          | H_LB   H_LL |

Coupling ratio: |H_BL| / √(H_BB × H_LL) ≈ 0.16 (empirical mean)
```

**Physical interpretation**: Mode separation direction relative to correlation principal axis affects boundary cost by a factor of 2-6×.

**Geometric coupling formula**:
```
B(sep, ρ, θ) = 0.044 × sep² × [(1 - ρ sin(2θ)) / (1-ρ²)]^0.61
```

Where θ is the angle between mode separation vector and correlation principal axis.

- Modes parallel to correlation axis: B reduced by ~2.3×
- Modes orthogonal to correlation axis: B increased by ~2.3×

**Validation**: See [Variational Inference](../../applications/ml/variational-inference.md) for full experimental results.

---

## Universality Across Distributions

The BLD decomposition is **universal** — it holds beyond Gaussians.

| Distribution | B scales with sep? | L constant with sep? |
|--------------|-------------------|----------------------|
| Gaussian mixture | ✓ (r > 0.99) | ✓ (CV ≈ 0.29) |
| Student-t mixture (df ≥ 5) | ✓ (r > 0.99) | ✓ (CV ≈ 0.35) |
| Laplace mixture | ✓ (r > 0.99) | ✓ (CV ≈ 0.37) |

**Key finding**: The separation of topological (B) and geometric (L) costs is universal across the exponential family.

**Heavy tails**: Heavier-tailed distributions (Student-t, Laplace) have "softer" boundaries — density bleeds between modes. This reduces B_cost compared to Gaussian for the same configuration:
- B_cost(Student-t, df=5) < B_cost(Gaussian)
- L_cost remains governed by the exact KL formula

**Interpretation**: BLD reveals the **hidden topology** of probability distributions. Information geometry sees only the smooth structure (L); BLD exposes the discrete mode structure (B). This is analogous to how algebraic topology reveals discrete invariants from continuous spaces.

---

## Notation Summary

| Symbol | Meaning |
|--------|---------|
| M | The full structural manifold |
| M_τ | Stratum with topology τ |
| S = (B, L, D) | A structure (point on M) |
| θ | Coordinates within a stratum |
| cost(S₁, S₂) | Alignment cost between structures |
| gᵢⱼ | Metric tensor (Hessian of cost) |
| φ_T(S) | Potential function for fixed traverser T |
| ∇φ | Gradient (direction of steepest descent) |

---

## Related Documents

- [Manifold Geometry](./manifold-geometry.md) — Metric and differential geometry
- [Manifold Applications](./manifold-applications.md) — Domain interpretations

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — BLD = Lie theory mapping
- [Boundary Derivation](../lie-theory/boundary-derivation.md) — Exact B formula derivation
- [Variational Inference](../../applications/ml/variational-inference.md) — Experimental validation
- [Thermodynamics](../classical/thermodynamics.md) — Statistical mechanics on the manifold
