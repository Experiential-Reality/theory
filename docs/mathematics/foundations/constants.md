---
status: DERIVED
layer: 0
key_result: "B=56, L=20, n=4, K=2, S=13 — all derived"
depends_on:
  - ../particle-physics/e7-derivation.md
  - ../lie-theory/lie-correspondence.md
  - ../lie-theory/killing-form.md
  - derivations/octonion-derivation.md
used_by:
  - definitions/bld-calculus.md
  - derivations/force-structure.md
  - derivations/energy-derivation.md
  - machine/universal-machine.md
  - machine/integer-machine.md
  - machine/detection-structure.md
  - definitions/ubit.md
---

# BLD Constants

## Abstract

The five fundamental BLD constants (B, L, n, K, S) are derived from axioms and structural closure requirements, not measured. B = 56 arises from triality structure (2 × dim(Spin(8))), L = 20 from Riemann tensor components, n = 4 from octonion reference fixing, K = 2 from bidirectional observation, and S = 13 from structural intervals. These constants determine all physical coupling constants through the formula α⁻¹ = n×L + B + 1 = 137. This file is the authoritative source for constant values and derivation references.

---

## Summary

**Five core constants, all derived:**

1. B = 56 — Boundary modes (2 × dim(Spin(8))) — [Constants](#the-constants)
2. L = 20 — Riemann tensor components — [Why L = Riemann](#why-l--riemann-tensor-components)
3. n = 4 — Spacetime dimensions (octonion reference fixing) — [Constants](#the-constants)
4. K = 2 — Killing form (bidirectional observation) — [Constants](#the-constants)
5. S = 13 — Structural intervals ((B−n)/n) — [Derived Combinations](#derived-combinations)

**One formula**: α⁻¹ = n×L + B + 1 = 80 + 56 + 1 = 137 — [Derivation Chain](#the-derivation-chain)

---

## The Constants

| Symbol | Value | Meaning | Derived From |
|--------|-------|---------|--------------|
| **B** | 56 | Boundary modes | 2 × dim(Spin(8)) = 2 × 28. See [E7 Derivation](../particle-physics/e7-derivation.md) |
| **L** | 20 | Riemann components | n²(n²-1)/12 = 16×15/12. See below and [Lie Correspondence](../lie-theory/lie-correspondence.md) |
| **n** | 4 | Spacetime dimensions | sl(2,ℂ) ⊂ sl(2,𝕆) from reference fixing. See [Octonion Derivation](derivations/octonion-derivation.md) |
| **K** | 2 | Killing form | Bidirectional observation (forward + back). See [Killing Form](../lie-theory/killing-form.md) |
| **S** | 13 | Structural intervals | (B - n)/n = (56 - 4)/4 = 13 |

---

## Why L = Riemann Tensor Components

**Question**: Why Riemann tensor and not connection coefficients (Christoffel symbols)?

**Answer**: L measures how links vary across structure. The Riemann tensor is the unique gauge-invariant measure of this.

| Object | Components (n=4) | Problem |
|--------|------------------|---------|
| Christoffel Γ^λ_μν | n³ = 64 | Coordinate-dependent (gauge artifact) |
| Riemann R^ρ_σμν | n²(n²-1)/12 = 20 | Gauge-invariant (geometric truth) |

**Physical meaning**: The Riemann tensor answers "if you parallel transport a vector around a loop, how much does it rotate?" This is exactly how links (connections between points) vary — the structural content of L.

**Why the formula n²(n²-1)/12**:
- Riemann has symmetries: R_abcd = -R_bacd = -R_abdc, R_abcd = R_cdab, R_[abc]d = 0
- These reduce n⁴ = 256 components to n²(n²-1)/12 = 20 independent ones
- This is a mathematical fact, not a choice

**Therefore**: L = 20 is the number of independent ways curvature (link variation) can exist in n=4 dimensions.

---

## Derived Combinations

| Expression | Value | Appears In |
|------------|-------|------------|
| n × L | 80 | Geometric structure (fine structure base) |
| n × L + B | 136 | Structure without traverser |
| n × L + B + 1 | 137 | Full structure (α⁻¹ integer part) |
| n² × S | 208 | Generational structure (μ/e base) |
| K / B | 2/56 ≈ 0.036 | Boundary quantum (observer correction) |
| K / (n × L) | 2/80 = 0.025 | Geometric correction |
| n × L × B | 4480 | Full structure product |
| K² + (n-1)² | 4 + 9 = S = 13 | Observation² + spatial² = structural intervals |
| S + 1 = B/n | 14 | Boundary per dimension = dim(G₂) |
| B - K = K(n-1)³ | 54 = 2×27 | Usable boundary capacity |
| L + n + 1 | 25 | Geometric-observer budget (intermittency denominator) |

---

## The Derivation Chain

```
Nothing is self-contradictory (logical necessity)
    ↓
B must exist (primordial distinction)
    ↓
traverse(-B, B) must CLOSE (self-consistency)
    ↓
Closure requires triality (stable 3-fold self-reference)
    ↓
Triality unique to Spin(8) → dim(so(8)) = 28
    ↓
K = 2 (Killing form, bidirectional)
    ↓
B = K × 28 = 56
    ↓
Octonions required → sl(2,𝕆) → sl(2,ℂ) → n = 4
    ↓
L = n²(n²-1)/12 = 20 (Riemann tensor)
    ↓
S = (B - n)/n = 13
```

---

## References

- [E7 Derivation](../particle-physics/e7-derivation.md) — B = 56 from triality
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — L = 20 from Riemann tensor
- [Octonion Derivation](derivations/octonion-derivation.md) — n = 4 from reference fixing
- [Killing Form](../lie-theory/killing-form.md) — K = 2 from bidirectional observation
- [Octonion Necessity](derivations/octonion-necessity.md) — Why these values are required (genesis closure)
