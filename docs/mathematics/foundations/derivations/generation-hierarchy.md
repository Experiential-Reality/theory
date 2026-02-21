---
status: DERIVED
layer: 1
key_result: "C₂ = R uniquely for so(8); S = 2C₂-1 = 13; n²S = 208 universal mass scale; structural μ/e = 207, τ/μ = 17"
depends_on:
  - equation-of-motion.md
  - gauge-structure.md
  - ../../lie-theory/killing-form.md
used_by:
  - ../../particle-physics/lepton-masses.md
  - ../../particle-physics/quark-masses.md
  - ../../../meta/proof-status.md
---

## Summary

**Generation hierarchy — from Casimir-curvature bridge to mass scale:**

1. C₂(vector) = R uniquely for so(8): bridges representation theory to Riemannian geometry — [§1](#1-casimir-curvature-bridge)
2. S = 2C₂ - 1 = 13: the generation constant derived from the vector Casimir — [§2](#2-s-from-casimir)
3. S₃ permutation group breaks triality into 3 generations with integer structural ratios — [§3](#3-s₃-generation-hierarchy)
4. n²S = 208: the universal mass scale shared by all fermion mass formulas — [§4](#4-n²s--208-universal-mass-scale)

| Result | Formula | Value | Test File |
|--------|---------|-------|-----------|
| Casimir bridge | C₂(vector) = R ⟺ d = 8 (D₄) | unique | test_eom_generation |
| Generation constant | S = 2C₂ - 1 | 13 | test_eom_generation |
| Mass scale | n² × S | 208 | test_eom_generation |
| μ/e structural | n²S - 1 | 207 | test_eom_generation |
| τ/μ structural | S + n | 17 | test_eom_generation |

# Generation Hierarchy: Casimir Bridge and Mass Scale

## Abstract

The [equation of motion](equation-of-motion.md) establishes so(8) as the dynamical algebra with scalar curvature R = 7 and vector Casimir C₂ = 7. The equality C₂ = R is unique to D₄ = so(8) among all so(n) algebras, bridging representation theory (particle mass terms) to Riemannian geometry (heat kernel, path integral). From this bridge: S = 2C₂ - 1 = 13, the generation constant. The triality automorphism group S₃ provides the three-generation structure, with symmetry breaking S₃ → Z₂ → 1 producing structural integer mass ratios μ/e = 207 = n²S - 1 and τ/μ = 17 = S + n. All fermion mass formulas share the scale n²S = 208 = dim(u(4)) × S, with corrections O(1/n²S) < 0.5%.

## 1. Casimir-Curvature Bridge

For so(d) with d the dimension of the fundamental representation, two independently defined quantities are:

- **Quadratic Casimir of the vector representation:** C₂(vector) = d - 1
- **Scalar curvature of SO(d) with bi-invariant metric:** R = d(d-1)/8

(The scalar curvature follows from the Killing form normalization and the formula R = -1/4 Σ \|[e_i, e_j]\|² for compact simple Lie groups.)

The equation C₂ = R gives:

```
d - 1 = d(d-1)/8
8 = d
```

**Unique solution: d = 8, i.e., D₄ = so(8).** (Here d = 2n in BLD notation, where n = 4 is the spacetime dimension.)

This bridge connects two domains:
- **Representation theory** (Casimir → mass terms, selection rules, particle quantum numbers)
- **Riemannian geometry** (curvature → heat kernel → path integral → quantum amplitudes)

The bridge is unique to the triality algebra — the same algebra forced by BLD completeness.

## 2. S from Casimir

With C₂ = 7 for so(8), the generation constant follows:

```
S = 2C₂ - 1 = 2(7) - 1 = 13
```

Cross-check with BLD constants: S = (B - n)/n = (56 - 4)/4 = 13. The two derivations (from Casimir and from BLD constants) agree.

Additionally:

```
B/n = 2C₂ = 14
```

This connects the BLD boundary constant B to the representation theory through the Casimir. The boundary-to-spacetime ratio is twice the vector Casimir.

## 3. S₃ Generation Hierarchy

The outer automorphism group of D₄ = so(8) is S₃, the permutation group on 3 elements. It acts by triality, permuting the three 8-dimensional representations (8_v, 8_s, 8_c).

**Character table of S₃:**

| Irrep | dim | e | (12) | (123) |
|-------|-----|---|------|-------|
| trivial | 1 | 1 | 1 | 1 |
| sign | 1 | 1 | -1 | 1 |
| standard | 2 | 2 | 0 | -1 |

Character orthogonality: Σ χ_i χ_j / |g| = δ_{ij}.

**Permutation representation.** S₃ acts on {8_v, 8_s, 8_c} by the 3-dim permutation representation, which decomposes as trivial ⊕ standard. The trivial part is the generation-symmetric sector; the standard part carries the generation structure.

**S₃ → Z₂ → 1 breaking.** The maximal subgroup chain S₃ ⊃ Z₂ ⊃ 1 gives two breaking steps:

1. **S₃ → Z₂:** The standard irrep of S₃ restricts to trivial + sign of Z₂. The broken generator connects to the largest Casimir eigenvalue, so the heaviest generation (τ) separates at this step.
2. **Z₂ → 1:** The remaining Z₂ symmetry breaks completely, separating the muon from the electron.

**Structural integer mass ratios.** The symmetry breaking produces exact integers before observation corrections:

```
μ/e (structural) = n²S - 1 = 16 × 13 - 1 = 207
τ/μ (structural) = S + n   = 13 + 4     = 17
τ/e (structural) = 207 × 17 = 3519
```

The observed ratios (206.768, 16.817) differ from these integers by K/X alignment gradients — the cost of continuous observation seeing discrete structure. The transcendental value 2πe ≈ 17.079 is how continuous measurement sees the discrete integer 17 (agreement within 0.5%).

## 4. n²S = 208 Universal Mass Scale

The product n²S = 16 × 13 = 208 is the universal generation scale. Its factors have distinct origins:

- **n² = 16 = dim(u(4))**: the [gauge algebra](gauge-structure.md) dimension, number of internal degrees of freedom
- **S = 13 = 2C₂ - 1**: the generation constant from the Casimir bridge (§1-§2)

**n²S = number of distinguishable structure positions** — the total number of states that the gauge algebra can distinguish across the generation hierarchy.

All fermion mass formulas share n²S as the dominant scale:

| Mass ratio | Formula | Value | % of n²S |
|------------|---------|-------|----------|
| μ/e | n²S - 1 | 207 | 99.5% |
| m_s/m_e | n²S - L - L/n | 183 | 88.0% |
| τ/μ | contains (n²S-1)/n²S | 207/208 | — |
| m_t correction | contains 1 - K/n²S | 206/208 | — |

All corrections are O(1/n²S) < 0.5%. Using a wrong S or wrong n gives predictions more than 5σ from experiment.

## Conclusion

The Casimir-curvature bridge C₂ = R, unique to so(8), connects the equation of motion's geometric structure to the particle mass hierarchy. The generation constant S = 2C₂ - 1 = 13 is not an independent parameter but a consequence of the vector representation's Casimir eigenvalue. The S₃ outer automorphism provides three generations with integer structural ratios (207, 17), and the scale n²S = 208 unifies all fermion mass formulas. The detailed mass predictions are derived in [lepton-masses.md](../../particle-physics/lepton-masses.md) and [quark-masses.md](../../particle-physics/quark-masses.md).

## References

### Internal

- [Equation of Motion](equation-of-motion.md) — scalar curvature R = 7, Casimir C₂ = 7
- [Gauge Structure](gauge-structure.md) — u(4) dimension = n² = 16
- [Killing Form](../../lie-theory/killing-form.md) — bi-invariant metric, curvature formulas
- [Lepton Masses](../../particle-physics/lepton-masses.md) — detailed mass predictions using n²S
- [Quark Masses](../../particle-physics/quark-masses.md) — quark mass formulas with n²S corrections
