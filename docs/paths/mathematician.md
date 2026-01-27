---
status: FOUNDATIONAL
layer: reference
depends_on: []
used_by:
  - practitioner.md
  - README.md
  - newcomer.md
  - ../mathematics/README.md
---

# Reading Path: Mathematician

> **Status**: Foundational

> For those who want the rigorous foundations.

This path covers the mathematical structure in depth.

## Summary

**Mathematician reading path — rigorous foundations:**

1. Formal Definitions: precise B, L, D specification — [Step 1](#step-1-formal-definitions)
2. Independence Proof: type-theoretic irreducibility — [Step 2](#step-2-independence-proof)
3. Lie Correspondence: D=generators, L=structure constants, B=topology — [Step 3](#step-3-the-lie-correspondence)
4. Worked Examples: so(2), su(2), Heisenberg, Poincaré — [Step 4](#step-4-worked-examples)
5. Structural Manifold: structures as points, alignment cost as divergence — [Step 5](#step-5-the-structural-manifold)
6. Conservation Laws: Noether's theorem in BLD — [Step 6](#step-6-conservation-laws)
7. Thermodynamics: second law as geometric theorem — [Step 7](#step-7-thermodynamics)
8. Euler Unification: e^(iπ)+1=0 connects both compensation mechanisms — [Step 8](#step-8-the-euler-unification)

| Result | Status |
|--------|--------|
| B/L/D irreducibility | Proven |
| BLD = Lie theory | Verified |
| L = -½ ln(1 - ρ²) | Exact theorem |

---

## Step 1: Formal Definitions

**Read**: [Structural Language](../theory/structural-language.md)

**Key takeaway**: Formal specification of B, L, D as mathematical objects.

---

## Step 2: Independence Proof

**Read**: [Irreducibility Proof](../mathematics/foundations/proofs/irreducibility-proof.md)

Then optionally: [Categorical Proof](../mathematics/foundations/proofs/irreducibility-categorical.md)

**Key takeaway**: Type-theoretic proof that B, L, D are independent primitives.

---

## Step 3: The Lie Correspondence

**Read**: [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md)

**Key takeaway**:
- D = Lie algebra generators
- L = Structure constants fᵢⱼᵏ
- B = Group topology (compact/non-compact)

---

## Step 4: Worked Examples

**Read**: [Lie Algebra Examples](../examples/lie-algebras.md)

**Key takeaway**: See so(2), su(2), Heisenberg, Poincaré algebras in BLD notation.

---

## Step 5: The Structural Manifold

**Read**: [The Structural Manifold](../mathematics/derived/manifold-foundations.md)

**Key takeaway**: Structures form a manifold. Alignment cost = divergence. Curvature comes from Lie bracket.

---

## Step 6: Conservation Laws

**Read**: [BLD Conservation](../mathematics/bld-conservation.md)

**Key takeaway**: Noether's theorem in BLD. Conservation laws ARE BLD conservation.

---

## Step 7: Thermodynamics

**Read**: [Thermodynamics](../mathematics/derived/thermodynamics.md)

**Key takeaway**: Second law as geometric theorem on the structural manifold.

---

## Step 8: The Euler Unification

**Read**: [π from BLD](../examples/pi-from-bld.md), [e from BLD](../examples/e-from-bld.md), and [Compensation Principle](../mathematics/foundations/structural/compensation-principle.md)

**Key takeaway**: Euler's formula e^(iπ) + 1 = 0 unifies the two compensation mechanisms:

| Mechanism | Constant | Lie Group Type | Physical Domain |
|-----------|----------|----------------|-----------------|
| **Exponential** | e | Non-compact | Cascades, depth, boosts |
| **Angular** | π | Compact | Rotations, phases, spin |
| **Both** | e^(iπ) | Mixed | Spirals (α-helix), Lorentz |

The exponential map exp(tX) IS compensation:
- For real t: exp(tX) grows without bound (exponential compensation)
- For imaginary t: exp(iθX) returns at 2π (angular compensation)
- For complex t: exp((a+iθ)X) spirals (both mechanisms)

---

## Additional Topics

- [Boundary Derivation](../mathematics/lie-theory/boundary-derivation.md) — B from SPD curvature
- [Canonical Hardness](../mathematics/foundations/structural/canonical-hardness.md) — Finding minimal BLD is NP-complete

---

## The Key Results

| Result | Status |
|--------|--------|
| B/L/D irreducibility | Proven |
| BLD = Lie theory | Verified |
| L = -½ ln(1 - ρ²) | Exact theorem |
| D×L scaling | R² = 1.0 |
| Noether correspondence | Derived |
| Euler unification | Exploratory |
| Completeness via e, π | Conjectured |

---

## See Also

- [Newcomer Path](./newcomer.md) — Gentler introduction
- [Practitioner Path](./practitioner.md) — For applied use
- [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md) — Key theorem
