---
status: DERIVED
depends_on:
  - ../foundations/irreducibility-proof.md
  - ../lie-theory/lie-correspondence.md
---

# Cosmological Structure from BLD

The L/D = 5 ratio follows from Lie theory; mapping to dark matter is conjectured.

**Source**: Extracted from `cosmology.md`

---

## The Core Derivation `[DERIVED]`

### Step 1: Lie Algebra Structure

A Lie algebra consists of three independent components:

| Component | Symbol | BLD Primitive |
|-----------|--------|---------------|
| Generators | Xᵢ | D (dimension) |
| Structure constants | fᵢⱼᵏ | L (link) |
| Topology | compact/non-compact | B (boundary) |

These are defined by the bracket relation:
```
[Xᵢ, Xⱼ] = fᵢⱼᵏXₖ
```

### Step 2: BLD Irreducibility `[PROVEN]`

From the [Irreducibility Proof](../foundations/irreducibility-proof.md):

- B, L, D provide distinct capabilities
- None is expressible in terms of the others
- **L is not reducible to D**

### Step 3: Degrees of Freedom in 4D Spacetime `[DERIVED]`

**D (Dimensions)**: 4 (spacetime dimensions)

**L (Geometry)**: Riemann tensor has n²(n²-1)/12 independent components

For n = 4:
```
L = 4²(4²-1)/12 = 16×15/12 = 20
```

**Ratio**:
```
L/D = 20/4 = 5
```

Geometric degrees of freedom are 5× dimensional degrees of freedom.

This is a **mathematical fact** about 4D manifolds with curvature.

---

## The Independence Theorem `[DERIVED]`

The Riemann curvature tensor in 4D has 20 independent components.

Einstein's equation (via matter Tμν) constrains only the Ricci part (10 components).

The **Weyl tensor** (10 components) is unconstrained by local matter — it represents pure geometric structure.

**Weyl curvature = L without D.** This already exists in standard GR.

---

## Why This Matters

### What Standard GR Says

Einstein's equation Gμν = 8πGTμν couples matter (D) to geometry (L).

But this coupling does not make L reducible to D. Geometry can exist without matter source.

### What BLD Adds

BLD identifies this as a structural fact: L and D are irreducible primitives. You cannot derive one from the other.

**Implication**: Some geometric structure (L) may have no matter source (D).

---

## Limitations of This Derivation

This document establishes:
- L/D = 5 for 4D spacetime `[DERIVED]`
- L and D are independent `[PROVEN]`
- Weyl curvature is matter-independent `[KNOWN GR]`

This document does NOT establish:
- That dark matter IS geometric L `[CONJECTURED]`
- That the 25%/27% ratio follows `[EMPIRICAL]`
- That the observer correction is valid `[EMPIRICAL]`

See [Dark Matter Mapping](dark-matter-mapping.md) for the conjectured application.

---

## Why Not MOND?

Modified Newtonian Dynamics (MOND) changes the gravitational law:
```
F = ma  →  F = ma·μ(a/a₀)
```

BLD does not modify laws. It identifies a **category error**:
- We assumed: all gravitational L must come from D
- Lie theory says: L and D are independent
- Therefore: some L has no D source

We're not changing physics. We're correcting how we classify gravitational effects.

---

## References

- [Irreducibility Proof](../foundations/irreducibility-proof.md) — L and D independence
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — BLD = Lie theory
- [Dark Matter Mapping](dark-matter-mapping.md) — Conjectured application
