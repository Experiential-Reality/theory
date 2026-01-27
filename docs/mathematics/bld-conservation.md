---
status: DERIVED
depends_on:
  - lie-theory/lie-correspondence.md
---

# BLD Conservation via Noether's Theorem

> **Status**: Validated

BLD conservation is Noether's theorem expressed in structural language. Every conservation law in physics corresponds to a symmetry, and every symmetry has BLD structure.

---

## Summary

**BLD conservation IS Noether's theorem:**

1. Noether: continuous symmetry → conserved quantity — [The Connection](#the-connection)
2. Symmetries are Lie groups with BLD structure: D=generators, L=structure constants, B=topology — [Mathematical Framework](#the-mathematical-framework)
3. D conserves: number of independent symmetry directions (charges) — [What Each Primitive Conserves](#what-each-primitive-conserves)
4. L conserves: composition rules for how charges interact — [What Each Primitive Conserves](#what-each-primitive-conserves)
5. B determines quantization: compact (closed) → discrete charges — [Why B Determines Quantization](#why-b-determines-quantization)

| Symmetry | Lie Group | D | B | Conserved |
|----------|-----------|---|---|-----------|
| Time | ℝ | 1 | Open | Energy |
| Rotation | SO(3) | 3 | Closed | Angular momentum |
| U(1) gauge | U(1) | 1 | Closed | Electric charge |

---

## The Connection

**Noether's Theorem** (1918): Every continuous symmetry of the action corresponds to a conserved quantity.

**BLD = Lie Theory**: The symmetries that Noether's theorem references are Lie groups. Their structure is:
- **D** = Lie algebra generators (directions of symmetry)
- **L** = Structure constants (how symmetries compose)
- **B** = Group topology (bounded vs unbounded)

**Therefore**: Conservation laws ARE BLD conservation.

---

## The Mathematical Framework

### Symmetries as Lie Groups

A **symmetry** is a transformation that leaves the physics unchanged. Continuous symmetries form **Lie groups**:

```
Symmetry transformation: x → x' = g · x

where g ∈ G (a Lie group)
```

The infinitesimal generators of G form the **Lie algebra** g:

```
g · x ≈ x + ε Xᵢ · x    (for small ε)

where Xᵢ are the generators
```

### Noether's Theorem (Precise Statement)

For a system with Lagrangian L(q, q̇, t), if the action S = ∫L dt is invariant under a continuous transformation with generator X, then:

```
Q = ∂L/∂q̇ · δq - X · L

is conserved: dQ/dt = 0
```

Each generator → one conserved charge.

### BLD Decomposition of Symmetries

Every Lie group G decomposes into BLD:

| Component | Lie Theory | BLD | Conserved |
|-----------|-----------|-----|-----------|
| Generators | dim(g) | **D** (count) | Number of conservation laws |
| Structure constants | fᵢⱼᵏ | **L** (relations) | How charges interact |
| Topology | Compact/non-compact | **B** (closure) | Whether charges are quantized |

---

## Physical Conservation Laws as BLD

### Spacetime Symmetries

| Symmetry | Lie Group | D | L | B | Conserved |
|----------|-----------|---|---|---|-----------|
| Time translation | ℝ | 1 | 0 (abelian) | Open | **Energy** |
| Space translation | ℝ³ | 3 | 0 (abelian) | Open | **Momentum** (3 components) |
| Rotation | SO(3) | 3 | εᵢⱼₖ | Closed | **Angular momentum** |
| Lorentz boost | SO(3,1) | 3 | Mixed | Open | **Center of mass motion** |

### Internal Symmetries

| Symmetry | Lie Group | D | L | B | Conserved |
|----------|-----------|---|---|---|-----------|
| U(1) gauge | U(1) | 1 | 0 (abelian) | Closed | **Electric charge** |
| SU(2) weak | SU(2) | 3 | εᵢⱼₖ | Closed | **Weak isospin** |
| SU(3) color | SU(3) | 8 | fᵢⱼₖ | Closed | **Color charge** |
| Baryon U(1) | U(1) | 1 | 0 (abelian) | Closed | **Baryon number** |

---

## What Each Primitive Conserves

### D Conservation (Generator Count)

The **number of independent symmetry directions** is conserved.

**Example**: Rotational symmetry has D = 3 (three rotation axes). No physical process can change this—you always have exactly three independent angular momenta.

**Physical meaning**: The dimensionality of the symmetry algebra is a structural invariant.

### L Conservation (Structure Constants)

The **composition rules** for symmetries are conserved.

**Example**: For SO(3), [Jx, Jy] = iJz. This relation CANNOT change—it's built into the structure of 3D space.

**Physical meaning**: How conserved charges combine is itself invariant.

### B Conservation (Topology)

The **boundedness** of the symmetry is conserved.

**Example**: Rotation is bounded (B = closed), so angular momentum is quantized. Translation is unbounded (B = open), so momentum is continuous.

**Physical meaning**: Whether a charge is quantized or continuous is a topological invariant.

---

## Why B Determines Quantization

**Theorem**: Compact Lie groups have discrete (quantized) representations.

**Proof sketch**:
1. Compact groups have finite volume
2. Representations must "fit" in this volume
3. Only discrete representations fit finitely

**In BLD terms**: Closed B → quantized charges.

| Symmetry | B | Charge |
|----------|---|--------|
| Rotation (SO(3)) | Closed | Angular momentum quantized: L = 0, 1, 2, ... |
| Spin (SU(2)) | Closed | Spin quantized: s = 0, ½, 1, 3/2, ... |
| U(1) gauge | Closed | Electric charge quantized: q = ..., -1, 0, 1, ... |
| Translation (ℝ) | Open | Momentum continuous |
| Boost | Open | Velocity continuous |

---

## The Circle and π

For SO(2) (planar rotation):

```
D = 1 (one generator: rotation angle θ)
L = 0 (abelian: rotations commute)
B = closed (θ + 2π = θ)
```

Noether's theorem: Rotational symmetry → angular momentum conservation.

The constant **2π** appears because it measures the "size" of B—how much D×L is needed to traverse the closed boundary once.

See [π from BLD](../examples/pi-from-bld.md) for the full derivation.

---

## Euler's Formula and the Exponential Map

The exponential map exp: g → G connects algebra (infinitesimal) to group (finite):

```
exp(θX) = group element from generator X at parameter θ
```

For SO(2): exp(iθ) = cos(θ) + i·sin(θ) — this IS Euler's formula.

**The Euler connection to conservation**:

| Group Type | Exponential Map | Conservation Property | Euler Component |
|------------|-----------------|----------------------|-----------------|
| **Compact** (SO(n), SU(n)) | exp(iθX) returns at 2π | Quantized charges | **π** |
| **Non-compact** (ℝ, boosts) | exp(tX) unbounded | Continuous spectrum | **e** |
| **Mixed** (Lorentz) | exp((a+iθ)X) | Both quantized and continuous | **Both** |

**Why e^(iπ) = -1 matters for physics**:
- Half rotation through SO(2) inverts the state (spin-½ → -spin-½)
- Full rotation (2π) returns to original (e^(i2π) = 1)
- This is the origin of fermion statistics: 360° rotation = identity

The exponential map IS the mechanism by which symmetries generate conservation laws. Euler's formula shows the two types of conservation (quantized vs continuous) are aspects of a single structure.

See [Euler's Formula in BLD](../glossary.md#euler) and [Lie Correspondence](./lie-theory/lie-correspondence.md).

---

## Conservation Under Transformation

When a system transforms, BLD is **redistributed** but not created or destroyed:

```
Before: System S₁ with symmetry G₁ = (D₁, L₁, B₁)
After:  System S₂ with symmetry G₂ = (D₂, L₂, B₂)

Conservation:
  - Σ Dᵢ conserved (total generator count)
  - L structure constants invariant
  - B topology preserved
```

**Example: Particle decay**

π⁰ → γ + γ

- Before: π⁰ has spin 0 (D = 0 for rotation)
- After: Two photons with spin ±1, but total angular momentum = 0
- **D conserved**: Total spin unchanged

---

## Formal Statement

**BLD-Noether Correspondence**:

Let G be a Lie group acting as a symmetry of a physical system.

Then:
1. Each generator Xᵢ ∈ g corresponds to a conserved charge Qᵢ
2. The number of charges = dim(g) = D
3. The charge algebra [Qᵢ, Qⱼ] = fᵢⱼᵏQₖ follows from L
4. Charges are quantized iff G is compact (B closed)

**The conservation laws of physics ARE the structural invariance of BLD.**

---

## Comparison to Previous Understanding

| Previous (Exploratory) | Current (Validated) |
|------------------------|---------------------|
| "B/L/D might be conserved" | Noether proves they ARE |
| Vague correspondence to physics | Exact mapping via Lie theory |
| Speculative | Derived from established mathematics |

The key insight: We don't need to prove BLD conservation separately—it follows directly from Noether's theorem once we recognize BLD = Lie theory.

---

## Open Questions

1. **Anomalies**: Some classical symmetries (conserved at classical level) are broken by quantum effects. What does this mean for BLD?
   - Example: Axial U(1) anomaly in QCD
   - Possible answer: Anomalies involve discrete (non-Lie) structure

2. **Spontaneous symmetry breaking**: When symmetry is hidden but not destroyed, how does BLD change?
   - Example: Higgs mechanism
   - Possible answer: B becomes "hidden" rather than absent

3. **Discrete symmetries**: Noether applies to continuous symmetries. What about discrete ones (P, C, T)?
   - These correspond to discrete groups, not Lie groups
   - BLD may need extension for discrete B structures

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Lie Correspondence](./lie-theory/lie-correspondence.md) — BLD = Lie theory mapping
- [π from BLD](../examples/pi-from-bld.md) — Why 2π appears in angular momentum
- [Lie Algebra Examples](../examples/lie-algebras.md) — Worked examples (so(3), Heisenberg, Poincaré)
- [Thermodynamics](./derived/thermodynamics.md) — Second law as geometric constraint
