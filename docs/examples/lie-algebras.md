---
status: FOUNDATIONAL
layer: 1
depends_on:
  - ../mathematics/lie-theory/lie-correspondence.md
used_by:
  - ../mathematics/quantum/quantum-mechanics.md
---

# Lie Algebra Examples in BLD

## Quick Summary (D≈7 Human Traversal)

**Lie algebras in BLD in 7 steps:**

1. **D = generators** — Each symmetry direction is a BLD dimension
2. **L = structure constants** — [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ are the links between generators
3. **B = topology** — Compact (closed B) vs non-compact (open B)
4. **so(2)** — 1 generator, no links (abelian), closed boundary
5. **su(2)** — 3 generators Jₓ,Jᵧ,Jᵤ, links via εᵢⱼₖ (Levi-Civita), closed
6. **Heisenberg** — Position (D), momentum (L), [x,p]=iℏ, open boundary
7. **Standard Model** — SU(3)×SU(2)×U(1) = 12 generators, specific links, closed

| Algebra | D (generators) | L (structure) | B (topology) |
|---------|----------------|---------------|--------------|
| so(2) | 1 | ∅ | closed |
| su(2) | 3 | εᵢⱼₖ | closed |
| Heisenberg | 3 | [x,p]=iℏ | open |

---

> **Status**: Foundational

Concrete examples showing the BLD = Lie theory correspondence for well-known Lie algebras.

---

## so(2): 2D Rotations

The simplest non-trivial example.

### The Lie Algebra

**so(2)** is the algebra of 2D rotations (the circle group SO(2)).

- **1 generator**: Rotation angle θ
- **Structure constants**: None (trivial, since there's only one generator)
- **Topology**: Compact (θ + 2π = θ)

### BLD Description

```
Structure:
  D: [rotation_angle]     # extent = 2π (or unbounded for the algebra)
  L: {}                   # no links (abelian)
  B: closed               # rotation is periodic
```

### Why It's Simple

With only one generator, there's nothing to commute. The algebra is **abelian**: [X, X] = 0 trivially.

All abelian Lie algebras look like this: multiple independent generators with no coupling (L = empty).

---

## so(3) / su(2): 3D Rotations and Spin

The canonical example of non-abelian structure.

### The Lie Algebra

**so(3)** describes 3D rotations. **su(2)** is its double cover (relevant for spin-½).

- **3 generators**: Jx, Jy, Jz (angular momentum operators)
- **Structure constants**: The Levi-Civita symbol εᵢⱼₖ
- **Topology**: Compact (all rotations are bounded)

### The Commutation Relations

```
[Jx, Jy] = iJz
[Jy, Jz] = iJx
[Jz, Jx] = iJy
```

Or in index notation: [Jᵢ, Jⱼ] = iεᵢⱼₖJₖ

### BLD Description

```
Structure:
  D: [Jx, Jy, Jz]                    # 3 generators (dimensions)

  L: {                               # structure constants
    (Jx, Jy) → iJz,                  # [Jx, Jy] = iJz
    (Jy, Jz) → iJx,                  # [Jy, Jz] = iJx
    (Jz, Jx) → iJy                   # [Jz, Jx] = iJy
  }

  B: closed                          # SO(3)/SU(2) are compact
```

### Verification (from scripts/verify_lie_bld.py)

The structure constants are εᵢⱼₖ, the Levi-Civita tensor:
- ε₁₂₃ = ε₂₃₁ = ε₃₁₂ = +1
- ε₃₂₁ = ε₁₃₂ = ε₂₁₃ = -1
- All others = 0

This matches exactly. L captures the antisymmetric coupling between rotation axes.

### Physical Meaning

- **D** = the three independent rotation axes (or spin directions)
- **L** = the fact that rotations don't commute (order matters)
- **B = closed** = quantized angular momentum (spin is discrete: 0, ½, 1, 3/2, ...)

---

## Heisenberg Algebra: Position and Momentum

The algebra underlying quantum mechanics.

### The Lie Algebra

The **Heisenberg algebra** h₃ describes position and momentum:

- **3 generators**: Q (position), P (momentum), I (identity/central)
- **Structure constants**: [Q, P] = iI, all others zero
- **Topology**: Non-compact (position and momentum are unbounded)

### The Commutation Relations

```
[Q, P] = iI
[Q, I] = 0
[P, I] = 0
```

This is the origin of Heisenberg's uncertainty principle.

### BLD Description

```
Structure:
  D: [Q, P, I]                       # 3 generators

  L: {                               # structure constants
    (Q, P) → iI                      # [Q, P] = iI (the uncertainty relation)
  }

  B: open                            # non-compact (unbounded)
```

### Physical Meaning

- **D** = position axis, momentum axis, and the "central direction"
- **L = iI** captures the uncertainty principle: Q and P don't commute
- **B = open** = continuous spectrum (not quantized like spin)

---

## Poincaré Algebra: Spacetime Symmetry

The symmetry of special relativity.

### The Lie Algebra

The **Poincaré algebra** describes spacetime transformations:

- **10 generators**:
  - 4 translations: Pμ (energy-momentum)
  - 6 Lorentz transformations: Mμν (3 rotations + 3 boosts)
- **Structure constants**: Complex (see below)
- **Topology**: Non-compact (boosts are unbounded)

### The Commutation Relations (selected)

```
[Pμ, Pν] = 0                        # translations commute
[Mμν, Pρ] = i(ημρPν - ηνρPμ)        # Lorentz transforms momentum
[Mμν, Mρσ] = i(ημρMνσ - ...)        # Lorentz algebra (so(3,1))
```

### BLD Description

```
Structure:
  D: [P₀, P₁, P₂, P₃,               # 4 translation generators
      M₀₁, M₀₂, M₀₃,                # 3 boosts
      M₁₂, M₂₃, M₃₁]                # 3 rotations

  L: {                               # structure constants
    # Translations are abelian
    (Pμ, Pν) → 0

    # Lorentz acts on translations
    (Mμν, Pρ) → linear combination of P's

    # Lorentz algebra
    (Mμν, Mρσ) → linear combination of M's
  }

  B: mixed                           # rotations compact, boosts non-compact
```

### Physical Meaning

- **D** = the 10 spacetime symmetry directions
- **L** captures how transformations combine (momentum transforms under boosts)
- **B** = rotations are bounded (compact), boosts are unbounded (non-compact)

The non-compact boosts explain why there's no maximum momentum (unlike maximum rotation).

---

## Summary Table

| Algebra | dim | D (generators) | L (structure) | B (topology) | Physics | Euler Type |
|---------|-----|----------------|---------------|--------------|---------|------------|
| so(2) | 1 | Rotation angle | None (abelian) | Closed | 2D rotation | **π** (angular) |
| so(3) | 3 | Jx, Jy, Jz | εᵢⱼₖ | Closed | Angular momentum | **π** (angular) |
| su(2) | 3 | Sx, Sy, Sz | εᵢⱼₖ | Closed | Spin | **π** (angular) |
| h₃ | 3 | Q, P, I | [Q,P]=iI | Open | Quantum mechanics | **e** (exponential) |
| so(3,1) | 6 | Mμν | Lorentz | Mixed | Special relativity | **Both** (e^(a+iθ)) |
| Poincaré | 10 | Pμ, Mμν | Complex | Mixed | Spacetime symmetry | **Both** (e^(a+iθ)) |

### Euler Type Classification

The **Euler type** indicates which compensation mechanism applies:

| Euler Type | Topology | Exponential Map | Physical Signature |
|------------|----------|-----------------|-------------------|
| **π (angular)** | Compact (closed B) | exp(iθX) periodic at 2π | Quantized, rotations |
| **e (exponential)** | Non-compact (open B) | exp(tX) unbounded | Continuous spectrum, boosts |
| **Both** | Mixed | exp((a+iθ)X) | Spirals, mixed symmetry |

**The connection to Euler's formula**: e^(iπ) + 1 = 0 unifies these:
- Compact groups use the **imaginary part**: e^(iθ) returns at 2π
- Non-compact groups use the **real part**: e^a extends to infinity
- Mixed groups use **both**: e^(a+iθ) spirals

---

## Key Patterns

### Abelian Algebras (L = empty)
- All generators commute
- Flat geometry
- Example: Translations (ℝⁿ)

### Compact Algebras (B = closed)
- Generators return to start (periodic)
- Quantized representations
- Example: Rotations, spin

### Non-compact Algebras (B = open)
- Generators extend infinitely
- Continuous spectrum
- Example: Boosts, translations

### The Link L Determines Everything
Given the structure constants fᵢⱼₖ, you can reconstruct:
- The algebra type
- The curvature (from Killing form)
- The representation theory
- The physics

This is why L is the most information-rich primitive.

---

## Verification

All examples verified in `scripts/verify_lie_bld.py`:

1. Structure constants match exactly for su(2)
2. Killing form relates to Fisher metric
3. Compact/non-compact matches closed/open boundary
4. Spin-½ representation (dim=2) matches extent

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md) — Full mapping
- [Why Lie Theory](../mathematics/lie-theory/why-lie-theory.md) — Accessible explanation
- [Constructive Lie](../mathematics/lie-theory/constructive-lie.md) — Alignment as homomorphism
- Verification: `scripts/verify_lie_bld.py`
