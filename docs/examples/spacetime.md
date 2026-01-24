---
status: VALIDATED
layer: 2
depends_on:
  - ../mathematics/lie-theory/lie-correspondence.md
  - ../mathematics/foundations/derivations/octonion-derivation.md
  - ../meta/epistemic-honesty.md
used_by:
  - ../applications/physics/electromagnetism.md
  - physics-traverser.md
  - README.md
---

# Spacetime (Three Primitives)

## Quick Summary (D≈7 Human Traversal)

**Spacetime in BLD in 7 steps:**

1. **Light cone = B** — Partitions intervals: timelike (ds²<0), lightlike (ds²=0), spacelike (ds²>0)
2. **Event horizon = B** — Partitions space: escapable (r>rₛ) vs trapped (r<rₛ)
3. **Metric = L** — Connects events: ds² = gμν dxμ dxν
4. **Curvature = L** — Parallel transport around loop reveals Riemann tensor
5. **4D = D** — Spacetime has 4 dimensions (t,x,y,z)
6. **D×L scaling** — Riemann has n²(n²-1)/12 = 20 components; metric has n(n+1)/2 = 10
7. **GR in BLD** — Reframing, not derivation; D×L scaling validated

| Component | BLD | Physics |
|-----------|-----|---------|
| Light cone | B | Causality |
| Metric | L | Interval |
| Spacetime | D₄ | 4 dimensions |

---

> **Status**: Validated (D×L scaling), Reframing (BLD structure), Exploratory (compensation)

> **Epistemic Note**: The "core" mapping of spacetime to (B, L, D) structure is **reframing** — it expresses well-known General Relativity in BLD language but does not derive or predict new physics. The D×L scaling (tensor components scaling with dimension) is validated as it reflects standard GR. The compensation section (wormholes) is speculative. See [Epistemic Honesty](../meta/epistemic-honesty.md).

> Spacetime is structure. Here is its BLD analysis.

---

## The Three Primitives

| Primitive | What it is |
|-----------|-----------|
| **boundary** | Partitions value space into regions of meaning |
| **link** | Connects one value to another |
| **dimension** | Axis of repetition (with extent) |

---

## Spacetime in Three Primitives

```
SPACETIME
│
├── boundary: light cone partitions interval → causality
│   │
│   │   ds² < 0 → timelike (causal, massive particles)
│   │   ds² = 0 → lightlike (causal, photons)
│   │   ds² > 0 → spacelike (acausal, no information)
│   │
│   └── (THE fundamental boundary of physics)
│
├── boundary: event horizon partitions space → escape
│   │
│   │   r > r_s → escapable (outside black hole)
│   │   r < r_s → trapped (inside black hole)
│   │
│   └── boundary: singularity partitions curvature → validity
│       │
│       │   R < ∞ → regular spacetime
│       │   R → ∞ → breakdown (GR fails)
│
├── boundary: metric signature partitions geometry → physics
│   │
│   │   (-,+,+,+) → Lorentzian (our universe)
│   │   (+,+,+,+) → Euclidean (imaginary time)
│
├── link: metric connects event → event
│   │
│   │   ds² = g_μν dx^μ dx^ν
│   │
│   └── link: geodesic connects point → point
│       │
│       │   δ∫ds = 0 (extremal path)
│       │
│       └── link: parallel transport connects vector → vector
│           │
│           │   ∇_μ V^ν = 0
│
├── link: curvature connects matter → geometry
│   │
│   │   R_μν - ½g_μν R = 8πG T_μν (Einstein equation)
│   │
│   └── (matter tells spacetime how to curve)
│
├── dimension[4]: spacetime coordinates
│   │            (extent = 4: t, x, y, z)
│   │
│   ├── dimension[3]: spatial
│   │                (extent = 3: x, y, z)
│   │
│   └── dimension[1]: temporal
│                    (extent = 1: t)
│
└── dimension[∞]: manifold points
                 (extent = continuous infinity)
```

---

## B/L/D Breakdown

### Boundaries (B)

| Boundary | Discriminator | Regions |
|----------|---------------|---------|
| Light cone | ds² = 0 | Timelike, Lightlike, Spacelike |
| Event horizon | r = r_s | Trapped, Escapable |
| Cosmological horizon | v = c | Observable, Unobservable |
| Singularity | R → ∞ | Regular, Breakdown |
| Signature | g_μν eigenvalues | Lorentzian, Euclidean |

### Links (L)

| Link | Formula | Properties |
|------|---------|------------|
| Metric | ds² = g_μν dx^μ dx^ν | Defines all intervals |
| Geodesic | δ∫ds = 0 | Shortest/longest path |
| Curvature | R_μν - ½g_μν R = 8πG T_μν | Matter ↔ geometry |
| Connection | Γ^λ_μν | Parallel transport |
| Causality | Within light cone | Information flow |

### Dimensions (D)

| Dimension | Extent | Description |
|-----------|--------|-------------|
| Spacetime | 4 | Full manifold coordinates |
| Spatial | 3 | Space directions |
| Temporal | 1 | Time direction |
| Events | ∞ | Points on manifold |

---

## Why n = 4? (Now Derived)

From the [Octonion Derivation](../mathematics/foundations/derivations/octonion-derivation.md), **n = 4 is now derived from BLD first principles**:

1. BLD observation requires bidirectional links → division property required
2. Hurwitz theorem: only ℝ, ℂ, ℍ, 𝕆 have division with norm
3. SU(3) color symmetry requires Aut ⊃ SU(3) → only octonions work
4. Fixing a reference octonion (for observation) breaks G₂ → SU(3)
5. Same symmetry breaking: so(9,1) → so(3,1) → **n = 4 derived**

This replaces the previous speculative arguments about "why 4D" with a rigorous derivation.

---

## Lie Theory: Lorentz Group

Spacetime symmetry is the **Lorentz group SO(3,1)**:

| BLD | Lorentz Group | Interpretation |
|-----|---------------|----------------|
| D | 6 generators | 3 rotations J_i + 3 boosts K_i |
| L | Structure constants | [J_i, J_j] = ε_ijk J_k |
| B | Non-compact topology | Boosts unbounded → c unreachable |

**The Lie algebra**:
```
Rotations:  [J_i, J_j] = ε_ijk J_k      (compact: periodic)
Boosts:     [K_i, K_j] = -ε_ijk J_k     (boost + boost = rotation!)
Mixed:      [J_i, K_j] = ε_ijk K_k      (rotation + boost = boost)
```

**Why c is unreachable**: The boost subgroup is non-compact. Unlike rotations (which cycle after 2π), boosts extend to infinity. The light cone is the asymptotic boundary of this non-compact structure.

**Proof (rapidity derivation)**:

The boost parameter (rapidity) φ relates to velocity by:
```
v = c · tanh(φ)
```

Since tanh(φ) ∈ (-1, 1) for all real φ:
- As φ → +∞, v → +c (but never reaches)
- As φ → -∞, v → -c (but never reaches)
- φ can take any real value (non-compact)

This is why the speed of light is a hard boundary (B): the non-compact topology of the boost group maps to the open interval (-c, +c).

**The Euler connection (both compensation mechanisms)**:

The Lorentz group demonstrates BOTH compensation mechanisms via the exponential map:

```
Rotation:    exp(iθ·J) = rotation by angle θ        [Angular: 2π closure]
Boost:       exp(φ·K) = boost with rapidity φ       [Exponential: unbounded]
Combined:    exp(φ·K + iθ·J) = general Lorentz      [Both mechanisms]
```

| Generator | Exponential Map | Compensation Type |
|-----------|-----------------|-------------------|
| J (rotation) | exp(iθJ) cycles at 2π | Angular: D×L = 2πB |
| K (boost) | exp(φK) → ∞ | Exponential: L^D accumulates |

The structure constant [K_i, K_j] = -ε_ijk J_k shows boosts compose to rotations — the exponential mechanism feeds into the angular mechanism. This is the Lie-algebraic source of Thomas precession.

**Rapidity IS a logarithm**:
```
tanh(φ) = v/c

φ = ½ ln[(1 + v/c)/(1 - v/c)] = arctanh(v/c)
```

Rapidity is the natural logarithm's presence in special relativity. Velocities don't add; rapidities do: φ_total = φ_1 + φ_2. This is exponential compensation: each boost multiplies, so logs add.

---

## D×L Scaling

**D multiplies L, not B**:

| Property | Scales with D? | Type | Formula |
|----------|----------------|------|---------|
| Metric components | Yes | L | D² = 16 |
| Christoffel symbols | Yes | L | D³ = 64 |
| Riemann tensor | Yes | L | D⁴ = 256 |
| Light cone angle | **No** | B | Always 45° |
| Causality structure | **No** | B | Always preserved |
| Signature | **No** | B | Always (-,+,+,+) |

**Proof (component counting)**:

For a D-dimensional manifold:
```
Metric g_μν:           D(D+1)/2 independent components
                       4D → 10 components (symmetric)

Christoffel Γ^λ_μν:    D × D(D+1)/2 = D²(D+1)/2 components
                       4D → 40 components

Riemann R^ρ_σμν:       D²(D²-1)/12 independent components
                       4D → 20 components (with symmetries)
                       Without symmetries: D⁴ = 256
```

**L scales polynomially with D. B (light cone, signature) is invariant.**

**Cross-validation**: String theory adds dimensions (D = 10, 11, 26) — L complexity explodes but light cone structure (B) is invariant.

---

## Compensation Principle

### Can L compensate for B?

**Theoretically yes (wormholes)**:
- Exotic matter (negative energy density) creates extreme curvature (L)
- Could connect causally disconnected regions
- L compensates for B (light cone)

**Practically no (energy conditions)**:
- Weak/strong energy conditions forbid exotic matter
- B (light cone) appears inviolable in classical GR

### Can B compensate for L?

**No**: You cannot create a shortcut by adding boundaries. Connecting distant regions requires curvature (L). Topology change requires geometry.

This matches the general BLD principle: L can (theoretically) compensate for B, B cannot compensate for L.

---

## Key Insights

### 1. Light Cone = Fundamental B

The light cone is physics' most fundamental boundary:
- Invariant under ALL Lorentz transformations
- Partitions causality absolutely
- Defines what "can affect" what

### 2. Metric = Fundamental L

The metric tensor is the fundamental link:
- Connects every event to every other event
- Encodes all gravitational information
- ds² = g_μν dx^μ dx^ν is the L formula for spacetime

### 3. Why 4D? (DERIVED)

From [Octonion Derivation](../mathematics/foundations/derivations/octonion-derivation.md):
- n = 4 follows from BLD observation requiring octonions
- Symmetry breaking: so(9,1) → so(3,1)
- **This is no longer speculative — it's derived from first principles**

---

## Mathematical Formalization

### The Metric as L

The spacetime interval is:
```
ds² = g_μν dx^μ dx^ν = -c²dt² + dx² + dy² + dz²  (flat)
```

The metric defines the L structure of spacetime — it specifies the connection strength between nearby events.

### Curvature as L×L Interaction

The Riemann tensor measures how L (parallel transport) fails to commute:
```
R^ρ_σμν V^σ = (∇_μ ∇_ν - ∇_ν ∇_μ) V^ρ
```

This is an L×L interaction term — links interacting with links.

### Einstein Equation as Alignment

```
R_μν - ½g_μν R = 8πG T_μν
```

**BLD interpretation**:
- Left side = geometry (L structure of spacetime)
- Right side = matter (L structure of energy-momentum)
- Equation = alignment condition

Spacetime curves until geometry aligns with matter distribution.

---

## Validation Status

| Claim | Evidence | Status |
|-------|----------|--------|
| D×L scaling (tensor components) | Standard GR, component counting | **Validated** |
| B invariance (light cone, signature) | Lorentz invariance theorem | **Validated** |
| SO(3,1) structure constants | Standard Lie theory [1] | **Validated** |
| Non-compactness → c boundary | Rapidity derivation above | **Validated** |
| n = 4 from BLD | Octonion derivation [2] | **Derived** |
| Wormholes as L compensation | Theoretical possibility only [3] | Exploratory |

**References**:
1. Weinberg, S. *The Quantum Theory of Fields*, Vol. 1, Ch. 2 — Lorentz group structure
2. [Octonion Derivation](../mathematics/foundations/derivations/octonion-derivation.md) — BLD → n=4
3. Morris, M. & Thorne, K. (1988) "Wormholes in spacetime" — Exotic matter requirements

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Octonion Derivation](../mathematics/foundations/derivations/octonion-derivation.md) — Why n = 4 (derived)
- [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md) — BLD = Lie theory
- [Thermodynamics](../mathematics/derived/thermodynamics.md) — Another physics domain
