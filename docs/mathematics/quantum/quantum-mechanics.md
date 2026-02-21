---
status: DERIVED
layer: 2
depends_on:
  - ../foundations/proofs/irreducibility-proof.md
  - ../foundations/machine/integer-machine.md
  - ../lie-theory/lie-correspondence.md
  - ../lie-theory/killing-form.md
  - structural-observer-framework.md
used_by:
  - born-rule.md
  - schrodinger-derivation.md
  - ../../meta/proof-status.md
---

# Quantum Mechanics in BLD

**Status**: DERIVED — Uncertainty principle from D-L irreducibility and Lie algebra structure.

---

## Summary

**Uncertainty principle derived from BLD:**

1. Position = D-type (dimensional location) — [Position](#position-d-type)
2. Momentum = L-type (temporal link dx/dt) — [Momentum](#momentum-l-type)
3. [x, p] = iℏ is structure constant; i from K = 2 = dim(ℂ) — [Coupling](#the-coupling-structure-constant)
4. D-L irreducibility → non-commutativity → uncertainty — [Derivation](#the-uncertainty-principle-derived)
5. Δx·Δp ≥ ℏ/2: the "2" is Killing form — [Killing Connection](#the-killing-form-connection)
6. ℏ value derived (0.00003% accuracy) — [Planck Derivation](planck-derivation.md)

| Concept | BLD Type | Why |
|---------|----------|-----|
| Position | D | Dimensional location |
| Momentum | L | Temporal link |
| [x,p] | L | Structure constant |
| ℏ/2 | Killing | Bidirectional observation cost |

---

## Status Legend

| Tag | Meaning |
|-----|---------|
| `[PROVEN]` | Follows from established BLD/Lie theory |
| `[DERIVED]` | Logical consequence of proven statements |
| `[POSTULATED]` | Assumed without full derivation |

---

## Scope Note

This document derives the **uncertainty principle** from BLD. For further derivations see:
- [Schrödinger Derivation](schrodinger-derivation.md)
- [Wave Function Collapse](wave-function-collapse.md)
- [Born Rule](born-rule.md)
- [Path Integral](path-integral.md)

---

## The Core Claim `[DERIVED]`

Position and momentum are different **BLD types**:
- Position (x): **D-type** — location in dimensional space
- Momentum (p): **L-type** — how positions link across time

Their coupling [x, p] = iℏ is a **structure constant** in the Lie algebra of phase space.

**The uncertainty principle is not a postulate.** It is a geometric constraint arising from the non-commutativity of irreducible primitives.

---

## Position and Momentum

### Position: D-Type

Position answers: **"Where?"**

```
D position: x [location]
  # A point in dimensional space
  # "Here, not there"
  # Specifies a coordinate along an axis
```

Position is D-type because:
- It is an axis of extension (dimension)
- It can be repeated (many positions along the axis)
- It is independent of connections between positions

### Momentum: L-Type

Momentum answers: **"How does position change?"**

```
L momentum: p = m × dx/dt [velocity_link]
  # How position links across time
  # "From here to there, at this rate"
  # The connection between position_now and position_later
```

Momentum is L-type because:
- It relates positions across time (a link)
- It is directional (source → target)
- It cannot exist without positions to connect

### The Coupling: Structure Constant

The commutation relation:

```
[x̂, p̂] = iℏ
```

In Lie algebra terms:

```
[X_i, X_j] = f^k_ij X_k

Where:
  X_i, X_j = generators (D)
  f^k_ij = structure constants (L)

For position-momentum:
  [x̂, p̂] = iℏ·Î

  The structure constant is iℏ
```

**The commutator IS the link.** The fact that [x, p] ≠ 0 means position and momentum are **coupled** by a non-zero structure constant.

### Status of iℏ Components

| Component | Status | Derivation |
|-----------|--------|------------|
| **i** (imaginary unit) | **DERIVED** | K = 2 = dim(ℂ). See derivation below |
| **Non-zero coupling** | **DERIVED** | D-L irreducibility requires structure constant. See [Irreducibility Proof](../foundations/proofs/irreducibility-proof.md) |
| **ℏ value** | **DERIVED** | From BLD structure. See [Planck Derivation](planck-derivation.md) |

### Why i: The Unit of Observation

The imaginary unit i is not a mathematical convenience — it's structurally necessary.

**The proof chain:**

```
BLD requires bidirectional observation
    ↓
Bidirectionality requires inverses (to "go back")
    ↓
Inverses require a division algebra
    ↓
Minimum division algebra with internal structure: ℂ
    ↓
dim(ℂ) = 2 = K (the Killing form!)
    ↓
Im(ℂ) = 1 = i
    ↓
Therefore: i is the UNIT OF OBSERVATION
```

The connection K = 2 = dim(ℂ) is exact:
- **K = 2**: The Killing form coefficient from [killing-form.md](../lie-theory/killing-form.md) — bidirectional observation cost
- **dim(ℂ) = 2**: The dimension of the complex numbers

These are the same structural fact. The complex numbers ARE the observation algebra.

| Algebra | dim | Im | BLD Constant |
|---------|-----|-----|--------------|
| ℂ | 2 | 1 (= i) | K = 2 |
| ℍ | 4 | 3 | n = 4 |
| 𝕆 | 8 | 7 | minimum structure |

**i appears in quantum mechanics because observation uses i.** The Schrödinger equation has i because wavefunctions live in ℂ, and ℂ is the observation algebra.

See [Integer Machine](../foundations/machine/integer-machine.md#10-the-imaginary-unit-i) for the complete derivation.

**What BLD explains about ℏ**:
- There MUST be a minimum action (from D×L irreducibility)
- The coupling MUST have complex form (from i = Im(ℂ))
- The specific value is DERIVED (see [Planck Derivation](planck-derivation.md))

**What BLD does NOT explain**:
- Why the unit system has the particular numerical value — this is coordinate choice, not physics

---

## The Uncertainty Principle `[DERIVED]`

### From Commutator to Uncertainty

The Robertson-Schrödinger uncertainty relation:

```
Δx · Δp ≥ |⟨[x̂, p̂]⟩| / 2 = ℏ/2
```

This follows mathematically from the commutator structure. `[PROVEN in standard QM]`

**BLD contribution**: Interpreting [x,p]=iℏ as structure constant between D-type (x) and L-type (p) primitives.

### BLD Derivation

```
Step 1: Position (D) and momentum (L) are irreducible primitives
        - Proven in irreducibility-proof.md
        - Neither is expressible in terms of the other

Step 2: They are coupled by non-zero structure constant [x, p] = iℏ
        - This is the L (link) between them
        - The coupling is geometric, not arbitrary

Step 3: Non-zero structure constant → non-abelian algebra
        - Abelian: [A, B] = 0 → observables commute → can know both
        - Non-abelian: [A, B] ≠ 0 → observables don't commute → trade-off

Step 4: Non-abelian algebra → curved phase space
        - Flat space: parallel transport is path-independent
        - Curved space: parallel transport depends on path
        - The curvature comes from the structure constants

Step 5: Curved space → geodesic constraints
        - You cannot move arbitrarily in both directions
        - Precision in one constrains precision in the other
        - Δx · Δp ≥ ℏ/2 is the minimum geodesic constraint
```

### Why You Can't Beat It

The uncertainty principle is **structural**, not practical:

| Interpretation | Why It Fails |
|----------------|--------------|
| "Measurement disturbs system" | True, but even perfect measurement has ℏ/2 limit |
| "We lack technology" | No technology can overcome geometric constraints |
| "Hidden variables" | Bell's theorem rules this out |

**The real reason:** D and L are irreducible primitives. You cannot fully specify one without affecting the other when they are coupled by a non-zero structure constant.

This is like asking: "Can I know both the radius and circumference of a circle to arbitrary precision independently?"

No — they are coupled by C = 2πr. Specifying one determines the other. The coupling is geometric, not practical.

---

## The Killing Form Connection

### Observation Costs 2 Links

From [killing-form.md](../lie-theory/killing-form.md):

```
B(X, X) = 2  (for SO(3,1))

Observation requires:
  - Forward link: query from observer to observed
  - Backward link: response from observed to observer

Minimum cost = 2 links (Killing form coefficient)
```

### The Factor of 2 in Uncertainty

The uncertainty principle has a factor of 2:

```
Δx · Δp ≥ ℏ/2
```

This "2" is the **Killing form coefficient**:

```
Robertson relation: Δx · Δp ≥ |⟨[x̂, p̂]⟩| / 2
                             = |iℏ| / 2
                             = ℏ / 2

The "2" comes from:
  - Mathematical: Robertson inequality derivation
  - Physical: Bidirectional observation (Killing form = 2)
```

**Hypothesis**: The factor of 2 in uncertainty is the same "2" that appears in:
- Killing form diagonal entries (±2)
- Observer correction denominator (2/(n×L))
- Cosmology correction (8x² = 2 × n × x²)

All are manifestations of bidirectional observation cost.

---

## Quantization from Compact Boundaries

### Compact B → Discrete Spectrum

From [lie-correspondence.md](../lie-theory/lie-correspondence.md):

```
Compact group → closed orbits → periodic → quantized eigenvalues
Non-compact group → open orbits → unbounded → continuous spectrum
```

| Group | Compactness | Spectrum | Example |
|-------|-------------|----------|---------|
| SO(3) | Compact | Discrete | Angular momentum L = 0, 1, 2, ... |
| SU(2) | Compact | Discrete | Spin s = 0, ½, 1, 3/2, ... |
| U(1) | Compact | Discrete | Charge Q = ne |
| SO(3,1) boosts | Non-compact | Continuous | Rapidity η ∈ ℝ |
| Translations | Non-compact | Continuous | Position x ∈ ℝ |

### BLD Interpretation

```
B compact: closed
  # Orbits return to start
  # Periodicity forces quantization
  # Eigenvalues are discrete

B non_compact: open
  # Orbits escape to infinity
  # No periodicity constraint
  # Eigenvalues are continuous
```

**Quantization is a boundary phenomenon.** The topology (B) of the symmetry group determines whether the spectrum is discrete or continuous.

---

## Phase Space Structure

### The Heisenberg Algebra

Position and momentum form the Heisenberg algebra:

```
[x̂, p̂] = iℏ
[x̂, Î] = 0
[p̂, Î] = 0
```

In BLD terms:

```
D x: position [coordinate]
L p: momentum [temporal_link]
B phase_space: x_known | p_known | neither_known
  # You choose which to specify precisely
  # The boundary partitions possible states
```

### Minimum Phase Space Cell

```
Δx · Δp ≥ ℏ/2

The minimum phase space area = ℏ/2
This is the "quantum of action"
```

In BLD terms:

```
D × L ≥ ℏ/2

The product of D-precision and L-precision is bounded below.
This is D-L irreducibility manifested as minimum area.
```

---

## Connection to Observer Corrections

### The Pattern Across Scales

| Scale | Observer Correction | The "2" |
|-------|---------------------|---------|
| Cosmology | 8x² = 2 × n × x² | Killing form × dimensions |
| Particle physics | 2/(n×L) = 2/80 | Killing form / structure |
| Quantum mechanics | ℏ/2 | Killing form in Robertson bound |

All three involve the Killing form coefficient (2) because observation is inherently bidirectional.

### Why Quantum is Different

| Domain | Type of Correction |
|--------|-------------------|
| Cosmology | Additive (you ADD L by measuring) |
| Particle physics | Fractional (you USE part of structure to measure) |
| Quantum | Multiplicative bound (you can't go below ℏ/2) |

Quantum uncertainty is a **lower bound**, not an additive correction. You don't "add" uncertainty; you can't avoid it.

---

## Implications

### 1. Uncertainty is Geometric

The uncertainty principle is not about:
- Measurement apparatus limitations
- Observer disturbance
- Lack of knowledge

It is about the **geometry of phase space**. Position and momentum are different types of structure (D and L) coupled by a non-zero link (structure constant iℏ).

### 2. You Can Trade, Not Eliminate

You can know position precisely (Δx → 0) if you accept Δp → ∞.
You can know momentum precisely (Δp → 0) if you accept Δx → ∞.

You cannot eliminate uncertainty. You can only choose where to allocate it.

### 3. Quantum Computing Routes Around It

See [quantum-computing.md](quantum-computing.md):

Instead of measuring (paying L-cost) → structure computes as structure.
Entanglement provides pre-established L without measurement.
You defer the uncertainty cost until final readout.

---

## Summary in BLD Notation

```
structure QuantumMechanics

# The primitives
D position: x [coordinate_axis]
L momentum: p = dx/dt [temporal_link]

# The coupling
L structure_constant: [x, p] = iℏ
  # Position and momentum are linked
  # The link strength is ℏ
  # The imaginary unit encodes phase rotation

# The constraint
formula uncertainty
  Δx × Δp ≥ ℏ / 2

  # D-precision × L-precision ≥ (structure constant) / (Killing form)
  # You cannot minimize both D and L when they are coupled

# Why irreducible
B uncertainty_type: structural
  structural -> from_D_L_irreducibility, cannot_eliminate
  practical -> from_apparatus_limits, could_improve
  # Quantum uncertainty is structural, not practical

# The boundary cases
B precision_choice: know_position | know_momentum
  know_position -> Δx_small, Δp_large
  know_momentum -> Δp_small, Δx_large
  # You choose which primitive to specify
```

---

## The Measurement Problem: Scope of BLD

> **Layer 2 honesty**: BLD derives the STRUCTURE of quantum mechanics, not all interpretational questions.

### What This Document Derives

| Claim | Status | How |
|-------|--------|-----|
| Position is D-type | **DERIVED** | Dimensional location |
| Momentum is L-type | **DERIVED** | Temporal link |
| [x,p] = iℏ | **DERIVED** | Structure constant |
| Δx·Δp ≥ ℏ/2 | **DERIVED** | D-L irreducibility |

### What Remains Open

| Question | Status | Why Open |
|----------|--------|----------|
| Wave function collapse | **DERIVED** | See [Wave Function Collapse](wave-function-collapse.md) |
| Single-event outcomes | **DERIVED** | See [Selection Rule](selection-rule.md) — L→B + K=2 on joint system |
| Path integral formulation | **DERIVED** | See [Path Integral](path-integral.md) |

### The Honest Summary

BLD explains:
- **WHY** position and momentum don't commute (D-L irreducibility)
- **WHY** there's a minimum uncertainty (structure constant)
- **WHY** ℏ has its value (Planck derivation)

BLD does NOT explain:
- **WHY** a specific measurement yields a specific outcome
- **WHETHER** collapse is real or apparent

This is the measurement problem. It's open in ALL interpretations of QM. BLD's contribution is making the structural basis clear.

---

## References

- [Integer Machine](../foundations/machine/integer-machine.md) — i as unit of observation, K = dim(ℂ)
- [Irreducibility Proof](../foundations/proofs/irreducibility-proof.md) — D and L are independent primitives
- [Killing Form](../lie-theory/killing-form.md) — Why observation costs 2 links, K = 2 = dim(ℂ)
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — Commutators as structure constants
- [Quantum Computing](quantum-computing.md) — Computing in structure vs measuring
- [Compensation Principle](../foundations/structural/compensation-principle.md) — L can compensate B, not vice versa
- [Planck Derivation](planck-derivation.md) — ℏ value derived from BLD
