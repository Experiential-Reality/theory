---
status: DERIVED
layer: 0
depends_on:
  - definitions/bld-calculus.md
  - proofs/irreducibility-proof.md
  - ../lie-theory/killing-form.md
used_by:
  - derivations/force-structure.md
  - ../particle-physics/fine-structure-consistency.md
  - ../particle-physics/higgs-self-coupling.md
  - ../cosmology/observer-correction.md
---

# Observation Cost: The K/X Principle

## Abstract

Every measurement includes a cost for traversing hidden experimental structure. This cost is K/X, where K = 2 (Killing form, bidirectional observation) and X is the hidden structure the detector couples to. This document formalizes the observation cost principle and derives X for each fundamental force.

---

## 1. The Observation Cost Theorem

**Theorem 1 (Observation Cost).** Every physical measurement satisfies:

```
Observed = Structural + K/X
```

Where:
- **Structural** = value from BLD axioms (visible structure)
- **K = 2** = Killing form (bidirectional observation cost)
- **X** = hidden experimental structure the detector couples to

*Proof.* From [Irreducibility Proof](proofs/irreducibility-proof.md): B, L, D cannot be expressed in terms of each other. Any measurement requires all three. The detector has structure (it couples to specific BLD components). This structure must be traversed to make the measurement. The traversal cost is K/X, where K = 2 from bidirectional observation (query + response). See [Killing Form](../lie-theory/killing-form.md). ∎

**Remark.** The correction K/X is not a fitting parameter. X is determined by detection physics — what the apparatus couples to.

---

## 2. Hidden Structure by Force

For each force, X is determined by what the detector couples to:

| Force | Detector Couples To | X (Hidden Structure) | K/X | Sign |
|-------|--------------------|--------------------|-----|------|
| **EM** | Boundaries (photon exchange) | B = 56 | 2/56 = 0.036 | + |
| **Weak** | Full structure (Z pole) | n×L×B = 4480 | 2/4480 = 0.00045 | + |
| **Strong** | Geometry (jets) | n+L = 24 | 2/24 = 0.083 | − |
| **Gravity** | Self (observer IS geometry) | n×L−K = 78 | 79/78 | × |

### 2.1 Electromagnetic (α⁻¹)

**EM detectors couple to B (boundary).**

Photon exchange creates/destroys partitions between states. The photon crosses boundaries. Therefore X = B = 56.

```
Structural: n×L + B + 1 = 137
Correction: +K/B = +2/56 = +0.036
Observed:   137.036
```

### 2.2 Weak (sin²θ_W)

**Z pole measurements couple to full structure (n×L×B).**

The Z boson couples to all fermions. At the Z pole, the measurement traverses geometric structure (n×L) and boundary structure (B). Therefore X = n×L×B = 4480.

```
Structural: 3/S = 0.2308
Correction: +K/(n×L×B) = +2/4480 = +0.00045
Observed:   0.23121
```

### 2.3 Strong (α_s⁻¹)

**Hadronic detectors couple to geometry (n+L).**

Jets traverse spacetime (n = 4) and Riemann curvature (L = 20). Gluons are confined to geometry. Therefore X = n+L = 24.

```
Structural: α⁻¹/n² = 8.56
Correction: −K/(n+L) = −2/24 = −0.083
Observed:   8.48
```

### 2.4 Gravity (M_P)

**The observer IS the geometry (self-reference).**

For gravity, the observer is embedded in what it measures. The hidden structure is geometry minus the observer's own observation cost: X = n×L−K = 78.

```
Correction factor: (n×L−1)/(n×L−K) = 79/78 = 1.01282
```

This is multiplicative (ratio) rather than additive because of self-reference.

---

## 3. The Sign Rule

**Definition (Detection Completeness).** The sign of K/X indicates traversal completeness:

| Sign | Meaning | Condition |
|------|---------|-----------|
| **+** | Incomplete traversal | Something escapes detection |
| **−** | Complete traversal | Everything is detected |

**Examples:**
- EM (+): Virtual photon not directly observed, only its effect
- Weak (+): Neutrinos escape (contaminate Z measurements)
- Strong (−): Jets fully detected, nothing escapes

See [Detection Structure](machine/detection-structure.md) for the formal T ∩ S criterion.

---

## 4. Higher-Order Corrections

For precision beyond first-order:

| Order | Form | When It Appears |
|-------|------|-----------------|
| First | K/X | Direct measurement |
| Second | K/X² or K/(X₁×X₂) | Two structures traversed |
| Accumulated | e²×... | Continuous limit effects |

**Example (α⁻¹ full formula):**
```
α⁻¹ = n×L + B + 1 + K/B + spatial − e²×(2B+n+K+2)/((2B+n+K+1)×(n×L)²×B²)
    = 137.035999177
```

Each term represents a deeper layer of hidden structure.

---

## 5. The Three-Layer Decomposition

**Theorem 2 (Three Layers).** Every measurement decomposes as:

```
Observed = Structural + K/X(experiment) + K/X(universe)
```

| Layer | Source | Example |
|-------|--------|---------|
| Structural | BLD axioms | n×L + B + 1 = 137 |
| K/X(experiment) | Detector's hidden structure | K/B = 2/56 |
| K/X(universe) | Universal machine cost | ~0.002% residual |

**Remark.** The small residuals (~0.002%) in predictions are K/X(universe) — the cost of the universe computing itself. See [Universal Machine](machine/universal-machine.md).

---

## 6. Summary

| Quantity | Structural | X | Correction | Observed | Residual |
|----------|------------|---|------------|----------|----------|
| α⁻¹ | 137 | B = 56 | +K/B | 137.036 | 0.0 ppt |
| sin²θ_W | 0.2308 | n×L×B = 4480 | +K/(n×L×B) | 0.23121 | 0.002% |
| α_s⁻¹ | 8.56 | n+L = 24 | −K/(n+L) | 8.48 | 0.02% |
| M_P | derived | n×L−K = 78 | ×79/78 | 1.22×10¹⁹ GeV | 0.002% |

---

## References

- [BLD Calculus](definitions/bld-calculus.md) — Foundational definitions
- [Irreducibility Proof](proofs/irreducibility-proof.md) — Why observation has cost
- [Killing Form](../lie-theory/killing-form.md) — K = 2 derivation
- [Detection Structure](machine/detection-structure.md) — T ∩ S formalism for sign rule
- [Force Structure](derivations/force-structure.md) — Complete force derivations
- [Universal Machine](machine/universal-machine.md) — K/X(universe) and residuals
