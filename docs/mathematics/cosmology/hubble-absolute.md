---
status: DERIVED
layer: 2
depends_on:
  - reference-scale-derivation.md
  - scale-derivation.md
  - ../quantum/planck-derivation.md
  - hubble-tension.md
  - ../lie-theory/killing-form.md
  - ../foundations/constants.md
used_by:
  - ../../meta/proof-status.md
---

# H₀ Absolute Value from BLD Structure

**Status**: DERIVED — Hubble constant absolute value derived from BLD constants + v (itself derived). Zero free parameters. 0.4σ agreement with Planck 2018.

---

## Summary

**Hubble constant derived from BLD constants, zero free parameters:**

1. Key discovery: H₀ = v × λ⁶⁸ where 68 = B + L - Kn — [The Formula](#the-formula)
2. λ = 1/√20 (BLD-derived cascade parameter) — [Lambda Parameter](#lambda-parameter)
3. 68 = B + L - Kn = 56 + 20 - 8: cosmological cascade modes — [Why 68](#why-68--b--l---kn)
4. H₀(CMB) = v × λ⁶⁸ ≈ 67.2 km/s/Mpc (0.4σ) — [The Calculation](#the-calculation)
5. H₀(local) = 67.2 × 13/12 ≈ 72.8 km/s/Mpc (0.2σ) — [Local Prediction](#local-prediction)
6. Cosmological cascade vs Planck cascade — [Cascade Comparison](#cascade-comparison)

| Measurement | Predicted | Observed | Deviation |
|-------------|-----------|----------|-----------|
| H₀(CMB) | 67.2 km/s/Mpc | 67.4 ± 0.5 km/s/Mpc | **0.4σ** |
| H₀(local) | 72.8 km/s/Mpc | 73.0 ± 1.0 km/s/Mpc | **0.2σ** |

---

## The Problem

### H₀ was empirical input

The Hubble tension resolution (see [Hubble Tension](hubble-tension.md)) derives the *ratio* between CMB and local H₀:

```
H₀(local) = H₀(CMB) × (1 + K/(n+L)) = H₀(CMB) × 13/12
```

But this required the CMB value H₀(CMB) = 67.4 km/s/Mpc as empirical input. The question remained: can BLD derive the absolute value?

### The challenge

H₀ has dimensions of inverse time (km/s/Mpc). BLD derives dimensionless ratios. To get a dimensionful answer, BLD needs to connect its structural constants to an absolute energy scale — which it does through v = 246.22 GeV (the reference scale, itself derived as the fixed point of self-observation; see [Reference Scale Derivation](reference-scale-derivation.md)).

---

## BLD Resolution

### The Formula

```
H₀(CMB) = v × λ^(B + L - Kn)
```

Where:
- **v** = 246.22 GeV (reference scale, derived from BLD)
- **λ** = 1/√L = 1/√20 (cascade parameter, derived from BLD)
- **B + L - Kn** = 56 + 20 - 8 = 68 (cosmological cascade exponent)

### Lambda Parameter

```
λ = 1/√L = 1/√20 ≈ 0.2236

Equivalently: λ² = K²/(n×L) = 4/80 = 1/20
```

This is the same cascade parameter that connects v to M_P:

```
v → M_P:  M_P = v × λ⁻²⁶ × corrections    (Planck cascade)
v → H₀:  H₀ = v × λ⁶⁸                      (cosmological cascade)
```

### Why 68 = B + L - Kn

The exponent counts **net cosmological cascade modes**:

| Component | Value | Meaning |
|-----------|-------|---------|
| B | 56 | Boundary modes (topological structure) |
| L | 20 | Link modes (geometric structure) |
| B + L | 76 | Total structural modes |
| K × n | 2 × 4 = 8 | Observation cost per dimension × dimensions |
| **B + L - Kn** | **68** | Net modes available for cosmological cascade |

**Interpretation**: The cosmological cascade from v down to H₀ uses ALL structural modes (both B and L), but pays observation cost K for each of the n spacetime dimensions.

Compare with the particle cascade (v up to M_P):
- Planck cascade uses only **forward boundary modes**: n_c = B/2 - K = 28 - 2 = 26
- Cosmological cascade uses **all structural modes**: B + L - Kn = 76 - 8 = 68

This makes physical sense:
- **Particle physics** (microscopic): structure flows "upward" using forward modes only
- **Cosmology** (macroscopic): structure flows "downward" using the full structural inventory

### The Calculation

Step by step:

```
1. v = 246.22 GeV                       (BLD-derived reference scale)
2. λ⁶⁸ = (1/√20)⁶⁸ = 20⁻³⁴             (cascade suppression)
3. 20³⁴ = 1.718 × 10⁴⁴                  (exact: 20³⁴)
4. λ⁶⁸ = 5.821 × 10⁻⁴⁵

5. H₀ = 246.22 × 5.821 × 10⁻⁴⁵
       = 1.433 × 10⁻⁴² GeV

Converting to s⁻¹:
6. H₀ = 1.433 × 10⁻⁴² / (6.582 × 10⁻²⁵ GeV·s)
       = 2.178 × 10⁻¹⁸ s⁻¹

Converting to km/s/Mpc:
7. H₀ = 2.178 × 10⁻¹⁸ × 3.086 × 10¹⁹ km/Mpc
       = 67.2 km/s/Mpc
```

Observed: H₀(CMB) = 67.4 ± 0.5 km/s/Mpc

**Agreement: 0.4σ**

### Local Prediction

Combining with the Hubble tension resolution:

```
H₀(local) = H₀(CMB,derived) × (1 + K/(n+L))
           = 67.2 × 13/12
           = 72.8 km/s/Mpc
```

Observed: H₀(local) = 73.0 ± 1.0 km/s/Mpc

**Agreement: 0.2σ**

---

## Cascade Comparison

### Two Directions from v

| Cascade | Direction | Exponent | Formula | Uses |
|---------|-----------|----------|---------|------|
| **Planck** (particle) | v → M_P (upward) | 26 = B/2 - K | Forward boundary minus observation | Forward modes only |
| **Cosmological** | v → H₀ (downward) | 68 = B + L - Kn | Total structure minus dimensional observation | ALL modes |

### Structural Pattern

Both cascades follow the same pattern: **relevant modes minus observation cost**.

| Cascade | Relevant Modes | Observation Cost | Net |
|---------|---------------|-----------------|-----|
| Planck | B/2 = 28 (forward boundary) | K = 2 | 26 |
| Cosmological | B + L = 76 (all structure) | Kn = 8 | 68 |

The Planck cascade pays K = 2 once (the Killing form).
The cosmological cascade pays K for each of n = 4 dimensions: K × n = 8.

### v as the Pivot

v sits between M_P and H₀:

```
H₀ ←── λ⁶⁸ ──→ v ←── λ⁻²⁶ ──→ M_P

H₀:   1.43 × 10⁻⁴² GeV
v:     2.46 × 10²  GeV
M_P:   1.22 × 10¹⁹ GeV
```

v is the **fixed point of self-observation** — the scale where observer capacity equals modes minus K. It is the natural pivot between microscopic (upward to M_P) and macroscopic (downward to H₀).

---

## Verification

### Numerical Match

| Quantity | Predicted | Observed | Deviation |
|----------|-----------|----------|-----------|
| H₀(CMB) | 67.2 km/s/Mpc | 67.4 ± 0.5 km/s/Mpc | **0.4σ** |
| H₀(local) | 72.8 km/s/Mpc | 73.0 ± 1.0 km/s/Mpc | **0.2σ** |

### Structural Consistency

The cascade exponent 68 = B + L - Kn uses constants that appear throughout BLD:

| Constant | Value | Other Uses |
|----------|-------|-----------|
| B | 56 | α⁻¹, Higgs mass, Planck mass, baryon asymmetry |
| L | 20 | α⁻¹, dark matter, Planck mass, all predictions |
| K | 2 | Born rule, entropy, Hubble tension, all corrections |
| n | 4 | All BLD predictions |

### Age of Universe Cross-Check

From the Friedmann equation with BLD energy densities (Ω_m = 8/25, Ω_Λ = 17/25):

```
t₀ × H₀ = ∫₀^∞ dz / ((1+z) × √(Ω_m(1+z)³ + Ω_Λ))
```

With H₀ = 67.2 km/s/Mpc and the BLD energy fractions, this gives t₀ ≈ 13.8 Gyr, matching the observed age of the universe.

---

## Implications

### H₀ is Derived, Not Empirical

Before this derivation:
- v was derived (fixed point of self-observation, 0.00014% error)
- M_P was derived (v × λ⁻²⁶ × corrections, 0.002% error)
- Energy fractions were derived (5%, 27%, 68%, 0% error)
- H₀ tension was resolved (13/12, 0% error)
- **But H₀(CMB) = 67.4 was empirical input**

Now:
- **H₀(CMB) = v × λ⁶⁸ = 67.2 km/s/Mpc** (0.4σ, zero free parameters)
- **H₀(local) = 67.2 × 13/12 = 72.8 km/s/Mpc** (0.2σ)

The entire cosmological distance ladder is now derived from BLD constants.

### Complete Scale Chain

```
BLD constants (B=56, L=20, n=4, K=2, S=13)
    ↓
v = 246.22 GeV           (fixed point, 0.00014%)
    ↓ (λ⁻²⁶)
M_P = 1.221 × 10¹⁹ GeV  (Planck cascade, 0.002%)
    ↓ (v × λ⁶⁸)
H₀ = 67.2 km/s/Mpc       (cosmological cascade, 0.4σ)
    ↓ (× 13/12)
H₀(local) = 72.8 km/s/Mpc (observer correction, 0.2σ)
```

From five integers to the expansion rate of the universe. Zero free parameters.

---

## References

### External Sources
- [Planck 2018 Results (arXiv:1807.06209)](https://arxiv.org/abs/1807.06209) — H₀ = 67.4 ± 0.5 km/s/Mpc
- [SH0ES 2022 (arXiv:2112.04510)](https://arxiv.org/abs/2112.04510) — H₀ = 73.0 ± 1.0 km/s/Mpc

### Internal BLD References
- [Reference Scale Derivation](reference-scale-derivation.md) — v = 246.22 GeV derived
- [Planck Derivation](../quantum/planck-derivation.md) — M_P = v × λ⁻²⁶ × corrections
- [Hubble Tension](hubble-tension.md) — H₀(local)/H₀(CMB) = 13/12
- [Scale Derivation](scale-derivation.md) — Full cascade chain
- [Killing Form](../lie-theory/killing-form.md) — K = 2 derivation
- [Observer Correction](observer-correction.md) — K/X framework
- [Constants](../foundations/constants.md) — B, L, n, K, S definitions
