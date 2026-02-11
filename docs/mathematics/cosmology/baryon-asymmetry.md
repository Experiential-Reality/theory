---
status: DERIVED
layer: 2
depends_on:
  - genesis-function.md
  - ../foundations/machine/universal-machine.md
  - ../lie-theory/killing-form.md
  - ../quantum/chirality-cpt.md
  - ../foundations/constants.md
used_by:
  - ../../meta/proof-status.md
---

# Baryon Asymmetry from BLD Structure

**Status**: DERIVED — Baryon-to-photon ratio derived from BLD constants. Zero free parameters. 1.0σ agreement with Planck 2018.

---

## Summary

**The baryon-to-photon ratio from BLD structure, zero free parameters:**

1. Formula: η = (K/B) × (1/L)⁶ × S/(S-1) — [The Formula](#the-formula)
2. K/B = 2/56: observer-to-boundary ratio (standard BLD correction) — [K/B Component](#kb-observer-to-boundary-ratio)
3. (1/L)⁶ where 6 = n(n-1)/2 = dim(SO(3,1)): Lorentz group dilution — [Lorentz Dilution](#lorentz-dilution-1l6)
4. S/(S-1) = 13/12: generation structure correction — [Generation Correction](#generation-correction-ss-1)
5. Genesis mechanism: traverse(-B,B) creates ±B partitions — [Genesis Mechanism](#genesis-mechanism)
6. Sakharov conditions from BLD — [Sakharov Conditions](#sakharov-conditions-from-bld)

### Exact Rational Fraction

| Quantity | BLD Formula | Exact Fraction | Decimal | Planck 2018 |
|----------|-------------|----------------|---------|-------------|
| η (baryon-to-photon) | (K/B)(1/L)⁶ × S/(S-1) | **13/21,504,000,000** | 6.045 × 10⁻¹⁰ | 6.104 ± 0.058 × 10⁻¹⁰ |

Agreement: **1.0σ**. Five integers (B=56, L=20, n=4, K=2, S=13), zero free parameters.

---

## The Problem

### The observed asymmetry

The visible universe is made almost entirely of matter, not antimatter. The baryon-to-photon ratio quantifies this:

```
η = n_b / n_γ = (6.104 ± 0.058) × 10⁻¹⁰
```

For every billion photons, there are about 6 baryons and essentially zero antibaryons. Standard cosmology does not derive this number — it is measured from Big Bang nucleosynthesis yields and CMB acoustic peaks, then used as a free parameter in ΛCDM.

### Sakharov conditions

Andrei Sakharov (1967) showed baryogenesis requires three conditions:

1. **Baryon number violation** — processes that change baryon number
2. **C and CP violation** — asymmetry between particle and antiparticle processes
3. **Departure from thermal equilibrium** — out-of-equilibrium dynamics to prevent washout

The Standard Model satisfies all three (sphaleron processes, CKM phase, electroweak phase transition), but the resulting asymmetry is too small by many orders of magnitude. No standard mechanism produces η ~ 10⁻¹⁰.

---

## BLD Resolution

### The Formula

```
η = (K/B) × (1/L)⁶ × S/(S-1)
  = (2/56) × (1/20)⁶ × (13/12)
  = (2 × 13) / (56 × 64,000,000 × 12)
  = 26 / 43,008,000,000
  = 13 / 21,504,000,000
  ≈ 6.045 × 10⁻¹⁰
```

Observed (Planck 2018): η = (6.104 ± 0.058) × 10⁻¹⁰

**Agreement: 1.0σ**

### K/B: Observer-to-Boundary Ratio

The factor K/B = 2/56 is the **standard BLD observer correction at the boundary scale**. It appears throughout the theory:

| Context | K/B Role |
|---------|----------|
| α⁻¹ = nL + B + 1 + **K/B** + ... | Boundary quantum correction |
| m_H = (v/2)(1 + 1/B)(1 - 1/(BL)) | Higgs mass correction |
| Observer correction framework | Observer sees fraction K/B of boundary |

In baryogenesis: the observer (made of +B matter) can only "see" K/B of the total boundary structure. This is the per-mode asymmetry — how much of the ±B partition is accessible from one side.

### Lorentz Dilution: (1/L)⁶

The exponent **6 = n(n-1)/2 = dim(SO(3,1))** is the dimension of the Lorentz group.

```
n = 4  (spacetime dimensions)
n(n-1)/2 = 4 × 3 / 2 = 6  (Lorentz group generators)
```

The six Lorentz generators are: 3 rotations + 3 boosts. Baryogenesis occurs during the electroweak phase transition, where Lorentz symmetry is the relevant spacetime symmetry. Each Lorentz degree of freedom dilutes the asymmetry by a factor of 1/L = 1/20:

```
Per Lorentz DOF: 1/L (Riemann structure per dimension)
Total Lorentz dilution: (1/L)⁶ = 1/20⁶ = 1/64,000,000
```

**Why 1/L per Lorentz DOF?** The asymmetry must propagate through spacetime structure. Each Lorentz generator connects to L = 20 Riemann components. The fraction of structure carrying the asymmetry per generator is 1/L.

### Generation Correction: S/(S-1)

The factor S/(S-1) = 13/12 is a **generation structure correction**. It appears throughout BLD:

| Context | S/(S-1) Role |
|---------|--------------|
| Hubble tension | H₀(local) = H₀(CMB) × (1 + 1/12) = H₀(CMB) × **13/12** |
| Baryon asymmetry | η includes factor S/(S-1) = **13/12** |

```
S = (B - n)/n = (56 - 4)/4 = 13    (structural intervals)
S - 1 = 12                          (observable intervals)
S/(S-1) = 13/12                     (structure-to-observation ratio)
```

The correction arises because the generation structure has S = 13 intervals, but observation can only resolve S - 1 = 12 transitions between them. The ratio 13/12 = 1 + 1/12 is the same K/(n+L) = 2/24 = 1/12 correction that appears in the Hubble tension.

**Cross-domain consistency**: The same 13/12 factor governs both the Hubble tension and the baryon asymmetry. This is not a coincidence — both involve observers measuring structure through the ring.

---

## Genesis Mechanism

### The Derivation Chain

1. **Genesis**: traverse(-B, B) creates ±B partitions
   - B must partition direction (nothing is self-contradictory)
   - +B = forward traversal = matter = time-forward
   - -B = backward traversal = antimatter = time-backward

2. **Observer selects +B**: We ARE the +B partition
   - The "asymmetry" is perspectival — -B sees the same universe with "more antimatter"
   - Neither side is privileged

3. **Per-mode asymmetry**: K/B = 2/56
   - Observer cost per boundary mode
   - Bidirectional observation (K=2) of B=56 modes

4. **Lorentz dilution**: (1/L)⁶
   - 6 = dim(SO(3,1)) Lorentz generators
   - Each generator dilutes by 1/L = 1/20

5. **Generation correction**: S/(S-1) = 13/12
   - Generation structure observable-to-full ratio

6. **Product**: η = (K/B)(1/L)⁶ × S/(S-1)

### Sakharov Conditions from BLD

| Sakharov Condition | Standard Physics | BLD Translation |
|-------------------|------------------|-----------------|
| **B-number violation** | Sphaleron processes | Traversing the +B/-B boundary in traverse(-B,B) |
| **C and CP violation** | CKM phase, weak interaction | S₃-derived CP phases (L component); +B ≠ -B = chirality |
| **Out-of-equilibrium** | Electroweak phase transition | D-dimension multiplicity + K/X observation cost |

**BLD unification**: All three conditions follow from the same genesis function. The universe **must** violate baryon number (traverse crosses ±B), **must** violate CP (+B ≠ -B by construction), and **must** depart from equilibrium (observation costs K/X). Baryogenesis is not an accident — it is structurally inevitable.

---

## Verification

### Numerical Match

| Quantity | Predicted | Observed | Deviation |
|----------|-----------|----------|-----------|
| η | 6.045 × 10⁻¹⁰ | 6.104 ± 0.058 × 10⁻¹⁰ | **1.0σ** |

### Exact Rational Structure

The prediction is an exact rational number:

```
η = 13 / 21,504,000,000

Numerator:   K × S / 2 = 2 × 13 / 2 = 13
Denominator: (B/K) × L⁶ × (S-1) = 28 × 64,000,000 × 12 = 21,504,000,000
```

If future measurements tighten the uncertainty on η, this exact fraction becomes increasingly falsifiable.

### Structural Consistency

The formula uses only BLD constants that appear in other predictions:

| Constant | Value | Also Used In |
|----------|-------|-------------|
| K | 2 | α⁻¹, Hubble tension, Born rule, entropy, ... |
| B | 56 | α⁻¹, Higgs mass, Planck mass, ... |
| L | 20 | α⁻¹, dark matter, quark masses, ... |
| n | 4 | All BLD predictions |
| S | 13 | Lepton masses, weak mixing, Hubble tension |

No new constants. No free parameters.

### S/(S-1) Cross-Check

The same 13/12 factor appears in the Hubble tension:

```
Hubble: H₀(local) = H₀(CMB) × (1 + K/(n+L)) = H₀(CMB) × (1 + 2/24) = H₀(CMB) × 13/12
Baryon: η includes S/(S-1) = 13/12

Both arise from: 13 structural intervals, 12 observable transitions
```

---

## What This Explains

1. **Why η ~ 10⁻¹⁰**: The Lorentz dilution (1/20)⁶ = 1.56 × 10⁻⁸ combined with K/B ≈ 0.036 gives the correct order of magnitude. The exponent 6 is geometrically determined by spacetime dimension.

2. **Why the Standard Model prediction is too small**: SM baryogenesis only accounts for CP violation (one L component), not the full BLD mechanism. The SM correctly identifies the Sakharov conditions but lacks the structural framework to compute the ratio.

3. **Why antimatter is "missing"**: It isn't missing. We are the +B partition. From -B, antimatter dominates. The universe is symmetric; observation is not.

4. **Why η is universal**: The same ratio appears everywhere because it depends only on BLD structure constants, not on specific particle properties or initial conditions.

---

## Comparison with Standard Approaches

| Aspect | Standard (ΛCDM/SM) | BLD |
|--------|-------------------|-----|
| η value | Free parameter | **Derived**: 13/21,504,000,000 |
| Mechanism | Unknown (SM gives η ~ 10⁻¹⁸, too small) | Genesis: traverse(-B,B) + Lorentz dilution |
| Sakharov conditions | Necessary conditions, insufficient mechanism | All three structurally inevitable |
| Antimatter | "Missing" — where did it go? | Not missing — perspectival (+B/-B) |
| Free parameters | 1 (η fitted to observations) | 0 |

---

## References

### External Sources
- [Planck 2018 Cosmological Parameters (arXiv:1807.06209)](https://arxiv.org/abs/1807.06209) — η = (6.104 ± 0.058) × 10⁻¹⁰
- [Sakharov 1967: Violation of CP invariance](https://doi.org/10.1070/PU1991v034n05ABEH002497) — Three conditions for baryogenesis
- [PDG Review: Big-Bang Nucleosynthesis](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-bbang-nucleosynthesis.pdf) — η from BBN

### Internal BLD References
- [Genesis Function](genesis-function.md) — traverse(-B, B) = existence
- [Chirality and CPT](../quantum/chirality-cpt.md) — +B/-B and CP violation
- [Killing Form](../lie-theory/killing-form.md) — K = 2 derivation
- [Hubble Tension](hubble-tension.md) — Same 13/12 correction
- [Observer Correction](observer-correction.md) — K/X framework
- [Constants](../foundations/constants.md) — B, L, n, K, S definitions
