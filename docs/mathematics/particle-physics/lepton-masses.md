---
status: EMPIRICAL
depends_on:
  - fine-structure-consistency.md
  - ../lie-theory/killing-form.md
---

# Lepton Masses from BLD Structure

Formulas match observations to ~2%, using fitted parameters.

**Source**: Extracted from `particle-masses.md`

---

## Status Legend

| Tag | Meaning |
|-----|---------|
| `[OBSERVED]` | Input from experiment |
| `[DERIVED]` | Follows from proven BLD principles |
| `[EMPIRICAL]` | Fit to observed data |
| `[POSTULATED]` | Assumed without derivation |

---

## The Problem

The Standard Model does not explain particle masses. They are input parameters:

| Particle | Mass | Why this value? |
|----------|------|-----------------|
| Electron | 0.511 MeV | Unknown |
| Muon | 105.7 MeV | Unknown |
| Tau | 1777 MeV | Unknown |

The Higgs mechanism explains *how* particles get mass, but not *why* specific values.

---

## BLD Structural Constants

See [Fine Structure Consistency](fine-structure-consistency.md) for detailed status of each constant.

```
n = 4    (spacetime dimensions)           [OBSERVED]
L = 20   (Riemann tensor components)      [DERIVED from n²(n²-1)/12]
B = 56   (determined by fitting α⁻¹)      [EMPIRICAL - see note]
S = 13   (intervals in the hierarchy)     [DERIVED from B, inherits EMPIRICAL status]
```

**Critical Note**: B = 56 is a fit parameter, not a derivation. All subsequent formulas inherit this empirical status.

---

## The Electron Mass `[EMPIRICAL]`

The electron mass is m_e = 0.511 MeV. `[OBSERVED]`
The Higgs VEV (vacuum expectation value) is v = 246 GeV. `[OBSERVED]`

### The Formula `[POSTULATED]`

```
m_e = v × α² × (n/L)²
```

### Calculation

```
α² = (1/137)² = 5.33 × 10⁻⁵
(n/L)² = (4/20)² = (1/5)² = 0.04

m_e = 246 GeV × 5.33×10⁻⁵ × 0.04
    = 0.524 MeV
```

### Result

| | Predicted | Observed | Error |
|-|-----------|----------|-------|
| m_e (structural) | 0.524 MeV | 0.511 MeV | 2.5% |

### With Observer Correction `[EMPIRICAL]`

The 2.5% systematic error is corrected by 2/(n×L):

```
m_e = v × α² × (n/L)² × (1 - 2/(n×L))
    = v × α² × (n/L)² × (78/80)
    = 0.524 MeV × 0.975
    = 0.511 MeV ✓
```

See [Observer Corrections](../cosmology/observer-correction.md) for the status of this correction.

---

## The Muon Mass `[EMPIRICAL]`

The muon is the second-generation electron. m_μ = 105.7 MeV. `[OBSERVED]`

### The Formula `[POSTULATED]`

Generation scaling involves n² and the structural intervals S:

```
m_μ = m_e × n² × S
```

### Calculation (Two Tracks)

**Track A (Phenomenological)** — anchor to observed m_e:
```
n² × S = 16 × 13 = 208

m_μ = 0.511 MeV × 208 = 106.3 MeV  (0.6% error)
```

**Track B (Structural)** — use predicted m_e:
```
m_μ = 0.524 MeV × 208 = 109.0 MeV  (3.1% error)
```

### Result

| Track | m_e used | Predicted m_μ | Observed | Error |
|-------|----------|---------------|----------|-------|
| A (phenomenological) | 0.511 MeV | 106.3 MeV | 105.7 MeV | 0.6% |
| B (structural) | 0.524 MeV | 109.0 MeV | 105.7 MeV | 3.1% |

**Note**: Track A gives better accuracy but uses observed m_e. Track B is theoretically purer but has larger error, suggesting incomplete theory.

---

## The Tau Mass `[EMPIRICAL]`

The tau is the third-generation electron. m_τ = 1777 MeV. `[OBSERVED]`

### The Formula `[POSTULATED]`

Third generation adds the dimensional correction:

```
m_τ = m_μ × (S + n)
```

**Inconsistency Note**: The muon uses n² × S (multiplicative), but tau uses S + n (additive). This asymmetry is unexplained structurally.

### Calculation (Two Tracks)

**Track A (Phenomenological)** — anchor to observed m_μ:
```
m_τ = 105.7 MeV × 17 = 1797 MeV  (1.1% error)
```

**Track B (Structural)** — use predicted m_μ:
```
m_τ = 109.0 MeV × 17 = 1853 MeV  (4.3% error)
```

### Result

| Track | m_μ used | Predicted m_τ | Observed | Error |
|-------|----------|---------------|----------|-------|
| A (phenomenological) | 105.7 MeV | 1797 MeV | 1777 MeV | 1.1% |
| B (structural) | 109.0 MeV | 1853 MeV | 1777 MeV | 4.3% |

---

## Summary: The Lepton Mass Formulas

### Track A: Phenomenological (Better Accuracy)

Uses observed m_e = 0.511 MeV as anchor:

| Particle | Formula | Predicted | Observed | Error |
|----------|---------|-----------|----------|-------|
| m_e | (observed anchor) | 0.511 MeV | 0.511 MeV | — |
| m_μ | m_e × n² × S | 106.3 MeV | 105.7 MeV | **0.6%** |
| m_τ | m_μ × (S + n) | 1797 MeV | 1777 MeV | **1.1%** |

### Track B: Structural (Larger Error)

Derives everything from v, α, n, L:

| Particle | Formula | Predicted | Observed | Error |
|----------|---------|-----------|----------|-------|
| m_e | v × α² × (n/L)² | 0.524 MeV | 0.511 MeV | 2.5% |
| m_μ | m_e(pred) × n² × S | 109.0 MeV | 105.7 MeV | 3.1% |
| m_τ | m_μ(pred) × (S + n) | 1853 MeV | 1777 MeV | **4.3%** |

**Key Insight**: Track B has larger cumulative error, suggesting the formulas are incomplete. The 2.5% "error" in electron mass may not be fully explained by observer correction.

### Track C: With Observer Correction

Applies 2/(n×L) = 2.5% correction:

| Particle | Formula | Predicted | Observed | Error |
|----------|---------|-----------|----------|-------|
| m_e | v × α² × (n/L)² × (78/80) | 0.511 MeV | 0.511 MeV | **0%** |
| m_μ | m_e(corr) × n² × S | 106.3 MeV | 105.7 MeV | **0.6%** |
| m_τ | m_μ(pred) × (S + n) | 1807 MeV | 1777 MeV | **1.7%** |

---

## The Pattern

```
Generation 1:  m₁ = v × α² × (n/L)²           (surface coupling)
Generation 2:  m₂ = m₁ × n² × S              (deep coupling)
Generation 3:  m₃ = m₂ × (S + n)             (complete coupling)
```

### Fully Expanded (Track B)

```
m_e = v × n² / [L² × (n×L + B + 1)²]

m_μ = v × n⁴ × S / [L² × (n×L + B + 1)²]

m_τ = v × n⁴ × S × (S + n) / [L² × (n×L + B + 1)²]
```

---

## Why Three Generations?

**Hypothesis** `[SPECULATIVE]`: There are exactly three generations because:
1. **Gen 1**: Couples at the n/L interface (dimensional/geometric boundary)
2. **Gen 2**: Couples through the full n→B hierarchy (13 intervals)
3. **Gen 3**: Couples to the completed structure (intervals + dimensions)

There is no "Gen 4" because the structure is complete at S + n.

---

## Theoretical Interpretation

### Mass as Structural Position

In BLD, mass is not a fundamental property. It is **structural position** — where a particle sits in the D→L→B hierarchy.

```
Light particles: near D (dimensional, surface)
Heavy particles: near B (topological, deep)
```

### The Higgs as Boundary

The Higgs field is a **boundary** (B) that:
1. Breaks electroweak symmetry (creates distinction)
2. Sets the fundamental mass scale (v = 246 GeV)
3. Couples to particles based on their structural depth

Particles with deeper structural position couple more strongly to the Higgs boundary, hence have more mass.

---

## Open Questions

1. **Why n² × S for muon but S + n for tau?** The formula inconsistency needs structural explanation.

2. **Why does Track B have growing error?** Suggests missing corrections or incomplete formulas.

3. **Can the observer correction be independently derived?** Currently post-hoc.

---

## Complete Formula Set

### What Works (< 2% error)

| Constant | Formula | Predicted | Observed | Error |
|----------|---------|-----------|----------|-------|
| α⁻¹ | n×L + B + 1 | 137 | 137.036 | 0.03% |
| m_e | v × α² × (n/L)² × (78/80) | 0.511 MeV | 0.511 MeV | **0%** |
| m_μ | m_e × n² × S | 106.3 MeV | 105.7 MeV | 0.6% |
| m_τ | m_μ × (S + n) | 1797 MeV | 1777 MeV | 1.1% |

**Note**: The electron mass formula includes the observer correction (78/80) = (n×L - 2)/(n×L).

### What Partially Works (< 10% error)

| Constant | Formula | Predicted | Observed | Error |
|----------|---------|-----------|----------|-------|
| m_u | m_e × (n + 2/3) | 2.4 MeV | 2.2 MeV | 9% |
| m_d | m_e × (2n + 1/3) | 4.3 MeV | 4.7 MeV | 9% |

See [Quark Masses](quark-masses.md) for details.

### What Needs Work

- Strange, charm, bottom, top quark masses
- W, Z, Higgs boson masses (see [Boson Masses](boson-masses.md))
- Neutrino masses (if nonzero)

---

## Predictions

If this framework is correct:

1. **No fourth generation**: The structure is complete at three generations. A fourth would require n×L + B + 1 > 137, changing α.

2. **Mass ratios are exact**: With more precise measurements, m_μ/m_e should approach exactly n² × S = 208.

3. **Heavy quark formulas exist**: Strange, charm, bottom, top masses should be derivable from BLD constants with additional factors for color and electroweak mixing.

4. **The Higgs mass is derivable**: m_H should be expressible in terms of v, n, L, B (formula not yet found).

---

## References

- [Fine Structure Consistency](fine-structure-consistency.md) — Status of α and B
- [Observer Corrections](../cosmology/observer-correction.md) — The 2.5% correction
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — D, L, B fundamentals
