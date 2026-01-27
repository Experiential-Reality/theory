---
status: PREDICTED
layer: 2
depends_on:
  - e7-derivation.md
  - boson-masses.md
  - ../cosmology/observer-correction.md
  - ../foundations/discovery-method.md
used_by: []
prediction_date: 2026-01-22
---

# Higgs Self-Coupling: A Novel BLD Prediction

**Status**: PREDICTED — Testable at HL-LHC. Not yet measured with sufficient precision.

---

## Summary

**Higgs self-coupling prediction (testable at HL-LHC):**

1. κ_λ(structural) = 1.000: Higgs potential is exactly SM — [Why κ_λ = 1](#why-κ_λstructural--1-exactly)
2. Detection uses HH → bb̄γγ: both EM (X=B=56) and hadronic (X=n+L=24) — [Detection Chain](#step-2-the-detection-chain)
3. Combined detection structure: X = B + (n+L) = 80 = n×L — [Detection Structure](#step-3-the-detection-structure-key-insight)
4. κ_λ(observed) = 1 + K/(n×L) = 1.025: detection adds 2.5% (K/(D×L) derived from [Cost = B + D×L](../lie-theory/killing-form.md#why-2nxl-derived-from-cost-formula)) — [The Correction](#step-4-the-correction)
5. Falsifiable: BLD confirmed if 1.025±0.03, falsified if 1.000±0.02 — [Falsification Conditions](#falsification-conditions)
6. Current bounds too loose: HL-LHC will test at ~5% precision — [Experimental Tests](#experimental-tests)

| Quantity | Structural | Observed | Correction |
|----------|------------|----------|------------|
| κ_λ | **1.000** | **1.025** | 1 + K/(n×L) |

**Prediction date**: 2026-01-22. Not yet measured with sufficient precision.

---

## The Prediction

```
κ_λ(structural) = 1.000    (exactly SM)
κ_λ(observed)   = 1.025    (includes detection correction)
```

**Prediction date**: 2026-01-22

**Current experimental constraint**: κ_λ ∈ [−1.6, 6.6] at 95% CL (ATLAS Run 3, 2024)

**Expected HL-LHC precision**: ~10% on κ_λ

---

## Why This Prediction Matters

This is a **novel, falsifiable prediction** made before experimental verification:

1. **Not post-hoc** — Current bounds are too loose to distinguish 1.000 from 1.025
2. **Specific number** — Not "approximately SM" but exactly 1.025
3. **Derived from structure** — Falls out of detection apparatus analysis
4. **Testable timeline** — HL-LHC will reach required precision

---

## The Derivation

### Step 1: Draw the Problem

**What is κ_λ?**

The Higgs self-coupling κ_λ measures whether the triple-Higgs vertex matches the Standard Model prediction:

```
κ_λ = λ_HHH(measured) / λ_HHH(SM)

SM predicts: κ_λ = 1
BSM physics would give: κ_λ ≠ 1
```

**How is it measured?**

Via HH (di-Higgs) production, primarily:
- gg → H* → HH (gluon fusion, top loop, virtual Higgs)
- Best channel: HH → bb̄γγ

### Step 2: The Detection Chain

```
THE MEASUREMENT STRUCTURE
═══════════════════════════════════════════════════════════════════════════

    pp collision (LHC)
         │
         ▼
    ┌─────────────────────────────────────────────────────────────────────┐
    │                         PHYSICS                                      │
    │                                                                      │
    │    g ────┐      ┌───────┐                                           │
    │          │      │ top   │                                           │
    │          ▼      │ loop  │                                           │
    │       ┌──●──────┤       │                                           │
    │       │         └───┬───┘                                           │
    │    g ────┘          │                                               │
    │                     ▼                                               │
    │                  ┌──●──┐                                            │
    │                  │ H*  │ (virtual Higgs)                            │
    │                  └──┬──┘                                            │
    │                     │                                               │
    │                     │ λ_HHH (the coupling we measure)               │
    │                     │                                               │
    │                  ┌──┴──┐                                            │
    │                  ▼     ▼                                            │
    │                  H     H                                            │
    │                  │     │                                            │
    │              ┌───┘     └───┐                                        │
    │              ▼             ▼                                        │
    │            bb̄            γγ                                        │
    │                                                                      │
    └──────────────┼─────────────┼────────────────────────────────────────┘
                   │             │
                   ▼             ▼
    ┌──────────────────────┐  ┌──────────────────────┐
    │   HADRONIC CALO      │  │   EM CALORIMETER     │
    │                      │  │                      │
    │  b-jets → hadrons    │  │  γ → e⁺e⁻ shower    │
    │  → nuclear cascade   │  │  → scintillation    │
    │                      │  │                      │
    │  STRONG interaction  │  │  EM interaction      │
    │  X = n + L = 24      │  │  X = B = 56          │
    └──────────────────────┘  └──────────────────────┘
                   │             │
                   └──────┬──────┘
                          ▼
    ┌─────────────────────────────────────────────────────────────────────┐
    │                    RECONSTRUCTION                                    │
    │                                                                      │
    │   Combine bb̄ + γγ → m_HH → σ(HH) → extract κ_λ                     │
    │                                                                      │
    └─────────────────────────────────────────────────────────────────────┘
```

### Step 3: The Detection Structure (Key Insight)

**The detector is BLD structure. The measurement traverses it.**

For **m_H measurement** via H → γγ:
- Photons detected via EM calorimeter
- EM interaction only
- X = B = 56
- Correction: 1/B

This matches the known Higgs mass formula:
```
m_H = (v/2) × (1 + 1/B) = 125.25 GeV ✓
```

For **κ_λ measurement** via HH → bb̄γγ:
- Photons detected via EM calorimeter → X = B = 56
- b-jets detected via hadronic calorimeter → X = n + L = 24
- **Both channels combined in ONE measurement**

Combined detection structure:
```
X_detection = B + (n + L) = 56 + 24 = 80 = n × L
```

This is the **full observer structure** — the same n×L = 80 that appears in lepton mass corrections.

### Step 4: The Correction

**Two-reference principle**: Machine (detector) + Structure (physics) must agree.

For κ_λ:
- Structure: The self-coupling λ_HHH
- Machine: ATLAS detector (EM + hadronic calorimeters)
- Machine structure: X = n×L = 80

Observer correction:
```
correction = K / X = K / (n×L) = 2/80 = 0.025
```

Therefore:
```
κ_λ(observed) = κ_λ(structural) × (1 + K/(n×L))
              = 1.000 × 1.025
              = 1.025
```

---

## The Pattern: Structural = Exact, Observed = Corrected

| Quantity | Structural Value | Observed Value | Correction | Error |
|----------|------------------|----------------|------------|-------|
| m_H | v/2 = 123.11 GeV | 125.25 GeV | 1 + 1/B | 0.05% |
| α⁻¹ | n×L + B + 1 = 137 | 137.036 | + K/B + ... | 0.0 ppt |
| m_e | v × α² × (n/L)² | 0.511 MeV | × (78/80) | 0% |
| **κ_λ** | **1.000** | **1.025** | **1 + K/(n×L)** | **TBD** |

**The pattern is consistent**: Structural values are clean (often integers or simple ratios). Observed values include K/X corrections from the measurement apparatus.

---

## Why κ_λ(structural) = 1 Exactly {#why-κ_λstructural--1-exactly}

The SM Higgs potential:
```
V(φ) = λ(|φ|² - v²/2)²
```

Gives:
```
m_H² = 2λv²
λ_HHH = 3m_H²/v = 6λv
```

In BLD:
- m_H(structural) = v/2
- Therefore: m_H² = v²/4
- Therefore: λ = m_H²/(2v²) = (v²/4)/(2v²) = 1/8
- Therefore: λ_HHH = 6 × (1/8) × v = 3v/4

The SM relationship λ_HHH = 3m_H²/v holds **exactly** at the structural level when m_H = v/2.

**There is no BSM physics in the Higgs sector.** The potential is exactly SM. What we measure includes observer corrections.

---

## Connection to Detection Physics

### Why EM Detection → B

Electromagnetic interactions are mediated by photons coupling to charge. In BLD:
- Charge is a boundary property (B)
- EM coupling α ~ 1/137 = 1/(n×L + B + ...)
- EM calorimeters detect via EM showers
- Detection structure: X = B = 56

### Why Hadronic Detection → n + L

Strong interactions are mediated by gluons coupling to color. In BLD:
- Strong coupling α_s ~ 1 at low energy, asymptotic freedom at high
- From [Strong Coupling](strong-coupling.md): X = n + L = 24
- Hadronic calorimeters detect via nuclear cascades
- Detection structure: X = n + L = 24

### Why Combined → n×L

When bb̄γγ is reconstructed:
- Both channels contribute to the SAME observable (σ_HH)
- The structures ADD: B + (n + L) = 56 + 24 = 80 = n×L
- This is the full observer structure

The 80 = n×L appears throughout BLD as the "observer geometry" — the structure through which any complete measurement must pass.

---

## Experimental Tests

### Current Status (2024-2025)

| Experiment | Channel | κ_λ Constraint (95% CL) |
|------------|---------|-------------------------|
| ATLAS Run 3 | bb̄γγ | [−1.6, 6.6] |
| CMS Run 3 | Combined | [−1.2, 7.5] |

**Current precision is insufficient** to distinguish κ_λ = 1.000 from κ_λ = 1.025.

### Future Projections

| Timeframe | Expected Precision | Can Test BLD? |
|-----------|-------------------|---------------|
| Run 3 complete (~2026) | ~50% on κ_λ | No |
| HL-LHC (~2035) | ~10% on κ_λ | Marginal |
| HL-LHC full (~2040) | ~5% on κ_λ | **Yes** |

**HL-LHC with full luminosity should distinguish 1.000 from 1.025 at ~1σ level.**

---

## Falsification Conditions

### BLD is CONFIRMED if:

```
κ_λ(measured) = 1.025 ± 0.03
```

This would mean:
- Structural coupling is exactly SM (κ_λ = 1)
- Observer correction K/(n×L) = 0.025 is real
- Detection structure determines measurement corrections

### BLD is FALSIFIED if:

```
κ_λ(measured) = 1.000 ± 0.02
```

This would mean:
- No observer correction exists
- Detection structure doesn't affect measurement
- The K/X framework fails for this observable

### BLD is INCOMPLETE if:

```
κ_λ(measured) = 1.10 ± 0.03 (or other value ≠ 1.000, ≠ 1.025)
```

This would mean either:
- BLD correction is wrong (different X?)
- Actual BSM physics in Higgs sector
- Both effects present

---

## Comparison with Other Predictions

| Prediction | Source | κ_λ Value |
|------------|--------|-----------|
| Standard Model | SM Higgs potential | 1.000 |
| **BLD (this work)** | Detection structure | **1.025** |
| MSSM (low tan β) | Supersymmetry | 0.8 - 1.0 |
| MSSM (high tan β) | Supersymmetry | 1.0 - 1.2 |
| 2HDM | Two Higgs doublets | 0.5 - 2.0 |
| Composite Higgs | Strong dynamics | 0.8 - 1.5 |

**BLD makes the most specific prediction**: exactly 1.025, derived from first principles.

---

## The Deeper Point

The exactness is not coincidental.

| Observable | Structural | Why Exact? |
|------------|------------|------------|
| α⁻¹ | 137 | n×L + B + 1 (integers from Lie structure) |
| m_H/v | 1/2 | Electroweak boundary (B partitions at midpoint) |
| κ_λ | 1 | SM relationship preserved (no new physics) |
| μ/e | 207 | n²S - 1 (generation structure minus phase) |

**BLD claims**: The universe is built from discrete structural primitives (B, L, D). Physical constants are INTEGER combinations of these. What we observe includes K/X corrections from measurement.

The Higgs self-coupling being exactly SM (κ_λ = 1) means:
- The Higgs potential has no BSM modifications
- Electroweak symmetry breaking is structurally exact
- The 125 GeV Higgs is the ONLY Higgs (no extended sector)

---

## Open Questions

1. **Can other HH channels be analyzed?**
   - HH → bb̄ττ: Would involve different X (tau detection)
   - HH → 4b: Pure hadronic, X = n+L = 24 (single detection TYPE)
   - Different channels should give consistent κ_λ after corrections

2. **Does the correction depend on √s?**
   - Run 3 at 13.6 TeV vs HL-LHC at 14 TeV
   - Should be negligible (detection structure unchanged)

3. **What about single-Higgs couplings?**
   - **ANSWERED**: See [Higgs Couplings](higgs-couplings.md) for complete κ predictions
   - All κ values follow the same K/X detection structure framework
   - κ_γ = κ_Z = 1.036, κ_W = 1.026, κ_b = 1.083, etc.

---

## Conclusion

**The BLD prediction for Higgs self-coupling:**

```
κ_λ(structural) = 1.000    — The Higgs potential is exactly SM
κ_λ(observed)   = 1.025    — Detection adds K/(n×L) = 2/80
```

**This is testable at HL-LHC.**

**This is not post-hoc.**

**This follows from the same K/X framework that derives α⁻¹, m_H, and particle masses.**

---

## References

### External Sources
- [ATLAS HH → bb̄γγ Run 3 (2024)](https://atlas.cern/Updates/Briefing/Higgs-Self-Interaction-Run-3) — Current κ_λ constraint
- [HL-LHC Higgs Projections](https://cds.cern.ch/record/2652762) — Expected future precision
- [PDG Higgs Review](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-higgs-boson.pdf) — Higgs properties summary

### Internal BLD References
- [Higgs Couplings](higgs-couplings.md) — **Complete κ predictions for all channels**
- [Boson Masses](boson-masses.md) — Higgs mass m_H = (v/2)(1 + 1/B)
- [Observer Corrections](../cosmology/observer-correction.md) — K/X framework
- [Fine Structure Consistency](fine-structure-consistency.md) — α⁻¹ derivation
- [Strong Coupling](strong-coupling.md) — Why X = n + L for strong
- [Discovery Method](../foundations/discovery-method.md) — How to find structure
