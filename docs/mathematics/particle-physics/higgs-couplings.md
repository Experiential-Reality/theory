---
status: PREDICTED
layer: 2
depends_on:
  - higgs-self-coupling.md
  - boson-masses.md
  - ../cosmology/observer-correction.md
  - ../foundations/derivations/force-structure.md
  - ../foundations/machine/detection-structure.md
used_by: []
prediction_date: 2026-01-22
---

# Higgs Coupling Modifiers: Complete BLD Predictions

**Status**: PREDICTED — All κ values predicted from detection structure. Testable now and at HL-LHC.

---

## Quick Summary (D~7 Human Traversal)

**All Higgs couplings in 7 steps:**

1. **κ(structural) = 1 exactly** — No BSM physics in Higgs sector
2. **κ(observed) = 1 + K/X** — Detection adds observer correction
3. **K = 2 always** — Killing form (bidirectional observation)
4. **X = detection structure** — What the detector physically measures
5. **EM detection → X = B = 56** — Photons, leptons via ionization
6. **Hadronic detection → X = n+L = 24** — Jets via nuclear showers
7. **Neutrino escape → add L = 20** — Information leaves undetected

| Detection Type | X Value | κ predicted |
|----------------|---------|-------------|
| EM only | B = 56 | **1.036** |
| Hadronic only | n+L = 24 | **1.083** |
| EM + Hadronic | B+(n+L) = 80 | **1.025** |

**Key validation**: ATLAS κ_V = **1.035 ± 0.031** falls within BLD range [1.026, 1.036].

---

## The Core Principle

```
STRUCTURAL vs OBSERVED

What EXISTS (structure):      κ = 1      (exactly SM, no BSM physics)
What we MEASURE (observed):   κ = 1 + K/X  (detection correction)

K = 2 (always — Killing form, bidirectional observation)
X = detection structure (depends on what detector physically sees)
```

**The Higgs couplings ARE exactly SM.** The apparent deviations from unity are observer corrections from the detection apparatus, not new physics.

---

## Detection Structure Analysis

### The Detector IS a BLD Structure

From [Observer Corrections](../cosmology/observer-correction.md):

> "The machine (observer) and structure (observed) are both BLD structures. The machine isn't special — it's just another structure that happens to be doing the measuring."

Every particle detector works by making particles interact with matter:
- **EM calorimeters**: Photons/electrons create EM showers (ionization, scintillation)
- **Hadronic calorimeters**: Hadrons create nuclear cascades (strong interaction)
- **Tracking**: Charged particles ionize gas/silicon (EM interaction)

### Detection Structure Values

| Detection Type | Physical Process | X Value | Source |
|----------------|------------------|---------|--------|
| **Electromagnetic** | Ionization, EM showers | B = 56 | EM couples to boundary |
| **Hadronic** | Nuclear cascades | n+L = 24 | Strong couples to geometry |
| **Combined** | Both processes | B+(n+L) = 80 | Structures add |
| **+ Neutrino escape** | Information lost | add L = 20 | Link leaves undetected |

### Why These X Values?

From [Force Structure](../foundations/derivations/force-structure.md):

```
Forces ARE K/X at Different Scales

| Force  | X (Structure) | K/X    | What Detector Traverses |
|--------|---------------|--------|-------------------------|
| EM     | B = 56        | 0.036  | Boundary structure      |
| Strong | n+L = 24      | 0.083  | Geometric structure     |
| Weak   | n×L×B = 4480  | 0.0004 | Full structure          |
```

**EM detection → B**: Photons couple to charge (boundary property). EM showers traverse B.

**Hadronic detection → n+L**: Strong force couples to color (geometric property). Nuclear cascades traverse n+L.

**Why add when combined?** When both EM and hadronic channels contribute to ONE observable, the structures ADD: B + (n+L) = 80 = n×L (the full observer geometry).

---

## The Neutrino Rule

**Neutrinos escape undetected. This affects the detection structure.**

### The Neutrino's BLD Structure

From [Neutrino Masses](neutrino-masses.md), the neutrino is:

```
NEUTRINO (ν) — L + D ONLY, NO B
════════════════════════════════════════════════════

    BLD Components:
      B: ✗ (∅)   — NO boundary, invisible to EM detectors
      L: ✓ (20)  — propagates through spacetime
      D: ✓ (4)   — 3 generations (νe, νμ, ντ)

    ○ ─ ─ L ─ ─ ○ ─ ─ L ─ ─ ○
    │           │           │
    L           L           L    (links only, no boundaries)
    │           │           │
    ○ ─ ─ L ─ ─ ○ ─ ─ L ─ ─ ○
```

**Detector = B (EM-based).** Neutrino = L+D (no B). They don't share structure.

### What Happens When a Neutrino "Escapes"

When a neutrino is produced (e.g., W → ℓν), it's not created from nothing — it's the L+D structure **breaking its last link** to the larger structure and being ejected.

```
BEFORE: W boson (connected structure)
        ┌───────────────┐
        │   W = B+L+D   │
        │       ↓       │
        │   ℓ ─L─ ν     │  (ℓ and ν connected by L)
        └───────────────┘

AFTER:  Link breaks, ν ejected
        ┌───────┐
        │   ℓ   │ ←── detected (has B)
        │  (B)  │
        └───────┘
              ↑
              L breaks here
              ↓
        ┌───────┐
        │   ν   │ ←── escapes (only L+D, no B)
        │ (L+D) │
        └───────┘
```

The neutrino takes L with it. The detector (B) can't follow.

### Why +L in Detection Structure

The measurement attempts to probe the full decay. The detector sees B (the lepton). The neutrino's L is **part of the structure being probed** but escapes detection.

```
X_effective = X_detector + X_escaped
            = B + L
            = 56 + 20 = 76
```

The measurement's structural footprint includes the L that escaped. Larger X means smaller correction — the measurement is "diluted" across more structure.

### Why Add L Once, Not Per Neutrino

B, L, D are structural **types**, not particle counts. Whether one or two neutrinos escape, the structural type that escapes is **L** (the link connecting neutrino structure to the interaction).

Multiple neutrinos of the same type don't add new structural dimensions — they probe the same L-type structure repeatedly.

### The Rule

```
When neutrino escapes: X_effective = X_base + L

Example: H → WW → ℓνℓν
  Base: EM detection of ℓ → X = B = 56
  Neutrino escapes: +L = 20 (the L-type structure that escapes)
  Effective: X = B + L = 76
  κ_W = 1 + K/76 = 1.026
```

---

## Detection Structure Formalism

For the complete T ∩ S detection formalism, see [Detection Structure](../foundations/machine/detection-structure.md).

**Quick reference:**
- T = traverser (detector's BLD components)
- S = particle structure
- Detection: T ∩ S ≠ ∅ → detected; T ∩ S = ∅ → escapes
- X = X_traverser + X_escaped
- Sign: "+" if something escapes, "−" if all detected

---

## Complete κ Predictions

### Detection Structure Diagrams

```
DETECTION CHAINS FOR HIGGS COUPLINGS
═══════════════════════════════════════════════════════════════════════════════

κ_γ : H → γγ (EM ONLY)
──────────────────────────────────────────────
    H ────→ γ ────→ EM Calorimeter
          γ ────→ (photon showers → ionization → B)

    X = B = 56
    κ_γ = 1 + 2/56 = 1.036

κ_Z : H → ZZ → 4ℓ (EM ONLY)
──────────────────────────────────────────────
    H ────→ Z ────→ ℓ⁺ℓ⁻ ────→ Tracker + EM Calo
          Z ────→ ℓ⁺ℓ⁻ ────→ (ionization → B)

    All products EM-detectable, no escapes
    X = B = 56
    κ_Z = 1 + 2/56 = 1.036

κ_μ : H → μμ (EM ONLY)
──────────────────────────────────────────────
    H ────→ μ⁺ ────→ Tracker + Muon Chambers
          μ⁻ ────→ (ionization → B)

    X = B = 56
    κ_μ = 1 + 2/56 = 1.036

κ_b : H → bb̄ (HADRONIC ONLY)
──────────────────────────────────────────────
    H ────→ b ────→ Hadronic Calorimeter
          b̄ ────→ (jet → nuclear cascade → n+L)

    X = n + L = 24
    κ_b = 1 + 2/24 = 1.083

κ_c : H → cc̄ (HADRONIC ONLY)
──────────────────────────────────────────────
    H ────→ c ────→ Hadronic Calorimeter
          c̄ ────→ (jet → nuclear cascade → n+L)

    X = n + L = 24
    κ_c = 1 + 2/24 = 1.083

κ_W : H → WW → ℓνℓν (EM + NEUTRINO)
──────────────────────────────────────────────
    H ────→ W⁺ ────→ ℓ⁺ ────→ EM detection (B)
                    ν  ────→ ESCAPES (carries L)
          W⁻ ────→ ℓ⁻ ────→ EM detection (B)
                    ν̄  ────→ ESCAPES (carries L)

    X = B + L = 56 + 20 = 76
    κ_W = 1 + 2/76 = 1.026

κ_τ : H → ττ (MIXED — WEIGHTED AVERAGE)
──────────────────────────────────────────────
    Hadronic τ decay (65%):
    H ────→ τ ────→ hadrons ────→ Hadronic Calo (n+L)
                    ν_τ     ────→ ESCAPES (+L)
    X_had = (n+L) + L = 44
    κ_τ(had) = 1 + 2/44 = 1.045

    Leptonic τ decay (35%):
    H ────→ τ ────→ ℓ    ────→ EM detection (B)
                    ν_τ   ────→ ESCAPES
                    ν_ℓ   ────→ ESCAPES
    X_lep = B + L = 76  (L is the structural TYPE, regardless of ν count)
    κ_τ(lep) = 1 + 2/76 = 1.026

    Weighted:
    κ_τ = 0.65 × 1.045 + 0.35 × 1.026 = 1.038

κ_λ : HH → bb̄γγ (EM + HADRONIC)
──────────────────────────────────────────────
    H ────→ H ────→ b  ────→ Hadronic Calo (n+L)
          H ────→ b̄  ────→ Hadronic Calo (n+L)
                   γ  ────→ EM Calo (B)
                   γ  ────→ EM Calo (B)

    Combined: X = B + (n+L) = 80 = n×L
    κ_λ = 1 + 2/80 = 1.025

κ_t : ttH → various (COMPLEX)
──────────────────────────────────────────────
    Detection TYPES add, not particle counts.

    Leptonic channel (ttH → ℓνb):
    - EM detection (lepton): B
    - Hadronic detection (b-jets): n+L
    - Neutrino escape: +L
    X = B + (n+L) + L = 100
    κ_t(lep) = 1 + 2/100 = 1.020

    Hadronic channel (ttH → jjb, all jets):
    - Only hadronic detection: n+L
    - No EM, no missing energy
    X = n+L = 24  (same as κ_b)
    κ_t(had) = 1 + 2/24 = 1.083

    Combined (typical ~50/50 lep/had for precision):
    κ_t ≈ 0.5 × 1.020 + 0.5 × 1.083 = 1.05
```

### Summary Table: All κ Predictions

| κ | Channel | Detection | Escapes | X | **Prediction** |
|---|---------|-----------|---------|---|----------------|
| κ_γ | H→γγ | EM | none | B = 56 | **1.036** |
| κ_Z | H→ZZ→4ℓ | EM | none | B = 56 | **1.036** |
| κ_μ | H→μμ | EM | none | B = 56 | **1.036** |
| κ_W | H→WW→ℓνℓν | EM | ν×2 | B+L = 76 | **1.026** |
| κ_τ | H→ττ | Mixed | ν | weighted | **1.038** |
| κ_b | H→bb̄ | Hadronic | none | n+L = 24 | **1.083** |
| κ_c | H→cc̄ | Hadronic | none | n+L = 24 | **1.083** |
| κ_t | ttH | Mixed | varies | varies | **1.02-1.08** |
| κ_λ | HH→bb̄γγ | EM+Had | none | B+(n+L) = 80 | **1.025** |

---

## Experimental Validation

### Current Data (ATLAS/CMS Combined)

From [ATLAS Nature 2022](https://www.nature.com/articles/s41586-022-04892-x) and [PDG 2024](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-higgs-boson.pdf):

| Measurement | Experimental | BLD Prediction | Match |
|-------------|--------------|----------------|-------|
| **κ_V** (W+Z combined) | **1.035 ± 0.031** | **[1.026, 1.036]** | **in range** |
| κ_γ | 1.05 ± 0.09 | 1.036 | 0.2σ |
| κ_Z | 1.01 ± 0.08 | 1.036 | 0.3σ |
| κ_W | 1.04 ± 0.08 | 1.026 | 0.2σ |
| κ_τ | 0.99 ± 0.08 | 1.038 | 0.6σ |
| κ_b | 0.98 ± 0.13 | 1.083 | 0.8σ |
| κ_μ | 1.21 ± 0.24 | 1.036 | 0.7σ |
| κ_t | 1.01 ± 0.11 | 1.02-1.08 | compatible |

**Critical observation**: κ_V = 1.035 ± 0.031 falls squarely in the BLD prediction range.

### Why κ_V Is the Best Test

The combined vector boson coupling κ_V has:
- Smallest relative uncertainty (~3%)
- Both channels (W via ℓν, Z via 4ℓ) are EM-dominated

**BLD prediction for κ_V depends on the experimental combination:**
```
κ_Z (BLD) = 1.036    (EM only, X = B)
κ_W (BLD) = 1.026    (EM + ν escape, X = B+L)

κ_V(BLD) ∈ [1.026, 1.036]

Measured: 1.035 ± 0.031
```

The measured 1.035 is closer to κ_Z, which makes sense: H→ZZ→4ℓ is a cleaner channel with smaller systematics, so it dominates the combination. BLD predicts this asymmetry — the channels have **different** κ values, and the combination should lean toward the cleaner one.

---

## The Pattern: κ_γ = κ_Z ≠ κ_W

**BLD makes a specific, testable prediction that differs from SM:**

```
SM prediction:     κ_γ = κ_Z = κ_W = 1.000  (all equal)
BLD prediction:    κ_γ = κ_Z = 1.036        (EM detection, no escapes)
                   κ_W = 1.026              (EM detection WITH ν escape)

Difference: κ_Z − κ_W = 0.010 (1%)
```

**This is a discriminating prediction.** The SM predicts all κ = 1.000 and equal. BLD predicts κ > 1 AND κ_W ≠ κ_Z.

Current data trends:
- κ_Z (1.01 ± 0.08) and κ_γ (1.05 ± 0.09) are statistically equal → consistent with both
- κ_W (1.04 ± 0.08) is between them → current errors too large to distinguish

As precision improves to ~2%, BLD predicts:
- κ_γ and κ_Z will converge to ~1.036 (same detection structure)
- κ_W will converge to ~1.026 (different due to ν escape)
- The 1% difference (κ_Z > κ_W) is real and structural

**If κ_Z = κ_W at 2% precision, BLD is falsified for this prediction.**

---

## The Hadronic Prediction: κ_b = 1.083

This is the **most distinctive prediction**:

```
κ_b = 1 + K/(n+L) = 1 + 2/24 = 1.083
```

**Why 8.3% enhancement?**

The b-quark Yukawa coupling is measured via H → bb̄ with b-tagging:
- b-jets detected via hadronic calorimeter
- Strong interaction dominates detection
- X = n+L = 24 (geometric structure)
- Larger correction than EM channels

Current measurement: κ_b = 0.98 ± 0.13 (1σ interval: [0.85, 1.11])

**BLD prediction 1.083 is within the 1σ interval.** As precision improves, this will be the critical test.

---

## Derived Relationships

### The κ_γ/κ_b Ratio

```
κ_γ/κ_b = (1 + 2/56)/(1 + 2/24)
        = 1.036/1.083
        = 0.957

This is purely structural:
= (B + K)/(B) × (n+L)/(n+L + K)
= (58/56) × (24/26)
= 0.957
```

### The κ_W/κ_Z Ratio

```
κ_W/κ_Z = (1 + 2/76)/(1 + 2/56)
        = 1.026/1.036
        = 0.990

Difference comes from neutrino escape:
X_W = B + L = 76  (ν carries L away)
X_Z = B = 56      (all products detected)
```

---

## Connection to Other Predictions

### Same Framework, Different Observables

| Observable | Structure | Detection | K/X | Result |
|------------|-----------|-----------|-----|--------|
| α⁻¹ | 137 | EM probe | +2/56 | 137.036 |
| m_H | v/2 | H→γγ (EM) | +1/56 | 125.31 GeV |
| κ_γ | 1 | EM | +2/56 | 1.036 |
| κ_b | 1 | Hadronic | +2/24 | 1.083 |
| κ_λ | 1 | EM+Had | +2/80 | 1.025 |

**The pattern is universal**: structure + K/X(detection) = observed.

### Why m_H Uses 1/B But κ Uses 2/B

From [Observer Corrections](../cosmology/observer-correction.md) skip ratio table:

| Measurement | K | Type |
|-------------|---|------|
| m_H | **1** | Property of single particle |
| α⁻¹ | **2** | Interaction strength |
| κ | **2** | Coupling (interaction) |

**The distinction is what's being measured:**

```
PROPERTY measurement (m_H):
  - Observe a single particle's energy/momentum
  - One "link" from observer to particle
  - K = 1 (unidirectional)
  - m_H = (v/2) × (1 + 1/B)

INTERACTION measurement (κ, α):
  - Observe how two things interact
  - Two "links": observer↔particle₁↔particle₂
  - K = 2 (bidirectional)
  - κ = 1 + 2/X
```

The κ measurements probe **coupling strengths** — how strongly the Higgs interacts with fermions/bosons. Interactions are inherently bidirectional (Higgs ↔ fermion), so K=2.

---

## Falsification Conditions

### BLD Is CONFIRMED If:

| κ | Required Measurement | Current Status |
|---|---------------------|----------------|
| κ_γ | 1.036 ± 0.03 | 1.05 ± 0.09 (compatible) |
| κ_Z | 1.036 ± 0.03 | 1.01 ± 0.08 (compatible) |
| κ_γ = κ_Z | within 1% | needs 3% precision |
| κ_W < κ_Z | by ~1% | needs 5% precision |
| κ_b | 1.083 ± 0.05 | 0.98 ± 0.13 (compatible) |
| κ_λ | 1.025 ± 0.03 | [−1.6, 6.6] (unmeasured) |

### BLD Is FALSIFIED If:

| Condition | What It Would Mean |
|-----------|-------------------|
| κ_γ ≠ κ_Z at 3σ (both ~1.0) | Detection doesn't matter |
| κ_b = 1.00 ± 0.03 | No hadronic correction |
| κ_λ = 1.00 ± 0.02 | No combined correction |
| All κ = 1.00 ± 0.02 | K/X framework fails |

### Critical Tests by Timeframe

| Timeframe | Achievable | BLD Prediction |
|-----------|------------|----------------|
| **Now** | κ_V = 1.035 ± 0.03 | **Compatible** (in range) |
| Run 3 (~2026) | κ_γ, κ_Z to 5% | κ_γ = κ_Z = 1.036 |
| HL-LHC (~2035) | κ_b to 5%, κ_λ to 10% | κ_b = 1.083, κ_λ = 1.025 |
| HL-LHC full (~2040) | All κ to 2-3% | Full pattern verification |

---

## The Deeper Point

### Why κ(structural) = 1 Exactly

The Standard Model Higgs sector is **structurally exact**:

```
V(φ) = λ(|φ|² - v²/2)²    ← SM potential, unchanged

All Yukawa couplings: y_f = m_f/v    ← SM relationship, exact
All gauge couplings: g²v²/4 = m_V²   ← SM relationship, exact
```

**There is no BSM physics in the Higgs sector.** The Higgs potential has exactly the SM form. All coupling relationships are exactly SM.

What we measure differs from 1.000 because **measurement itself has a structure**, and that structure contributes K/X.

### The Detection Structure IS the Correction

The apparent κ > 1 values are not:
- New physics
- Radiative corrections
- Systematic errors

They ARE:
- The detector's BLD interacting with the signal's BLD
- Universal skip ratio K/X at the detection scale
- Same phenomenon as α⁻¹ = 137.036 vs 137

### Why This Matters

If BLD is correct, then:

1. **No BSM hints in Higgs couplings** — The κ ≠ 1 values are detection artifacts
2. **No extended Higgs sector** — Single SM Higgs is sufficient
3. **Detection corrections are predictable** — Can be computed from first principles
4. **Same K/X everywhere** — Unifies particle physics with cosmology

---

## Summary

```
THE BLD PREDICTION FOR HIGGS COUPLINGS

κ(structural) = 1      — All couplings exactly SM
κ(observed) = 1 + K/X  — Detection adds universal correction

K = 2 (always)
X = detection structure:
    EM detection:      B = 56       → κ = 1.036
    Hadronic:          n+L = 24     → κ = 1.083
    Combined:          80           → κ = 1.025
    + ν escape:        add L = 20

Current validation:
    κ_V = 1.035 ± 0.031 (ATLAS)
    BLD = [1.026, 1.036] (depends on W/Z weighting)
    Match: within range

This is not post-hoc.
This follows from the same K/X framework that derives α⁻¹, m_H, and all particle masses.
```

---

## References

### External Sources
- [ATLAS Nature 2022](https://www.nature.com/articles/s41586-022-04892-x) — Higgs coupling measurements
- [PDG 2024 Higgs Review](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-higgs-boson.pdf) — Current experimental status
- [HL-LHC Higgs Projections](https://cds.cern.ch/record/2652762) — Future precision expectations
- [CMS Higgs Combination](https://cms.cern/news/higgs-boson-properties) — Combined measurements

### Internal BLD References
- [Higgs Self-Coupling](higgs-self-coupling.md) — κ_λ = 1.025 detailed derivation
- [Boson Masses](boson-masses.md) — m_H = (v/2)(1 + 1/B) derivation
- [Observer Corrections](../cosmology/observer-correction.md) — Two-reference framework
- [Force Structure](../foundations/derivations/force-structure.md) — Why X = B for EM, X = n+L for strong
- [Fine Structure Consistency](fine-structure-consistency.md) — α⁻¹ = 137.036 from same framework
