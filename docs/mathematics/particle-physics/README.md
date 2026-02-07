---
status: DERIVED
layer: 2
key_result: "15+ particle physics quantities derived at sub-percent accuracy"
depends_on:
  - ../foundations/derivations/force-structure.md
  - ../foundations/derivations/octonion-derivation.md
  - ../lie-theory/lie-correspondence.md
used_by:
  - ../../meta/proof-status.md
  - ../../README.md
---

## Summary

**Particle physics from structural constants — 15+ quantities at sub-percent accuracy:**

1. All particles classified from BLD structure — [particle-classification.md](particle-classification.md)
2. α⁻¹ = 137.036 exact, from B = 56 — [e7-derivation.md](e7-derivation.md)
3. Lepton mass ratios exact (μ/e, τ/μ) — [lepton-masses.md](lepton-masses.md)
4. All 6 quark masses < 0.5% error — [quark-masses.md](quark-masses.md)
5. Higgs 125.20 GeV exact — [boson-masses.md](boson-masses.md)
6. **Novel prediction**: κ_λ = 1.025 testable at HL-LHC — [higgs-self-coupling.md](higgs-self-coupling.md)

# BLD Particle Physics

**Layer 2**: Particle physics derived from BLD structural constants.

## Contents

| File | Status | Description |
|------|--------|-------------|
| [particle-classification.md](particle-classification.md) | DERIVED | Complete particle spectrum from BLD |
| [e7-derivation.md](e7-derivation.md) | DERIVED | B = 56, α⁻¹ = 137.036 from triality |
| [fine-structure-consistency.md](fine-structure-consistency.md) | DERIVED | α⁻¹ = n×L + B + 1 + 2/B verification |
| [strong-coupling.md](strong-coupling.md) | DERIVED | α_s⁻¹ = α⁻¹/n² − K/(n+L) = 8.482 |
| [lepton-masses.md](lepton-masses.md) | DERIVED | Electron, muon, tau mass ratios (exact) |
| [boson-masses.md](boson-masses.md) | DERIVED | Higgs, W, Z masses |
| [quark-masses.md](quark-masses.md) | DERIVED | All 6 quark masses (<0.5% error) |
| [e7-connection.md](e7-connection.md) | DERIVED | B=56 and exceptional Lie algebras |
| [neutrino-masses.md](neutrino-masses.md) | DERIVED | Neutrino masses from missing B coupling |
| [higgs-self-coupling.md](higgs-self-coupling.md) | **PREDICTED** | κ_λ = 1.025 (testable at HL-LHC) |
| [higgs-couplings.md](higgs-couplings.md) | **PREDICTED** | All κ values from detection structure |

## Key Predictions

| Quantity | Formula | Predicted | Observed | Error | Meas. Prec. |
|----------|---------|-----------|----------|-------|-------------|
| α⁻¹ | n×L + B + 1 + K/B + spatial − e²×120/(119×(n×L×B)²) | 137.035999177 | 137.035999177 | **matches CODATA** | 0.15 ppt |
| sin²θ_W | 3/S + K/(n×L×B) | 0.231215 | 0.23121 | **~0.002%** | ~0.1% |
| α_s⁻¹ | α⁻¹/n² − K/(n+L) | 8.4814 | 8.482 | **~0.02%** | ~1% |
| m_H | (v/K)(1 + 1/B)(1 − 1/(B×L)) | **125.20 GeV** | 125.20 GeV | **0.0%** | 0.14% |
| m_Z | (v/e)(137/136)(1 − K/B²) | 91.187 GeV | 91.188 GeV | **0.5 MeV** | 2.1 MeV |
| m_W | m_Z × cos(θ_W) × (209/208) × (1 + 1/6452) | 80.373 GeV | 80.377 GeV | **3.7 MeV** | 12 MeV |
| τ/μ | 2πe × 3 corrections | 16.81716 | 16.81709 | **4 ppm** | 70 ppm |
| μ/e | base × couplings + e²(S+1)/((n×L)²B²S²) | 206.7682826 | 206.7682827 | **0.5 ppb** | 22,000 ppt |
| m_u | m_d / (K×S/(S-1)) | 2.16 MeV | 2.16 MeV | **0.0%** | ~20% |
| m_d | m_s / (L + K/L) | 4.65 MeV | 4.67 MeV | **0.4%** | ~10% |
| m_s | m_e × (n²S - L - L/n) | 93.5 MeV | 93.4 MeV | **0.1%** | ~3% |
| m_c | m_s × (S + K/3) | 1276 MeV | 1270 MeV | **0.5%** | ~2% |
| m_b | m_c × (3 + K/7) | 4193 MeV | 4180 MeV | **0.2%** | ~1% |
| m_t | v/√K × (1 - K/n²S) | 172.4 GeV | 172.69 GeV | **0.17%** | ~0.3% |
| **κ_λ** | **1 + K/(n×L)** | **1.025** | **[−1.6, 6.6]** | **TBD** | **~10% (HL-LHC)** |
| **κ_V** | **1 + K/B** | **[1.026, 1.036]** | **1.035 ± 0.031** | **in range** | **~3%** |
| **κ_b** | **1 + K/(n+L)** | **1.083** | **0.98 ± 0.13** | **compatible** | **~13%** |
| **κ_γ** | **1 + K/B** | **1.036** | **1.05 ± 0.09** | **0.2σ** | **~9%** |

> **Note**: All predictions are at or below current measurement precision. The "Error" column shows deviation from central measured value; "Meas. Prec." shows experimental uncertainty (CODATA 2022 / PDG 2024).

## Key Insight: Observation Cost K/X

**Principle**: Observed = Structural + K/X(experiment)

All corrections follow the observation cost K/X where:
- **K = 2** (Killing form, always)
- **X** = structure being traversed
- **Sign** = traversal completeness

| Force | X (Structure) | K/X | What Measurement Traverses |
|-------|---------------|-----|---------------------------|
| EM | B = 56 | +K/B = +0.036 | Boundary structure |
| Weak | n×L×B = 4480 | +K/(n×L×B) = +0.00045 | Full geometric-boundary |
| Strong | n+L = 24 | −K/(n+L) = −0.083 | Geometry only |

**The ± sign rule:**
- **"+"** = traversal incomplete (something unobserved, e.g., neutrino escapes)
- **"−"** = traversal complete (everything observed, e.g., jets fully detected)

See [Force Structure](../foundations/derivations/force-structure.md) for complete derivations.

## The One Empirical Input

> **"SU(3) matter exists"** — This is the single empirical fact that BLD cannot derive. Everything else follows.

## Reading Order

1. **Start**: `particle-classification.md` — what particles can exist and why
2. **Then**: `e7-derivation.md` — how B = 56 is derived
3. **Then**: `lepton-masses.md` — mass ratio derivations
4. **Then**: `fine-structure-consistency.md` — α⁻¹ verification
5. **Finally**: `strong-coupling.md` — completing the force derivations
