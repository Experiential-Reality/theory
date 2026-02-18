/- BLD Calculus — Quark Mass Predictions

   Primordial quark mass ratios from BLD constants (rational parts).
   Transcendental corrections (involving e^(-K/B) etc.) require
   real analysis infrastructure.

   FUTURE (medium — rational parts now, transcendental corrections later):
   - Full mass ratios with K/X corrections
   - Running coupling effects
   - CKM matrix elements

   Reference: particle-physics/quark-mass-predictions.md
-/

import Mathlib.Tactic.NormNum
import BLD.Constants

namespace BLD.QuarkMasses

/-- Up/down mass ratio: m_u/m_d = 1/K = 1/2.
    (observed: 0.47 ± 0.07). -/
theorem mu_md_ratio : 1 / (BLD.K : ℚ) = 1 / 2 := by
  norm_num [BLD.K]

/-- Strange/down mass ratio: m_s/m_d = L = 20.
    (observed: ~20, from m_s ≈ 95 MeV, m_d ≈ 4.7 MeV). -/
theorem ms_md_ratio : (BLD.L : ℚ) = 20 := by norm_num [BLD.L]

/-- Charm/strange mass ratio: m_c/m_s = S = 13.
    (observed: ~13.4, from m_c ≈ 1.27 GeV, m_s ≈ 95 MeV). -/
theorem mc_ms_ratio : (BLD.S : ℚ) = 13 := by norm_num [BLD.S]

/-- Bottom/charm mass ratio: m_b/m_c = 3 + K/7 = 23/7.
    (observed: ~3.3, from m_b ≈ 4.18 GeV, m_c ≈ 1.27 GeV). -/
theorem mb_mc_ratio : 3 + (BLD.K : ℚ) / 7 = 23 / 7 := by
  norm_num [BLD.K]

/-- Top mass rational factor: 1 - K/(n²S) = 1 - 2/208 = 103/104.
    Multiplied by v = 246 GeV gives m_t primordial. -/
theorem mt_rational_factor :
    1 - (BLD.K : ℚ) / (BLD.n ^ 2 * BLD.S) = 103 / 104 := by
  norm_num [BLD.K, BLD.n, BLD.S]

-- ═══════════════════════════════════════════════════════════
-- Lepton mass ratio correction factors (paper §1651, §1658)
-- ═══════════════════════════════════════════════════════════

/-- μ/e correction: (n²S - 1)/(n²S) = 207/208. -/
theorem mu_correction_1 :
    (BLD.n ^ 2 * BLD.S - 1 : ℚ) / (BLD.n ^ 2 * BLD.S) = 207 / 208 := by
  norm_num [BLD.n, BLD.S]

/-- τ/μ correction 1: (nL - 1)/nL = 79/80. -/
theorem tau_correction_1 :
    (BLD.n * BLD.L - 1 : ℚ) / (BLD.n * BLD.L) = 79 / 80 := by
  norm_num [BLD.n, BLD.L]

/-- τ/μ correction 2: (nLS + K)/(nLS) = 521/520. -/
theorem tau_correction_2 :
    (BLD.n * BLD.L * BLD.S + BLD.K : ℚ) / (BLD.n * BLD.L * BLD.S) = 521 / 520 := by
  norm_num [BLD.n, BLD.L, BLD.S, BLD.K]

/-- Top quark K/X correction: K/(n²S) = 1/104.
    The top quark receives only the weak correction. -/
theorem top_quark_correction :
    (BLD.K : ℚ) / (BLD.n ^ 2 * BLD.S) = 1 / 104 := by
  norm_num [BLD.K, BLD.n, BLD.S]

end BLD.QuarkMasses
