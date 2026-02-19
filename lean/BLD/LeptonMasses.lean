/- BLD Calculus — Lepton Mass Predictions

   Muon/electron mass ratio correction factors achieving 0.5 ppb accuracy:

     μ/e = (n²S−1) × nLS/(nLS+1) × (1−1/((nL)²+nS)) × (1−1/(nLB²)) × (1+O(10⁻⁸))
         = 207 × 1040/1041 × 6451/6452 × 250879/250880 × (1+...)
         = 206.7682826 (observed: 206.7682827 ± 5×10⁻⁷)

   The fifth factor involves e² (transcendental) and is blocked on real analysis.
   τ/μ rational corrections are in QuarkMasses.lean (mu_correction_1, tau_correction_1/2).

   Also: neutrino mass rational factor predicting m_νe ≈ 16 meV.

   Reference: digest.md §6, §10, bld.py lepton_masses
-/

import Mathlib.Tactic.NormNum
import BLD.Constants

namespace BLD.LeptonMasses

-- ═══════════════════════════════════════════════════════════
-- μ/e cascade: rational correction factors
-- ═══════════════════════════════════════════════════════════

/-- μ/e factor 1 (primordial − phase): n²S − 1 = 207.
    The discrete primordial integer 208 loses 1 unit to phase. -/
theorem mu_e_factor_1 : BLD.n ^ 2 * BLD.S - 1 = 207 := by decide

/-- μ/e factor 2: nLS/(nLS+1) = 1040/1041.
    First K/X cascade correction. -/
theorem mu_e_factor_2 :
    (BLD.n * BLD.L * BLD.S : ℚ) / (BLD.n * BLD.L * BLD.S + 1) = 1040 / 1041 := by
  norm_num [BLD.n, BLD.L, BLD.S]

/-- μ/e factor 3: 1 − 1/((nL)²+nS) = 6451/6452.
    Second-order observer geometry correction.
    W boson uses +1/6452 (opposite sign, same structure). -/
theorem mu_e_factor_3 :
    1 - 1 / ((BLD.n * BLD.L : ℚ) ^ 2 + BLD.n * BLD.S) = 6451 / 6452 := by
  norm_num [BLD.n, BLD.L, BLD.S]

/-- μ/e factor 4: 1 − 1/(nLB²) = 250879/250880.
    Third-order boundary structure correction. -/
theorem mu_e_factor_4 :
    1 - 1 / ((BLD.n : ℚ) * BLD.L * BLD.B ^ 2) = 250879 / 250880 := by
  norm_num [BLD.n, BLD.L, BLD.B]

-- ═══════════════════════════════════════════════════════════
-- Neutrino mass rational factor
-- ═══════════════════════════════════════════════════════════

/-- Neutrino mass factor: (K/B)² × K/(nL) × (1 + K/(nLB)).
    m_νe = m_e × this factor ≈ 0.511 MeV × 3.19×10⁻⁸ ≈ 16 meV.
    Testable prediction: normal ordering, KATRIN bound < 0.8 eV. -/
theorem neutrino_mass_factor :
    ((BLD.K : ℚ) / BLD.B) ^ 2 * (BLD.K / (BLD.n * BLD.L))
    * (1 + BLD.K / (BLD.n * BLD.L * BLD.B))
    = 2241 / 70246400 := by
  norm_num [BLD.K, BLD.B, BLD.n, BLD.L]

/-- Neutrino suppression decomposition:
    (K/B)² = 1/784 — boundary suppression squared
    K/(nL) = 1/40 — geometric suppression
    1+K/(nLB) = 2241/2240 — small observer correction. -/
theorem neutrino_factor_decomposition :
    ((BLD.K : ℚ) / BLD.B) ^ 2 = 1 / 784 ∧
    (BLD.K : ℚ) / (BLD.n * BLD.L) = 1 / 40 ∧
    1 + (BLD.K : ℚ) / (BLD.n * BLD.L * BLD.B) = 2241 / 2240 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [BLD.K, BLD.B, BLD.n, BLD.L]

end BLD.LeptonMasses
