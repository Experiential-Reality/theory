/- BLD Calculus — Boson Mass Predictions

   Rational factors in Higgs, Z, and W boson mass formulas.
   Full formulas involve v (VEV) and e (Euler's number) which are
   transcendental; the rational correction factors are proved here.

   Higgs: m_H = (v/2) · (1+1/B) · (1-1/(BL)) = 125.20 GeV
   Z:     m_Z = (v/e) · (137/136) · (1-K/B²) = 91.187 GeV
   W:     m_W = m_Z · √((S-3)/S) · (n²S+1)/(n²S) · (1+1/((nL)²+nS)) = 80.373 GeV

   Reference: digest.md §8, bld.py boson_masses
-/

import Mathlib.Tactic.NormNum
import BLD.Constants

namespace BLD.BosonMasses

-- ═══════════════════════════════════════════════════════════
-- Higgs mass rational factors
-- m_H = (v/2) · (1 + 1/B) · (1 − 1/(BL))
-- ═══════════════════════════════════════════════════════════

/-- Higgs factor 1: 1 + 1/B = 57/56. -/
theorem higgs_factor_1 : 1 + 1 / (BLD.B : ℚ) = 57 / 56 := by
  norm_num [BLD.B]

/-- Higgs factor 2: 1 − 1/(BL) = 1119/1120. -/
theorem higgs_factor_2 : 1 - 1 / ((BLD.B : ℚ) * BLD.L) = 1119 / 1120 := by
  norm_num [BLD.B, BLD.L]

-- ═══════════════════════════════════════════════════════════
-- Z boson mass rational factors
-- m_Z = (v/e) · (α⁻¹/(α⁻¹−1)) · (1 − K/B²)
-- ═══════════════════════════════════════════════════════════

/-- Z factor 1: α⁻¹/(α⁻¹−1) = 137/136.
    Uses the integer part of the fine structure constant. -/
theorem Z_factor_1 : (137 : ℚ) / (137 - 1) = 137 / 136 := by norm_num

/-- Z factor 2: 1 − K/B² = 1567/1568.
    Boundary quantum correction to the Z mass. -/
theorem Z_factor_2 : 1 - (BLD.K : ℚ) / BLD.B ^ 2 = 1567 / 1568 := by
  norm_num [BLD.K, BLD.B]

-- ═══════════════════════════════════════════════════════════
-- W boson mass rational factors
-- m_W = m_Z · √((S−3)/S) · (n²S+1)/(n²S) · (1 + 1/((nL)²+nS))
-- ═══════════════════════════════════════════════════════════

/-- W/Z mass-squared ratio (tree level): (S−3)/S = 10/13.
    The square root √(10/13) gives the W/Z mass ratio. -/
theorem W_tree_ratio_sq : ((BLD.S : ℚ) - 3) / BLD.S = 10 / 13 := by
  norm_num [BLD.S]

/-- W correction 1: (n²S+1)/(n²S) = 209/208.
    Shares the n²S = 208 structure with the muon ratio. -/
theorem W_correction_1 :
    (BLD.n ^ 2 * BLD.S + 1 : ℚ) / (BLD.n ^ 2 * BLD.S) = 209 / 208 := by
  norm_num [BLD.n, BLD.S]

/-- W correction 2: 1 + 1/((nL)²+nS) = 6453/6452.
    Shares the (nL)²+nS = 6452 structure with the muon ratio (opposite sign). -/
theorem W_correction_2 :
    1 + 1 / ((BLD.n * BLD.L : ℚ) ^ 2 + BLD.n * BLD.S) = 6453 / 6452 := by
  norm_num [BLD.n, BLD.L, BLD.S]

/-- W-muon shared denominator: (nL)² + nS = 6452.
    W uses +1/6452 (incomplete detection), muon uses −1/6452 (confinement). -/
theorem W_muon_shared_denominator :
    (BLD.n * BLD.L : ℚ) ^ 2 + BLD.n * BLD.S = 6452 := by
  norm_num [BLD.n, BLD.L, BLD.S]

end BLD.BosonMasses
