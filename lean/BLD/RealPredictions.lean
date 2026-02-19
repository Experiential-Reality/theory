/- BLD Calculus — Real-Valued Predictions

   Predictions requiring transcendental functions (π, e, √) stated as
   exact symbolic formulas over ℝ.

   Tier 1 (algebraic √): Fully proved — Cabibbo angle, W/Z ratio, Planck √
   Tier 2 (symbolic): Exact definitions using Real.pi, Real.exp, Real.sqrt
     with all rational factors verified by norm_num.

   Reference: docs/mathematics/digest.md §5–15
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Sqrt
import BLD.Constants

noncomputable section

namespace BLD.RealPredictions

open Real

-- ═══════════════════════════════════════════════════════════
-- Section 1: Algebraic √ cases (Tier 1 — fully proved)
-- ═══════════════════════════════════════════════════════════

/-- **Cabibbo angle squared**: sin²(arctan(3/13)) = 9/178.
    Purely rational after squaring — no √ needed.
    (observed |V_us|² = 0.0503, predicted 9/178 = 0.05056). -/
theorem cabibbo_angle_sq :
    sin (arctan ((3 : ℝ) / 13)) ^ 2 = 9 / 178 := by
  rw [sin_sq_arctan]; norm_num

/-- **Cabibbo angle exact**: |V_us| = sin(arctan((n-1)/S)) = 3/√178.
    From BLD: (n-1)/S = 3/13, and sin(arctan(x)) = x/√(1+x²).
    (observed: 0.2243 ± 0.0005, predicted: 3/√178 ≈ 0.2249). -/
theorem cabibbo_angle :
    sin (arctan ((3 : ℝ) / 13)) = 3 / sqrt 178 := by
  rw [sin_arctan]
  rw [show (1 : ℝ) + (3 / 13) ^ 2 = 178 / (13 : ℝ) ^ 2 from by norm_num]
  rw [sqrt_div (by norm_num : (0 : ℝ) ≤ 178)]
  rw [sqrt_sq (by norm_num : (0 : ℝ) ≤ 13)]
  have hsq : sqrt (178 : ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr (by norm_num))
  field_simp

/-- **W/Z mass ratio — tree level**: (S-3)/S = 10/13.
    The Weinberg angle structure from BLD constants. -/
theorem W_Z_tree_level : ((BLD.S : ℚ) - 3) / BLD.S = 10 / 13 := by
  norm_num [BLD.S]

/-- **W/Z correction 1**: (n²S+1)/(n²S) = 209/208. -/
theorem W_correction_1 :
    ((BLD.n : ℚ) ^ 2 * BLD.S + 1) / (BLD.n ^ 2 * BLD.S) = 209 / 208 := by
  norm_num [BLD.n, BLD.S]

/-- **W/Z correction 2**: ((nL)²+nS+1)/((nL)²+nS) = 6453/6452. -/
theorem W_correction_2 :
    (((BLD.n : ℚ) * BLD.L) ^ 2 + BLD.n * BLD.S + 1) /
    ((BLD.n * BLD.L) ^ 2 + BLD.n * BLD.S) = 6453 / 6452 := by
  norm_num [BLD.n, BLD.L, BLD.S]

/-- **W/Z ratio squared** is purely rational (√ squares away):
    (m_W/m_Z)² = (10/13) × (209/208)² × (6453/6452)². -/
theorem W_Z_ratio_sq :
    (10 : ℝ) / 13 * ((209 : ℝ) / 208) ^ 2 * ((6453 : ℝ) / 6452) ^ 2 =
    (sqrt ((10 : ℝ) / 13) * (209 / 208) * (6453 / 6452)) ^ 2 := by
  rw [mul_pow, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 10 / 13)]

/-- **Planck mass √ factor**: (√(5/14))² = 5/14.
    The capacity ratio √(5/(S+1)) in the Planck cascade. -/
theorem planck_sqrt_sq : sqrt ((5 : ℝ) / 14) ^ 2 = 5 / 14 :=
  sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 14)

/-- Planck cascade exponent: B/2 − K = n + L + K = 26.
    The λ² cascade runs for 13 steps (λ² = 1/L, so L^13). -/
theorem planck_exponent : BLD.n + BLD.L + BLD.K = 26 := by decide

-- ═══════════════════════════════════════════════════════════
-- Section 2: Symbolic formulas (Tier 2)
-- ═══════════════════════════════════════════════════════════

/-- **τ/μ mass ratio** = 2πe × (207/208) × (79/80) × (521/520).
    Primordial integer: S + n = 17. Continuous limit: 2πe ≈ 17.079.
    (observed: 16.8171 ± 0.0012, predicted ≈ 16.8172). -/
def tau_over_mu : ℝ :=
  2 * π * exp 1 * (207 / 208) * (79 / 80) * (521 / 520)

/-- Rational part of τ/μ verified from BLD constants. -/
theorem tau_over_mu_correction_1 :
    ((BLD.n : ℚ) ^ 2 * BLD.S - 1) / (BLD.n ^ 2 * BLD.S) = 207 / 208 := by
  norm_num [BLD.n, BLD.S]

theorem tau_over_mu_correction_2 :
    ((BLD.n : ℚ) * BLD.L - 1) / (BLD.n * BLD.L) = 79 / 80 := by
  norm_num [BLD.n, BLD.L]

theorem tau_over_mu_correction_3 :
    (1 + 2 / ((BLD.n : ℚ) * BLD.L * BLD.S)) =  521 / 520 := by
  norm_num [BLD.n, BLD.L, BLD.S]

/-- **α⁻¹ full formula** including the transcendental e² correction.
    The rational terms give 137.035999..., the e² term subtracts ~3.7×10⁻⁷.
    (observed: 137.035999177 ± 0.000000021). -/
def alpha_inv_full : ℝ :=
  137 + (1 : ℝ) / 28 + 1 / 3360 - 3 / 358400 - 1 / 250880
  - exp 1 ^ 2 * 120 / (119 * 6400 * 3136)

/-- Rational part of α⁻¹: sum of integer + 4 rational K/X corrections. -/
theorem alpha_inv_rational :
    (137 : ℚ) + 1 / 28 + 1 / 3360 - 3 / 358400 - 1 / 250880
    = 1031387747 / 7526400 := by norm_num

/-- The e² coefficient in α⁻¹: (2B+n+K+2)/((2B+n+K+1)·(nL)²·B²) = 120/(119·6400·3136). -/
theorem alpha_e2_coefficient :
    (2 * BLD.B + BLD.n + BLD.K + 2 : ℚ) /
    ((2 * BLD.B + BLD.n + BLD.K + 1) * (BLD.n * BLD.L) ^ 2 * BLD.B ^ 2) =
    120 / (119 * 6400 * 3136) := by
  norm_num [BLD.B, BLD.n, BLD.K, BLD.L]

/-- **Higgs mass**: m_H = (v/2) × (57/56) × (1119/1120).
    (observed: 125.20 ± 0.11 GeV). -/
def higgs_mass (v : ℝ) : ℝ :=
  v / 2 * (57 / 56) * (1119 / 1120)

theorem higgs_factor_1 : 1 + 1 / (BLD.B : ℚ) = 57 / 56 := by
  norm_num [BLD.B]

theorem higgs_factor_2 : 1 - 1 / ((BLD.B : ℚ) * BLD.L) = 1119 / 1120 := by
  norm_num [BLD.B, BLD.L]

/-- **Z boson mass**: m_Z = (v/e) × (137/136) × (1567/1568).
    The factor v/e uses Euler's number e = exp(1).
    (observed: 91.1876 ± 0.0021 GeV). -/
def Z_mass (v : ℝ) : ℝ :=
  v / exp 1 * (137 / 136) * (1567 / 1568)

theorem Z_factor_1 : ((BLD.n : ℚ) * BLD.L + BLD.B + 1) /
    (BLD.n * BLD.L + BLD.B) = 137 / 136 := by
  norm_num [BLD.n, BLD.L, BLD.B]

theorem Z_factor_2 : 1 - BLD.K / (BLD.B : ℚ) ^ 2 = 1567 / 1568 := by
  norm_num [BLD.K, BLD.B]

/-- **W boson mass**: m_W = m_Z × √(10/13) × (209/208) × (6453/6452).
    Uses √((S-3)/S) which is irrational.
    (observed: 80.377 ± 0.012 GeV). -/
def W_mass (m_Z : ℝ) : ℝ :=
  m_Z * sqrt (10 / 13) * (209 / 208) * (6453 / 6452)

/-- **Top quark mass**: m_t = v/√2 × (103/104).
    v/√K where K = 2. Top decays before confining → couples directly to VEV.
    (observed: 172.69 ± 0.30 GeV). -/
def top_mass (v : ℝ) : ℝ :=
  v / sqrt 2 * (103 / 104)

theorem top_correction : 1 - BLD.K / ((BLD.n : ℚ) ^ 2 * BLD.S) = 103 / 104 := by
  norm_num [BLD.K, BLD.n, BLD.S]

/-- **Planck mass**: M_P = v × 20¹³ × √(5/14) × (79/78) × (1 + 6/250880).
    Cascade: v → M_P via L^13 suppression with capacity and observer corrections.
    (observed: 1.22091 × 10¹⁹ GeV). -/
def planck_mass (v : ℝ) : ℝ :=
  v * (20 : ℝ) ^ 13 * sqrt (5 / 14) * (79 / 78) * (1 + 6 / 250880)

theorem planck_observer : ((BLD.n : ℚ) * BLD.L - BLD.K + 1) /
    (BLD.n * BLD.L - BLD.K) = 79 / 78 := by
  norm_num [BLD.n, BLD.L, BLD.K]

theorem planck_fine_correction :
    1 + (BLD.K : ℚ) * 3 / (BLD.n * BLD.L * BLD.B ^ 2) = 125443 / 125440 := by
  norm_num [BLD.K, BLD.n, BLD.L, BLD.B]

/-- Feigenbaum intermediate: X = n + K + K/n + 1/L = 131/20. -/
def feigenbaum_X : ℝ := (131 : ℝ) / 20

theorem feigenbaum_X_from_BLD :
    (BLD.n : ℚ) + BLD.K + BLD.K / BLD.n + 1 / BLD.L = 131 / 20 := by
  norm_num [BLD.n, BLD.K, BLD.L]

/-- **Feigenbaum δ**: √(L + K − K²/L + 1/exp(X)).
    The rational part under the √: L + K − K²/L = 20 + 2 − 1/5 = 109/5 = 21.8.
    (observed: 4.6692016091, predicted ≈ 4.66920). -/
def feigenbaum_delta : ℝ :=
  sqrt (109 / 5 + 1 / exp feigenbaum_X)

theorem feigenbaum_delta_rational :
    (BLD.L : ℚ) + BLD.K - BLD.K ^ 2 / BLD.L = 109 / 5 := by
  norm_num [BLD.L, BLD.K]

/-- Without the transcendental correction: √(109/5) ≈ 4.6690.
    The 1/exp(X) ≈ 0.00143 correction brings it to ≈ 4.66920. -/
theorem feigenbaum_delta_approx_sq :
    sqrt ((109 : ℝ) / 5) ^ 2 = 109 / 5 :=
  sq_sqrt (by norm_num : (0 : ℝ) ≤ 109 / 5)

/-- **Feigenbaum α**: K + 1/K + 1/((n+K)·B) − 1/((L+1−1/n²)·exp(X)).
    Rational primordial: K + 1/K = 5/2 = 2.5.
    (observed: 2.5029078750, predicted ≈ 2.50291). -/
def feigenbaum_alpha : ℝ :=
  5 / 2 + 1 / (6 * 56) - 1 / ((20 + 1 - (1 : ℝ) / 16) * exp feigenbaum_X)

theorem feigenbaum_alpha_rational :
    (BLD.K : ℚ) + 1 / BLD.K + 1 / ((BLD.n + BLD.K) * BLD.B) = 841 / 336 := by
  norm_num [BLD.K, BLD.n, BLD.B]

theorem feigenbaum_alpha_denom :
    (BLD.L : ℚ) + 1 - 1 / BLD.n ^ 2 = 335 / 16 := by
  norm_num [BLD.L, BLD.n]

end BLD.RealPredictions

end -- noncomputable section
