/- BLD Calculus — Observer Corrections

   The K/X correction principle: every measurement adds a traversal
   cost K/X where K=2 (observation cost) and X is the structure
   being traversed.

   Key insight: primordial values are integers, decimals come from
   observation costs. α⁻¹ = 137 + corrections.

   Reference: observer-correction.md, detection-structure.md
-/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import BLD.Constants

namespace BLD.Observer

-- ═══════════════════════════════════════════════════════════
-- The K/X correction principle
-- ═══════════════════════════════════════════════════════════

/-- A K/X correction: observation cost K distributed over structure X.
    Sign: positive if something escapes detection, negative if all detected. -/
structure KXCorrection where
  X : ℚ        -- structure being traversed
  sign : Int   -- +1 (escape) or -1 (complete detection)
  hX : X ≠ 0

/-- The correction value: sign × K/X. -/
def KXCorrection.value (c : KXCorrection) : ℚ :=
  c.sign * (BLD.K : ℚ) / c.X

-- ═══════════════════════════════════════════════════════════
-- Detection channel X values (from BLD constants)
-- ═══════════════════════════════════════════════════════════

/-- EM channel: X = B = 56 (detector couples to boundary). -/
theorem X_em : (BLD.B : ℚ) = 56 := by norm_num [BLD.B]

/-- Strong channel: X = n + L = 24 (detector couples to geometry). -/
theorem X_strong : (BLD.n : ℚ) + BLD.L = 24 := by norm_num [BLD.n, BLD.L]

/-- Combined channel: X = n × L = 80 (full observer geometry). -/
theorem X_combined : (BLD.n : ℚ) * BLD.L = 80 := by norm_num [BLD.n, BLD.L]

/-- W channel: X = B + L = 76 (EM + neutrino escape). -/
theorem X_w_channel : (BLD.B : ℚ) + BLD.L = 76 := by norm_num [BLD.B, BLD.L]

-- ═══════════════════════════════════════════════════════════
-- Primordial integers
-- ═══════════════════════════════════════════════════════════

/-- μ/e primordial = n²S = 208. Observed ≈ 206.77 after K/X corrections. -/
theorem mu_over_e_primordial : BLD.n ^ 2 * BLD.S = 208 := by decide

/-- τ/μ primordial = S + n = 17. Observed ≈ 16.82 after K/X corrections. -/
theorem tau_over_mu_primordial : BLD.S + BLD.n = 17 := by decide

/-- α⁻¹ primordial = nL + B + 1 = 137. Observed ≈ 137.036 after corrections. -/
theorem alpha_inv_primordial : BLD.n * BLD.L + BLD.B + 1 = 137 := by decide

-- ═══════════════════════════════════════════════════════════
-- α⁻¹ correction terms (rational part)
-- Reference: bld.py alpha_inv_full, observer-correction.md §4
-- ═══════════════════════════════════════════════════════════

/-- First correction: K/B = 2/56 = 1/28 ≈ 0.03571.
    Boundary quantum: observation touches B boundary modes. -/
theorem alpha_correction_1 : (BLD.K : ℚ) / BLD.B = 1 / 28 := by
  norm_num [BLD.K, BLD.B]

/-- Second correction: n/((n-1) × nL × B) = 4/(3 × 80 × 56) = 1/3360 ≈ 0.000298.
    Outbound spatial: traversal through nL geometry, penalized by (n-1). -/
theorem alpha_correction_2 :
    (BLD.n : ℚ) / ((BLD.n - 1) * (BLD.n * BLD.L) * BLD.B) = 1 / 3360 := by
  norm_num [BLD.n, BLD.L, BLD.B]

/-- Third correction: -(n-1)/(nL² × B) = -3/(6400 × 56) = -1/119467.
    Return spatial: coming back through geometry. -/
theorem alpha_correction_3 :
    -((BLD.n : ℚ) - 1) / ((BLD.n * BLD.L) ^ 2 * BLD.B) = -3 / 358400 := by
  norm_num [BLD.n, BLD.L, BLD.B]

/-- Fourth correction: -1/(nL × B²) = -1/(80 × 3136) = -1/250880.
    Return boundary: coming back through boundary structure. -/
theorem alpha_correction_4 :
    -(1 : ℚ) / ((BLD.n * BLD.L) * BLD.B ^ 2) = -1 / 250880 := by
  norm_num [BLD.n, BLD.L, BLD.B]

/-- Sum of all four rational corrections.
    Total rational correction ≈ 0.035714 + 0.000298 - 0.000008 - 0.000004
                               ≈ 0.036000.
    The remaining ~0.000 comes from the accumulated (transcendental) term. -/
theorem alpha_rational_corrections :
    (BLD.K : ℚ) / BLD.B
    + BLD.n / ((BLD.n - 1) * (BLD.n * BLD.L) * BLD.B)
    - (BLD.n - 1) / ((BLD.n * BLD.L) ^ 2 * BLD.B)
    - 1 / ((BLD.n * BLD.L) * BLD.B ^ 2)
    = 270947 / 7526400 := by
  norm_num [BLD.K, BLD.n, BLD.L, BLD.B]

-- ═══════════════════════════════════════════════════════════
-- Correction ordering (larger corrections dominate)
-- ═══════════════════════════════════════════════════════════

/-- K/B is the dominant correction (> 0.03). -/
theorem correction_1_dominant : (1 : ℚ) / 28 > 1 / 100 := by norm_num

/-- The spatial correction is two orders smaller. -/
theorem correction_2_small : (1 : ℚ) / 3360 < 1 / 1000 := by norm_num

/-- Return corrections are negligible (< 10⁻⁵). -/
theorem correction_3_negligible : (3 : ℚ) / 358400 < 1 / 100000 := by norm_num

-- ═══════════════════════════════════════════════════════════
-- K/X correction universality
-- ═══════════════════════════════════════════════════════════

/-- The K/X principle: all Higgs coupling corrections are K/X
    for different X values. They share the same numerator K=2. -/
theorem kx_universality :
    (BLD.K : ℚ) / BLD.B = 1 / 28 ∧
    BLD.K / (BLD.B + BLD.L) = 1 / 38 ∧
    BLD.K / (BLD.n + BLD.L) = 1 / 12 ∧
    BLD.K / (BLD.n * BLD.L) = 1 / 40 := by
  constructor <;> [skip; constructor <;> [skip; constructor]] <;>
    norm_num [BLD.K, BLD.B, BLD.L, BLD.n]

/-- Correction hierarchy: K/X decreases as X increases.
    B < B+L < n×L, so K/B > K/(B+L) > K/(nL). -/
theorem correction_hierarchy :
    (1 : ℚ) / 28 > 1 / 38 ∧ (1 : ℚ) / 38 > 1 / 40 := by
  constructor <;> norm_num

end BLD.Observer
