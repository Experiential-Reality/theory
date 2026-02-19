/- BLD Calculus — σ₈ and Baryon Asymmetry

   The matter clustering amplitude σ₈ and baryon asymmetry
   from BLD constants.

   Reference: cosmology/sigma8-derivation.md
-/

import Mathlib.Tactic.NormNum
import BLD.Constants

namespace BLD.Cosmology

/-- σ₈ primordial: L/(n+L) = 20/24 = 5/6 ≈ 0.833. -/
theorem sigma8_primordial : (BLD.L : ℚ) / (BLD.n + BLD.L) = 5 / 6 := by
  norm_num [BLD.L, BLD.n]

/-- σ₈ CMB-corrected: (L/(n+L))(1 - K/(nL)) = 13/16 = 0.8125.
    (observed: 0.811 ± 0.006). -/
theorem sigma8_CMB :
    (BLD.L : ℚ) / (BLD.n + BLD.L) * (1 - BLD.K / (BLD.n * BLD.L)) = 13 / 16 := by
  norm_num [BLD.L, BLD.n, BLD.K]

/-- Baryon asymmetry (rational part):
    η = (K/B)(1/L⁶)(S/(S-1)) = 13/21504000000 ≈ 6.046 × 10⁻¹⁰.
    (observed: (6.1 ± 0.04) × 10⁻¹⁰). -/
theorem baryon_asymmetry_rational :
    (BLD.K : ℚ) / BLD.B * (1 / BLD.L ^ 6) * (BLD.S / (BLD.S - 1))
    = 13 / 21504000000 := by
  norm_num [BLD.K, BLD.B, BLD.L, BLD.S]

/-- Lorentz dilution: (1/L)⁶ = 1/64000000.
    Six powers of link suppression in the baryon asymmetry. -/
theorem lorentz_dilution : (1 / BLD.L : ℚ) ^ 6 = 1 / 64000000 := by
  norm_num [BLD.L]

/-- σ₈ local: σ₈(CMB) × (1 − K/(2L)) = 13/16 × 19/20 = 247/320 ≈ 0.772.
    (observed: 0.77 ± 0.02). -/
theorem sigma8_local :
    (13 : ℚ) / 16 * (1 - BLD.K / (2 * BLD.L)) = 247 / 320 := by
  norm_num [BLD.K, BLD.L]

/-- σ₈ local from primordial: the full three-step chain.
    σ₈(local) = (L/(n+L)) × (1−K/(nL)) × (1−K/(2L)) = 247/320. -/
theorem sigma8_local_full :
    (BLD.L : ℚ) / (BLD.n + BLD.L)
    * (1 - BLD.K / (BLD.n * BLD.L))
    * (1 - BLD.K / (2 * BLD.L)) = 247 / 320 := by
  norm_num [BLD.L, BLD.n, BLD.K]

/-- Baryon asymmetry exponent: n(n−1)/2 = 6 = dim(SO(3,1)).
    The (1/L)⁶ suppression uses the Lorentz group dimension. -/
theorem baryon_lorentz_exponent : BLD.n * (BLD.n - 1) / 2 = 6 := by decide

end BLD.Cosmology
