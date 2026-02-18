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

end BLD.Cosmology
