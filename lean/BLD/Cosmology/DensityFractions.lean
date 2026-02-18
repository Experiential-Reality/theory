/- BLD Calculus — Cosmological Density Fractions

   The BLD constants predict the cosmic energy budget:
     Baryonic matter:  Ω_b  = n/(nL) = 1/20 = 5%
     Dark matter:      Ω_DM = 1/n + Kn/L² = 27/100 = 27%
     Dark energy:      Ω_Λ  = 1 - Ω_b - Ω_DM = 17/25 = 68%

   Reference: cosmology/dark-matter-derivation.md
-/

import Mathlib.Tactic.NormNum
import BLD.Constants

namespace BLD.Cosmology

/-- Baryonic matter fraction: Ω_b = n/(nL) = 1/L = 1/20 = 5%.
    (observed: 0.0493 ± 0.0006). -/
theorem omega_baryonic : (BLD.n : ℚ) / (BLD.n * BLD.L) = 1 / 20 := by
  norm_num [BLD.n, BLD.L]

/-- Dark matter fraction: Ω_DM = 1/n + Kn/L² = 27/100 = 27%.
    (observed: 0.265 ± 0.007). -/
theorem omega_DM : 1 / (BLD.n : ℚ) + BLD.K * BLD.n / BLD.L ^ 2 = 27 / 100 := by
  norm_num [BLD.n, BLD.K, BLD.L]

/-- Dark energy fraction: Ω_Λ = 1 - (n+L)/(nL) - Kn/L² = 17/25 = 68%.
    (observed: 0.685 ± 0.007). -/
theorem omega_DE :
    1 - ((BLD.n : ℚ) + BLD.L) / (BLD.n * BLD.L)
    - BLD.K * BLD.n / BLD.L ^ 2 = 17 / 25 := by
  norm_num [BLD.n, BLD.L, BLD.K]

/-- Density closure: Ω_b + Ω_DM + Ω_Λ = 1.
    The three fractions exactly sum to unity. -/
theorem density_closure : (1 : ℚ) / 20 + 27 / 100 + 17 / 25 = 1 := by norm_num

end BLD.Cosmology
