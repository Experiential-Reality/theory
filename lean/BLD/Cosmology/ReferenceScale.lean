/- BLD Calculus — Reference Scale Cascade

   The cascade from Higgs VEV to Planck mass uses three
   rational factors: λ² (suppression), capacity ratio,
   and observer correction.

   Reference: cosmology/reference-scale-derivation.md, bld-paper §4.2
-/

import Mathlib.Tactic.NormNum
import BLD.Constants

namespace BLD.Cosmology

/-- Cascade suppression: λ² = K²/(nL) = 1/20.
    Each cascade step suppresses by this factor. -/
theorem cascade_lambda_sq :
    (BLD.K : ℚ) ^ 2 / (BLD.n * BLD.L) = 1 / 20 := by
  norm_num [BLD.K, BLD.n, BLD.L]

/-- Capacity ratio: (S+1)/(L/n) = 14/5.
    Link/boundary capacity ratio in the cascade. -/
theorem capacity_ratio :
    (BLD.S + 1 : ℚ) / (BLD.L / BLD.n) = 14 / 5 := by
  norm_num [BLD.S, BLD.L, BLD.n]

/-- Observer correction: (nL - K)/(nL - 1) = 78/79.
    Self-referential correction in the cascade. -/
theorem cascade_observer_correction :
    (BLD.n * BLD.L - BLD.K : ℚ) / (BLD.n * BLD.L - 1) = 78 / 79 := by
  norm_num [BLD.n, BLD.L, BLD.K]

end BLD.Cosmology
