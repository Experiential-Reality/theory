/- BLD Calculus — Muon g-2 Anomaly

   Muon anomalous magnetic moment from BLD constants.
   Falsification-table prediction: a_μ ≈ 250 × 10⁻¹¹.

   Primordial: K²/(α⁻¹² × (nL)² × S) = 1/390395200
   Detection:  (B+L)/(B+L+K) = 38/39
   Observed:   primordial × detection = 19/7612706400

   Reference: particle-physics/muon-g2.md, bld-paper §1942-1943
-/

import Mathlib.Tactic.NormNum
import BLD.Constants

namespace BLD.MuonAnomaly

/-- Muon g-2 primordial: K²/(α⁻¹² × (nL)² × S) = 1/390395200.
    ≈ 256 × 10⁻¹¹. -/
theorem muon_g2_primordial :
    (BLD.K : ℚ) ^ 2 / ((BLD.n * BLD.L + BLD.B + 1) ^ 2
    * (BLD.n * BLD.L) ^ 2 * BLD.S) = 1 / 390395200 := by
  norm_num [BLD.K, BLD.n, BLD.L, BLD.B, BLD.S]

/-- Detection correction: (B+L)/(B+L+K) = 76/78 = 38/39.
    Neutrino escape channel correction. -/
theorem muon_g2_detection :
    ((BLD.B + BLD.L : ℚ)) / (BLD.B + BLD.L + BLD.K) = 38 / 39 := by
  norm_num [BLD.B, BLD.L, BLD.K]

/-- Observed muon g-2: primordial × detection = 19/7612706400.
    ≈ 250 × 10⁻¹¹ (observed: (251.1 ± 5.9) × 10⁻¹¹). -/
theorem muon_g2_observed :
    (BLD.K : ℚ) ^ 2 * (BLD.B + BLD.L) /
    ((BLD.n * BLD.L + BLD.B + 1) ^ 2
    * (BLD.n * BLD.L) ^ 2 * BLD.S * (BLD.B + BLD.L + BLD.K))
    = 19 / 7612706400 := by
  norm_num [BLD.K, BLD.n, BLD.L, BLD.B, BLD.S]

end BLD.MuonAnomaly
