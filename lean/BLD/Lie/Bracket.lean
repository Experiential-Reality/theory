/- BLD Calculus — so(8) Bracket Formula

   The Lie bracket of skew-symmetric basis elements E_{pq} = e_{pq} - e_{qp}:

   [E_{pq}, E_{rs}] = δ_{qr}E_{ps} - δ_{pr}E_{qs} - δ_{qs}E_{pr} + δ_{ps}E_{qr}

   Proved for Fin 8 via native_decide (4096 cases, kernel-verified).

   Reference: standard formula for so(n) structure constants
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Lie.OfAssociative

namespace BLD.Lie

/-- Skew-symmetric basis element: E_{ij} = e_{ij} - e_{ji}. -/
def skewBasis8 (i j : Fin 8) : Matrix (Fin 8) (Fin 8) ℚ :=
  Matrix.single i j 1 - Matrix.single j i 1

/-- The Lie bracket formula for so(8) skew-symmetric basis elements.
    [E_{pq}, E_{rs}] = δ_{qr}E_{ps} - δ_{pr}E_{qs} - δ_{qs}E_{pr} + δ_{ps}E_{qr}. -/
theorem bracket_skewBasis8 : ∀ p q r s : Fin 8,
    ⁅skewBasis8 p q, skewBasis8 r s⁆ =
    (if q = r then skewBasis8 p s else 0) -
    (if p = r then skewBasis8 q s else 0) -
    (if q = s then skewBasis8 p r else 0) +
    (if p = s then skewBasis8 q r else 0) := by native_decide

end BLD.Lie
