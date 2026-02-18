/- BLD Calculus — Gauge Algebra and Force Structure

   Arithmetic facts about gauge subalgebra dimensions.
   The structural proofs (explicit bracket computations, centralizer
   dimension, adjoint decomposition) require medium-difficulty
   Lie algebra computation and are noted for future work.

   FUTURE (medium — requires explicit so(8) bracket computation):
   - 12 SM generators close to u(4) = su(4) ⊕ u(1) (Pati-Salam)
   - Centralizer of su(3) in so(8) has dimension 2
   - Adjoint 28 decomposes as 16 + 6 + 6 under u(4)

   Reference: lie-theory/force-structure.md
-/

import BLD.Constants

namespace BLD.Lie.Gauge

/-- dim(su(3)) = 3² - 1 = 8 (gluon count). -/
theorem su3_dim : 3 ^ 2 - 1 = 8 := by decide

/-- dim(su(2)) = 2² - 1 = 3 (weak boson count). -/
theorem su2_dim : 2 ^ 2 - 1 = 3 := by decide

/-- dim(u(4)) = 4² = 16 (Pati-Salam gauge group). -/
theorem u4_dim : 4 ^ 2 = 16 := by decide

/-- Adjoint decomposition: 28 = 16 + 6 + 6.
    The so(8) adjoint splits as u(4) ⊕ Λ²(4) ⊕ Λ²(4̄). -/
theorem adjoint_decomposition : 16 + 6 + 6 = 28 := by decide

/-- Centralizer dimension: dim(so(8)) - dim(su(3)) - 18 = 2.
    The centralizer of su(3) in so(8) is too small for su(2). -/
theorem centralizer_too_small : 28 - 8 - 18 = 2 := by decide

/-- su(2) exceeds the centralizer: dim(su(2)) > dim(centralizer). -/
theorem su2_exceeds_centralizer : 2 < 3 := by decide

/-- Complement generators: 6 with |Y|=2/3 + 6 with |Y|=1/3 = 12. -/
theorem complement_generators : 6 + 6 = 12 := by decide

/-- Full adjoint: u(4) + complement = 16 + 12 = 28 = so(8). -/
theorem full_adjoint : 16 + 12 = 28 := by decide

end BLD.Lie.Gauge
