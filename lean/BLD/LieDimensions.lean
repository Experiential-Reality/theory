/- BLD Calculus — Lie Algebra Dimensions and Casimir Bridge

   Dimensions of all 9 Dynkin types, the Casimir-curvature bridge
   uniqueness theorem, and BLD-significant identities.

   Reference: lie-correspondence.md, e7-derivation.md
-/

import BLD.Lie.Cartan.Defs
import BLD.Constants

namespace BLD.Lie.LieDimensions

open Cartan

-- ═══════════════════════════════════════════════════════════
-- Exceptional algebra dimensions
-- ═══════════════════════════════════════════════════════════

theorem dim_G2 : DynkinType.G₂.dim = 14 := by rfl
theorem dim_F4 : DynkinType.F₄.dim = 52 := by rfl
theorem dim_E6 : DynkinType.E₆.dim = 78 := by rfl
theorem dim_E7 : DynkinType.E₇.dim = 133 := by rfl
theorem dim_E8 : DynkinType.E₈.dim = 248 := by rfl

-- ═══════════════════════════════════════════════════════════
-- Classical algebras at rank 4 (BLD rank)
-- ═══════════════════════════════════════════════════════════

theorem dim_A4 : (DynkinType.A 4 (by omega)).dim = 24 := by rfl
theorem dim_B4 : (DynkinType.B 4 (by omega)).dim = 36 := by rfl
theorem dim_C4 : (DynkinType.C 4 (by omega)).dim = 36 := by rfl
theorem dim_D4 : (DynkinType.D 4 (by omega)).dim = 28 := by rfl

-- ═══════════════════════════════════════════════════════════
-- BLD-significant identities
-- ═══════════════════════════════════════════════════════════

/-- F₄ dim = B - n: the exceptional algebra dimension equals
    the boundary count minus spacetime dimension. -/
theorem F4_eq_B_minus_n : DynkinType.F₄.dim = BLD.B - BLD.n := by decide

/-- E₇ dim = rank + 2 × positive roots: 133 = 7 + 2 × 63. -/
theorem E7_rank_plus_2roots : DynkinType.E₇.dim = 7 + 2 * 63 := by decide

-- ═══════════════════════════════════════════════════════════
-- Casimir-curvature bridge
-- ═══════════════════════════════════════════════════════════

/-- The Casimir bridge equation 8(d-1) = d(d-1) has exactly two solutions:
    d = 1 (trivial) or d = 8 (octonions/spacetime).
    This selects spacetime dimension from the equality of
    Casimir eigenvalue and scalar curvature. -/
theorem casimir_bridge_uniqueness (d : ℕ) (hd : 1 ≤ d)
    (h : 8 * (d - 1) = d * (d - 1)) :
    d = 1 ∨ d = 8 := by
  rcases eq_or_lt_of_le hd with rfl | hlt
  · left; rfl
  · right
    have hpos : 0 < d - 1 := by omega
    have := Nat.eq_of_mul_eq_mul_right hpos h
    omega

/-- D₄ Casimir: dim(D₄)/rank = 28/4 = 7 = C₂(vector representation). -/
theorem D4_casimir : (DynkinType.D 4 (by omega)).dim / 4 = 7 := by decide

/-- Generation constant: S = 2C₂ - 1 = 2×7 - 1 = 13. -/
theorem generation_from_casimir : 2 * 7 - 1 = BLD.S := by decide

/-- Boundary/spacetime ratio: B/n = 2C₂ = 14. -/
theorem boundary_casimir_ratio : BLD.B / BLD.n = 2 * 7 := by decide

-- ═══════════════════════════════════════════════════════════
-- Exceptional algebra BLD formulas (paper §588-599)
-- ═══════════════════════════════════════════════════════════

/-- G₂ = K × Im(O): 2 × 7 = 14. -/
theorem G2_eq_K_times_ImO : 2 * 7 = DynkinType.G₂.dim := by decide

/-- E₆ = F₄ + fund(F₄): 52 + 26 = 78. -/
theorem E6_eq_F4_plus_fund : 52 + 26 = DynkinType.E₆.dim := by decide

/-- E₇ Tits decomposition: Der(H) + F₄ + Im(H)⊗J₃(O)₀ = 3 + 52 + 78 = 133. -/
theorem E7_tits_decomposition : 3 + 52 + 78 = DynkinType.E₇.dim := by decide

/-- E₈ = E₇ + fund(E₇) + remainder: 133 + 56 + 59 = 248. -/
theorem E8_eq_E7_plus_fund : 133 + 56 + 59 = DynkinType.E₈.dim := by decide

-- ═══════════════════════════════════════════════════════════
-- Division algebra gauge dimensions (paper §842)
-- ═══════════════════════════════════════════════════════════

/-- SM gauge dimension: ℝ(0) + ℂ(1) + ℍ(3) + 𝕆(8) = 12. -/
theorem sm_gauge_dim : 0 + 1 + 3 + 8 = 12 := by decide

/-- Lorentz group dimension: n(n-1)/2 = 6. -/
theorem lorentz_dim : BLD.n * (BLD.n - 1) / 2 = 6 := by decide

/-- E₈ from BLD constants: n(B+n+K) = 4 × 62 = 248 = dim(E₈). -/
theorem E8_from_BLD : BLD.n * (BLD.B + BLD.n + BLD.K) = DynkinType.E₈.dim := by decide

/-- E₈ branching E₇ × SU(2): 133 + 3 + 2×56 = 248. -/
theorem E8_branching_E7_SU2 :
    DynkinType.E₇.dim + 3 + 2 * 56 = DynkinType.E₈.dim := by decide

/-- Fund(E₇) = B: fundamental representation dimension equals boundary count. -/
theorem fund_E7_eq_B : 56 = BLD.B := by decide

/-- E₆ from BLD constants: B + L + K = 56 + 20 + 2 = 78 = dim(E₆). -/
theorem E6_from_BLD : BLD.B + BLD.L + BLD.K = DynkinType.E₆.dim := by decide

end BLD.Lie.LieDimensions
