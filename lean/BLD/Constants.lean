/- BLD Calculus — Structural Constants

   The five fundamental constants: B=56, L=20, n=4, K=2, S=13.
   All constant identities proven by the `decide` tactic
   (kernel-verified arithmetic).

   Reference: bld.py lines 23-28, bld-calculus.md Proposition 8.5
-/

import BLD.Basic
import BLD.Cardinality

namespace BLD

/-- Boundary count: 2 × dim(Spin(8)) = 2 × 28. -/
def B : Nat := 56

/-- Link count: Riemann tensor components = n²(n²-1)/12. -/
def L : Nat := 20

/-- Spacetime dimension: from octonion reference fixing. -/
def n : Nat := 4

/-- Observation cost: bidirectional traversal (Killing form). -/
def K : Nat := 2

/-- Structural intervals: (B - n) / n. -/
def S : Nat := 13

-- ═══════════════════════════════════════════════════════════
-- Constant identities (five equations that determine K=2)
-- Reference: test_predictions.py::test_constant_identities
-- ═══════════════════════════════════════════════════════════

theorem S_def : S = (B - n) / n := by decide
theorem K_sq_eq_n : K ^ 2 = n := by decide
theorem L_formula : L = n ^ 2 * (n ^ 2 - 1) / 12 := by decide
theorem S_formula : S = K ^ 2 + (n - 1) ^ 2 := by decide
theorem B_formula : B = n * (S + 1) := by decide

-- ═══════════════════════════════════════════════════════════
-- Mode count: α⁻¹ = 137
-- Reference: bld-calculus.md Proposition 8.5
-- ═══════════════════════════════════════════════════════════

/-- α⁻¹ = n×L + B + 1 = 80 + 56 + 1 = 137. -/
theorem alpha_inv : n * L + B + 1 = 137 := by decide

/-- The three mode count components. -/
theorem mode_count_components :
    n * L = 80 ∧ B = 56 ∧ (1 : Nat) = 1 := by decide

-- ═══════════════════════════════════════════════════════════
-- Spin(8) structure
-- Reference: test_structure.py::test_spin8_boundary
-- ═══════════════════════════════════════════════════════════

/-- dim(so(8)) = 8×7/2 = 28. -/
theorem dim_so8 : 8 * 7 / 2 = 28 := by decide

/-- B = 2 × dim(so(8)). -/
theorem B_eq_2_dim_so8 : B = 2 * (8 * 7 / 2) := by decide

/-- B - K = K(n-1)³ = 54. -/
theorem boundary_capacity : B - K = K * (n - 1) ^ 3 := by decide

-- ═══════════════════════════════════════════════════════════
-- K = 2 rigidity
-- The constant system is uniquely determined by K = 2.
-- ═══════════════════════════════════════════════════════════

/-- Compute α⁻¹ from K alone using the identity chain:
    n = K², L = n²(n²-1)/12, S = K² + (n-1)², B = n(S+1).
    Then α⁻¹ = n×L + B + 1. -/
private def alpha_from_K (k : Nat) : Nat :=
  let nn := k ^ 2
  let ll := nn ^ 2 * (nn ^ 2 - 1) / 12
  let ss := k ^ 2 + (nn - 1) ^ 2
  let bb := nn * (ss + 1)
  nn * ll + bb + 1

/-- K = 1 gives α⁻¹ = 3, not 137. -/
theorem alpha_K1 : alpha_from_K 1 = 3 := by decide

/-- K = 2 gives α⁻¹ = 137. -/
theorem alpha_K2 : alpha_from_K 2 = 137 := by decide

/-- K = 3 gives α⁻¹ ≠ 137. -/
theorem alpha_K3 : alpha_from_K 3 ≠ 137 := by decide

/-- **K = 2 is the unique value in {1,...,5} giving α⁻¹ = 137.**
    The identity chain n = K², L = n²(n²-1)/12, S = K² + (n-1)²,
    B = n(S+1), α⁻¹ = n×L + B + 1 yields 137 only for K = 2. -/
theorem K2_unique : ∀ k : Nat, 1 ≤ k → k ≤ 5 →
    alpha_from_K k = 137 → k = 2 := by
  intro k hk1 hk5
  have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  obtain rfl | rfl | rfl | rfl | rfl := this <;> decide

end BLD
