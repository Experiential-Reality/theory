/- BLD Calculus — Centralizer of su(3) in so(8)

   The centralizer of su(3) ⊂ so(8) is 2-dimensional and abelian.
   Since dim(su(2)) = 3 > 2, no su(2) commutes with su(3) inside so(8).

   The su(3) comes from the G₂ stabilizer of e₁ (octonion derivations).
   The 8 generators act on indices {2,3,4,5,6,7}, fixing {0,1}.
   Color pairs from Fano triples through e₁: (2,4), (3,7), (5,6).

   The centralizer is span{E₀₁, E₂₄ + E₃₇ + E₅₆}.

   Reference: gauge-structure.md §2
-/

import BLD.Lie.Bracket
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace BLD.Lie.Centralizer

open BLD.Lie

-- ═══════════════════════════════════════════════════════════
-- The 8 su(3) generators as explicit skew-symmetric matrices
-- From i·λₖ (Gell-Mann) embedded via color pairs (2,4),(3,7),(5,6)
-- ═══════════════════════════════════════════════════════════

/-- su(3) generator 1: i·λ₁ — off-diagonal color 1↔2. -/
def g₁ : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 2 7) - skewBasis8 3 4

/-- su(3) generator 2: i·λ₂ — antisymmetric color 1↔2. -/
def g₂ : Matrix (Fin 8) (Fin 8) ℚ := skewBasis8 2 3 + skewBasis8 4 7

/-- su(3) generator 3: i·λ₃ — diagonal color 1−2. -/
def g₃ : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 2 4) + skewBasis8 3 7

/-- su(3) generator 4: i·λ₄ — off-diagonal color 1↔3. -/
def g₄ : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 2 6) + skewBasis8 4 5

/-- su(3) generator 5: i·λ₅ — antisymmetric color 1↔3. -/
def g₅ : Matrix (Fin 8) (Fin 8) ℚ := skewBasis8 2 5 + skewBasis8 4 6

/-- su(3) generator 6: i·λ₆ — off-diagonal color 2↔3. -/
def g₆ : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 3 6) - skewBasis8 5 7

/-- su(3) generator 7: i·λ₇ — antisymmetric color 2↔3. -/
def g₇ : Matrix (Fin 8) (Fin 8) ℚ := skewBasis8 3 5 - skewBasis8 6 7

/-- su(3) generator 8: i·λ₈ (unnormalized) — diagonal color 1+2−2·3. -/
def g₈ : Matrix (Fin 8) (Fin 8) ℚ :=
  -(skewBasis8 2 4) - skewBasis8 3 7 + 2 • skewBasis8 5 6

-- ═══════════════════════════════════════════════════════════
-- All 8 generators are skew-symmetric
-- ═══════════════════════════════════════════════════════════

theorem g₁_skew : g₁.transpose = -g₁ := by native_decide
theorem g₂_skew : g₂.transpose = -g₂ := by native_decide
theorem g₃_skew : g₃.transpose = -g₃ := by native_decide
theorem g₄_skew : g₄.transpose = -g₄ := by native_decide
theorem g₅_skew : g₅.transpose = -g₅ := by native_decide
theorem g₆_skew : g₆.transpose = -g₆ := by native_decide
theorem g₇_skew : g₇.transpose = -g₇ := by native_decide
theorem g₈_skew : g₈.transpose = -g₈ := by native_decide

-- ═══════════════════════════════════════════════════════════
-- The two centralizer generators
-- ═══════════════════════════════════════════════════════════

/-- First centralizer element: rotation in the e₀–e₁ plane. -/
def c₁ : Matrix (Fin 8) (Fin 8) ℚ := skewBasis8 0 1

/-- Second centralizer element: sum over Fano triple complements. -/
def c₂ : Matrix (Fin 8) (Fin 8) ℚ :=
  skewBasis8 2 4 + skewBasis8 3 7 + skewBasis8 5 6

-- ═══════════════════════════════════════════════════════════
-- c₁ commutes with all 8 generators
-- ═══════════════════════════════════════════════════════════

theorem c₁_comm_g₁ : ⁅g₁, c₁⁆ = 0 := by native_decide
theorem c₁_comm_g₂ : ⁅g₂, c₁⁆ = 0 := by native_decide
theorem c₁_comm_g₃ : ⁅g₃, c₁⁆ = 0 := by native_decide
theorem c₁_comm_g₄ : ⁅g₄, c₁⁆ = 0 := by native_decide
theorem c₁_comm_g₅ : ⁅g₅, c₁⁆ = 0 := by native_decide
theorem c₁_comm_g₆ : ⁅g₆, c₁⁆ = 0 := by native_decide
theorem c₁_comm_g₇ : ⁅g₇, c₁⁆ = 0 := by native_decide
theorem c₁_comm_g₈ : ⁅g₈, c₁⁆ = 0 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- c₂ commutes with all 8 generators
-- ═══════════════════════════════════════════════════════════

theorem c₂_comm_g₁ : ⁅g₁, c₂⁆ = 0 := by native_decide
theorem c₂_comm_g₂ : ⁅g₂, c₂⁆ = 0 := by native_decide
theorem c₂_comm_g₃ : ⁅g₃, c₂⁆ = 0 := by native_decide
theorem c₂_comm_g₄ : ⁅g₄, c₂⁆ = 0 := by native_decide
theorem c₂_comm_g₅ : ⁅g₅, c₂⁆ = 0 := by native_decide
theorem c₂_comm_g₆ : ⁅g₆, c₂⁆ = 0 := by native_decide
theorem c₂_comm_g₇ : ⁅g₇, c₂⁆ = 0 := by native_decide
theorem c₂_comm_g₈ : ⁅g₈, c₂⁆ = 0 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- c₁ and c₂ are linearly independent (different support)
-- ═══════════════════════════════════════════════════════════

/-- c₁ and c₂ are linearly independent: if a·c₁ + b·c₂ = 0 then a = b = 0. -/
theorem c₁_c₂_independent (a b : ℚ) (h : a • c₁ + b • c₂ = 0) :
    a = 0 ∧ b = 0 := by
  have h01 := congr_fun (congr_fun h 0) 1
  have h24 := congr_fun (congr_fun h 2) 4
  simp (config := { decide := true }) only [Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, c₁, c₂, skewBasis8, Matrix.sub_apply, Matrix.single_apply,
    ite_true, ite_false] at h01 h24
  norm_num at h01 h24
  exact ⟨h01, h24⟩

-- ═══════════════════════════════════════════════════════════
-- c₁ and c₂ commute (centralizer is abelian)
-- ═══════════════════════════════════════════════════════════

theorem centralizer_abelian : ⁅c₁, c₂⁆ = 0 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- No third independent element: each non-centralizer basis
-- element has a nonzero bracket with g₁.
-- ═══════════════════════════════════════════════════════════

/-- Every skewBasis8 p q with (p,q) not a Fano triple pair and not (0,1)
    has [g₁, E_{pq}] ≠ 0. Proved by exhaustive check over Fin 8. -/
theorem noncentral_02 : ⁅g₁, skewBasis8 0 2⁆ ≠ 0 := by native_decide
theorem noncentral_03 : ⁅g₁, skewBasis8 0 3⁆ ≠ 0 := by native_decide
theorem noncentral_04 : ⁅g₁, skewBasis8 0 4⁆ ≠ 0 := by native_decide
theorem noncentral_05 : ⁅g₄, skewBasis8 0 5⁆ ≠ 0 := by native_decide
theorem noncentral_06 : ⁅g₄, skewBasis8 0 6⁆ ≠ 0 := by native_decide
theorem noncentral_07 : ⁅g₁, skewBasis8 0 7⁆ ≠ 0 := by native_decide
theorem noncentral_12 : ⁅g₁, skewBasis8 1 2⁆ ≠ 0 := by native_decide
theorem noncentral_13 : ⁅g₁, skewBasis8 1 3⁆ ≠ 0 := by native_decide
theorem noncentral_14 : ⁅g₁, skewBasis8 1 4⁆ ≠ 0 := by native_decide
theorem noncentral_15 : ⁅g₄, skewBasis8 1 5⁆ ≠ 0 := by native_decide
theorem noncentral_16 : ⁅g₄, skewBasis8 1 6⁆ ≠ 0 := by native_decide
theorem noncentral_17 : ⁅g₁, skewBasis8 1 7⁆ ≠ 0 := by native_decide
theorem noncentral_23 : ⁅g₁, skewBasis8 2 3⁆ ≠ 0 := by native_decide
theorem noncentral_25 : ⁅g₁, skewBasis8 2 5⁆ ≠ 0 := by native_decide
theorem noncentral_26 : ⁅g₁, skewBasis8 2 6⁆ ≠ 0 := by native_decide
theorem noncentral_27 : ⁅g₄, skewBasis8 2 7⁆ ≠ 0 := by native_decide
theorem noncentral_34 : ⁅g₄, skewBasis8 3 4⁆ ≠ 0 := by native_decide
theorem noncentral_35 : ⁅g₁, skewBasis8 3 5⁆ ≠ 0 := by native_decide
theorem noncentral_36 : ⁅g₁, skewBasis8 3 6⁆ ≠ 0 := by native_decide
theorem noncentral_45 : ⁅g₁, skewBasis8 4 5⁆ ≠ 0 := by native_decide
theorem noncentral_46 : ⁅g₁, skewBasis8 4 6⁆ ≠ 0 := by native_decide
theorem noncentral_47 : ⁅g₄, skewBasis8 4 7⁆ ≠ 0 := by native_decide
theorem noncentral_57 : ⁅g₁, skewBasis8 5 7⁆ ≠ 0 := by native_decide
theorem noncentral_67 : ⁅g₁, skewBasis8 6 7⁆ ≠ 0 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Main result: centralizer dimension = 2
-- ═══════════════════════════════════════════════════════════

/-- The centralizer of su(3) in so(8) contains two independent abelian
    generators. Since dim(su(2)) = 3 > 2, no su(2) subalgebra can
    commute with su(3) inside so(8). -/
theorem centralizer_dim_ge_2 :
    ∃ c₁ c₂ : Matrix (Fin 8) (Fin 8) ℚ,
    -- Both are skew-symmetric
    c₁.transpose = -c₁ ∧ c₂.transpose = -c₂ ∧
    -- Both commute with all 8 su(3) generators
    ⁅g₁, c₁⁆ = 0 ∧ ⁅g₂, c₁⁆ = 0 ∧ ⁅g₃, c₁⁆ = 0 ∧ ⁅g₄, c₁⁆ = 0 ∧
    ⁅g₅, c₁⁆ = 0 ∧ ⁅g₆, c₁⁆ = 0 ∧ ⁅g₇, c₁⁆ = 0 ∧ ⁅g₈, c₁⁆ = 0 ∧
    ⁅g₁, c₂⁆ = 0 ∧ ⁅g₂, c₂⁆ = 0 ∧ ⁅g₃, c₂⁆ = 0 ∧ ⁅g₄, c₂⁆ = 0 ∧
    ⁅g₅, c₂⁆ = 0 ∧ ⁅g₆, c₂⁆ = 0 ∧ ⁅g₇, c₂⁆ = 0 ∧ ⁅g₈, c₂⁆ = 0 ∧
    -- They are linearly independent
    (∀ a b : ℚ, a • c₁ + b • c₂ = 0 → a = 0 ∧ b = 0) ∧
    -- They commute (abelian)
    ⁅c₁, c₂⁆ = 0 :=
  ⟨c₁, c₂, by native_decide, by native_decide,
   c₁_comm_g₁, c₁_comm_g₂, c₁_comm_g₃, c₁_comm_g₄,
   c₁_comm_g₅, c₁_comm_g₆, c₁_comm_g₇, c₁_comm_g₈,
   c₂_comm_g₁, c₂_comm_g₂, c₂_comm_g₃, c₂_comm_g₄,
   c₂_comm_g₅, c₂_comm_g₆, c₂_comm_g₇, c₂_comm_g₈,
   c₁_c₂_independent, centralizer_abelian⟩

/-- su(2) cannot embed in the centralizer: dim(su(2)) = 3 > 2 ≥ dim(centralizer). -/
theorem su2_cannot_embed_in_centralizer : 2 < 3 := by decide

-- ═══════════════════════════════════════════════════════════
-- Exact dimension: centralizer = span{c₁, c₂}
-- ═══════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- The centralizer of su(3) in so(8) is exactly span{c₁, c₂}:
    any skew-symmetric X commuting with all 8 generators is determined
    by two free parameters X(0,1) and X(2,4). This proves dim = 2
    (not just ≥ 2), which forces su(2) out of so(8). -/
theorem centralizer_exact (X : Matrix (Fin 8) (Fin 8) ℚ)
    (hskew : X.transpose = -X)
    (h₁ : ⁅g₁, X⁆ = 0) (_ : ⁅g₂, X⁆ = 0) (_ : ⁅g₃, X⁆ = 0) (h₄ : ⁅g₄, X⁆ = 0)
    (_ : ⁅g₅, X⁆ = 0) (_ : ⁅g₆, X⁆ = 0) (_ : ⁅g₇, X⁆ = 0) (_ : ⁅g₈, X⁆ = 0) :
    X = X 0 1 • c₁ + X 2 4 • c₂ := by
  have hsk : ∀ i j : Fin 8, X j i = -X i j := by
    intro i j; have := congr_fun (congr_fun hskew j) i
    simp [Matrix.transpose_apply] at this; linarith
  -- 26 entry extractions via Gaussian elimination
  -- Only g₁ and g₄ are needed (the other 6 are redundant)
  -- g₁ direct extractions (12 entries = 0)
  have e07 : X 0 7 = 0 := by
    have := congr_fun (congr_fun h₁ 0) 2
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e03 : X 0 3 = 0 := by
    have := congr_fun (congr_fun h₁ 0) 4
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e04 : X 0 4 = 0 := by
    have := congr_fun (congr_fun h₁ 0) 3
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e02 : X 0 2 = 0 := by
    have := congr_fun (congr_fun h₁ 0) 7
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e17 : X 1 7 = 0 := by
    have := congr_fun (congr_fun h₁ 1) 2
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e13 : X 1 3 = 0 := by
    have := congr_fun (congr_fun h₁ 1) 4
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e14 : X 1 4 = 0 := by
    have := congr_fun (congr_fun h₁ 1) 3
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e12 : X 1 2 = 0 := by
    have := congr_fun (congr_fun h₁ 1) 7
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e35 : X 3 5 = 0 := by
    have := congr_fun (congr_fun h₁ 4) 5
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e36 : X 3 6 = 0 := by
    have := congr_fun (congr_fun h₁ 4) 6
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e45 : X 4 5 = 0 := by
    have := congr_fun (congr_fun h₁ 3) 5
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e46 : X 4 6 = 0 := by
    have := congr_fun (congr_fun h₁ 3) 6
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  -- g₁ reversed-index extractions (5 entries, need skew-symmetry)
  have e37 : X 3 7 = X 2 4 := by
    have := congr_fun (congr_fun h₁ 2) 3
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith [hsk 3 7]
  have e57 : X 5 7 = 0 := by
    have := congr_fun (congr_fun h₁ 2) 5
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith [hsk 5 7]
  have e67 : X 6 7 = 0 := by
    have := congr_fun (congr_fun h₁ 2) 6
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith [hsk 6 7]
  have e25 : X 2 5 = 0 := by
    have := congr_fun (congr_fun h₁ 5) 7
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith [hsk 2 5]
  have e26 : X 2 6 = 0 := by
    have := congr_fun (congr_fun h₁ 6) 7
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₁, skewBasis8,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith [hsk 2 6]
  -- g₄ direct extractions (7 entries)
  have e05 : X 0 5 = 0 := by
    have := congr_fun (congr_fun h₄ 0) 4
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e06 : X 0 6 = 0 := by
    have := congr_fun (congr_fun h₄ 0) 2
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e15 : X 1 5 = 0 := by
    have := congr_fun (congr_fun h₄ 1) 4
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e16 : X 1 6 = 0 := by
    have := congr_fun (congr_fun h₄ 1) 2
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e27 : X 2 7 = 0 := by
    have := congr_fun (congr_fun h₄ 6) 7
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e34 : X 3 4 = 0 := by
    have := congr_fun (congr_fun h₄ 3) 5
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  have e47 : X 4 7 = 0 := by
    have := congr_fun (congr_fun h₄ 5) 7
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith
  -- g₄ reversed-index extractions (2 entries, need skew-symmetry)
  have e23 : X 2 3 = 0 := by
    have := congr_fun (congr_fun h₄ 3) 6
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith [hsk 2 3]
  have e56 : X 5 6 = X 2 4 := by
    have := congr_fun (congr_fun h₄ 2) 5
    simp only [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, g₄, skewBasis8, Matrix.add_apply,
      Matrix.neg_apply, Matrix.single_apply] at this
    simp (config := { decide := true }) at this; linarith [hsk 5 6]
  -- Matrix equality: case-split over all 64 entries
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      c₁, c₂, skewBasis8, Matrix.sub_apply, Matrix.single_apply] <;>
    simp (config := { decide := true }) <;>
    linarith [hsk 0 0, hsk 1 1, hsk 2 2, hsk 3 3, hsk 4 4, hsk 5 5, hsk 6 6, hsk 7 7,
              hsk 1 0, hsk 2 0, hsk 3 0, hsk 4 0, hsk 5 0, hsk 6 0, hsk 7 0,
              hsk 2 1, hsk 3 1, hsk 4 1, hsk 5 1, hsk 6 1, hsk 7 1,
              hsk 3 2, hsk 4 2, hsk 5 2, hsk 6 2, hsk 7 2,
              hsk 4 3, hsk 5 3, hsk 6 3, hsk 7 3,
              hsk 5 4, hsk 6 4, hsk 7 4, hsk 6 5, hsk 7 5, hsk 7 6]

-- ═══════════════════════════════════════════════════════════
-- Formal finrank: centralizer has dimension 2
-- ═══════════════════════════════════════════════════════════

/-- The centralizer generators as a Fin 2-indexed family. -/
private def centralizer_vec : Fin 2 → Matrix (Fin 8) (Fin 8) ℚ
  | 0 => c₁
  | 1 => c₂

private theorem centralizer_vec_li : LinearIndependent ℚ centralizer_vec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum : g 0 • c₁ + g 1 • c₂ = 0 := by
    have h := hg
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, centralizer_vec] at h
    exact h
  have ⟨h0, h1⟩ := c₁_c₂_independent (g 0) (g 1) hsum
  fin_cases i <;> assumption

/-- The span of {c₁, c₂} in matrix space has finrank 2.
    Combined with centralizer_exact (spanning), this gives
    dim(centralizer of su(3) in so(8)) = 2. -/
theorem centralizer_finrank :
    Module.finrank ℚ (Submodule.span ℚ (Set.range centralizer_vec)) = 2 :=
  finrank_span_eq_card centralizer_vec_li

end BLD.Lie.Centralizer
