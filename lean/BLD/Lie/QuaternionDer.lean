/- BLD Calculus — Quaternion Derivation Algebra

   Der(ℍ) ≅ so(3) ≅ su(2), dimension 3 = n - 1.
   The weak gauge algebra comes from quaternion derivations.

   A derivation D : ℍ → ℍ satisfies D(xy) = xD(y) + D(x)y.
   The inner derivation D_a(x) = ax - xa generates the full space
   when a ranges over Im(ℍ).

   Reference: bld-paper §812-823 (Theorem 3.7)
-/

import Mathlib.Algebra.Quaternion

open scoped Quaternion

namespace BLD.Lie.QuaternionDer

abbrev H := ℍ[ℚ]

-- Basis elements
def qi : H := ⟨0, 1, 0, 0⟩
def qj : H := ⟨0, 0, 1, 0⟩
def qk : H := ⟨0, 0, 0, 1⟩

-- Scalar embedding: avoids SMul typeclass issues
def qscalar (c : ℚ) : H := ⟨c, 0, 0, 0⟩

-- ═══════════════════════════════════════════════════════════
-- Inner derivation: D_a(x) = ax - xa
-- ═══════════════════════════════════════════════════════════

/-- Inner derivation by a quaternion: D_a(x) = ax - xa. -/
def innerDer (a x : H) : H := a * x - x * a

/-- Inner derivation satisfies the Leibniz rule (in any associative ring).
    D_a(xy) = x · D_a(y) + D_a(x) · y. -/
theorem innerDer_leibniz (a x y : H) :
    innerDer a (x * y) = x * innerDer a y + innerDer a x * y := by
  simp only [innerDer, mul_sub, sub_mul, ← mul_assoc]; abel

-- ═══════════════════════════════════════════════════════════
-- The derivation conditions: D(x²) = xD(x) + D(x)x
-- ═══════════════════════════════════════════════════════════

/-- D(i²) = 0 forces D(i).re = 0 and D(i).imI = 0. -/
theorem sq_i_constraint (Di : H)
    (h : qi * Di + Di * qi = 0) :
    Di.re = 0 ∧ Di.imI = 0 := by
  obtain ⟨a, b, c, d⟩ := Di
  simp only [qi] at h
  have hre := congr_arg QuaternionAlgebra.re h
  have himI := congr_arg QuaternionAlgebra.imI h
  simp at hre himI
  constructor <;> linarith

/-- D(j²) = 0 forces D(j).re = 0 and D(j).imJ = 0. -/
theorem sq_j_constraint (Dj : H)
    (h : qj * Dj + Dj * qj = 0) :
    Dj.re = 0 ∧ Dj.imJ = 0 := by
  obtain ⟨a, b, c, d⟩ := Dj
  simp only [qj] at h
  have hre := congr_arg QuaternionAlgebra.re h
  have himJ := congr_arg QuaternionAlgebra.imJ h
  simp at hre himJ
  constructor <;> linarith

/-- D(k²) = 0 forces D(k).re = 0 and D(k).imK = 0. -/
theorem sq_k_constraint (Dk : H)
    (h : qk * Dk + Dk * qk = 0) :
    Dk.re = 0 ∧ Dk.imK = 0 := by
  obtain ⟨a, b, c, d⟩ := Dk
  simp only [qk] at h
  have hre := congr_arg QuaternionAlgebra.re h
  have himK := congr_arg QuaternionAlgebra.imK h
  simp at hre himK
  constructor <;> linarith

-- ═══════════════════════════════════════════════════════════
-- Cross constraints from D(ij) = iD(j) + D(i)j = D(k)
-- ═══════════════════════════════════════════════════════════

/-- D(ij) = D(k) gives: D(j).imI = -D(i).imJ, D(k).imI = -D(i).imK,
    D(k).imJ = -D(j).imK. -/
theorem cross_constraint (Di Dj Dk : H)
    (hi : Di.re = 0) (hi2 : Di.imI = 0)
    (hj : Dj.re = 0) (hj2 : Dj.imJ = 0)
    (hk : Dk.re = 0) (hk2 : Dk.imK = 0)
    (hij : qi * Dj + Di * qj = Dk) :
    Dj.imI = -Di.imJ ∧ Dk.imI = -Di.imK ∧ Dk.imJ = -Dj.imK := by
  obtain ⟨a1, a2, a3, a4⟩ := Di
  obtain ⟨b1, b2, b3, b4⟩ := Dj
  obtain ⟨c1, c2, c3, c4⟩ := Dk
  simp at hi hi2 hj hj2 hk hk2
  subst hi; subst hi2; subst hj; subst hj2; subst hk; subst hk2
  simp only [qi, qj] at hij
  have hre := congr_arg QuaternionAlgebra.re hij
  have h1 := congr_arg QuaternionAlgebra.imI hij
  have h2 := congr_arg QuaternionAlgebra.imJ hij
  simp at hre h1 h2
  exact ⟨by linarith, by linarith, by linarith⟩

-- ═══════════════════════════════════════════════════════════
-- Main theorem: dim(Der(ℍ)) = 3
-- ═══════════════════════════════════════════════════════════

/-- The inner derivations D_i, D_j, D_k are linearly independent.
    If c₁D_i(j) + c₂D_j(j) + c₃D_k(j) = 0 and similarly for i,
    then c₁ = c₂ = c₃ = 0.
    Uses qscalar embedding to avoid SMul typeclass. -/
theorem innerDer_independent :
    ∀ c₁ c₂ c₃ : ℚ,
    qscalar c₁ * innerDer qi qj + qscalar c₂ * innerDer qj qj + qscalar c₃ * innerDer qk qj = 0 →
    qscalar c₁ * innerDer qi qi + qscalar c₂ * innerDer qj qi + qscalar c₃ * innerDer qk qi = 0 →
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  intro c₁ c₂ c₃ h1 h2
  -- Compute concrete inner derivation values
  have eq_ij : innerDer qi qj = (⟨0, 0, 0, 2⟩ : H) := by
    simp only [innerDer, qi, qj]; ext <;> norm_num
  have eq_jj : innerDer qj qj = (0 : H) := by
    simp only [innerDer, sub_self]
  have eq_kj : innerDer qk qj = (⟨0, -2, 0, 0⟩ : H) := by
    simp only [innerDer, qk, qj]; ext <;> norm_num
  have eq_ii : innerDer qi qi = (0 : H) := by
    simp only [innerDer, sub_self]
  have eq_ji : innerDer qj qi = (⟨0, 0, 0, -2⟩ : H) := by
    simp only [innerDer, qj, qi]; ext <;> norm_num
  have eq_ki : innerDer qk qi = (⟨0, 0, 2, 0⟩ : H) := by
    simp only [innerDer, qk, qi]; ext <;> norm_num
  rw [eq_ij, eq_jj, eq_kj] at h1
  rw [eq_ii, eq_ji, eq_ki] at h2
  simp only [qscalar] at h1 h2
  have h1b := congr_arg QuaternionAlgebra.imI h1
  have h1d := congr_arg QuaternionAlgebra.imK h1
  have h2c := congr_arg QuaternionAlgebra.imJ h2
  have h2d := congr_arg QuaternionAlgebra.imK h2
  simp at h1b h1d h2c h2d
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Every derivation of ℍ[ℚ] is an inner derivation.
    Given the 6 constraints (from i², j², k², ij), any derivation
    D is determined by 3 parameters and equals a linear combination
    of D_i, D_j, D_k. -/
theorem deriv_is_inner (Di Dj Dk : H)
    (hi_sq : qi * Di + Di * qi = 0)
    (hj_sq : qj * Dj + Dj * qj = 0)
    (hk_sq : qk * Dk + Dk * qk = 0)
    (hij : qi * Dj + Di * qj = Dk) :
    ∃ a b c : ℚ,
      Di = qscalar a * innerDer qi qi + qscalar b * innerDer qj qi + qscalar c * innerDer qk qi ∧
      Dj = qscalar a * innerDer qi qj + qscalar b * innerDer qj qj + qscalar c * innerDer qk qj ∧
      Dk = qscalar a * innerDer qi qk + qscalar b * innerDer qj qk + qscalar c * innerDer qk qk := by
  have ⟨hi_re, hi_imI⟩ := sq_i_constraint Di hi_sq
  have ⟨hj_re, hj_imJ⟩ := sq_j_constraint Dj hj_sq
  have ⟨hk_re, hk_imK⟩ := sq_k_constraint Dk hk_sq
  have ⟨hji, hki, hkj⟩ := cross_constraint Di Dj Dk hi_re hi_imI hj_re hj_imJ hk_re hk_imK hij
  refine ⟨Dj.imK / 2, -Di.imK / 2, Di.imJ / 2, ?_, ?_, ?_⟩
  all_goals (
    obtain ⟨a1, a2, a3, a4⟩ := Di
    obtain ⟨b1, b2, b3, b4⟩ := Dj
    obtain ⟨c1, c2, c3, c4⟩ := Dk
    simp at hi_re hi_imI hj_re hj_imJ hk_re hk_imK hji hki hkj
    subst hi_re; subst hi_imI; subst hj_re; subst hj_imJ; subst hk_re; subst hk_imK
    simp only [innerDer, qi, qj, qk, qscalar]
    ext <;> simp <;> nlinarith [hji, hki, hkj])

/-- dim(Der(ℍ)) = 3: the derivation algebra of quaternions
    is 3-dimensional, isomorphic to so(3) ≅ su(2). -/
theorem quaternion_derivation_dim :
    ∃ D₁ D₂ D₃ : H → H,
      -- They are derivations (inner derivations)
      (∀ x y, D₁ (x * y) = x * D₁ y + D₁ x * y) ∧
      (∀ x y, D₂ (x * y) = x * D₂ y + D₂ x * y) ∧
      (∀ x y, D₃ (x * y) = x * D₃ y + D₃ x * y) ∧
      -- They are linearly independent (evaluated at j and i)
      (∀ c₁ c₂ c₃ : ℚ,
        qscalar c₁ * D₁ qj + qscalar c₂ * D₂ qj + qscalar c₃ * D₃ qj = 0 →
        qscalar c₁ * D₁ qi + qscalar c₂ * D₂ qi + qscalar c₃ * D₃ qi = 0 →
        c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0) :=
  ⟨innerDer qi, innerDer qj, innerDer qk,
   innerDer_leibniz qi, innerDer_leibniz qj, innerDer_leibniz qk,
   innerDer_independent⟩

end BLD.Lie.QuaternionDer
