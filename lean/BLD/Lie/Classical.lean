/- BLD Calculus — Lie Theory Bridge: Classical Lie Algebras

   Connects BLD constants to so(8) = Lie(Spin(8)):
   - so(8) is the D₄ Lie algebra (skew-adjoint 8×8 matrices)
   - dim(so(8)) = 8×7/2 = 28
   - B = 2 × dim(so(8)) = 56

   Reference: bld-calculus.md §6.2, lie-correspondence.md §3
-/

import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Matrix.Cartan
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import BLD.Lie.Basic
import BLD.Constants

namespace BLD.Lie

noncomputable def so8 (R : Type*) [CommRing R] :=
  LieAlgebra.Orthogonal.so (Fin 8) R

theorem mem_so8 (R : Type*) [CommRing R] (A : Matrix (Fin 8) (Fin 8) R) :
    A ∈ so8 R ↔ Matrix.transpose A = -A :=
  LieAlgebra.Orthogonal.mem_so (Fin 8) R A

theorem D4_rank : Fintype.card (Fin 4) = 4 := by decide
theorem D4_rank_eq_n : Fintype.card (Fin 4) = BLD.n := by decide
theorem dim_so8_arithmetic : 8 * 7 / 2 = 28 := by decide
theorem B_eq_2_dim_so8 : BLD.B = 2 * 28 := by decide

/-! ### Proof that finrank(so(8,ℚ)) = 28 -/

private abbrev SkewIdx := {p : Fin 8 × Fin 8 // p.1 < p.2}

private theorem card_skewIdx : Fintype.card SkewIdx = 28 := by native_decide

private def skewMat (p : SkewIdx) : Matrix (Fin 8) (Fin 8) ℚ :=
  Matrix.single p.val.1 p.val.2 1 - Matrix.single p.val.2 p.val.1 1

private theorem skewMat_mem (p : SkewIdx) : skewMat p ∈ so8 ℚ := by
  rw [mem_so8, skewMat, Matrix.transpose_sub, Matrix.transpose_single,
      Matrix.transpose_single, neg_sub]

private def bv (p : SkewIdx) : ↥(so8 ℚ) := ⟨skewMat p, skewMat_mem p⟩

private theorem skewMat_self (p : SkewIdx) :
    skewMat p p.val.1 p.val.2 = 1 := by
  simp [skewMat, Matrix.sub_apply,
        show p.val.1 ≠ p.val.2 from Fin.ne_of_lt p.property]

private theorem skewMat_other (p q : SkewIdx) (hpq : p ≠ q) :
    skewMat p q.val.1 q.val.2 = 0 := by
  simp only [skewMat, Matrix.sub_apply, Matrix.single_apply]
  have hne1 : ¬(p.val.1 = q.val.1 ∧ p.val.2 = q.val.2) :=
    fun ⟨h1, h2⟩ => hpq (Subtype.ext (Prod.ext h1 h2))
  have hne2 : ¬(p.val.2 = q.val.1 ∧ p.val.1 = q.val.2) :=
    fun ⟨h1, h2⟩ => absurd (h1 ▸ h2 ▸ p.property) (not_lt.mpr (le_of_lt q.property))
  simp [hne1, hne2]

-- Helper: evaluate a finite sum of scaled matrices at a specific entry
private theorem sum_skewMat_entry (c : SkewIdx → ℚ) (a b : Fin 8) :
    (∑ p : SkewIdx, c p • skewMat p) a b = ∑ p : SkewIdx, c p * skewMat p a b := by
  rw [Matrix.sum_apply]; simp [Matrix.smul_apply, smul_eq_mul]

-- Linear independence in matrix space
private theorem skewMat_li : LinearIndependent ℚ skewMat := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h : ∑ p : SkewIdx, g p * skewMat p k.val.1 k.val.2 = 0 := by
    rw [← sum_skewMat_entry, hg]; rfl
  rwa [Finset.sum_eq_single k
    (fun a _ hak => by rw [skewMat_other a k hak, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h),
    skewMat_self, mul_one] at h

-- Lift to subtype
private theorem bv_li : LinearIndependent ℚ bv :=
  LinearIndependent.of_comp ((so8 ℚ).toSubmodule.subtype) skewMat_li

-- Diagonal of skew-adjoint is zero
private theorem skew_diag_zero {A : Matrix (Fin 8) (Fin 8) ℚ}
    (hA : Matrix.transpose A = -A) (a : Fin 8) : A a a = 0 := by
  have := congr_fun (congr_fun hA a) a
  simp [Matrix.transpose_apply, Matrix.neg_apply] at this
  linarith

-- Helper: entry of sum where only one term contributes
private theorem sum_skewMat_entry_eq (c : SkewIdx → ℚ) (p : SkewIdx) :
    (∑ q : SkewIdx, c q * skewMat q p.val.1 p.val.2) = c p := by
  rw [Finset.sum_eq_single p
    (fun a _ hak => by rw [skewMat_other a p hak, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h),
    skewMat_self, mul_one]

-- A skew-adjoint matrix equals ∑_{i<j} A(i,j) • (E_ij - E_ji)
private theorem skew_reconstruct {A : Matrix (Fin 8) (Fin 8) ℚ}
    (hA : Matrix.transpose A = -A) :
    A = ∑ p : SkewIdx, A p.val.1 p.val.2 • skewMat p := by
  ext a b
  rw [sum_skewMat_entry]
  rcases lt_trichotomy a b with hab | rfl | hab
  · -- a < b: the pair (a,b) contributes A(a,b)
    rw [Finset.sum_eq_single ⟨(a, b), hab⟩ ?_ ?_]
    · simp [skewMat_self ⟨(a,b), hab⟩]
    · intro q _ hq
      have hne1 : ¬(q.val.1 = a ∧ q.val.2 = b) :=
        fun ⟨h1, h2⟩ => hq (Subtype.ext (Prod.ext h1 h2))
      have hne2 : ¬(q.val.2 = a ∧ q.val.1 = b) :=
        fun ⟨h1, h2⟩ => absurd (h1 ▸ h2 ▸ q.property) (not_lt.mpr (le_of_lt hab))
      simp only [skewMat, Matrix.sub_apply, Matrix.single_apply, hne1, hne2,
                 if_false, sub_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- a = b: diagonal is zero
    rw [skew_diag_zero hA]
    symm; apply Finset.sum_eq_zero
    intro ⟨⟨i, j⟩, hij⟩ _
    have hne1 : ¬(i = a ∧ j = a) := fun ⟨h1, h2⟩ => absurd (h1 ▸ h2 ▸ hij) (lt_irrefl _)
    have hne2 : ¬(j = a ∧ i = a) := fun ⟨h1, h2⟩ => absurd (h2 ▸ h1 ▸ hij) (lt_irrefl _)
    simp only [skewMat, Matrix.sub_apply, Matrix.single_apply, hne1, hne2,
               if_false, sub_zero, mul_zero]
  · -- a > b: the pair (b,a) contributes -A(b,a) = A(a,b)
    rw [Finset.sum_eq_single ⟨(b, a), hab⟩ ?_ ?_]
    · simp only [skewMat, Matrix.sub_apply, Matrix.single_apply]
      have hne : b ≠ a := Fin.ne_of_lt hab
      simp only [hne, hne.symm, and_self, ite_false, ite_true,
                 zero_sub, mul_neg, mul_one]
      have := congr_fun (congr_fun hA a) b
      simp [Matrix.transpose_apply, Matrix.neg_apply] at this
      linarith
    · intro q _ hq
      have hne1 : ¬(q.val.1 = a ∧ q.val.2 = b) :=
        fun ⟨h1, h2⟩ => absurd (h1 ▸ h2 ▸ q.property) (not_lt.mpr (le_of_lt hab))
      have hne2 : ¬(q.val.2 = a ∧ q.val.1 = b) :=
        fun ⟨h1, h2⟩ => hq (Subtype.ext (Prod.ext h2 h1))
      simp only [skewMat, Matrix.sub_apply, Matrix.single_apply, hne1, hne2,
                 if_false, sub_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

-- Spanning
private theorem bv_span : ⊤ ≤ Submodule.span ℚ (Set.range bv) := by
  intro ⟨A, hA⟩ _
  have hA' := (mem_so8 ℚ A).mp hA
  suffices h : (⟨A, hA⟩ : ↥(so8 ℚ)) = ∑ p : SkewIdx, A p.val.1 p.val.2 • bv p by
    rw [h]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  apply Subtype.ext
  show A = (∑ p : SkewIdx, A p.val.1 p.val.2 • bv p).val
  rw [show (∑ p : SkewIdx, A p.val.1 p.val.2 • bv p).val =
      ∑ p : SkewIdx, A p.val.1 p.val.2 • skewMat p from by
    simp [bv]]
  exact skew_reconstruct hA'

/-- The module dimension of so(8,ℚ) is 28. -/
theorem so8_finrank : Module.finrank ℚ (so8 ℚ) = 28 := by
  have b := Module.Basis.mk bv_li bv_span
  rw [Module.finrank_eq_card_basis b, card_skewIdx]

/-- B = 2 × finrank(so(8,ℚ)). -/
theorem B_eq_2_finrank_so8 : BLD.B = 2 * Module.finrank ℚ (so8 ℚ) := by
  rw [so8_finrank]; decide

end BLD.Lie
