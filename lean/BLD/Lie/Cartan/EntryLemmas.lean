/- BLD Calculus — Cartan Classification: Entry Lemmas

   Parametric Cartan matrix entry lemmas for A, B, C, D types,
   path reversal, extension helpers, marks vectors, and weight-3 impossibility.
-/

import BLD.Lie.Cartan.Structure

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

-- ═══════════════════════════════════════════════════════════
-- E₈ marks (dual Coxeter labels)
-- ═══════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════
-- Parametric Cartan matrix entry lemmas (A, B, C, D)
-- ═══════════════════════════════════════════════════════════

/-- Deleting the last vertex of A_{k+1} gives A_k. -/
theorem A_castSucc_eq (k : ℕ) (i j : Fin k) :
    CartanMatrix.A (k + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A k i j := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.castSucc_inj, Fin.val_castSucc]

/-- Deleting the first vertex of A_{k+1} gives A_k. -/
theorem A_succ_eq (k : ℕ) (i j : Fin k) :
    CartanMatrix.A (k + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.A k i j := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.succ_inj, Fin.val_succ]
  split_ifs <;> omega

/-- A_{k+1} first row: vertex 0 connects only to vertex 1. -/
theorem A_first_row (k : ℕ) (j : Fin k) :
    CartanMatrix.A (k + 1) 0 (Fin.succ j) = if j.val = 0 then -1 else 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_succ,
    show (0 : Fin (k+1)).val = 0 from rfl]
  have hj := j.isLt
  split_ifs <;> simp only [or_false, not_false_eq_true] at * <;> omega

/-- A_{k+1} first column (A is symmetric). -/
theorem A_first_col (k : ℕ) (i : Fin k) :
    CartanMatrix.A (k + 1) (Fin.succ i) 0 = if i.val = 0 then -1 else 0 := by
  rw [show CartanMatrix.A (k+1) (Fin.succ i) 0 =
      CartanMatrix.A (k+1) 0 (Fin.succ i) from by
    have := congr_fun (congr_fun (CartanMatrix.A_isSymm (n := k + 1)) 0) (Fin.succ i)
    rwa [Matrix.transpose_apply] at this]
  exact A_first_row k i

/-- A_{k+1} last row: connects only to vertex k-1. -/
theorem A_last_row (k : ℕ) (i : Fin k) :
    CartanMatrix.A (k + 1) (Fin.last k) (Fin.castSucc i) =
    if i.val = k - 1 then -1 else 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
  have hi := i.isLt
  split_ifs <;> omega

/-- A_{k+1} last column (A is symmetric). -/
theorem A_last_col (k : ℕ) (i : Fin k) :
    CartanMatrix.A (k + 1) (Fin.castSucc i) (Fin.last k) =
    if i.val = k - 1 then -1 else 0 := by
  rw [show CartanMatrix.A (k+1) (Fin.castSucc i) (Fin.last k) =
      CartanMatrix.A (k+1) (Fin.last k) (Fin.castSucc i) from by
    have := congr_fun (congr_fun (CartanMatrix.A_isSymm (n := k + 1)) (Fin.last k)) (Fin.castSucc i)
    rwa [Matrix.transpose_apply] at this]
  exact A_last_row k i

/-- Adjacent entries in A-type Cartan matrix are -1. -/
theorem A_adj (m : ℕ) (i j : Fin m) (hij : i ≠ j)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    CartanMatrix.A m i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij, if_pos hadj]

/-- Non-adjacent, non-diagonal entries in A-type Cartan matrix are 0. -/
theorem A_nonadj (m : ℕ) (i j : Fin m) (hij : i ≠ j)
    (hnadj : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    CartanMatrix.A m i j = 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij, if_neg hnadj]

/-- A sub-path of A_n starting at offset c gives A_k. -/
theorem A_shift_submatrix (k n c : ℕ) (hc : c + k ≤ n) (i j : Fin k) :
    CartanMatrix.A n ⟨i.val + c, by omega⟩ ⟨j.val + c, by omega⟩ = CartanMatrix.A k i j := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> omega

/-- Deleting the last vertex of B_{k+1} gives A_k. -/
theorem B_castSucc_eq_A (k : ℕ) (i j : Fin k) :
    CartanMatrix.B (k + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A k i j := by
  simp only [CartanMatrix.B, CartanMatrix.A, Matrix.of_apply, Fin.castSucc_inj, Fin.val_castSucc]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

/-- B_{k+1} last row: vertex k connects to vertex k-1 with weight -1. -/
theorem B_last_row (k : ℕ) (i : Fin k) :
    CartanMatrix.B (k + 1) (Fin.last k) (Fin.castSucc i) =
    if i.val = k - 1 then -1 else 0 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
  have hi := i.isLt
  split_ifs <;> omega

/-- B_{k+1} last column: vertex k-1 connects to k with weight -2. -/
theorem B_last_col (k : ℕ) (i : Fin k) :
    CartanMatrix.B (k + 1) (Fin.castSucc i) (Fin.last k) =
    if i.val = k - 1 then -2 else 0 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
  have hi := i.isLt
  split_ifs <;> omega

/-- Deleting the last vertex of C_{k+1} gives A_k. -/
theorem C_castSucc_eq_A (k : ℕ) (i j : Fin k) :
    CartanMatrix.C (k + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A k i j := by
  simp only [CartanMatrix.C, CartanMatrix.A, Matrix.of_apply, Fin.castSucc_inj, Fin.val_castSucc]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

/-- C_{k+1} last row: vertex k connects to vertex k-1 with weight -2. -/
theorem C_last_row (k : ℕ) (i : Fin k) :
    CartanMatrix.C (k + 1) (Fin.last k) (Fin.castSucc i) =
    if i.val = k - 1 then -2 else 0 := by
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
  have hi := i.isLt
  split_ifs <;> omega

/-- C_{k+1} last column: vertex k-1 connects to k with weight -1. -/
theorem C_last_col (k : ℕ) (i : Fin k) :
    CartanMatrix.C (k + 1) (Fin.castSucc i) (Fin.last k) =
    if i.val = k - 1 then -1 else 0 := by
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
  have hi := i.isLt
  split_ifs <;> omega

/-- Deleting the last vertex of D_{k+1} gives A_k when k ≥ 3. -/
theorem D_castSucc_eq_A (k : ℕ) (hk : 3 ≤ k) (i j : Fin k) :
    CartanMatrix.D (k + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A k i j := by
  simp only [CartanMatrix.D, CartanMatrix.A, Matrix.of_apply, Fin.castSucc_inj, Fin.val_castSucc]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

/-- D_{k+1} last row: vertex k connects to vertex k-2 (fork, k ≥ 3). -/
theorem D_last_row (k : ℕ) (hk : 3 ≤ k) (i : Fin k) :
    CartanMatrix.D (k + 1) (Fin.last k) (Fin.castSucc i) =
    if i.val + 2 = k then -1 else 0 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
  have hi := i.isLt
  split_ifs <;> simp_all <;> omega

/-- D_{k+1} last column (D is symmetric). -/
theorem D_last_col (k : ℕ) (hk : 3 ≤ k) (i : Fin k) :
    CartanMatrix.D (k + 1) (Fin.castSucc i) (Fin.last k) =
    if i.val + 2 = k then -1 else 0 := by
  rw [show CartanMatrix.D (k+1) (Fin.castSucc i) (Fin.last k) =
      CartanMatrix.D (k+1) (Fin.last k) (Fin.castSucc i) from by
    have := congr_fun (congr_fun (CartanMatrix.D_isSymm (n := k + 1)) (Fin.last k)) (Fin.castSucc i)
    rwa [Matrix.transpose_apply] at this]
  exact D_last_row k hk i

-- ═══════════════════════════════════════════════════════════
-- Path reversal for A_n
-- ═══════════════════════════════════════════════════════════

/-- Reversal permutation on Fin (n+1): sends i to n-i. -/
def finRev (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun i := ⟨n - i.val, by omega⟩
  invFun i := ⟨n - i.val, by omega⟩
  left_inv i := by
    apply Fin.ext; simp only [Fin.val_mk]
    have := i.isLt; omega
  right_inv i := by
    apply Fin.ext; simp only [Fin.val_mk]
    have := i.isLt; omega

@[simp] theorem finRev_val (n : ℕ) (i : Fin (n + 1)) : (finRev n i).val = n - i.val := rfl

/-- A_{n+1} is invariant under path reversal. -/
theorem A_finRev_eq (n : ℕ) (i j : Fin (n + 1)) :
    CartanMatrix.A (n + 1) (finRev n i) (finRev n j) = CartanMatrix.A (n + 1) i j := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, finRev_val]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

-- ═══════════════════════════════════════════════════════════
-- General "extend at last" helper
-- ═══════════════════════════════════════════════════════════

/-- Given a GCM A with leaf v, and a target matrix T whose castSucc-submatrix
    matches A's submatrix and whose last row/column matches A's leaf, construct
    a CartanEquiv A T. Reusable across A→A, A→B, A→C, B→B, D→D, etc. -/
theorem extend_at_last {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (v : Fin (n+3))
    (e' : Fin (n+2) ≃ Fin (n+2))
    (T : Matrix (Fin (n+3)) (Fin (n+3)) ℤ)
    (hT_diag : T (Fin.last (n+2)) (Fin.last (n+2)) = 2)
    (hT_sub : ∀ i j : Fin (n+2),
        T (Fin.castSucc (e' i)) (Fin.castSucc (e' j)) = A (v.succAbove i) (v.succAbove j))
    (hT_row : ∀ m : Fin (n+2),
        T (Fin.last (n+2)) (Fin.castSucc (e' m)) = A v (v.succAbove m))
    (hT_col : ∀ m : Fin (n+2),
        T (Fin.castSucc (e' m)) (Fin.last (n+2)) = A (v.succAbove m) v)
    : CartanEquiv A T := by
  let f : Fin (n+3) → Fin (n+3) := fun i =>
    if h : ∃ m : Fin (n+2), v.succAbove m = i then Fin.castSucc (e' h.choose)
    else Fin.last (n+2)
  have hf_v : f v = Fin.last (n+2) := by
    simp only [f]; rw [dif_neg]; push_neg; exact fun k => Fin.succAbove_ne v k
  have hf_sub : ∀ m : Fin (n+2), f (v.succAbove m) = Fin.castSucc (e' m) := by
    intro m; simp only [f]
    have hex : ∃ m' : Fin (n+2), v.succAbove m' = v.succAbove m := ⟨m, rfl⟩
    rw [dif_pos hex, show hex.choose = m from Fin.succAbove_right_injective hex.choose_spec]
  have hf_inj : Function.Injective f := by
    intro i j hij
    rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · exact hi.trans hj.symm
      · exfalso; rw [hi, hj, hf_v, hf_sub] at hij
        exact absurd (congr_arg Fin.val hij) (by simp [Fin.val_castSucc]; omega)
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · exfalso; rw [hi, hj, hf_sub, hf_v] at hij
        exact absurd (congr_arg Fin.val hij) (by simp [Fin.val_castSucc]; omega)
      · rw [hi, hj]; congr 1; rw [hi, hj, hf_sub, hf_sub] at hij
        exact e'.injective (Fin.castSucc_injective _ hij)
  let σ := Equiv.ofBijective f hf_inj.bijective_of_finite
  refine ⟨σ, fun i j => ?_⟩
  show T (f i) (f j) = A i j
  rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
  · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
    · rw [hi, hj, hf_v]; exact hT_diag.trans (hGCM.diag v).symm
    · rw [hi, hj, hf_v, hf_sub]; exact hT_row kj
  · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
    · rw [hi, hj, hf_sub, hf_v]; exact hT_col ki
    · rw [hi, hj, hf_sub, hf_sub]; exact hT_sub ki kj

/-- Given a GCM A with leaf v, and a target matrix T whose succ-submatrix
    matches A's submatrix and whose first row/column matches A's leaf, construct
    a CartanEquiv A T. Maps v → 0 and v.succAbove m → Fin.succ (e' m). -/
theorem extend_at_zero {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (v : Fin (n+3))
    (e' : Fin (n+2) ≃ Fin (n+2))
    (T : Matrix (Fin (n+3)) (Fin (n+3)) ℤ)
    (hT_diag : T 0 0 = 2)
    (hT_sub : ∀ i j : Fin (n+2),
        T (Fin.succ (e' i)) (Fin.succ (e' j)) = A (v.succAbove i) (v.succAbove j))
    (hT_row : ∀ m : Fin (n+2),
        T 0 (Fin.succ (e' m)) = A v (v.succAbove m))
    (hT_col : ∀ m : Fin (n+2),
        T (Fin.succ (e' m)) 0 = A (v.succAbove m) v)
    : CartanEquiv A T := by
  let f : Fin (n+3) → Fin (n+3) := fun i =>
    if h : ∃ m : Fin (n+2), v.succAbove m = i then Fin.succ (e' h.choose)
    else 0
  have hf_v : f v = 0 := by
    simp only [f]; rw [dif_neg]; push_neg; exact fun k => Fin.succAbove_ne v k
  have hf_sub : ∀ m : Fin (n+2), f (v.succAbove m) = Fin.succ (e' m) := by
    intro m; simp only [f]
    have hex : ∃ m' : Fin (n+2), v.succAbove m' = v.succAbove m := ⟨m, rfl⟩
    rw [dif_pos hex, show hex.choose = m from Fin.succAbove_right_injective hex.choose_spec]
  have hf_inj : Function.Injective f := by
    intro i j hij
    rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · exact hi.trans hj.symm
      · exfalso; rw [hi, hj, hf_v, hf_sub] at hij
        exact absurd hij (Fin.succ_ne_zero (e' kj)).symm
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · exfalso; rw [hi, hj, hf_sub, hf_v] at hij
        exact absurd hij (Fin.succ_ne_zero (e' ki))
      · rw [hi, hj]; congr 1; rw [hi, hj, hf_sub, hf_sub] at hij
        exact e'.injective (Fin.succ_inj.mp hij)
  let σ := Equiv.ofBijective f hf_inj.bijective_of_finite
  refine ⟨σ, fun i j => ?_⟩
  show T (f i) (f j) = A i j
  rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
  · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
    · rw [hi, hj, hf_v]; exact hT_diag.trans (hGCM.diag v).symm
    · rw [hi, hj, hf_v, hf_sub]; exact hT_row kj
  · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
    · rw [hi, hj, hf_sub, hf_v]; exact hT_col ki
    · rw [hi, hj, hf_sub, hf_sub]; exact hT_sub ki kj

/-- Generic extension: maps v to target position p, submatrix via p.succAbove ∘ e'. -/
theorem extend_at {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (v : Fin (n+3))
    (e' : Fin (n+2) ≃ Fin (n+2))
    (T : Matrix (Fin (n+3)) (Fin (n+3)) ℤ)
    (p : Fin (n+3))
    (hT_diag : T p p = 2)
    (hT_sub : ∀ i j : Fin (n+2),
        T (p.succAbove (e' i)) (p.succAbove (e' j)) = A (v.succAbove i) (v.succAbove j))
    (hT_row : ∀ m : Fin (n+2),
        T p (p.succAbove (e' m)) = A v (v.succAbove m))
    (hT_col : ∀ m : Fin (n+2),
        T (p.succAbove (e' m)) p = A (v.succAbove m) v)
    : CartanEquiv A T := by
  let f : Fin (n+3) → Fin (n+3) := fun i =>
    if h : ∃ m : Fin (n+2), v.succAbove m = i then p.succAbove (e' h.choose)
    else p
  have hf_v : f v = p := by
    simp only [f]; rw [dif_neg]; push_neg; exact fun k => Fin.succAbove_ne v k
  have hf_sub : ∀ m : Fin (n+2), f (v.succAbove m) = p.succAbove (e' m) := by
    intro m; simp only [f]
    have hex : ∃ m' : Fin (n+2), v.succAbove m' = v.succAbove m := ⟨m, rfl⟩
    rw [dif_pos hex, show hex.choose = m from Fin.succAbove_right_injective hex.choose_spec]
  have hf_inj : Function.Injective f := by
    intro i j hij
    rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · exact hi.trans hj.symm
      · exfalso; rw [hi, hj, hf_v, hf_sub] at hij
        exact absurd hij.symm (Fin.succAbove_ne p (e' kj))
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · exfalso; rw [hi, hj, hf_sub, hf_v] at hij
        exact absurd hij (Fin.succAbove_ne p (e' ki))
      · rw [hi, hj]; congr 1; rw [hi, hj, hf_sub, hf_sub] at hij
        exact e'.injective (Fin.succAbove_right_injective hij)
  let σ := Equiv.ofBijective f hf_inj.bijective_of_finite
  refine ⟨σ, fun i j => ?_⟩
  show T (f i) (f j) = A i j
  rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
  · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
    · rw [hi, hj, hf_v]; exact hT_diag.trans (hGCM.diag v).symm
    · rw [hi, hj, hf_v, hf_sub]; exact hT_row kj
  · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
    · rw [hi, hj, hf_sub, hf_v]; exact hT_col ki
    · rw [hi, hj, hf_sub, hf_sub]; exact hT_sub ki kj

/-- The marks (dual Coxeter labels) of E₈: components of the null vector
    of the affine extension Ẽ₈. These satisfy E₈ · marks = (0,...,0,1)
    where only the vertex-7 component is nonzero. -/
def marksE8 : Fin 8 → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

/-- The E₈ marks are ≥ 2. -/
theorem marksE8_ge_two : ∀ i : Fin 8, 2 ≤ marksE8 i := by decide

/-- E₈ · marks has a single nonzero entry at vertex 7. -/
theorem E8_mulVec_marks : CartanMatrix.E₈.mulVec marksE8 = fun i =>
    if i = 7 then 1 else 0 := by decide

/-- Marks vector for F₄: dual Coxeter labels. F₄ · marksF4 = (1,0,0,0). -/
def marksF4 : Fin 4 → ℤ := ![2, 3, 2, 1]

theorem F4_mulVec_marks : CartanMatrix.F₄.mulVec marksF4 = fun i =>
    if i = 0 then 1 else 0 := by decide

/-- Affine null marks for F₄: F₄ · affmarksF4 = (0,0,0,1).
    Used for vertex-3 attachment contradictions. -/
def affmarksF4 : Fin 4 → ℤ := ![2, 4, 3, 2]

theorem F4_mulVec_affmarks : CartanMatrix.F₄.mulVec affmarksF4 = fun i =>
    if i = 3 then 1 else 0 := by decide

/-- Marks vector for E₇: dual Coxeter labels. E₇ · marksE7 = (1,0,...,0). -/
def marksE7 : Fin 7 → ℤ := ![2, 2, 3, 4, 3, 2, 1]

theorem E7_mulVec_marks : CartanMatrix.E₇.mulVec marksE7 = fun i =>
    if i = 0 then 1 else 0 := by decide

/-- E₈ restricted to first 7 indices equals E₇. -/
theorem E8_castSucc_eq_E7 : ∀ i j : Fin 7,
    CartanMatrix.E₈ (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.E₇ i j := by decide

/-- E₈ last row/column: vertex 7 connects only to vertex 6. -/
theorem E8_last_row : ∀ i : Fin 7,
    CartanMatrix.E₈ 7 (Fin.castSucc i) = if i = 6 then -1 else 0 := by decide

/-- E₇ weight-2 submatrix, case A(v,u)=-1, A(u,v)=-2.
    Rows/cols 0-5 = E₇ vertices 1-6, row/col 6 = leaf v. -/
def e7w2c1 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2, -1,  0,  0,  0,  0;
     -1, -1,  2, -1,  0,  0,  0;
      0,  0, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -2;
      0,  0,  0,  0,  0, -1,  2]

theorem e7w2c1_null : e7w2c1.mulVec ![1, 1, 2, 2, 2, 2, 1] = 0 := by decide

/-- E₇ weight-2 submatrix, case A(v,u)=-2, A(u,v)=-1. -/
def e7w2c2 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2, -1,  0,  0,  0,  0;
     -1, -1,  2, -1,  0,  0,  0;
      0,  0, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0, -2,  2]

theorem e7w2c2_null : e7w2c2.mulVec ![1, 1, 2, 2, 2, 2, 2] = 0 := by decide

/-- E₇ vertices 1-6 sub-block equals first 6×6 of e7w2c1 (= e7w2c2). -/
theorem E7_sub_eq : ∀ i j : Fin 6,
    CartanMatrix.E₇ (Fin.succ i) (Fin.succ j) =
    e7w2c1 (Fin.castSucc i) (Fin.castSucc j) := by decide

end BLD.Lie.Cartan
