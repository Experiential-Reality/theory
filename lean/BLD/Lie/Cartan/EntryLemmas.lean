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

/-- Deleting vertex 0 of B_{k+1} gives B_k. -/
theorem B_succ_eq_B (k : ℕ) (i j : Fin k) :
    CartanMatrix.B (k + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.B k i j := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.succ_inj, Fin.val_succ]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

/-- B_{k+1} first row: vertex 0 connects only to vertex 1 with weight -1. -/
theorem B_first_row (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    CartanMatrix.B (k + 1) 0 (Fin.succ j) =
    if j.val = 0 then -1 else 0 := by
  have hj := j.isLt
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.val_zero, Fin.val_succ]
  rw [if_neg (by simp [Fin.ext_iff])]
  by_cases hj0 : j.val = 0
  · rw [if_pos (show 0 + 1 = j.val + 1 by omega),
        if_neg (show ¬(j.val + 1 = k + 1 - 1) by omega),
        if_pos hj0]
  · rw [if_neg (show ¬(0 + 1 = j.val + 1) by omega),
        if_neg (show ¬(j.val + 1 + 1 = 0) by omega),
        if_neg hj0]

/-- B_{k+1} first column: vertex 1 connects to vertex 0 with weight -1. -/
theorem B_first_col (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    CartanMatrix.B (k + 1) (Fin.succ j) 0 =
    if j.val = 0 then -1 else 0 := by
  have hj := j.isLt
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.val_zero, Fin.val_succ]
  rw [if_neg (by simp [Fin.ext_iff]), if_neg (show ¬(j.val + 1 + 1 = 0) by omega)]
  by_cases hj0 : j.val = 0
  · rw [if_pos (show 0 + 1 = j.val + 1 by omega), if_pos hj0]
  · rw [if_neg (show ¬(0 + 1 = j.val + 1) by omega), if_neg hj0]

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

/-- Deleting vertex 0 of C_{k+1} gives C_k. -/
theorem C_succ_eq_C (k : ℕ) (i j : Fin k) :
    CartanMatrix.C (k + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.C k i j := by
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.succ_inj, Fin.val_succ]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

/-- C_{k+1} first row: vertex 0 connects only to vertex 1 with weight -1. -/
theorem C_first_row (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    CartanMatrix.C (k + 1) 0 (Fin.succ j) =
    if j.val = 0 then -1 else 0 := by
  have hj := j.isLt
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.val_zero, Fin.val_succ]
  rw [if_neg (by simp [Fin.ext_iff])]
  by_cases hj0 : j.val = 0
  · rw [if_pos (show 0 + 1 = j.val + 1 by omega), if_pos hj0]
  · rw [if_neg (show ¬(0 + 1 = j.val + 1) by omega),
        if_neg (show ¬(j.val + 1 + 1 = 0) by omega),
        if_neg hj0]

/-- C_{k+1} first column: vertex 1 connects to vertex 0 with weight -1. -/
theorem C_first_col (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    CartanMatrix.C (k + 1) (Fin.succ j) 0 =
    if j.val = 0 then -1 else 0 := by
  have hj := j.isLt
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.val_zero, Fin.val_succ]
  rw [if_neg (by simp [Fin.ext_iff]), if_neg (show ¬(j.val + 1 + 1 = 0) by omega)]
  by_cases hj0 : j.val = 0
  · rw [if_pos (show 0 + 1 = j.val + 1 by omega),
        if_neg (show ¬(j.val + 1 = k + 1 - 1) by omega),
        if_pos hj0]
  · rw [if_neg (show ¬(0 + 1 = j.val + 1) by omega), if_neg hj0]

/-- Deleting the last vertex of D_{k+1} gives A_k when k ≥ 3. -/
theorem D_castSucc_eq_A (k : ℕ) (hk : 3 ≤ k) (i j : Fin k) :
    CartanMatrix.D (k + 1) (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A k i j := by
  simp only [CartanMatrix.D, CartanMatrix.A, Matrix.of_apply, Fin.castSucc_inj, Fin.val_castSucc]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

/-- A sub-path of D_{n+2} starting at offset c gives A_k, provided all indices
    stay in the path portion (away from the fork). -/
theorem D_path_shift_eq_A (k : ℕ) (n c : ℕ) (hn : 3 ≤ n + 2)
    (hc : c + k ≤ n) (i j : Fin k) :
    CartanMatrix.D (n + 2) ⟨i.val + c, by omega⟩ ⟨j.val + c, by omega⟩ =
    CartanMatrix.A k i j := by
  simp only [CartanMatrix.D, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

/-- Fork entries of D_{n+2}: the fork vertex n-1 connects to n-2, n, n+1 with entry -1. -/
theorem D_fork_entry (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) (ha : a < n + 2) (hb : b < n + 2)
    (hab : a = n - 1 ∧ (b = n - 2 ∨ b = n ∨ b = n + 1) ∨
           b = n - 1 ∧ (a = n - 2 ∨ a = n ∨ a = n + 1)) :
    CartanMatrix.D (n + 2) ⟨a, ha⟩ ⟨b, hb⟩ = -1 := by
  simp [CartanMatrix.D, Fin.ext_iff]; rcases hab with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases h with rfl | rfl | rfl <;> split_ifs <;> omega

/-- Non-adjacent fork entries of D_{n+2}: pp↔fl1, pp↔fl2, fl1↔fl2 all give 0. -/
theorem D_fork_zero (n : ℕ) (hn : 2 ≤ n) (a b : ℕ) (ha : a < n + 2) (hb : b < n + 2)
    (hab : a = n - 2 ∧ (b = n ∨ b = n + 1) ∨
           b = n - 2 ∧ (a = n ∨ a = n + 1) ∨
           a = n ∧ b = n + 1 ∨ b = n ∧ a = n + 1) :
    CartanMatrix.D (n + 2) ⟨a, ha⟩ ⟨b, hb⟩ = 0 := by
  simp [CartanMatrix.D, Fin.ext_iff]
  rcases hab with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
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

/-- Deleting vertex 0 of D_{k+1} gives D_k when k ≥ 4. -/
theorem D_succ_eq_D (k : ℕ) (hk : 4 ≤ k) (i j : Fin k) :
    CartanMatrix.D (k + 1) (Fin.succ i) (Fin.succ j) = CartanMatrix.D k i j := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.succ_inj, Fin.val_succ]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

/-- D_{k+1} first row: vertex 0 connects only to vertex 1 when k ≥ 4. -/
theorem D_first_row (k : ℕ) (hk : 4 ≤ k) (j : Fin k) :
    CartanMatrix.D (k + 1) 0 (Fin.succ j) =
    if j.val = 0 then -1 else 0 := by
  have hj := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_zero, Fin.val_succ]
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases hj0 : j.val = 0
  · rw [if_pos ⟨by omega, by omega⟩,
        show (if j.val = 0 then (-1 : ℤ) else 0) = -1 from if_pos hj0]
  · rw [if_neg (by push_neg; omega),
        if_neg (by push_neg; omega),
        if_neg (by push_neg; omega),
        if_neg (fun ⟨_, h⟩ => by cases h with | inl h => omega | inr h => omega),
        show (if j.val = 0 then (-1 : ℤ) else 0) = 0 from if_neg hj0]

/-- D_{k+1} first column: vertex 0 connects only to vertex 1 when k ≥ 4. -/
theorem D_first_col (k : ℕ) (hk : 4 ≤ k) (j : Fin k) :
    CartanMatrix.D (k + 1) (Fin.succ j) 0 =
    if j.val = 0 then -1 else 0 := by
  rw [show CartanMatrix.D (k+1) (Fin.succ j) 0 =
      CartanMatrix.D (k+1) 0 (Fin.succ j) from by
    have := congr_fun (congr_fun (CartanMatrix.D_isSymm (n := k + 1)) 0) (Fin.succ j)
    rwa [Matrix.transpose_apply] at this]
  exact D_first_row k hk j

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

-- ═══════════════════════════════════════════════════════════
-- Row sum lemmas for B, C, D (used for weight-2 contradictions)
-- ═══════════════════════════════════════════════════════════

/-- C_k row sums: row 0 sums to 1, all other rows sum to 0. -/
theorem C_rowSum (k : ℕ) (hk : 2 ≤ k) (i : Fin k) :
    ∑ j : Fin k, CartanMatrix.C k i j = if i.val = 0 then 1 else 0 := by
  suffices ∀ k, 2 ≤ k → ∀ i : Fin k,
      ∑ j, CartanMatrix.C k i j = if i.val = 0 then 1 else 0 from this k hk i
  intro k; induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk i
    by_cases hk1 : k = 1
    · subst hk1; fin_cases i <;> native_decide
    have hk2 : 2 ≤ k := by omega
    rw [Fin.sum_univ_succ]
    match i with
    | ⟨0, hi0⟩ =>
      -- Row 0: C(0,0) + ∑_j C(0, succ j) = 1
      -- First evaluate ↑⟨0, ...⟩ = 0
      simp only [show (⟨0, hi0⟩ : Fin (k+1)).val = 0 from rfl, ↓reduceIte]
      -- C(0,0) = 2
      have h00 : CartanMatrix.C (k + 1) ⟨0, hi0⟩ 0 = 2 := by simp [CartanMatrix.C]
      rw [h00]
      -- ∑_j C(0, succ j): rewrite using C_first_row
      have hfr : ∀ j : Fin k, CartanMatrix.C (k + 1) ⟨0, hi0⟩ (Fin.succ j) =
          if j.val = 0 then -1 else 0 := by
        intro j; show CartanMatrix.C (k+1) 0 (Fin.succ j) = _
        exact C_first_row k hk2 j
      simp_rw [hfr]
      rw [Fintype.sum_eq_single (⟨0, by omega⟩ : Fin k) (by
        intro j hj; rw [if_neg (show j.val ≠ 0 from fun h => hj (Fin.ext h))])]
      norm_num
    | ⟨i' + 1, hi'⟩ =>
      simp only [show (⟨i' + 1, _⟩ : Fin (k + 1)).val = i' + 1 from rfl,
        show i' + 1 ≠ 0 from by omega, ↓reduceIte]
      have hfc : CartanMatrix.C (k + 1) ⟨i' + 1, hi'⟩ 0 =
          if (⟨i', by omega⟩ : Fin k).val = 0 then -1 else 0 := by
        rw [show (⟨i' + 1, hi'⟩ : Fin (k + 1)) = Fin.succ ⟨i', by omega⟩ from rfl]
        exact C_first_col k hk2 ⟨i', by omega⟩
      rw [hfc]
      have : ∀ j : Fin k, CartanMatrix.C (k + 1) ⟨i' + 1, hi'⟩ (Fin.succ j) =
          CartanMatrix.C k ⟨i', by omega⟩ j := by
        intro j
        rw [show (⟨i' + 1, hi'⟩ : Fin (k + 1)) = Fin.succ ⟨i', by omega⟩ from rfl]
        exact C_succ_eq_C k ⟨i', by omega⟩ j
      simp_rw [this, ih hk2 ⟨i', by omega⟩]; split_ifs <;> omega

/-- B_k marks vector: f(j) = 2 except f(k-1) = 1. -/
def B_marks (k : ℕ) (j : Fin k) : ℤ := if j.val + 1 = k then 1 else 2

/-- B_k · B_marks = (2, 0, ..., 0). -/
theorem B_mulVec_marks (k : ℕ) (hk : 2 ≤ k) (i : Fin k) :
    ∑ j : Fin k, CartanMatrix.B k i j * B_marks k j = if i.val = 0 then 2 else 0 := by
  suffices ∀ k, 2 ≤ k → ∀ i : Fin k,
      ∑ j, CartanMatrix.B k i j * B_marks k j = if i.val = 0 then 2 else 0 from this k hk i
  intro k; induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk i
    by_cases hk1 : k = 1
    · subst hk1; fin_cases i <;> native_decide
    have hk2 : 2 ≤ k := by omega
    rw [Fin.sum_univ_succ]
    have hf0 : B_marks (k+1) 0 = 2 := by simp [B_marks]; omega
    have hfs : ∀ j : Fin k, B_marks (k+1) (Fin.succ j) = B_marks k j := by
      intro j; simp only [B_marks, Fin.val_succ]
      show (if j.val + 1 + 1 = k + 1 then (1:ℤ) else 2) = if j.val + 1 = k then 1 else 2
      split_ifs <;> omega
    match i with
    | ⟨0, hi0⟩ =>
      simp only [show (⟨0, hi0⟩ : Fin (k+1)).val = 0 from rfl, ↓reduceIte]
      have h00 : CartanMatrix.B (k + 1) ⟨0, hi0⟩ 0 = 2 := by simp [CartanMatrix.B]
      rw [h00, hf0]
      have hfr : ∀ j : Fin k, CartanMatrix.B (k + 1) ⟨0, hi0⟩ (Fin.succ j) =
          if j.val = 0 then -1 else 0 := by
        intro j; show CartanMatrix.B (k+1) 0 (Fin.succ j) = _; exact B_first_row k hk2 j
      simp_rw [hfr, hfs]
      rw [Fintype.sum_eq_single (⟨0, by omega⟩ : Fin k) (by
        intro j hj; rw [if_neg (show j.val ≠ 0 from fun h => hj (Fin.ext h))]; ring)]
      simp only [show (⟨0, by omega⟩ : Fin k).val = 0 from rfl, ↓reduceIte]
      have : B_marks k ⟨0, by omega⟩ = 2 := by
        simp only [B_marks, show (⟨0, by omega⟩ : Fin k).val = 0 from rfl]; split_ifs <;> omega
      linarith
    | ⟨i' + 1, hi'⟩ =>
      simp only [show (⟨i' + 1, _⟩ : Fin (k + 1)).val = i' + 1 from rfl,
        show i' + 1 ≠ 0 from by omega, ↓reduceIte]
      have hfc : CartanMatrix.B (k + 1) ⟨i' + 1, hi'⟩ 0 =
          if (⟨i', by omega⟩ : Fin k).val = 0 then -1 else 0 := by
        rw [show (⟨i' + 1, hi'⟩ : Fin (k + 1)) = Fin.succ ⟨i', by omega⟩ from rfl]
        exact B_first_col k hk2 ⟨i', by omega⟩
      rw [hfc, hf0]
      have : ∀ j : Fin k, CartanMatrix.B (k + 1) ⟨i' + 1, hi'⟩ (Fin.succ j) =
          CartanMatrix.B k ⟨i', by omega⟩ j := by
        intro j
        rw [show (⟨i' + 1, hi'⟩ : Fin (k + 1)) = Fin.succ ⟨i', by omega⟩ from rfl]
        exact B_succ_eq_B k ⟨i', by omega⟩ j
      simp_rw [this, hfs, ih hk2 ⟨i', by omega⟩]; split_ifs <;> omega

/-- D_k marks vector: f(j) = 2 except last two entries are 1. -/
def D_marks (k : ℕ) (j : Fin k) : ℤ := if j.val + 2 ≥ k then 1 else 2

/-- D_k · D_marks = (2, 0, ..., 0). -/
theorem D_mulVec_marks (k : ℕ) (hk : 4 ≤ k) (i : Fin k) :
    ∑ j : Fin k, CartanMatrix.D k i j * D_marks k j = if i.val = 0 then 2 else 0 := by
  suffices ∀ k, 4 ≤ k → ∀ i : Fin k,
      ∑ j, CartanMatrix.D k i j * D_marks k j = if i.val = 0 then 2 else 0 from this k hk i
  intro k; induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk i
    by_cases hk4 : k = 3
    · subst hk4; fin_cases i <;> native_decide
    have hk4' : 4 ≤ k := by omega
    rw [Fin.sum_univ_succ]
    have hf0 : D_marks (k+1) 0 = 2 := by simp [D_marks]; omega
    have hfs : ∀ j : Fin k, D_marks (k+1) (Fin.succ j) = D_marks k j := by
      intro j; simp only [D_marks, Fin.val_succ]; split_ifs <;> omega
    match i with
    | ⟨0, hi0⟩ =>
      simp only [show (⟨0, hi0⟩ : Fin (k+1)).val = 0 from rfl, ↓reduceIte]
      have h00 : CartanMatrix.D (k + 1) ⟨0, hi0⟩ 0 = 2 := by simp [CartanMatrix.D]
      rw [h00, hf0]
      have hfr : ∀ j : Fin k, CartanMatrix.D (k + 1) ⟨0, hi0⟩ (Fin.succ j) =
          if j.val = 0 then -1 else 0 := by
        intro j; show CartanMatrix.D (k+1) 0 (Fin.succ j) = _; exact D_first_row k hk4' j
      simp_rw [hfr, hfs]
      rw [Fintype.sum_eq_single (⟨0, by omega⟩ : Fin k) (by
        intro j hj; rw [if_neg (show j.val ≠ 0 from fun h => hj (Fin.ext h))]; ring)]
      simp only [show (⟨0, by omega⟩ : Fin k).val = 0 from rfl, ↓reduceIte]
      have : D_marks k ⟨0, by omega⟩ = 2 := by
        simp only [D_marks, show (⟨0, by omega⟩ : Fin k).val = 0 from rfl]; split_ifs <;> omega
      linarith
    | ⟨i' + 1, hi'⟩ =>
      simp only [show (⟨i' + 1, _⟩ : Fin (k + 1)).val = i' + 1 from rfl,
        show i' + 1 ≠ 0 from by omega, ↓reduceIte]
      have hfc : CartanMatrix.D (k + 1) ⟨i' + 1, hi'⟩ 0 =
          if (⟨i', by omega⟩ : Fin k).val = 0 then -1 else 0 := by
        rw [show (⟨i' + 1, hi'⟩ : Fin (k + 1)) = Fin.succ ⟨i', by omega⟩ from rfl]
        exact D_first_col k hk4' ⟨i', by omega⟩
      rw [hfc, hf0]
      have : ∀ j : Fin k, CartanMatrix.D (k + 1) ⟨i' + 1, hi'⟩ (Fin.succ j) =
          CartanMatrix.D k ⟨i', by omega⟩ j := by
        intro j
        rw [show (⟨i' + 1, hi'⟩ : Fin (k + 1)) = Fin.succ ⟨i', by omega⟩ from rfl]
        exact D_succ_eq_D k hk4' ⟨i', by omega⟩ j
      simp_rw [this, hfs, ih hk4' ⟨i', by omega⟩]; split_ifs <;> omega

/-- A sub-path of B_k starting at offset c gives B_m where m = k - c. -/
theorem B_shift (k c : ℕ) (hc : c + 2 ≤ k) (i j : Fin (k - c)) :
    CartanMatrix.B k ⟨i.val + c, by omega⟩ ⟨j.val + c, by omega⟩ =
    CartanMatrix.B (k - c) i j := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> omega

/-- A sub-path of C_k starting at offset c gives C_m where m = k - c. -/
theorem C_shift (k c : ℕ) (hc : c + 2 ≤ k) (i j : Fin (k - c)) :
    CartanMatrix.C k ⟨i.val + c, by omega⟩ ⟨j.val + c, by omega⟩ =
    CartanMatrix.C (k - c) i j := by
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> omega

/-- Column 0 of B_m: B_m(i, 0) = 2 if i=0, -1 if i=1, 0 otherwise. -/
theorem B_col_zero (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    CartanMatrix.B m i ⟨0, by omega⟩ = if i.val = 0 then 2 else if i.val = 1 then -1 else 0 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  have := i.isLt; split_ifs <;> omega

/-- B_m · (nullvec_sub) = e₁ where nullvec_sub(0) = 1, nullvec_sub(j≥1) = B_marks(m,j).
    Derived from B_mulVec_marks and the column-0 structure. -/
theorem B_mulVec_nullsub (m : ℕ) (hm : 3 ≤ m) (i : Fin m) :
    ∑ j : Fin m, CartanMatrix.B m i j *
      (if j.val = 0 then 1 else B_marks m j) =
    if i.val = 1 then 1 else 0 := by
  -- nullsub = B_marks - e₀ (since B_marks(0) = 2 and nullsub(0) = 1)
  -- B_m · nullsub = B_m · B_marks - B_m · e₀ = (2,0,...) - col₀(B_m) = (0,1,0,...)
  have hBm := B_mulVec_marks m (by omega) i
  -- Express nullsub as B_marks - (1,0,...,0)
  have hsplit : ∀ j : Fin m, CartanMatrix.B m i j *
      (if j.val = 0 then 1 else B_marks m j) =
      CartanMatrix.B m i j * B_marks m j - (if j.val = 0 then CartanMatrix.B m i j else 0) := by
    intro j; by_cases hj : j.val = 0
    · rw [if_pos hj, if_pos hj]; have : B_marks m j = 2 := by
        simp [B_marks]; omega
      rw [this]; ring
    · rw [if_neg hj, if_neg hj]; ring
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [hBm]
  have hcol : ∑ j : Fin m, (if j.val = 0 then CartanMatrix.B m i j else 0) =
      CartanMatrix.B m i ⟨0, by omega⟩ := by
    rw [Fintype.sum_eq_single (⟨0, by omega⟩ : Fin m) (fun j hj => by
      rw [if_neg (show j.val ≠ 0 from fun h => hj (Fin.ext h))])]
    rw [show (⟨0, by omega⟩ : Fin m).val = 0 from rfl, if_pos rfl]
  rw [hcol, B_col_zero m (by omega)]
  split_ifs <;> omega

-- ═══════════════════════════════════════════════════════════
/-- Shifting D: D_{k+c}(⟨i+c,_⟩, ⟨j+c,_⟩) = D_k(i, j) when k ≥ 4. -/
theorem D_shift (k c : ℕ) (hk : 4 ≤ k) (i j : Fin k) :
    CartanMatrix.D (k + c) ⟨i.val + c, by omega⟩ ⟨j.val + c, by omega⟩ =
    CartanMatrix.D k i j := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
  have hi := i.isLt; have hj := j.isLt
  split_ifs <;> omega

-- Sum reindexing helper
-- ═══════════════════════════════════════════════════════════

/-- Shifting a sum: terms below threshold p are zero, terms at or above are reindexed. -/
theorem sum_shift {n p : ℕ} (hp : p ≤ n) (f : Fin (n - p) → ℚ) :
    ∑ q : Fin n, (if h : p ≤ q.val then f ⟨q.val - p, by omega⟩ else (0 : ℚ)) =
    ∑ j : Fin (n - p), f j := by
  have hn : p + (n - p) = n := Nat.add_sub_cancel' hp
  trans ∑ q : Fin (p + (n - p)),
      (if h : p ≤ q.val then f ⟨q.val - p, by omega⟩ else (0 : ℚ))
  · exact (Fintype.sum_equiv (finCongr hn) _ _ (fun x => by simp [finCongr])).symm
  rw [Fin.sum_univ_add]
  have hleft : ∑ i : Fin p, (if h : p ≤ (Fin.castAdd (n - p) i).val then
      f ⟨(Fin.castAdd (n - p) i).val - p, by omega⟩ else (0 : ℚ)) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    rw [dif_neg (by simp [Fin.val_castAdd])]
  rw [hleft, zero_add]
  congr 1; ext j
  rw [dif_pos (by simp [Fin.val_natAdd])]
  congr 1; ext; simp [Fin.val_natAdd]

end BLD.Lie.Cartan
