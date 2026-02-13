/- BLD Calculus — Cartan Classification: Graph Structure

   Coxeter weight bounds, acyclicity, degree bounds, vertex deletion,
   and leaf existence for positive-definite GCMs.
-/

import BLD.Lie.Cartan.Forbidden

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

-- ═══════════════════════════════════════════════════════════
-- Coxeter weight bound
-- ═══════════════════════════════════════════════════════════

/-- The Coxeter weight of an edge in a GCM: w(i,j) = A(i,j) * A(j,i).
    For connected vertices i ≠ j, this is a positive integer ≤ 3
    in a positive definite GCM. -/
def coxeterWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℤ :=
  A i j * A j i

/-- Helper: a sum over Fin n with only 2 nonzero terms at i, j. -/
theorem sum_two {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (f : Fin n → ℚ) (hf : ∀ k, k ≠ i → k ≠ j → f k = 0) :
    ∑ k, f k = f i + f j := by
  rw [show ∑ k, f k = ∑ k ∈ ({i, j} : Finset (Fin n)), f k from by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk; exact hf k hk.1 hk.2]
  exact Finset.sum_pair hij

/-- Helper: a sum over Fin n with only 3 nonzero terms at i, j, k. -/
theorem sum_three {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (f : Fin n → ℚ) (hf : ∀ l, l ≠ i → l ≠ j → l ≠ k → f l = 0) :
    ∑ l, f l = f i + f j + f k := by
  rw [show ∑ l, f l = ∑ l ∈ ({i, j, k} : Finset (Fin n)), f l from by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    push_neg at hl; exact hf l hl.1 hl.2.1 hl.2.2]
  rw [Finset.sum_insert (show i ∉ ({j, k} : Finset _) by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hij, hik⟩)]
  rw [Finset.sum_pair hjk]; ring

/-- Helper: a sum over Fin n with only 4 nonzero terms. -/
theorem sum_four {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (f : Fin n → ℚ) (hf : ∀ m, m ≠ i → m ≠ j → m ≠ k → m ≠ l → f m = 0) :
    ∑ m, f m = f i + f j + f k + f l := by
  rw [show ∑ m, f m = ∑ m ∈ ({i, j, k, l} : Finset (Fin n)), f m from by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro m _ hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    push_neg at hm; exact hf m hm.1 hm.2.1 hm.2.2.1 hm.2.2.2]
  rw [Finset.sum_insert (show i ∉ ({j, k, l} : Finset _) by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hij, hik, hil⟩)]
  rw [Finset.sum_insert (show j ∉ ({k, l} : Finset _) by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hjk, hjl⟩)]
  rw [Finset.sum_pair hkl]; ring

/-- Helper: a sum over Fin n with only 5 nonzero terms. -/
theorem sum_five {n : ℕ} {a b c d e : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e)
    (f : Fin n → ℚ) (hf : ∀ m, m ≠ a → m ≠ b → m ≠ c → m ≠ d → m ≠ e → f m = 0) :
    ∑ m, f m = f a + f b + f c + f d + f e := by
  rw [show ∑ m, f m = ∑ m ∈ ({a, b, c, d, e} : Finset (Fin n)), f m from by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro m _ hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    push_neg at hm; exact hf m hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2]
  rw [Finset.sum_insert (show a ∉ ({b, c, d, e} : Finset _) by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hab, hac, had, hae⟩)]
  rw [Finset.sum_insert (show b ∉ ({c, d, e} : Finset _) by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hbc, hbd, hbe⟩)]
  rw [Finset.sum_insert (show c ∉ ({d, e} : Finset _) by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hcd, hce⟩)]
  rw [Finset.sum_pair hde]; ring

/-- In a positive definite GCM, A(i,j) * A(j,i) < 4 (Coxeter weight ≤ 3).
    Proof: the test vector v(i) = 1, v(j) = -A(j,i)/2 gives
    qform = d_i · (4 - A(i,j)·A(j,i)) / 2, which is ≤ 0 when the product ≥ 4. -/
theorem coxeter_weight_lt_four {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (hS : IsSymmetrizable A) (hPD : IsPosDef A hS)
    (i j : Fin n) (hij : i ≠ j) :
    coxeterWeight A i j < 4 := by
  unfold coxeterWeight; by_contra hge; push_neg at hge
  -- hge : 4 ≤ A i j * A j i
  -- Test vector: v(i) = 1, v(j) = -(A j i)/2, else 0
  -- We avoid `let` to prevent normalization issues with rw
  set v : Fin n → ℚ := fun k =>
    if k = i then 1 else if k = j then -(↑(A j i : ℤ) : ℚ) / 2 else 0
  -- Key properties of v
  have v0 : ∀ k, k ≠ i → k ≠ j → v k = 0 := fun k h1 h2 => by
    simp only [v, if_neg h1, if_neg h2]
  have hv : v ≠ 0 := by
    intro h0; have := congr_fun h0 i
    simp only [v, if_pos rfl, Pi.zero_apply] at this
    exact one_ne_zero this
  -- Inner sum at row i: reduces to 2 - A(i,j)*A(j,i)/2
  have inner_i : ∑ s, (↑(A i s) : ℚ) * v s =
      2 - (↑(A i j : ℤ) : ℚ) * (↑(A j i : ℤ) : ℚ) / 2 := by
    rw [sum_two hij (fun s => (↑(A i s) : ℚ) * v s)
      (fun k h1 h2 => by simp only [v0 k h1 h2, mul_zero])]
    simp only [v, if_pos rfl, if_neg (Ne.symm hij), hGCM.diag i]
    push_cast; ring
  -- Inner sum at row j: vanishes (A(j,i) - A(j,i) = 0)
  have inner_j : ∑ s, (↑(A j s) : ℚ) * v s = 0 := by
    rw [sum_two hij (fun s => (↑(A j s) : ℚ) * v s)
      (fun k h1 h2 => by simp only [v0 k h1 h2, mul_zero])]
    simp only [v, if_pos rfl, if_neg (Ne.symm hij), hGCM.diag j]
    push_cast; ring
  -- Outer sum: reduces to d_i * inner_i (the j term vanishes)
  have hq : qform hS.d A v =
      hS.d i * (2 - (↑(A i j : ℤ) : ℚ) * (↑(A j i : ℤ) : ℚ) / 2) := by
    rw [qform_eq_sum_mul,
        sum_two hij (fun r => hS.d r * v r * ∑ s, (↑(A r s) : ℚ) * v s)
          (fun k h1 h2 => by simp only [v0 k h1 h2]; ring)]
    simp only [v, if_pos rfl, if_neg (Ne.symm hij)]
    rw [inner_i, inner_j]; ring
  -- Show qform ≤ 0 (contradicting pos-def)
  have h_cast : (4 : ℚ) ≤ (↑(A i j : ℤ) : ℚ) * (↑(A j i : ℤ) : ℚ) := by
    exact_mod_cast hge
  have hq_le : qform hS.d A v ≤ 0 := by
    rw [hq]; nlinarith [hS.d_pos i]
  exact absurd (hPD v hv) (not_lt.mpr hq_le)

-- ═══════════════════════════════════════════════════════════
-- Coxeter weight properties
-- ═══════════════════════════════════════════════════════════

/-- In a GCM, Coxeter weights are non-negative (both off-diagonal entries ≤ 0). -/
theorem coxeter_weight_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (i j : Fin n) (hij : i ≠ j) :
    0 ≤ coxeterWeight A i j := by
  unfold coxeterWeight
  nlinarith [hGCM.off_diag_nonpos i j hij, hGCM.off_diag_nonpos j i hij.symm]

-- ═══════════════════════════════════════════════════════════
-- Acyclicity: no cycles in pos-def GCM graph
-- ═══════════════════════════════════════════════════════════

/-- If a principal submatrix (via embedding f : Fin m ↪ Fin n) has all
    integer row sums ≤ 0 and m ≥ 1, the full matrix is not positive definite.
    Proof: the all-ones vector on the image gives qform ≤ 0. -/
theorem not_posDef_of_submatrix_rowsum_nonpos {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℤ} (hS : IsSymmetrizable A)
    (f : Fin m ↪ Fin n) (hm : 0 < m)
    (hrow : ∀ i : Fin m, ∑ j : Fin m, A (f i) (f j) ≤ 0) :
    ¬ IsPosDef A hS := by
  apply not_posDef_of_nonpos hS (indicator f (fun _ => 1))
    (indicator_ne_zero f _ (fun h => absurd (congr_fun h ⟨0, hm⟩) one_ne_zero))
  rw [qform_eq_sum_mul]
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : ∃ l, f l = i
  · obtain ⟨l, rfl⟩ := hi
    simp only [indicator_apply]
    suffices h : ∑ j, (↑(A (f l) j) : ℚ) * indicator f (fun _ => (1 : ℚ)) j ≤ 0 by
      nlinarith [hS.d_pos (f l)]
    rw [show ∑ j : Fin n, (↑(A (f l) j) : ℚ) * indicator f (fun _ => (1 : ℚ)) j =
        ∑ j ∈ Finset.univ.map f, (↑(A (f l) j) : ℚ) * indicator f (fun _ => 1) j from by
      symm; apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists] at hj
      simp [indicator_zero f _ j hj],
    Finset.sum_map]
    simp_rw [indicator_apply, mul_one]
    exact_mod_cast hrow l
  · simp [indicator_zero f _ i (not_exists.mp hi)]

/-- A pos-def GCM graph has no cycles: if k ≥ 3 distinct vertices form a cycle
    (each adjacent to the next, cyclically), the matrix is not positive definite.
    Proof: each cycle row sum is 2 + (≤ -1) + (≤ -1) + (rest ≤ 0) ≤ 0. -/
theorem not_posDef_of_cycle {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (hS : IsSymmetrizable A) (hk : 3 ≤ k)
    (f : Fin k ↪ Fin n)
    (hadj : ∀ l : Fin k,
      A (f l) (f ⟨(l.val + 1) % k, Nat.mod_lt _ (by omega)⟩) ≠ 0) :
    ¬ IsPosDef A hS := by
  apply not_posDef_of_submatrix_rowsum_nonpos hS f (by omega)
  intro l
  -- Decompose: diagonal + off-diagonal
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), hGCM.diag (f l)]
  -- Need: Σ_{m ≠ l} A(f l, f m) ≤ -2
  suffices h : ∑ m ∈ Finset.univ.erase l, A (f l) (f m) ≤ -2 by omega
  -- Successor and predecessor in the cycle
  let s : Fin k := ⟨(l.val + 1) % k, Nat.mod_lt _ (by omega)⟩
  let p : Fin k := ⟨(l.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  -- Eliminate % using Nat.mod_eq_of_lt / Nat.mod_self before omega
  have hsl : s ≠ l := by
    intro h; have hv : (l.val + 1) % k = l.val := congrArg Fin.val h
    by_cases heq : l.val + 1 = k
    · rw [heq, Nat.mod_self] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega : l.val + 1 < k)] at hv; omega
  have hpl : p ≠ l := by
    intro h; have hv : (l.val + k - 1) % k = l.val := congrArg Fin.val h
    by_cases h0 : l.val = 0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)] at hv; omega
    · rw [show l.val + k - 1 = l.val - 1 + k from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.val - 1 < k)] at hv; omega
  have hsp : s ≠ p := by
    intro h; have hv : (l.val + 1) % k = (l.val + k - 1) % k := congrArg Fin.val h
    by_cases heq : l.val + 1 = k
    · rw [heq, Nat.mod_self] at hv
      by_cases h0 : l.val = 0
      · omega  -- h0 + heq give k = 1, contradicts hk
      · rw [show l.val + k - 1 = l.val - 1 + k from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.val - 1 < k)] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega : l.val + 1 < k)] at hv
      by_cases h0 : l.val = 0
      · simp only [h0, Nat.zero_add] at hv
        rw [Nat.mod_eq_of_lt (by omega : k - 1 < k)] at hv; omega
      · rw [show l.val + k - 1 = l.val - 1 + k from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.val - 1 < k)] at hv; omega
  -- Helper: distinctness of images
  have hne_ls : f l ≠ f s := fun h => absurd (f.injective h).symm hsl
  have hne_lp : f l ≠ f p := fun h => absurd (f.injective h).symm hpl
  -- Both ≤ -1: successor by hypothesis, predecessor by zero_iff
  have hs_adj : A (f l) (f s) ≤ -1 := by
    have h1 : A (f l) (f s) ≤ 0 := hGCM.off_diag_nonpos (f l) (f s) hne_ls
    have h2 : A (f l) (f s) ≠ 0 := hadj l
    omega
  have hp_adj : A (f l) (f p) ≤ -1 := by
    have h_eq : (⟨(p.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = l := by
      ext; show ((l.val + k - 1) % k + 1) % k = l.val
      by_cases h0 : l.val = 0
      · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k),
            show k - 1 + 1 = k from by omega, Nat.mod_self]
      · rw [show l.val + k - 1 = l.val - 1 + k from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.val - 1 < k),
            show l.val - 1 + 1 = l.val from by omega, Nat.mod_eq_of_lt l.isLt]
    have h1 := hadj p; rw [h_eq] at h1  -- h1 : A (f p) (f l) ≠ 0
    have h2 : A (f l) (f p) ≠ 0 := mt (hGCM.zero_iff (f l) (f p) hne_lp).mp h1
    have h3 : A (f l) (f p) ≤ 0 := hGCM.off_diag_nonpos (f l) (f p) hne_lp
    omega
  -- Extract s and p from the sum, bound the rest ≤ 0
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hsl, Finset.mem_univ s⟩),
      ← Finset.add_sum_erase _ _
        (Finset.mem_erase.mpr ⟨Ne.symm hsp, Finset.mem_erase.mpr ⟨hpl, Finset.mem_univ p⟩⟩)]
  have h_rest : ∑ m ∈ ((Finset.univ.erase l).erase s).erase p, A (f l) (f m) ≤ 0 :=
    Finset.sum_nonpos fun m hm => by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm
      exact hGCM.off_diag_nonpos (f l) (f m)
        (fun h => absurd (f.injective h).symm hm.2.2)
  linarith

-- ═══════════════════════════════════════════════════════════
-- D₄ uniqueness among Dynkin types
-- ═══════════════════════════════════════════════════════════

/-- D₄ is the unique Dynkin type with rank 4 and dimension 28.
    This means BLD's identification of so(8) is forced by the constants. -/
theorem D4_unique_type (t : DynkinType) (hr : t.rank = 4) (hd : t.dim = 28) :
    t = .D 4 (by omega) := by
  cases t with
  | A n h => simp [DynkinType.rank] at hr; subst hr; simp [DynkinType.dim] at hd
  | B n h => simp [DynkinType.rank] at hr; subst hr; simp [DynkinType.dim] at hd
  | C n h => simp [DynkinType.rank] at hr; subst hr; simp [DynkinType.dim] at hd
  | D n h => simp [DynkinType.rank] at hr; subst hr; rfl
  | E₆ => simp [DynkinType.rank] at hr
  | E₇ => simp [DynkinType.rank] at hr
  | E₈ => simp [DynkinType.rank] at hr
  | F₄ => simp [DynkinType.dim] at hd
  | G₂ => simp [DynkinType.rank] at hr

-- ═══════════════════════════════════════════════════════════
-- Classification infrastructure
-- ═══════════════════════════════════════════════════════════

/-- Delete vertex v from a matrix, giving a principal submatrix. -/
def deleteVertex {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (v : Fin (n+1)) :
    Matrix (Fin n) (Fin n) ℤ :=
  A.submatrix v.succAbove v.succAbove

theorem deleteVertex_isGCM {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ}
    (hGCM : IsGCM A) (v : Fin (n+1)) : IsGCM (deleteVertex A v) where
  diag i := by simp [deleteVertex, submatrix_apply, hGCM.diag]
  off_diag_nonpos i j h := by
    simp only [deleteVertex, submatrix_apply]
    exact hGCM.off_diag_nonpos _ _ (fun e => h (Fin.succAbove_right_injective e))
  zero_iff i j h := by
    simp only [deleteVertex, submatrix_apply]
    exact hGCM.zero_iff _ _ (fun e => h (Fin.succAbove_right_injective e))

noncomputable def deleteVertex_symmetrizable {n : ℕ}
    {A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ}
    (hSym : IsSymmetrizable A) (v : Fin (n+1)) :
    IsSymmetrizable (deleteVertex A v) where
  d i := hSym.d (v.succAbove i)
  d_pos i := hSym.d_pos _
  sym i j := by simp only [deleteVertex, submatrix_apply]; exact hSym.sym _ _

theorem deleteVertex_isPosDef {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ}
    {hSym : IsSymmetrizable A} (hPD : IsPosDef A hSym) (v : Fin (n+1)) :
    IsPosDef (deleteVertex A v) (deleteVertex_symmetrizable hSym v) := by
  intro x hx
  -- Reuse the existing indicator infrastructure to extend x by zero at v
  let f : Fin n ↪ Fin (n+1) := ⟨v.succAbove, Fin.succAbove_right_injective⟩
  have hy := indicator_ne_zero f x hx
  have hyv : indicator f x v = 0 :=
    indicator_zero f x v (fun l => Fin.succAbove_ne v l)
  have hyi : ∀ i, indicator f x (v.succAbove i) = x i := indicator_apply f x
  -- Relate submatrix qform to full-matrix qform with indicator extension
  suffices h : qform (deleteVertex_symmetrizable hSym v).d (deleteVertex A v) x =
      qform hSym.d A (indicator f x) by
    rw [h]; exact hPD _ hy
  simp only [qform, deleteVertex, submatrix_apply, deleteVertex_symmetrizable]
  -- Decompose full-matrix double sum: v-terms vanish, rest matches submatrix
  symm
  rw [Fin.sum_univ_succAbove _ v]
  simp only [hyv, zero_mul, mul_zero, sum_const_zero, zero_add]
  congr 1; ext i
  rw [Fin.sum_univ_succAbove _ v]
  simp only [hyv, mul_zero, zero_add, hyi]

/-- The number of neighbors of vertex i in a GCM. -/
noncomputable def gcmDegree {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => j ≠ i ∧ A i j ≠ 0)).card

/-- In a pos-def GCM, every vertex has degree ≤ 3.
    Proof: degree ≥ 4 would give a test vector with qform ≤ 0. -/
theorem gcmDegree_le_three {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (i : Fin n) : gcmDegree A i ≤ 3 := by
  by_contra hge; push_neg at hge
  let S := Finset.univ.filter (fun j : Fin n => j ≠ i ∧ A i j ≠ 0)
  change 4 ≤ S.card at hge
  have hS_sub : S ⊆ Finset.univ.erase i := fun k hk => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact Finset.mem_erase.mpr ⟨hk.1, Finset.mem_univ k⟩
  have hS_adj : ∀ k ∈ S, A i k ≤ -1 := fun k hk => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have := hGCM.off_diag_nonpos i k hk.1.symm; omega
  -- Test vector: w(i) = 2, w(j) = 1 for j ∈ S, else 0
  let w : Fin n → ℚ := fun k => if k = i then 2 else if k ∈ S then 1 else 0
  have hw : w ≠ 0 := by
    intro h; have := congr_fun h i
    simp only [w, if_pos rfl, Pi.zero_apply] at this; norm_num at this
  -- Inner sum at center row i ≤ 0
  have h_center : ∑ k, (A i k : ℚ) * w k ≤ 0 := by
    -- Extract the i-term, bound the rest
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [w, if_pos rfl, hGCM.diag i]; push_cast
    -- Goal: 2 * 2 + Σ_{k≠i} (↑(A i k)) * w k ≤ 0
    suffices h : ∑ k ∈ Finset.univ.erase i, (A i k : ℚ) * w k ≤ -4 by linarith
    calc ∑ k ∈ Finset.univ.erase i, (A i k : ℚ) * w k
        ≤ ∑ k ∈ Finset.univ.erase i, (if k ∈ S then (A i k : ℚ) else 0) := by
          apply Finset.sum_le_sum; intro k hk
          simp only [Finset.mem_erase] at hk
          simp only [w, if_neg hk.1]
          split_ifs with hkS
          · simp
          · simp
      _ = ∑ k ∈ S, (A i k : ℚ) := by
          rw [← Finset.sum_subset hS_sub (fun k _ hkS => if_neg hkS)]
          exact Finset.sum_congr rfl (fun k hk => if_pos hk)
      _ ≤ ∑ _k ∈ S, (-1 : ℚ) := by
          apply Finset.sum_le_sum; intro k hk
          exact_mod_cast hS_adj k hk
      _ = -(S.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ -4 := by
          have : (4 : ℚ) ≤ S.card := by exact_mod_cast hge
          linarith
  -- Inner sum at neighbor row r ∈ S ≤ 0
  have h_nbr : ∀ r, r ≠ i → r ∈ S → ∑ k, (A r k : ℚ) * w k ≤ 0 := by
    intro r hr_ne hr_S
    have hri : (A r i : ℚ) ≤ -1 := by
      have h1 := hGCM.off_diag_nonpos r i hr_ne
      have h2 : A i r ≠ 0 := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hr_S
        exact hr_S.2
      have h3 : A r i ≠ 0 := fun h => h2 ((hGCM.zero_iff r i hr_ne).mp h)
      have : A r i ≤ -1 := by omega
      exact_mod_cast this
    -- Extract i-term and r-term, bound the rest
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [w, if_pos rfl]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hr_ne, Finset.mem_univ r⟩)]
    simp only [if_neg hr_ne, if_pos hr_S, mul_one, hGCM.diag r]; push_cast
    -- Goal: ↑(A r i) * 2 + (2 + Σ rest) ≤ 0
    suffices h : ∑ k ∈ (Finset.univ.erase i).erase r, (A r k : ℚ) * w k ≤ 0 by linarith
    apply Finset.sum_nonpos; intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    simp only [w, if_neg hk.2]
    split_ifs with hkS
    · exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hGCM.off_diag_nonpos r k hk.1.symm) (by norm_num)
    · simp
  -- Combine: qform ≤ 0
  apply absurd (hPD w hw); push_neg
  rw [qform_eq_sum_mul]
  apply Finset.sum_nonpos; intro r _
  by_cases hr_i : r = i
  · rw [hr_i]; simp only [w, if_pos rfl]
    nlinarith [hSym.d_pos i, h_center]
  · by_cases hr_S : r ∈ S
    · simp only [w, if_neg hr_i, if_pos hr_S]
      nlinarith [hSym.d_pos r, h_nbr r hr_i hr_S]
    · simp only [w, if_neg hr_i, if_neg hr_S, mul_zero, zero_mul]; exact le_refl _

/-- The adjacency relation of toGraph is decidable. -/
instance toGraph_decRel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGCM A) :
    DecidableRel (toGraph A hGCM).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ A i j ≠ 0))

/-- gcmDegree equals the SimpleGraph degree of the associated graph. -/
theorem gcmDegree_eq_degree {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (v : Fin n) :
    gcmDegree A v = (toGraph A hGCM).degree v := by
  simp only [gcmDegree, SimpleGraph.degree]
  congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset, toGraph]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩

/-- A pos-def GCM graph is acyclic: any cycle would contradict positive-definiteness
    via not_posDef_of_cycle. -/
theorem isAcyclic_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym) :
    (toGraph A hGCM).IsAcyclic := by
  intro v c hc
  -- c is a cycle at v in toGraph A hGCM, with length ≥ 3
  have hlen : 3 ≤ c.length := by
    have h1 := hc.three_le_length
    exact h1
  -- Extract vertices: getVert is injective on {0, ..., length-1}
  let k := c.length
  let f : Fin k → Fin n := fun i => c.getVert i
  -- f is injective (from IsCycle.getVert_injOn')
  have hf_inj : Function.Injective f := by
    intro a b hab
    have ha : (a : ℕ) ≤ k - 1 := by omega
    have hb : (b : ℕ) ≤ k - 1 := by omega
    exact Fin.ext (hc.getVert_injOn' (Set.mem_setOf.mpr ha) (Set.mem_setOf.mpr hb) hab)
  -- Each vertex is adjacent to its successor (cyclically)
  have hadj : ∀ l : Fin k,
      A (f l) (f ⟨(l.val + 1) % k, Nat.mod_lt _ (by omega)⟩) ≠ 0 := by
    intro l
    have h_adj := c.adj_getVert_succ (by omega : l.val < c.length)
    simp only [toGraph] at h_adj
    by_cases hl : l.val + 1 < k
    · -- l+1 < k: getVert (l+1 % k) = getVert (l+1)
      simp only [f, Nat.mod_eq_of_lt hl]
      exact h_adj.2
    · -- l+1 = k: wrap around, getVert (l+1) = getVert k = v = getVert 0
      have hlk : l.val + 1 = k := by omega
      simp only [f, hlk, Nat.mod_self]
      -- h_adj says Adj (getVert l) (getVert (l+1))
      -- getVert (l+1) = getVert k = v = getVert 0
      have hgk : c.getVert (l.val + 1) = c.getVert 0 := by
        rw [hlk]; rw [c.getVert_length]; exact c.getVert_zero.symm
      rw [hgk] at h_adj
      exact h_adj.2
  -- Apply not_posDef_of_cycle
  exact absurd hPD (not_posDef_of_cycle hGCM hSym hlen ⟨f, hf_inj⟩ hadj)

/-- In a connected pos-def GCM on ≥ 3 vertices, some vertex has degree 1. -/
theorem exists_leaf {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A)
    (hConn : IsConnected A hGCM) (hPD : IsPosDef A hSym) :
    ∃ v : Fin (n+3), gcmDegree A v = 1 := by
  -- The graph is a tree (connected + acyclic)
  have hTree : (toGraph A hGCM).IsTree :=
    ⟨hConn, isAcyclic_of_posDef hGCM hSym hPD⟩
  -- Nontrivial: Fin (n+3) has ≥ 2 elements
  haveI : Nontrivial (Fin (n+3)) := inferInstance
  -- A nontrivial tree has a vertex of degree 1
  obtain ⟨v, hv⟩ := hTree.exists_vert_degree_one_of_nontrivial
  exact ⟨v, by rw [gcmDegree_eq_degree hGCM]; exact hv⟩

/-- Deleting a leaf from a connected GCM preserves connectivity.
    The leaf's unique neighbor remains connected to all other vertices
    via paths that didn't use the leaf. -/
theorem deleteVertex_connected_of_leaf {n : ℕ}
    {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hConn : IsConnected A hGCM)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1) :
    IsConnected (deleteVertex A v) (deleteVertex_isGCM hGCM v) := by
  -- Translate gcmDegree to graph degree
  have hdeg : (toGraph A hGCM).degree v = 1 := by
    rw [← gcmDegree_eq_degree hGCM]; exact hleaf
  -- Mathlib: removing a degree-1 vertex preserves connectivity
  have hind := hConn.induce_compl_singleton_of_degree_eq_one hdeg
  -- Build graph isomorphism: deleted graph ≃g induced subgraph on {v}ᶜ
  let e : toGraph (deleteVertex A v) (deleteVertex_isGCM hGCM v) ≃g
      (toGraph A hGCM).induce ({v}ᶜ : Set (Fin (n+3))) := {
    toEquiv := Equiv.ofBijective
      (fun i => ⟨v.succAbove i,
        Set.mem_compl_singleton_iff.mpr (Fin.succAbove_ne v i)⟩)
      ⟨fun a b h => Fin.succAbove_right_injective (congrArg Subtype.val h),
       fun ⟨w, hw⟩ => by
         rw [Set.mem_compl_singleton_iff] at hw
         obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hw
         exact ⟨z, Subtype.ext hz⟩⟩
    map_rel_iff' {a b} := by
      simp only [Equiv.ofBijective_apply, toGraph, deleteVertex, submatrix_apply]
      constructor
      · rintro ⟨hne, hA⟩
        exact ⟨fun h => hne (congrArg (Fin.succAbove v) h), hA⟩
      · rintro ⟨hne, hA⟩
        exact ⟨fun h => hne (Fin.succAbove_right_injective h), hA⟩ }
  -- Transfer connectivity via the isomorphism
  exact e.connected_iff.mpr hind

/-- Given a sub-matrix matching DynkinType t' and a leaf vertex v,
    determine the full DynkinType of the extended matrix.
    This is the combinatorial heart of the Cartan classification. -/
theorem cartanEquiv_rank_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {t : DynkinType} (h : CartanEquiv A t.cartanMatrix.2) : n = t.cartanMatrix.1 := by
  obtain ⟨e, _⟩ := h
  have := e.bijective
  exact Fintype.card_fin n ▸ Fintype.card_fin t.cartanMatrix.1 ▸
    Fintype.card_congr e ▸ rfl

/-- In a connected GCM on ≥ 2 vertices, every vertex has at least one neighbor. -/
theorem exists_neighbor_of_connected {m : ℕ} {B : Matrix (Fin (m+2)) (Fin (m+2)) ℤ}
    (hGCM : IsGCM B) (hConn : IsConnected B hGCM) (i : Fin (m+2)) :
    ∃ j, j ≠ i ∧ B i j ≠ 0 := by
  by_contra hall; push_neg at hall
  have hiso : ∀ j, ¬(toGraph B hGCM).Adj i j := by
    intro j ⟨hne, hA⟩; exact hA (hall j hne.symm)
  -- Pick any other vertex (exists since m+2 ≥ 2)
  obtain ⟨k, hk⟩ := exists_ne i
  -- Connected: walk from i to k
  obtain ⟨w⟩ := hConn.preconnected i k
  -- Walk has positive length since i ≠ k
  have hlen : 0 < w.length := by
    rcases w with _ | ⟨_, _⟩
    · exact absurd rfl hk
    · simp [SimpleGraph.Walk.length]
  -- First step: getVert 0 and getVert 1 are adjacent
  have hadj := w.adj_getVert_succ (i := 0) hlen
  rw [w.getVert_zero] at hadj
  exact hiso _ hadj

end BLD.Lie.Cartan
