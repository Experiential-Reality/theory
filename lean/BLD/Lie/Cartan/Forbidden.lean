/- BLD Calculus — Cartan Classification: Forbidden Subgraph Analysis

   Infrastructure for showing matrices are not positive definite via
   null vectors, indicator extensions, and affine Dynkin diagrams.
-/

import BLD.Lie.Cartan.Defs

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

-- ═══════════════════════════════════════════════════════════
-- Forbidden subgraph analysis — infrastructure
-- ═══════════════════════════════════════════════════════════

/-- qform as Σᵢ dᵢ·xᵢ·(Σⱼ Aᵢⱼ·xⱼ), pulling xᵢ out of the inner sum. -/
theorem qform_eq_sum_mul {n : ℕ} (d : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℚ) :
    qform d A x = ∑ i, d i * x i * ∑ j, (A i j : ℚ) * x j := by
  simp only [qform, Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; ring

/-- If every outer term vanishes (either xᵢ = 0 or the inner sum is 0), qform is 0. -/
theorem qform_zero_of_null {n : ℕ} (d : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℚ)
    (h : ∀ i, x i = 0 ∨ ∑ j, (A i j : ℚ) * x j = 0) :
    qform d A x = 0 := by
  rw [qform_eq_sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  rcases h i with h0 | h0 <;> simp [h0]

/-- If there exists a nonzero vector with qform ≤ 0, A is not positive definite. -/
theorem not_posDef_of_nonpos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSymmetrizable A) (v : Fin n → ℚ) (hv : v ≠ 0)
    (hq : qform hS.d A v ≤ 0) : ¬ IsPosDef A hS :=
  fun hPD => absurd (hPD v hv) (not_lt.mpr hq)

-- ═══════════════════════════════════════════════════════════
-- Submatrix null vector extension
-- ═══════════════════════════════════════════════════════════

/-- Extend a vector on Fin m to Fin n via an embedding, zero outside the range. -/
noncomputable def indicator {n m : ℕ} (f : Fin m ↪ Fin n) (v : Fin m → ℚ) : Fin n → ℚ :=
  fun j => if h : ∃ l, f l = j then v h.choose else 0

theorem indicator_apply {n m : ℕ} (f : Fin m ↪ Fin n) (v : Fin m → ℚ) (i : Fin m) :
    indicator f v (f i) = v i := by
  unfold indicator
  have hex : ∃ l, f l = f i := ⟨i, rfl⟩
  rw [dif_pos hex]
  exact congr_arg v (f.injective hex.choose_spec)

theorem indicator_zero {n m : ℕ} (f : Fin m ↪ Fin n) (v : Fin m → ℚ) (j : Fin n)
    (hj : ∀ l, f l ≠ j) : indicator f v j = 0 := by
  simp only [indicator, dif_neg (not_exists.mpr hj)]

theorem indicator_ne_zero {n m : ℕ} (f : Fin m ↪ Fin n) (v : Fin m → ℚ) (hv : v ≠ 0) :
    indicator f v ≠ 0 := by
  intro h; apply hv; ext i
  have := congr_fun h (f i)
  rwa [indicator_apply] at this

/-- Core theorem: if a principal submatrix (indexed by f) has a null vector v
    (meaning each restricted row applied to v gives 0), then the full matrix
    is not positive definite. The null vector is extended by zeros. -/
theorem not_posDef_of_submatrix_null {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℤ} (hS : IsSymmetrizable A)
    (f : Fin m ↪ Fin n) (v : Fin m → ℚ) (hv : v ≠ 0)
    (hNull : ∀ i : Fin m, ∑ j : Fin m, (A (f i) (f j) : ℚ) * v j = 0) :
    ¬ IsPosDef A hS := by
  let w := indicator f v
  apply not_posDef_of_nonpos hS w (indicator_ne_zero f v hv) (le_of_eq _)
  apply qform_zero_of_null
  intro k
  by_cases hk : ∃ l, f l = k
  · obtain ⟨i, rfl⟩ := hk
    right
    -- Need: ∑ j, (A (f i) j : ℚ) * w j = 0
    -- w j ≠ 0 only when j = f l for some l, and then w (f l) = v l
    -- So the sum reduces to ∑ l, A(f i, f l) * v l = 0 by hNull
    show ∑ j : Fin n, (↑(A (f i) j) : ℚ) * indicator f v j = 0
    -- Step 1: terms outside range(f) vanish, reduce to sum over image
    rw [show ∑ j : Fin n, (↑(A (f i) j) : ℚ) * indicator f v j
        = ∑ j ∈ Finset.univ.map f, (↑(A (f i) j) : ℚ) * indicator f v j from by
      symm; apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists] at hj
      simp [indicator_zero f v j hj]]
    -- Step 2: reindex sum over image to sum over Fin m
    rw [Finset.sum_map]
    -- Step 3: replace indicator f v (f l) with v l
    simp_rw [indicator_apply]
    exact hNull i
  · left
    exact indicator_zero f v k (not_exists.mp hk)

/-- Submatrix version of not_posDef_of_int_null: if a principal submatrix
    A(f·,f·) has an integer null vector, then A is not positive definite. -/
theorem not_posDef_of_submatrix_int_null {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℤ} (hS : IsSymmetrizable A)
    (f : Fin m ↪ Fin n) (M : Matrix (Fin m) (Fin m) ℤ)
    (hM : ∀ i j, A (f i) (f j) = M i j)
    (v : Fin m → ℤ) (hv : v ≠ 0)
    (hNull : M.mulVec v = 0) : ¬ IsPosDef A hS := by
  apply not_posDef_of_submatrix_null hS f (fun i => (v i : ℚ))
  · intro h; apply hv; ext i
    have := congr_fun h i; simp only [Pi.zero_apply] at this
    exact_mod_cast this
  · intro i
    have hi : (M.mulVec v) i = 0 := by rw [hNull]; rfl
    simp only [mulVec, dotProduct] at hi
    have hcast : (↑(∑ j, M i j * v j) : ℚ) = 0 := by exact_mod_cast hi
    simp only [Int.cast_sum, Int.cast_mul] at hcast
    convert hcast using 1
    congr 1; ext j; rw [hM]

-- ═══════════════════════════════════════════════════════════
-- Affine Dynkin diagrams and their null vectors
-- ═══════════════════════════════════════════════════════════

/-- Cyclic adjacency: i and j are cyclically adjacent in Fin k.
    Avoids Nat.mod so that omega can reason about it. -/
def cyclicAdj (k : ℕ) (i j : Fin k) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
  (i.val + 1 = k ∧ j.val = 0) ∨ (j.val + 1 = k ∧ i.val = 0)

instance (k : ℕ) (i j : Fin k) : Decidable (cyclicAdj k i j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- The affine Ã_{k-1} Cartan matrix (k × k circulant).
    For k ≥ 3: diagonal 2, cyclic-adjacent entries -1, rest 0.
    The null vector is (1,1,...,1). -/
def affineA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if cyclicAdj k i j then -1
    else 0

/-- Each row of the affine Ã matrix sums to 0 (for k ≥ 3).
    Proof: decompose entry as 2·[diag] - [succ] - [pred], sum each indicator. -/
theorem affineA_row_sum_zero (k : ℕ) (hk : 3 ≤ k) (i : Fin k) :
    ∑ j : Fin k, affineA k i j = 0 := by
  simp only [affineA, of_apply]
  -- Define successor and predecessor
  have h_succ_lt : (if i.val + 1 < k then i.val + 1 else 0) < k := by split_ifs <;> omega
  have h_pred_lt : (if 0 < i.val then i.val - 1 else k - 1) < k := by split_ifs <;> omega
  let s : Fin k := ⟨if i.val + 1 < k then i.val + 1 else 0, h_succ_lt⟩
  let p : Fin k := ⟨if 0 < i.val then i.val - 1 else k - 1, h_pred_lt⟩
  have hs_adj : cyclicAdj k i s := by simp only [cyclicAdj, s]; split_ifs <;> omega
  have hp_adj : cyclicAdj k i p := by simp only [cyclicAdj, p]; split_ifs <;> omega
  have hs_ne : s ≠ i := by intro h; have := congr_arg Fin.val h; simp [s] at this; split_ifs at this <;> omega
  have hp_ne : p ≠ i := by intro h; have := congr_arg Fin.val h; simp [p] at this; split_ifs at this <;> omega
  have hsp : s ≠ p := by intro h; have := congr_arg Fin.val h; simp [s, p] at this; split_ifs at this <;> omega
  -- Any adjacent vertex is s or p
  have h_only : ∀ j : Fin k, cyclicAdj k i j → j = s ∨ j = p := by
    intro j hj; simp only [cyclicAdj] at hj; simp only [s, p, Fin.ext_iff]
    rcases hj with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (split_ifs <;> omega)
  -- The 3 distinct elements {i, s, p} give entries 2, -1, -1
  -- All other entries are 0. Extract these 3 terms.
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hs_ne, Finset.mem_univ s⟩)]
  simp only [show (i : Fin k) = s ↔ False from ⟨fun h => hs_ne h.symm, False.elim⟩, ite_false,
    show cyclicAdj k i s = True from propext ⟨fun _ => trivial, fun _ => hs_adj⟩, ite_true]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr
    ⟨hsp.symm, Finset.mem_erase.mpr ⟨hp_ne, Finset.mem_univ p⟩⟩)]
  simp only [show (i : Fin k) = p ↔ False from ⟨fun h => hp_ne h.symm, False.elim⟩, ite_false,
    show cyclicAdj k i p = True from propext ⟨fun _ => trivial, fun _ => hp_adj⟩, ite_true]
  -- Remaining sum: all entries are 0
  have h_rest : ∀ j ∈ ((Finset.univ.erase i).erase s).erase p,
      (if i = j then (2 : ℤ) else if cyclicAdj k i j then -1 else 0) = 0 := by
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, ne_eq] at hj
    have hji : j ≠ i := hj.2.2.1
    have hjs : j ≠ s := hj.2.1
    have hjp : j ≠ p := hj.1
    simp only [show i = j ↔ False from ⟨fun h => hji h.symm, False.elim⟩, ite_false]
    have : ¬ cyclicAdj k i j := fun h => by
      rcases h_only j h with rfl | rfl <;> contradiction
    simp [this]
  rw [Finset.sum_eq_zero h_rest]
  norm_num

/-- The affine Ã matrix (k ≥ 3) is not positive definite:
    the all-ones vector gives qform = 0. -/
theorem affineA_not_posDef (k : ℕ) (hk : 3 ≤ k)
    (hS : IsSymmetrizable (affineA k)) :
    ¬ IsPosDef (affineA k) hS := by
  have hv : (fun (_ : Fin k) => (1 : ℚ)) ≠ 0 :=
    fun h => absurd (congr_fun h ⟨0, by omega⟩) one_ne_zero
  apply not_posDef_of_nonpos hS (fun _ => 1) hv
  -- Show qform = 0 via row sums
  have hq : qform hS.d (affineA k) (fun _ => 1) = 0 := by
    simp only [qform, mul_one]
    conv_lhs => arg 2; ext i; rw [← Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [show (∑ j : Fin k, (affineA k i j : ℚ)) =
        ((∑ j, affineA k i j : ℤ) : ℚ) from by push_cast; rfl]
    rw [affineA_row_sum_zero k hk i]; simp
  exact le_of_eq hq

-- ═══════════════════════════════════════════════════════════
-- Exceptional affine Dynkin diagrams
-- ═══════════════════════════════════════════════════════════

/-- Affine D̃₄: the D₄ diagram with one extra node.
    5 vertices: center (0) connected to 4 leaves (1,2,3,4).
    Null vector: (2,1,1,1,1). -/
def affineD4 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![ 2, -1, -1, -1, -1;
     -1,  2,  0,  0,  0;
     -1,  0,  2,  0,  0;
     -1,  0,  0,  2,  0;
     -1,  0,  0,  0,  2]

theorem affineD4_null : affineD4.mulVec ![2, 1, 1, 1, 1] = 0 := by decide

/-- Affine Ẽ₆ matrix (7 × 7): branch at node 2 with three arms of length 2.
    Diagram: 0-1-2-3-4 with branch 2-5-6.
    Null vector: (1,2,3,2,1,2,1). -/
def affineE6 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0;
      0, -1,  2, -1,  0, -1,  0;
      0,  0, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2,  0,  0;
      0,  0, -1,  0,  0,  2, -1;
      0,  0,  0,  0,  0, -1,  2]

theorem affineE6_null : affineE6.mulVec ![1, 2, 3, 2, 1, 2, 1] = 0 := by decide

/-- Affine Ẽ₇ matrix (8 × 8): path 0-1-2-3-4-5-6 with branch 3-7.
    Arms from branch (node 3): (3, 3, 1).
    Null vector: (1,2,3,4,3,2,1,2). -/
def affineE7 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0,  0;
      0, -1,  2, -1,  0,  0,  0,  0;
      0,  0, -1,  2, -1,  0,  0, -1;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2,  0;
      0,  0,  0, -1,  0,  0,  0,  2]

theorem affineE7_null : affineE7.mulVec ![1, 2, 3, 4, 3, 2, 1, 2] = 0 := by decide

/-- Affine Ẽ₈ matrix (9 × 9): path 0-1-2-3-4-5-6-7 with branch 2-8.
    Arms from branch (node 2): (2, 5, 1).
    Null vector: (2,4,6,5,4,3,2,1,3). -/
def affineE8 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0,  0,  0;
      0, -1,  2, -1,  0,  0,  0,  0, -1;
      0,  0, -1,  2, -1,  0,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0,  0, -1,  2,  0;
      0,  0, -1,  0,  0,  0,  0,  0,  2]

theorem affineE8_null : affineE8.mulVec ![2, 4, 6, 5, 4, 3, 2, 1, 3] = 0 := by decide

/-- Ẽ₇ restricted to first 7 vertices (the path) equals A_7. -/
theorem affineE7_path : ∀ i j : Fin 7,
    affineE7 (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A 7 i j := by decide

/-- Ẽ₇ last row: vertex 7 connects only to vertex 3. -/
theorem affineE7_row_branch : ∀ j : Fin 7,
    affineE7 (Fin.last 7) (Fin.castSucc j) = if j.val = 3 then -1 else 0 := by decide

/-- Ẽ₇ last column: vertex 3 connects to vertex 7. -/
theorem affineE7_col_branch : ∀ j : Fin 7,
    affineE7 (Fin.castSucc j) (Fin.last 7) = if j.val = 3 then -1 else 0 := by decide

/-- Ẽ₈ restricted to first 8 vertices (the path) equals A_8. -/
theorem affineE8_path : ∀ i j : Fin 8,
    affineE8 (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.A 8 i j := by decide

/-- Ẽ₈ last row: vertex 8 connects only to vertex 2. -/
theorem affineE8_row_branch : ∀ j : Fin 8,
    affineE8 (Fin.last 8) (Fin.castSucc j) = if j.val = 2 then -1 else 0 := by decide

/-- Ẽ₈ last column: vertex 2 connects to vertex 8. -/
theorem affineE8_col_branch : ∀ j : Fin 8,
    affineE8 (Fin.castSucc j) (Fin.last 8) = if j.val = 2 then -1 else 0 := by decide

/-- E₆ with vertex 1 deleted (via succAbove) equals A_5. -/
theorem E6_succAbove_one_eq_A : ∀ i j : Fin 5,
    CartanMatrix.E₆ ((1 : Fin 6).succAbove i) ((1 : Fin 6).succAbove j) =
    CartanMatrix.A 5 i j := by decide

/-- E₆ row 1: vertex 1 connects only to vertex 3, i.e., succAbove(1,2). -/
theorem E6_at_one_row : ∀ j : Fin 5,
    CartanMatrix.E₆ 1 ((1 : Fin 6).succAbove j) = if j.val = 2 then -1 else 0 := by decide

/-- E₆ column 1: vertex 3 connects to vertex 1. -/
theorem E6_at_one_col : ∀ j : Fin 5,
    CartanMatrix.E₆ ((1 : Fin 6).succAbove j) 1 = if j.val = 2 then -1 else 0 := by decide

/-- E₇ with vertex 1 deleted equals A_6. -/
theorem E7_succAbove_one_eq_A : ∀ i j : Fin 6,
    CartanMatrix.E₇ ((1 : Fin 7).succAbove i) ((1 : Fin 7).succAbove j) =
    CartanMatrix.A 6 i j := by decide

/-- E₇ row 1: vertex 1 connects only to succAbove(1,2) = vertex 3. -/
theorem E7_at_one_row : ∀ j : Fin 6,
    CartanMatrix.E₇ 1 ((1 : Fin 7).succAbove j) = if j.val = 2 then -1 else 0 := by decide

/-- E₇ column 1. -/
theorem E7_at_one_col : ∀ j : Fin 6,
    CartanMatrix.E₇ ((1 : Fin 7).succAbove j) 1 = if j.val = 2 then -1 else 0 := by decide

/-- E₈ with vertex 1 deleted equals A_7. -/
theorem E8_succAbove_one_eq_A : ∀ i j : Fin 7,
    CartanMatrix.E₈ ((1 : Fin 8).succAbove i) ((1 : Fin 8).succAbove j) =
    CartanMatrix.A 7 i j := by decide

/-- E₈ row 1: vertex 1 connects only to succAbove(1,2) = vertex 3. -/
theorem E8_at_one_row : ∀ j : Fin 7,
    CartanMatrix.E₈ 1 ((1 : Fin 8).succAbove j) = if j.val = 2 then -1 else 0 := by decide

/-- E₈ column 1. -/
theorem E8_at_one_col : ∀ j : Fin 7,
    CartanMatrix.E₈ ((1 : Fin 8).succAbove j) 1 = if j.val = 2 then -1 else 0 := by decide

-- ═══════════════════════════════════════════════════════════
-- Affine types are not positive definite
-- ═══════════════════════════════════════════════════════════

/-- If A has an integer null vector (A·v = 0), then A is not positive definite
    for any symmetrizer. This bridges integer mulVec to rational qform. -/
theorem not_posDef_of_int_null {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSymmetrizable A) (v : Fin n → ℤ) (hv : v ≠ 0)
    (hNull : A.mulVec v = 0) : ¬ IsPosDef A hS := by
  let w : Fin n → ℚ := fun i => (v i : ℚ)
  have hw : w ≠ 0 := by
    intro h; apply hv; ext i
    have hi := congr_fun h i
    simp only [Pi.zero_apply] at hi ⊢
    exact_mod_cast (show (v i : ℚ) = 0 from hi)
  apply not_posDef_of_nonpos hS w hw (le_of_eq _)
  rw [qform_eq_sum_mul]
  apply Finset.sum_eq_zero; intro i _
  suffices h : ∑ j, (A i j : ℚ) * w j = 0 by simp [h]
  have hi : (A.mulVec v) i = 0 := by rw [hNull]; rfl
  simp only [mulVec, dotProduct] at hi
  have : (↑(∑ j, A i j * v j) : ℚ) = 0 := by exact_mod_cast hi
  simpa [Int.cast_sum, Int.cast_mul] using this

theorem affineD4_not_posDef (hS : IsSymmetrizable affineD4) :
    ¬ IsPosDef affineD4 hS :=
  not_posDef_of_int_null hS _ (by decide) affineD4_null

theorem affineE6_not_posDef (hS : IsSymmetrizable affineE6) :
    ¬ IsPosDef affineE6 hS :=
  not_posDef_of_int_null hS _ (by decide) affineE6_null

theorem affineE7_not_posDef (hS : IsSymmetrizable affineE7) :
    ¬ IsPosDef affineE7 hS :=
  not_posDef_of_int_null hS _ (by decide) affineE7_null

theorem affineE8_not_posDef (hS : IsSymmetrizable affineE8) :
    ¬ IsPosDef affineE8 hS :=
  not_posDef_of_int_null hS _ (by decide) affineE8_null

end BLD.Lie.Cartan
