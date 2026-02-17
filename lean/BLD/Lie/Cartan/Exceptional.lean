/- BLD Calculus — Cartan Classification: Exceptional Cases

   E₆ extension proof and E₈ no-extension proof.
   Includes E₆ infrastructure (null vector matrices, marks, flips)
   and the weight-3 impossibility theorem.
-/

import BLD.Lie.Cartan.EntryLemmas

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

-- E₆ infrastructure
-- ═══════════════════════════════════════════════════════════

/-- Marks vector for E₆: dual Coxeter labels. E₆ · marksE6 = (3,0,...,0). -/
def marksE6 : Fin 6 → ℤ := ![4, 3, 5, 6, 4, 2]

theorem E6_mulVec_marks : CartanMatrix.E₆.mulVec marksE6 = fun i =>
    if i = 0 then 3 else 0 := by decide

/-- E₇ restricted to first 6 indices equals E₆. -/
theorem E7_castSucc_eq_E6 : ∀ i j : Fin 6,
    CartanMatrix.E₇ (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.E₆ i j := by decide

/-- E₇ last row/column: vertex 6 connects only to vertex 5. -/
theorem E7_last_row : ∀ i : Fin 6,
    CartanMatrix.E₇ 6 (Fin.castSucc i) = if i = 5 then -1 else 0 := by decide

/-- E₆ weight-2 submatrix, case A(v,u)=-1, A(u,v)=-2.
    Rows/cols 0-4 = E₆ vertices 1-5, row/col 5 = leaf v. -/
private def e6w2c1 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0, -1,  0,  0,  0;
      0,  2, -1,  0,  0,  0;
     -1, -1,  2, -1,  0,  0;
      0,  0, -1,  2, -1,  0;
      0,  0,  0, -1,  2, -2;
      0,  0,  0,  0, -1,  2]

private theorem e6w2c1_null : e6w2c1.mulVec ![1, 1, 2, 2, 2, 1] = 0 := by decide

/-- E₆ weight-2 submatrix, case A(v,u)=-2, A(u,v)=-1. -/
private def e6w2c2 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0, -1,  0,  0,  0;
      0,  2, -1,  0,  0,  0;
     -1, -1,  2, -1,  0,  0;
      0,  0, -1,  2, -1,  0;
      0,  0,  0, -1,  2, -1;
      0,  0,  0,  0, -2,  2]

private theorem e6w2c2_null : e6w2c2.mulVec ![1, 1, 2, 2, 2, 2] = 0 := by decide

/-- E₆ vertices 1-5 sub-block equals first 5×5 of e6w2c1 (= e6w2c2). -/
private theorem E6_sub_eq : ∀ i j : Fin 5,
    CartanMatrix.E₆ (Fin.succ i) (Fin.succ j) =
    e6w2c1 (Fin.castSucc i) (Fin.castSucc j) := by decide

/-- Custom vector for E₆ weight-1 contradictions at vertices 1, 2, 4.
    E₆ · customE6 = (0,1,0,0,0,0): nonzero only at vertex 1. -/
private def customE6 : Fin 6 → ℤ := ![1, 2, 2, 3, 2, 1]

private theorem E6_mulVec_custom : CartanMatrix.E₆.mulVec customE6 = fun i =>
    if i = 1 then 1 else 0 := by decide

private theorem customE6_pos : ∀ i : Fin 6, 0 < customE6 i := by decide

/-- customE6 at vertices 1, 2, 4 equals 2. -/
private theorem customE6_eq_two : ∀ i : Fin 6, i ≠ 5 → i ≠ 3 → i ≠ 0 →
    customE6 i = 2 := by decide

/-- E₆ has an automorphism: 0↔5, 2↔4, 1↔1, 3↔3. -/
private def e6flip : Fin 6 → Fin 6 := ![5, 1, 4, 3, 2, 0]

private theorem e6flip_eq_E6 : ∀ i j : Fin 6,
    CartanMatrix.E₆ (e6flip i) (e6flip j) = CartanMatrix.E₆ i j := by decide

private theorem e6flip_zero : e6flip 0 = 5 := by decide

/-- 4×4 submatrix for degree-2 vertex weight 2, A(v,u)=-1, A(u,v)=-2.
    Center u has 2 neighbors w1, w2 in E₆. -/
private def e6_deg2_w2c1 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 2, -1,  0,  0;
     -2,  2, -1, -1;
      0, -1,  2,  0;
      0, -1,  0,  2]

private theorem e6_deg2_w2c1_null : e6_deg2_w2c1.mulVec ![1, 2, 1, 1] = 0 := by decide

/-- 4×4 submatrix for degree-2 vertex weight 2, A(v,u)=-2, A(u,v)=-1. -/
private def e6_deg2_w2c2 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 2, -2,  0,  0;
     -1,  2, -1, -1;
      0, -1,  2,  0;
      0, -1,  0,  2]

private theorem e6_deg2_w2c2_null : e6_deg2_w2c2.mulVec ![2, 2, 1, 1] = 0 := by decide

/-- Verify e6_deg2_w2c1 subblock matches E₆ for vertex 2 (neighbors 0, 3). -/
private theorem e6_deg2_sub_v2 : ∀ i j : Fin 3,
    CartanMatrix.E₆ ((![2, 0, 3] : Fin 3 → Fin 6) i)
                     ((![2, 0, 3] : Fin 3 → Fin 6) j) =
    e6_deg2_w2c1 (Fin.succ i) (Fin.succ j) := by decide

/-- Verify e6_deg2_w2c1 subblock matches E₆ for vertex 4 (neighbors 3, 5). -/
private theorem e6_deg2_sub_v4 : ∀ i j : Fin 3,
    CartanMatrix.E₆ ((![4, 3, 5] : Fin 3 → Fin 6) i)
                     ((![4, 3, 5] : Fin 3 → Fin 6) j) =
    e6_deg2_w2c1 (Fin.succ i) (Fin.succ j) := by decide

/-- 6×6 submatrix for vertex 0 weight 2, A(v,u)=-1, A(u,v)=-2.
    Vertices: v, E₆-0, E₆-2, E₆-3, E₆-1, E₆-4 (omitting E₆-5). -/
private def e6v0w2c1 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2, -1,  0,  0,  0,  0;
     -2,  2, -1,  0,  0,  0;
      0, -1,  2, -1,  0,  0;
      0,  0, -1,  2, -1, -1;
      0,  0,  0, -1,  2,  0;
      0,  0,  0, -1,  0,  2]

private theorem e6v0w2c1_null : e6v0w2c1.mulVec ![1, 2, 2, 2, 1, 1] = 0 := by decide

/-- 6×6 submatrix for vertex 0 weight 2, A(v,u)=-2, A(u,v)=-1. -/
private def e6v0w2c2 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2, -2,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0;
      0, -1,  2, -1,  0,  0;
      0,  0, -1,  2, -1, -1;
      0,  0,  0, -1,  2,  0;
      0,  0,  0, -1,  0,  2]

private theorem e6v0w2c2_null : e6v0w2c2.mulVec ![2, 2, 2, 2, 1, 1] = 0 := by decide

/-- E₆ subblock for vertex 0 embedding: E₆ vertices [0,2,3,1,4] (omitting 5). -/
private theorem E6_v0w2_sub : ∀ i j : Fin 5,
    CartanMatrix.E₆ ((![0, 2, 3, 1, 4] : Fin 5 → Fin 6) i)
                     ((![0, 2, 3, 1, 4] : Fin 5 → Fin 6) j) =
    e6v0w2c1 (Fin.succ i) (Fin.succ j) := by decide

/-- The c1 and c2 vertex-0 weight-2 matrices share the same succ×succ subblock. -/
private theorem E6_v0w2_sub_c2 : ∀ i j : Fin 5,
    CartanMatrix.E₆ ((![0, 2, 3, 1, 4] : Fin 5 → Fin 6) i)
                     ((![0, 2, 3, 1, 4] : Fin 5 → Fin 6) j) =
    e6v0w2c2 (Fin.succ i) (Fin.succ j) := by decide

/-- 5×5 submatrix for vertex 1 weight 2, A(v,u)=-1, A(u,v)=-2.
    Vertices: v, E₆-1, E₆-3, E₆-2, E₆-4. -/
private def e6v1w2c1 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![ 2, -1,  0,  0,  0;
     -2,  2, -1,  0,  0;
      0, -1,  2, -1, -1;
      0,  0, -1,  2,  0;
      0,  0, -1,  0,  2]

private theorem e6v1w2c1_null : e6v1w2c1.mulVec ![1, 2, 2, 1, 1] = 0 := by decide

/-- 5×5 submatrix for vertex 1 weight 2, A(v,u)=-2, A(u,v)=-1. -/
private def e6v1w2c2 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![ 2, -2,  0,  0,  0;
     -1,  2, -1,  0,  0;
      0, -1,  2, -1, -1;
      0,  0, -1,  2,  0;
      0,  0, -1,  0,  2]

private theorem e6v1w2c2_null : e6v1w2c2.mulVec ![2, 2, 2, 1, 1] = 0 := by decide

/-- E₆ subblock for vertex 1 embedding: E₆ vertices [1,3,2,4]. -/
private theorem E6_v1w2_sub : ∀ i j : Fin 4,
    CartanMatrix.E₆ ((![1, 3, 2, 4] : Fin 4 → Fin 6) i)
                     ((![1, 3, 2, 4] : Fin 4 → Fin 6) j) =
    e6v1w2c1 (Fin.succ i) (Fin.succ j) := by decide

/-- Weight 3 is impossible when rank ≥ 3: a 3-vertex path with Coxeter weight 3
    on one edge always has a non-positive-definite symmetrization. -/
theorem weight3_impossible {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1)
    (u : Fin (n+3)) (huv : u ≠ v) (hAvu : A v u ≠ 0)
    (w : Fin (n+3)) (hwu : w ≠ u) (hwv : w ≠ v) (hAuw : A u w ≠ 0)
    (hw3 : A v u * A u v = 3) : False := by
  have hAvu_neg : A v u ≤ -1 := by have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_ne : A u v ≠ 0 := fun h => hAvu ((hGCM.zero_iff u v huv).mp h)
  have hAuv_neg : A u v ≤ -1 := by have := hGCM.off_diag_nonpos u v huv; omega
  have hAuw_neg : A u w ≤ -1 := by have := hGCM.off_diag_nonpos u w hwu.symm; omega
  have hAwu_ne : A w u ≠ 0 := fun h => hAuw ((hGCM.zero_iff w u hwu).mp h)
  have hAwu_neg : A w u ≤ -1 := by have := hGCM.off_diag_nonpos w u hwu; omega
  -- v is a leaf, so A v w = 0 (v only connects to u)
  have hAvw : A v w = 0 := by
    by_contra hvw
    have hmem_u : u ∈ Finset.univ.filter (fun j => j ≠ v ∧ A v j ≠ 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨huv, hAvu⟩
    have hmem_w : w ∈ Finset.univ.filter (fun j => j ≠ v ∧ A v j ≠ 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hwv, hvw⟩
    have hcard : 2 ≤ (Finset.univ.filter (fun j => j ≠ v ∧ A v j ≠ 0)).card :=
      Finset.one_lt_card.mpr ⟨u, hmem_u, w, hmem_w, hwu.symm⟩
    unfold gcmDegree at hleaf; omega
  have hAwv : A w v = 0 := by rwa [← hGCM.zero_iff v w hwv.symm]
  have huw_wt : 1 ≤ A u w * A w u := by nlinarith
  -- Test vector: x(v) = -A(v,u), x(u) = 2, x(w) = -A(w,u), rest = 0.
  -- Inner sums at rows v and w vanish by construction.
  -- Row u gives d(u)·2·(1 - coxeterWeight(u,w)) ≤ 0.
  set x : Fin (n+3) → ℚ := fun i =>
    if i = v then -(↑(A v u : ℤ) : ℚ)
    else if i = u then 2
    else if i = w then -(↑(A w u : ℤ) : ℚ)
    else 0
  have hx : x ≠ 0 := by
    intro h; have := congr_fun h u
    simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
  have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ w → x k = 0 :=
    fun k h1 h2 h3 => by simp [x, h1, h2, h3]
  -- Inner sum at row v vanishes
  have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
    rw [sum_two huv.symm _ (fun k hkv hku => by
      by_cases hkw : k = w
      · subst hkw; simp only [hAvw, Int.cast_zero, zero_mul]
      · simp [x0 k hkv hku hkw])]
    simp only [x, ↓reduceIte, if_neg huv, hGCM.diag v]; push_cast; ring
  -- Inner sum at row w vanishes
  have inner_w : ∑ j, (↑(A w j) : ℚ) * x j = 0 := by
    rw [sum_two hwu _ (fun k hkw hku => by
      by_cases hkv : k = v
      · subst hkv; simp only [hAwv, Int.cast_zero, zero_mul]
      · simp [x0 k hkv hku hkw])]
    simp only [x, if_neg hwv, if_neg hwu, if_neg huv, ↓reduceIte, hGCM.diag w]
    push_cast; ring
  -- qform reduces to the single row-u contribution
  have hq : qform hSym.d A x = hSym.d u * 2 * ∑ j, (↑(A u j) : ℚ) * x j := by
    rw [qform_eq_sum_mul]
    have hsingle := Finset.sum_eq_single u
      (fun b _ hb => show hSym.d b * x b * ∑ j, (↑(A b j) : ℚ) * x j = 0 from by
        by_cases hbv : b = v
        · subst hbv; simp [inner_v]
        · by_cases hbw : b = w
          · subst hbw; simp [inner_w]
          · simp [x0 b hbv hb hbw])
      (fun h => absurd (Finset.mem_univ u) h)
    rw [hsingle]; simp only [x, if_neg huv, ↓reduceIte]
  -- qform ≤ 0 (contradicting positive definiteness)
  have hq_le : qform hSym.d A x ≤ 0 := by
    rw [hq]
    suffices h : ∑ j, (↑(A u j) : ℚ) * x j ≤ 0 by nlinarith [hSym.d_pos u]
    rw [sum_three huv.symm hwv.symm hwu.symm _ (fun l hlv hlu hlw => by
      simp [x0 l hlv hlu hlw])]
    simp only [x, ↓reduceIte, if_neg huv, if_neg hwv, if_neg hwu, hGCM.diag u]; push_cast
    have h1 : (↑(A v u * A u v) : ℚ) = 3 := by exact_mod_cast hw3
    have h2 : (1 : ℚ) ≤ ↑(A u w * A w u) := by exact_mod_cast huw_wt
    simp only [Int.cast_mul] at h1 h2; nlinarith [mul_comm (↑(A v u) : ℚ) (↑(A u v) : ℚ)]
  exact absurd hPD (not_posDef_of_nonpos hSym x hx hq_le)

set_option maxHeartbeats 400000 in
/-- E₆ vertex 5 case: weight 1 → E₇, weight 2 → contradiction via null vectors. -/
private theorem e6_v5_case {A : Matrix (Fin 7) (Fin 7) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v u : Fin 7) (_huv : u ≠ v)
    (hcw_le2 : A v u * A u v ≤ 2)
    (e' : Fin 6 ≃ Fin 6)
    (u_idx : Fin 6) (hu_idx : v.succAbove u_idx = u)
    (hsub : ∀ i j : Fin 6, A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.E₆ (e' i) (e' j))
    (hAv0 : ∀ k : Fin 6, k ≠ u_idx → A v (v.succAbove k) = 0)
    (hAvu_neg : A v u ≤ -1) (hAuv_neg : A u v ≤ -1)
    (hcw_pos : 1 ≤ A v u * A u v)
    (h5 : e' u_idx = 5) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  by_cases hw1 : A v u * A u v = 1
  · -- Weight 1: both entries = -1. Construct E₇.
    have hAvu_eq : A v u = -1 := by nlinarith
    have hAuv_eq : A u v = -1 := by nlinarith
    refine ⟨DynkinType.E₇, ?_⟩
    let f : Fin 7 → Fin 7 := fun i =>
      if h : ∃ k : Fin 6, v.succAbove k = i then Fin.castSucc (e' h.choose) else 6
    have hf_v : f v = 6 := by
      simp only [f]; rw [dif_neg]; push_neg
      exact fun k => Fin.succAbove_ne v k
    have hf_sub : ∀ k : Fin 6, f (v.succAbove k) = Fin.castSucc (e' k) := by
      intro k; simp only [f]
      have hex : ∃ k' : Fin 6, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
      rw [dif_pos hex]
      have : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
      rw [this]
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
        · rw [hi, hj]; congr 1
          rw [hi, hj, hf_sub, hf_sub] at hij
          exact e'.injective (Fin.castSucc_injective _ hij)
    have hf_bij := hf_inj.bijective_of_finite
    let σ := Equiv.ofBijective f hf_bij
    refine ⟨σ, fun i j => ?_⟩
    show CartanMatrix.E₇ (f i) (f j) = A i j
    rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · rw [hi, hj]; simp only [hf_v, hGCM.diag]; decide
      · rw [hi, hj, hf_v, hf_sub, E7_last_row]
        by_cases hkj : kj = u_idx
        · subst hkj; rw [h5]; simp [hu_idx, hAvu_eq]
        · rw [if_neg (show e' kj ≠ 5 from fun h => hkj (e'.injective (h.trans h5.symm)))]
          simp [hAv0 kj hkj]
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · rw [hi, hj, hf_sub, hf_v]
        have hE7_sym : CartanMatrix.E₇ (Fin.castSucc (e' ki)) 6 =
            CartanMatrix.E₇ 6 (Fin.castSucc (e' ki)) := by
          have : ∀ a b : Fin 7, CartanMatrix.E₇ a b = CartanMatrix.E₇ b a := by decide
          exact this _ _
        rw [hE7_sym, E7_last_row]
        by_cases hki : ki = u_idx
        · subst hki; rw [h5]; simp [hu_idx, hAuv_eq]
        · rw [if_neg (show e' ki ≠ 5 from fun h => hki (e'.injective (h.trans h5.symm)))]
          have hAvk : A v (v.succAbove ki) = 0 := hAv0 ki hki
          exact ((hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v ki))).mp hAvk).symm
      · rw [hi, hj, hf_sub, hf_sub, E7_castSucc_eq_E6, ← hsub]
  · -- Weight 2 at vertex 5: contradiction via null vectors
    exfalso
    have hw2 : A v u * A u v = 2 := by omega
    have hcases : (A v u = -1 ∧ A u v = -2) ∨ (A v u = -2 ∧ A u v = -1) := by
      have : A v u = -1 ∨ A v u = -2 := by
        have hAvu_ge : -2 ≤ A v u := by
          by_contra hlt; push_neg at hlt
          have h3 : A v u ≤ -3 := by omega
          nlinarith [mul_nonneg_of_nonpos_of_nonpos (show A v u + 2 ≤ 0 by omega)
            (show A u v + 1 ≤ 0 by omega)]
        omega
      rcases this with h | h <;> [left; right] <;> constructor <;> [exact h; nlinarith; exact h; nlinarith]
    have he'symm5 : e'.symm 5 = u_idx := by rw [← h5, e'.symm_apply_apply]
    let g : Fin 5 → Fin 7 := fun k => v.succAbove (e'.symm (Fin.succ k))
    let φ : Fin 6 → Fin 7 := fun i =>
      if h : (i : ℕ) < 5 then g ⟨i, h⟩ else v
    have hφ_lt : ∀ (i : Fin 6) (hi : (i : ℕ) < 5), φ i = g ⟨i, hi⟩ := by
      intro i hi; simp only [φ, hi, ↓reduceDIte]
    have hφ5 : ∀ (i : Fin 6), ¬ (i : ℕ) < 5 → φ i = v := by
      intro i hi; simp only [φ, hi, ↓reduceDIte]
    have hk_ne_u : ∀ k : Fin 5, k ≠ 4 → e'.symm (Fin.succ k) ≠ u_idx := by
      intro k hk heq; apply hk
      have h1 := e'.symm.injective (heq.trans he'symm5.symm)
      exact Fin.ext (by have := Fin.ext_iff.mp h1; simp at this; omega)
    have hAg_v : ∀ k : Fin 5, k ≠ 4 → A (g k) v = 0 := by
      intro k hk; show A (v.succAbove _) v = 0
      have h0 := hAv0 _ (hk_ne_u k hk)
      exact (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v _))).mp h0
    have hAv_g : ∀ k : Fin 5, k ≠ 4 → A v (g k) = 0 := by
      intro k hk; show A v (v.succAbove _) = 0; exact hAv0 _ (hk_ne_u k hk)
    have hsucc4_eq_5 : Fin.succ (4 : Fin 5) = (5 : Fin 6) := by decide
    have hg4_eq : g 4 = u := by
      show v.succAbove (e'.symm (Fin.succ 4)) = u
      rw [hsucc4_eq_5, he'symm5, hu_idx]
    have hgg : ∀ ki kj : Fin 5, A (g ki) (g kj) =
        CartanMatrix.E₆ (Fin.succ ki) (Fin.succ kj) := by
      intro ki kj; simp only [g]
      rw [hsub, e'.apply_symm_apply, e'.apply_symm_apply]
    have hφ_inj : Function.Injective φ := by
      intro i j hij; simp only [φ] at hij
      by_cases hi : (i : ℕ) < 5 <;> by_cases hj : (j : ℕ) < 5 <;>
        simp only [hi, hj, ↓reduceDIte] at hij
      · exact Fin.ext (show (i : ℕ) = j from by
          have := Fin.ext_iff.mp (Fin.succ_injective _
            (e'.symm.injective (Fin.succAbove_right_injective hij)))
          simpa using this)
      · exact absurd hij (Fin.succAbove_ne v _)
      · exact absurd hij.symm (Fin.succAbove_ne v _)
      · exact Fin.ext (by omega)
    let φ_emb : Fin 6 ↪ Fin 7 := ⟨φ, hφ_inj⟩
    have hentry : ∀ (Avu Auv : ℤ) (hAvu : A v u = Avu) (hAuv : A u v = Auv)
        (M : Matrix (Fin 6) (Fin 6) ℤ)
        (hM1 : ∀ ki kj : Fin 5,
          M (Fin.castSucc ki) (Fin.castSucc kj) =
          CartanMatrix.E₆ (Fin.succ ki) (Fin.succ kj))
        (hM2 : M 5 5 = 2) (hM3 : M 4 5 = Auv) (hM4 : M 5 4 = Avu)
        (hM5 : ∀ k : Fin 5, k ≠ 4 → M (Fin.castSucc k) 5 = 0)
        (hM6 : ∀ k : Fin 5, k ≠ 4 → M 5 (Fin.castSucc k) = 0),
        ∀ i j : Fin 6, A (φ i) (φ j) = M i j := by
      intro Avu Auv hAvu hAuv M hM1 hM2 hM3 hM4 hM5 hM6 i j
      have hcs : ∀ (k : Fin 6) (hk : (k : ℕ) < 5),
          Fin.castSucc (⟨k, hk⟩ : Fin 5) = k := fun _ _ => Fin.ext rfl
      by_cases hi : (i : ℕ) < 5 <;> by_cases hj : (j : ℕ) < 5
      · rw [hφ_lt i hi, hφ_lt j hj, hgg, ← hM1, hcs i hi, hcs j hj]
      · have hj5 : j = 5 := Fin.ext (by omega)
        subst hj5; rw [hφ_lt i hi, hφ5 5 (by omega)]
        by_cases hki4 : (⟨(i : ℕ), hi⟩ : Fin 5) = 4
        · rw [show g ⟨i, hi⟩ = u from by
            rw [show (⟨(i : ℕ), hi⟩ : Fin 5) = 4 from hki4]; exact hg4_eq]
          rw [hAuv, ← hM3]; congr 1; exact Fin.ext (by simp [Fin.ext_iff] at hki4; omega)
        · rw [hAg_v _ hki4, ← hM5 _ hki4, hcs i hi]
      · have hi5 : i = 5 := Fin.ext (by omega)
        subst hi5; rw [hφ5 5 (by omega), hφ_lt j hj]
        by_cases hkj4 : (⟨(j : ℕ), hj⟩ : Fin 5) = 4
        · rw [show g ⟨j, hj⟩ = u from by
            rw [show (⟨(j : ℕ), hj⟩ : Fin 5) = 4 from hkj4]; exact hg4_eq]
          rw [hAvu, ← hM4]; congr 1; exact Fin.ext (by simp [Fin.ext_iff] at hkj4; omega)
        · rw [hAv_g _ hkj4, ← hM6 _ hkj4, hcs j hj]
      · have hi5 : i = 5 := Fin.ext (by omega)
        have hj5 : j = 5 := Fin.ext (by omega)
        subst hi5; subst hj5
        rw [hGCM.diag, ← hM2]
    rcases hcases with ⟨hvu_eq, huv_eq⟩ | ⟨hvu_eq, huv_eq⟩
    · apply absurd hPD
      exact not_posDef_of_submatrix_int_null hSym φ_emb e6w2c1
        (hentry (-1) (-2) hvu_eq huv_eq e6w2c1
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        _ (by decide) e6w2c1_null
    · apply absurd hPD
      exact not_posDef_of_submatrix_int_null hSym φ_emb e6w2c2
        (hentry (-2) (-1) hvu_eq huv_eq e6w2c2
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
        _ (by decide) e6w2c2_null

set_option maxHeartbeats 800000 in
/-- E₆ vertex 0 case: weight 1 → E₇ (via e6flip automorphism),
    weight 2 → contradiction via null vectors. -/
private theorem e6_v0_case {A : Matrix (Fin 7) (Fin 7) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v u : Fin 7) (_huv : u ≠ v)
    (hcw_le2 : A v u * A u v ≤ 2)
    (e' : Fin 6 ≃ Fin 6)
    (u_idx : Fin 6) (hu_idx : v.succAbove u_idx = u)
    (hsub : ∀ i j : Fin 6, A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.E₆ (e' i) (e' j))
    (hAv0 : ∀ k : Fin 6, k ≠ u_idx → A v (v.succAbove k) = 0)
    (hAvu_neg : A v u ≤ -1) (hAuv_neg : A u v ≤ -1)
    (hcw_pos : 1 ≤ A v u * A u v)
    (h0 : e' u_idx = 0) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  by_cases hw1 : A v u * A u v = 1
  · -- Weight 1: both = -1. Construct E₇ using e6flip automorphism.
    have hAvu_eq : A v u = -1 := by nlinarith
    have hAuv_eq : A u v = -1 := by nlinarith
    refine ⟨DynkinType.E₇, ?_⟩
    let e6flip_equiv : Fin 6 ≃ Fin 6 :=
      ⟨e6flip, e6flip, fun x => by fin_cases x <;> decide,
       fun x => by fin_cases x <;> decide⟩
    let e'f : Fin 6 ≃ Fin 6 := e'.trans e6flip_equiv
    have hsub' : ∀ i j : Fin 6, A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.E₆ (e'f i) (e'f j) := by
      intro i j; rw [hsub]; exact (e6flip_eq_E6 (e' i) (e' j)).symm
    have h5' : e'f u_idx = 5 := by
      show e6flip (e' u_idx) = 5; rw [h0]; decide
    let f : Fin 7 → Fin 7 := fun i =>
      if h : ∃ k : Fin 6, v.succAbove k = i then Fin.castSucc (e'f h.choose) else 6
    have hf_v : f v = 6 := by
      simp only [f]; rw [dif_neg]; push_neg
      exact fun k => Fin.succAbove_ne v k
    have hf_sub : ∀ k : Fin 6, f (v.succAbove k) = Fin.castSucc (e'f k) := by
      intro k; simp only [f]
      have hex : ∃ k' : Fin 6, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
      rw [dif_pos hex]
      have : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
      rw [this]
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
        · rw [hi, hj]; congr 1
          rw [hi, hj, hf_sub, hf_sub] at hij
          exact e'f.injective (Fin.castSucc_injective _ hij)
    have hf_bij := hf_inj.bijective_of_finite
    let σ := Equiv.ofBijective f hf_bij
    refine ⟨σ, fun i j => ?_⟩
    show CartanMatrix.E₇ (f i) (f j) = A i j
    rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · rw [hi, hj]; simp only [hf_v, hGCM.diag]; decide
      · rw [hi, hj, hf_v, hf_sub, E7_last_row]
        by_cases hkj : kj = u_idx
        · subst hkj; rw [h5']; simp [hu_idx, hAvu_eq]
        · rw [if_neg (show e'f kj ≠ 5 from
            fun h => hkj (e'f.injective (h.trans h5'.symm)))]
          simp [hAv0 kj hkj]
    · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
      · rw [hi, hj, hf_sub, hf_v]
        have hE7_sym : CartanMatrix.E₇ (Fin.castSucc (e'f ki)) 6 =
            CartanMatrix.E₇ 6 (Fin.castSucc (e'f ki)) := by
          have : ∀ a b : Fin 7, CartanMatrix.E₇ a b = CartanMatrix.E₇ b a := by decide
          exact this _ _
        rw [hE7_sym, E7_last_row]
        by_cases hki : ki = u_idx
        · subst hki; rw [h5']; simp [hu_idx, hAuv_eq]
        · rw [if_neg (show e'f ki ≠ 5 from
            fun h => hki (e'f.injective (h.trans h5'.symm)))]
          have hAvk : A v (v.succAbove ki) = 0 := hAv0 ki hki
          exact ((hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v ki))).mp hAvk).symm
      · rw [hi, hj, hf_sub, hf_sub, E7_castSucc_eq_E6, ← hsub']
  · -- Weight 2: null vector contradiction on 6×6 submatrix
    exfalso
    have hw2 : A v u * A u v = 2 := by omega
    have hcases : (A v u = -1 ∧ A u v = -2) ∨ (A v u = -2 ∧ A u v = -1) := by
      have : A v u = -1 ∨ A v u = -2 := by
        have : -2 ≤ A v u := by
          by_contra hlt; push_neg at hlt
          nlinarith [mul_nonneg_of_nonpos_of_nonpos (show A v u + 2 ≤ 0 by omega)
            (show A u v + 1 ≤ 0 by omega)]
        omega
      rcases this with h | h <;> [left; right] <;> constructor <;>
        [exact h; nlinarith; exact h; nlinarith]
    have he'symm0 : e'.symm 0 = u_idx := by rw [← h0, e'.symm_apply_apply]
    let verts : Fin 5 → Fin 6 := ![0, 2, 3, 1, 4]
    let g : Fin 5 → Fin 7 := fun k => v.succAbove (e'.symm (verts k))
    have hg0_eq : g 0 = u := by
      show v.succAbove (e'.symm ((![0, 2, 3, 1, 4] : Fin 5 → Fin 6) 0)) = u
      simp; rw [he'symm0, hu_idx]
    let φ : Fin 6 → Fin 7 := Fin.cons v g
    have hφ0 : φ 0 = v := by simp only [φ, Fin.cons_zero]
    have hφS : ∀ k : Fin 5, φ (Fin.succ k) = g k := by
      intro k; simp only [φ, Fin.cons_succ]
    have hφ_inj : Function.Injective φ := by
      intro i j hij
      rcases i.eq_zero_or_eq_succ with rfl | ⟨i', rfl⟩ <;>
        rcases j.eq_zero_or_eq_succ with rfl | ⟨j', rfl⟩
      · rfl
      · exfalso; rw [hφ0, hφS] at hij
        exact Fin.succAbove_ne v _ hij.symm
      · exfalso; rw [hφ0, hφS] at hij
        exact Fin.succAbove_ne v _ hij
      · rw [hφS, hφS] at hij; congr 1
        have h1 := Fin.succAbove_right_injective hij
        have h2 := e'.symm.injective h1
        have : (⟨i'.val, by omega⟩ : Fin 5) = ⟨j'.val, by omega⟩ := by
          fin_cases i' <;> fin_cases j' <;> simp_all [verts, g]
        exact Fin.ext (Fin.ext_iff.mp this)
    let φ_emb : Fin 6 ↪ Fin 7 := ⟨φ, hφ_inj⟩
    have hk_ne_u : ∀ k : Fin 5, verts k ≠ 0 →
        e'.symm (verts k) ≠ u_idx := by
      intro k hk heq; exact hk (e'.symm.injective (heq.trans he'symm0.symm))
    have hgg : ∀ ki kj : Fin 5, A (g ki) (g kj) =
        CartanMatrix.E₆ (verts ki) (verts kj) := by
      intro ki kj; show A (v.succAbove _) (v.succAbove _) = _
      rw [hsub, e'.apply_symm_apply, e'.apply_symm_apply]
    have hentry_v0 : ∀ (Avu Auv : ℤ) (hAvu' : A v u = Avu) (hAuv' : A u v = Auv)
        (M : Matrix (Fin 6) (Fin 6) ℤ)
        (hM1 : ∀ ki kj : Fin 5, M (Fin.succ ki) (Fin.succ kj) =
          CartanMatrix.E₆ (verts ki) (verts kj))
        (hM2 : M 0 0 = 2) (hM3 : M 0 (Fin.succ 0) = Avu) (hM4 : M (Fin.succ 0) 0 = Auv)
        (hM5 : ∀ k : Fin 5, verts k ≠ 0 → M (Fin.succ k) 0 = 0)
        (hM6 : ∀ k : Fin 5, verts k ≠ 0 → M 0 (Fin.succ k) = 0),
        ∀ i j : Fin 6, A (φ i) (φ j) = M i j := by
      intro Avu Auv hAvu' hAuv' M hM1 hM2 hM3 hM4 hM5 hM6 i j
      rcases i.eq_zero_or_eq_succ with rfl | ⟨i', rfl⟩ <;>
        rcases j.eq_zero_or_eq_succ with rfl | ⟨j', rfl⟩
      · rw [hφ0, hGCM.diag, ← hM2]
      · rw [hφ0, hφS]
        by_cases hj0 : j' = 0
        · subst hj0; rw [hg0_eq, hAvu', ← hM3]
        · have : verts j' ≠ 0 := by
            fin_cases j' <;> simp_all [verts]
          rw [show A v (g j') = 0 from hAv0 _ (hk_ne_u j' this), ← hM6 _ this]
      · rw [hφ0, hφS]
        by_cases hi0 : i' = 0
        · subst hi0; rw [hg0_eq, hAuv', ← hM4]
        · have : verts i' ≠ 0 := by
            fin_cases i' <;> simp_all [verts]
          have h0' := hAv0 _ (hk_ne_u i' this)
          rw [show A (g i') v = 0 from
            (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v _))).mp h0',
            ← hM5 _ this]
      · rw [hφS, hφS, hgg, ← hM1]
    rcases hcases with ⟨hvu_eq, huv_eq⟩ | ⟨hvu_eq, huv_eq⟩
    · apply absurd hPD
      exact not_posDef_of_submatrix_int_null hSym φ_emb e6v0w2c1
        (hentry_v0 (-1) (-2) hvu_eq huv_eq e6v0w2c1
          (fun ki kj => (E6_v0w2_sub ki kj).symm)
          (by decide) (by decide) (by decide)
          (by intro k hk; fin_cases k <;> simp_all [verts] <;> decide)
          (by intro k hk; fin_cases k <;> simp_all [verts] <;> decide))
        _ (by decide) e6v0w2c1_null
    · apply absurd hPD
      exact not_posDef_of_submatrix_int_null hSym φ_emb e6v0w2c2
        (hentry_v0 (-2) (-1) hvu_eq huv_eq e6v0w2c2
          (fun ki kj => (E6_v0w2_sub_c2 ki kj).symm)
          (by decide) (by decide) (by decide)
          (by intro k hk; fin_cases k <;> simp_all [verts] <;> decide)
          (by intro k hk; fin_cases k <;> simp_all [verts] <;> decide))
        _ (by decide) e6v0w2c2_null

set_option maxHeartbeats 400000 in
/-- E₆ marks case: attachment at vertices 1, 2, 4 (all have customE6 = 2) gives
    qform ≤ 0 via d-equality and the customE6 test vector. -/
private theorem e6_marks_case {A : Matrix (Fin 7) (Fin 7) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v u : Fin 7) (_huv : u ≠ v)
    (e' : Fin 6 ≃ Fin 6)
    (u_idx : Fin 6) (hu_idx : v.succAbove u_idx = u)
    (hsub : ∀ i j : Fin 6, A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.E₆ (e' i) (e' j))
    (hAv0 : ∀ k : Fin 6, k ≠ u_idx → A v (v.succAbove k) = 0)
    (hAvu_neg : A v u ≤ -1) (hAuv_neg : A u v ≤ -1)
    (_hcw_pos : 1 ≤ A v u * A u v)
    (hMarks : customE6 (e' u_idx) = 2) : False := by
  -- D-equality on E₆ subgraph: E₆ is symmetric → edge d-values equal
  have hedge : ∀ p q : Fin 6, p ≠ q → CartanMatrix.E₆ p q ≠ 0 →
      hSym.d (v.succAbove (e'.symm p)) = hSym.d (v.succAbove (e'.symm q)) := by
    intro p q _ hE
    have h := hSym.sym (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))
    have hA_pq : A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q)) =
        CartanMatrix.E₆ p q := by rw [hsub]; simp [Equiv.apply_symm_apply]
    have hA_qp : A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p)) =
        CartanMatrix.E₆ q p := by rw [hsub]; simp [Equiv.apply_symm_apply]
    have hEsym : CartanMatrix.E₆ q p = CartanMatrix.E₆ p q := by
      have := congr_fun (congr_fun CartanMatrix.E₆_isSymm p) q
      rwa [Matrix.transpose_apply] at this
    rw [show (↑(A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))) : ℚ)
        = ↑(CartanMatrix.E₆ p q) from by rw [hA_pq],
      show (↑(A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p))) : ℚ)
        = ↑(CartanMatrix.E₆ p q) from by rw [hA_qp, hEsym]] at h
    exact mul_right_cancel₀ (by exact_mod_cast hE : (↑(CartanMatrix.E₆ p q) : ℚ) ≠ 0) h
  -- Chain along E₆ edges: 0↔2, 2↔3, 1↔3, 3↔4, 4↔5
  have h02 := hedge 0 2 (by decide) (by decide)
  have h23 := hedge 2 3 (by decide) (by decide)
  have h13 := hedge 1 3 (by decide) (by decide)
  have h34 := hedge 3 4 (by decide) (by decide)
  have h45 := hedge 4 5 (by decide) (by decide)
  have hD_all : ∀ p : Fin 6,
      hSym.d (v.succAbove (e'.symm p)) = hSym.d (v.succAbove (e'.symm 3)) := by
    intro p; fin_cases p
    · exact h02.trans h23
    · exact h13
    · exact h23
    · rfl
    · exact h34.symm
    · exact h45.symm.trans h34.symm
  -- d at vertex mapping to E₆-1 = d(u)
  have hd1_eq_u : hSym.d (v.succAbove (e'.symm 1)) = hSym.d u := by
    rw [hD_all 1, ← hD_all (e' u_idx), Equiv.symm_apply_apply, hu_idx]
  -- Test vector: x(v) = -A(v,u), x(sA k) = customE6(e' k)
  set c : ℚ := -(↑(A v u) : ℚ)
  have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
  have hc_pos : 0 < c := by simp only [c]; linarith
  set x : Fin 7 → ℚ := fun i =>
    if h : ∃ k : Fin 6, v.succAbove k = i then ↑(customE6 (e' h.choose))
    else c
  have hx_sub : ∀ k : Fin 6, x (v.succAbove k) = ↑(customE6 (e' k)) := by
    intro k; simp only [x]
    have hex : ∃ k' : Fin 6, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
    rw [dif_pos hex]
    have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
    rw [heq]
  have hx_v : x v = c := by
    simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
  have hx : x ≠ 0 := by
    intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
  -- Inner sum at leaf v: 2c + A(v,u)*2 = 0 (since c = -A(v,u))
  set mj : ℤ := customE6 (e' u_idx)
  have hmj : mj = 2 := hMarks
  have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
    rw [Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hGCM.diag v, hx_sub]
    have hsum : ∑ k : Fin 6, (↑(A v (v.succAbove k)) : ℚ) * ↑(customE6 (e' k)) =
        ↑(A v u) * ↑mj := by
      rw [← show (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(customE6 (e' u_idx)) =
          ↑(A v u) * ↑mj from by rw [hu_idx]]
      exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
    rw [hsum, hmj]; push_cast; ring
  -- E₆·customE6 reindexing through e'
  have e6custom_sum : ∀ k : Fin 6,
      ∑ l : Fin 6, (↑(CartanMatrix.E₆ (e' k) (e' l)) : ℚ) * ↑(customE6 (e' l)) =
      if e' k = 1 then 1 else 0 := by
    intro k
    rw [Equiv.sum_comp e' (fun p => (↑(CartanMatrix.E₆ (e' k) p) : ℚ) * ↑(customE6 p))]
    have h := congr_fun E6_mulVec_custom (e' k)
    simp only [mulVec, dotProduct] at h
    have hcast : ∑ p, (↑(CartanMatrix.E₆ (e' k) p) : ℚ) * ↑(customE6 p)
        = (↑(∑ p, CartanMatrix.E₆ (e' k) p * customE6 p) : ℚ) := by push_cast; rfl
    rw [hcast, h]; push_cast; split_ifs <;> simp
  -- Inner sum at non-v vertex k
  have inner_sub : ∀ k : Fin 6, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
      ↑(A (v.succAbove k) v) * c +
      (if e' k = 1 then 1 else 0) := by
    intro k
    rw [Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hx_sub]; congr 1
    have : ∀ l : Fin 6, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(customE6 (e' l))
        = (↑(CartanMatrix.E₆ (e' k) (e' l)) : ℚ) * ↑(customE6 (e' l)) := by
      intro l; rw [hsub]
    simp_rw [this]
    exact e6custom_sum k
  -- Symmetrizability trick: d(sA k)*A(sA k, v) = d(v)*A(v, sA k)
  have sym_trick : ∀ k : Fin 6,
      hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ) =
      hSym.d v * (↑(A v (v.succAbove k)) : ℚ) := by
    intro k; linarith [hSym.sym (v.succAbove k) v]
  -- Show qform ≤ 0
  apply absurd hPD
  apply not_posDef_of_nonpos hSym x hx
  rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
  simp only [hx_v, hx_sub, inner_v, inner_sub]
  -- Leaf row = d(v)*c*0 = 0; simplify
  have hleaf_zero : hSym.d v * c * (0 : ℚ) = 0 := by ring
  rw [hleaf_zero, zero_add]
  -- Non-v sum: split into cross + residual
  have hsplit : ∀ k : Fin 6,
      hSym.d (v.succAbove k) * ↑(customE6 (e' k)) *
      (↑(A (v.succAbove k) v) * c + if e' k = (1 : Fin 6) then (1 : ℚ) else 0) =
      c * (hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ)) * ↑(customE6 (e' k)) +
      hSym.d (v.succAbove k) * ↑(customE6 (e' k)) *
      (if e' k = (1 : Fin 6) then (1 : ℚ) else 0) := by intro k; ring
  simp_rw [hsplit, sym_trick]
  rw [Finset.sum_add_distrib]
  -- Cross-term sum = c*d(v)*A(v,u)*mj (only u_idx contributes)
  have hcross : ∑ k : Fin 6, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
      ↑(customE6 (e' k)) = c * hSym.d v * (↑(A v u) * ↑mj) := by
    simp_rw [show ∀ k : Fin 6, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
        ↑(customE6 (e' k)) = c * hSym.d v * ((↑(A v (v.succAbove k)) : ℚ) *
        ↑(customE6 (e' k))) from fun k => by ring]
    rw [← Finset.mul_sum]; congr 1
    rw [← show (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(customE6 (e' u_idx)) =
        ↑(A v u) * ↑mj from by rw [hu_idx]]
    exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
  -- Residual sum = 2*d(u) (only vertex 1 contributes, via D-equality)
  have hresid : ∑ k : Fin 6, hSym.d (v.succAbove k) * ↑(customE6 (e' k)) *
      (if e' k = (1 : Fin 6) then (1 : ℚ) else 0) =
      2 * hSym.d u := by
    simp_rw [show ∀ k : Fin 6, hSym.d (v.succAbove k) * ↑(customE6 (e' k)) *
        (if e' k = (1 : Fin 6) then (1 : ℚ) else 0) =
        if e' k = 1 then hSym.d (v.succAbove k) * ↑(customE6 (e' k)) else 0 from
      fun k => by split_ifs <;> ring]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hmem : Finset.univ.filter (fun k : Fin 6 => e' k = 1) = {e'.symm 1} := by
      ext k; simp [Finset.mem_filter, Equiv.eq_symm_apply]
    rw [hmem, Finset.sum_singleton, Equiv.apply_symm_apply]
    show hSym.d (v.succAbove (e'.symm 1)) * ↑(customE6 1) = 2 * hSym.d u
    rw [hd1_eq_u]; simp [customE6]; ring
  rw [hcross, hresid, hmj]
  -- Total: c*d(v)*A(v,u)*2 + 2*d(u) = 2*d(u)*(1 - A(u,v)*A(v,u)) ≤ 0
  have hsym_vu' : hSym.d v * (↑(A v u) : ℚ) = hSym.d u * (↑(A u v) : ℚ) := by
    linarith [hSym.sym v u]
  have hdu : 0 < hSym.d u := hSym.d_pos u
  have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
  have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
  -- c*d(v)*A(v,u)*2 = -d(v)*A(v,u)²*2 = -d(u)*A(u,v)*A(v,u)*2
  have hrewrite : c * hSym.d v * (↑(A v u) * ↑(2 : ℤ)) + 2 * hSym.d u =
      2 * hSym.d u * (1 - (↑(A u v) : ℚ) * (↑(A v u) : ℚ)) := by
    simp only [c]; push_cast; nlinarith [hsym_vu']
  rw [hrewrite]
  -- 2*d(u)*(1-w) ≤ 0 since w = A(u,v)*A(v,u) ≥ 1
  have hab : 1 ≤ (↑(A u v) : ℚ) * (↑(A v u) : ℚ) := by
    have := mul_le_mul_of_nonpos_left hAuv_q (show (↑(A v u) : ℚ) ≤ 0 by linarith)
    linarith
  nlinarith

set_option maxHeartbeats 400000 in
/-- E₆ can only be extended to E₇. Any leaf attachment either gives CartanEquiv to E₇
    or contradicts positive definiteness. -/
theorem e6_extension {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3))
    (u : Fin (n+3)) (huv : u ≠ v) (hAvu : A v u ≠ 0) (hAuv : A u v ≠ 0)
    (huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u)
    (hcw_le2 : A v u * A u v ≤ 2)
    (ht' : CartanEquiv (deleteVertex A v) CartanMatrix.E₆) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  have hn : n = 4 := by
    obtain ⟨e, _⟩ := ht'; have := Fintype.card_congr e
    simp only [Fintype.card_fin] at this; omega
  subst hn
  obtain ⟨e', he'⟩ := ht'
  obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
  have hsub : ∀ i j : Fin 6, A (v.succAbove i) (v.succAbove j) =
      CartanMatrix.E₆ (e' i) (e' j) := fun i j => (he' i j).symm
  have hAv0 : ∀ k : Fin 6, k ≠ u_idx → A v (v.succAbove k) = 0 := by
    intro k hk
    have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
    have hne_u : v.succAbove k ≠ u := fun h =>
      hk (Fin.succAbove_right_injective (hu_idx ▸ h))
    by_contra hvk; exact hne_u (huniq _ hne_v hvk)
  have hAvu_neg : A v u ≤ -1 := by
    have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_neg : A u v ≤ -1 := by
    have := hGCM.off_diag_nonpos u v huv; omega
  have hcw_pos : 1 ≤ A v u * A u v := by nlinarith
  -- Dispatch to sub-case helpers
  by_cases h5 : e' u_idx = 5
  · exact e6_v5_case hGCM hSym hPD v u huv hcw_le2 e' u_idx hu_idx hsub hAv0
      hAvu_neg hAuv_neg hcw_pos h5
  · by_cases h3 : e' u_idx = 3
    · -- u maps to trivalent vertex 3: degree 4 in full graph → contradiction
      exfalso
      -- E₆ vertex 3 connects to 1, 2, 4. Lift these to full graph.
      have hAu_lift : ∀ p : Fin 6, CartanMatrix.E₆ 3 p ≠ 0 →
          A u (v.succAbove (e'.symm p)) ≠ 0 := by
        intro p hp
        have h1 := hsub u_idx (e'.symm p)
        rw [hu_idx] at h1
        rw [h3, e'.apply_symm_apply] at h1
        rwa [h1]
      -- u has ≥ 4 neighbors: v, lift(1), lift(2), lift(4)
      apply absurd (gcmDegree_le_three hGCM hSym hPD u); push_neg
      unfold gcmDegree
      -- Build 4-element subset of degree set
      have hsa_ne : ∀ a b : Fin 6, a ≠ b →
          v.succAbove (e'.symm a) ≠ v.succAbove (e'.symm b) :=
        fun _ _ h heq => h (e'.symm.injective (Fin.succAbove_right_injective heq))
      have hsa_ne_u : ∀ p : Fin 6, p ≠ 3 →
          v.succAbove (e'.symm p) ≠ u := by
        intro p hp heq
        have h1 : e'.symm p = u_idx :=
          Fin.succAbove_right_injective (heq.trans hu_idx.symm)
        exact hp (by rw [← h3, ← h1, e'.apply_symm_apply])
      -- 4 distinct neighbors of u
      have hv_ne1 : v ≠ v.succAbove (e'.symm 1) := Ne.symm (Fin.succAbove_ne v _)
      have hv_ne2 : v ≠ v.succAbove (e'.symm 2) := Ne.symm (Fin.succAbove_ne v _)
      have hv_ne4 : v ≠ v.succAbove (e'.symm 4) := Ne.symm (Fin.succAbove_ne v _)
      have h12 : v.succAbove (e'.symm 1) ≠ v.succAbove (e'.symm 2) :=
        hsa_ne 1 2 (by decide)
      have h14 : v.succAbove (e'.symm 1) ≠ v.succAbove (e'.symm 4) :=
        hsa_ne 1 4 (by decide)
      have h24 : v.succAbove (e'.symm 2) ≠ v.succAbove (e'.symm 4) :=
        hsa_ne 2 4 (by decide)
      have hmem : ∀ j ∈ ({v, v.succAbove (e'.symm 1), v.succAbove (e'.symm 2),
          v.succAbove (e'.symm 4)} : Finset (Fin 7)),
          j ∈ Finset.univ.filter (fun j => j ≠ u ∧ A u j ≠ 0) := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hj with rfl | rfl | rfl | rfl
        · exact ⟨huv.symm, hAuv⟩
        · exact ⟨hsa_ne_u 1 (by decide), hAu_lift 1 (by decide)⟩
        · exact ⟨hsa_ne_u 2 (by decide), hAu_lift 2 (by decide)⟩
        · exact ⟨hsa_ne_u 4 (by decide), hAu_lift 4 (by decide)⟩
      calc (Finset.univ.filter (fun j => j ≠ u ∧ A u j ≠ 0)).card
          ≥ ({v, v.succAbove (e'.symm 1), v.succAbove (e'.symm 2),
              v.succAbove (e'.symm 4)} : Finset (Fin 7)).card :=
            Finset.card_le_card hmem
        _ = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hv_ne1, hv_ne2, hv_ne4]),
                Finset.card_insert_of_notMem (by simp [h12, h14]),
                Finset.card_insert_of_notMem (by simp [h24]),
                Finset.card_singleton]
    · by_cases h0 : e' u_idx = 0
      · exact e6_v0_case hGCM hSym hPD v u huv hcw_le2 e' u_idx hu_idx hsub hAv0
          hAvu_neg hAuv_neg hcw_pos h0
      · -- Vertices 1, 2, 4: customE6 marks contradiction
        exfalso
        exact e6_marks_case hGCM hSym hPD v u huv e' u_idx hu_idx
          hsub hAv0 hAvu_neg hAuv_neg hcw_pos
          (customE6_eq_two _ h5 h3 h0)

/-- E₈ cannot be extended: any pos-def GCM whose principal submatrix is
    CartanEquiv to E₈ is a contradiction.
    Proof: the E₈ marks vector extended with -A(v,u) at the leaf gives a
    non-positive qform. Key ingredients:
    - E₈·marks = (0,...,0,1) with only vertex-7 nonzero
    - marks ≥ 2 everywhere
    - d-values on E₈ subgraph are all equal (E₈ symmetric + connected)
    - symmetrizability converts cross-terms to use d(v) -/
theorem e8_no_extension {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1)
    (ht' : CartanEquiv (deleteVertex A v) CartanMatrix.E₈) : False := by
  -- Rank: n + 2 = 8, so the matrix is 9×9
  have hn : n = 6 := by
    obtain ⟨e, _⟩ := ht'; have := Fintype.card_congr e
    simp only [Fintype.card_fin] at this; omega
  subst hn
  -- Extract leaf structure
  have hleaf' := hleaf; unfold gcmDegree at hleaf'
  obtain ⟨u, hu_set⟩ := Finset.card_eq_one.mp hleaf'
  have hu_mem := hu_set ▸ Finset.mem_singleton_self u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu_mem
  have huv : u ≠ v := hu_mem.1
  have hAvu : A v u ≠ 0 := hu_mem.2
  have huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u := by
    intro j hjv hjA
    have hmem : j ∈ Finset.univ.filter (fun j : Fin 9 => j ≠ v ∧ A v j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjv, hjA⟩
    rw [hu_set] at hmem; exact Finset.mem_singleton.mp hmem
  obtain ⟨e', he'⟩ := ht'
  obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
  have hAvu_neg : A v u ≤ -1 := by
    have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_ne : A u v ≠ 0 := fun h => hAvu ((hGCM.zero_iff u v huv).mp h)
  have hAuv_neg : A u v ≤ -1 := by
    have := hGCM.off_diag_nonpos u v huv; omega
  -- Leaf zero entries: v only connects to u
  have hAv0 : ∀ k : Fin 8, k ≠ u_idx → A v (v.succAbove k) = 0 := by
    intro k hk
    have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
    have hne_u : v.succAbove k ≠ u := fun h =>
      hk (Fin.succAbove_right_injective (hu_idx ▸ h))
    by_contra hvk; exact hne_u (huniq _ hne_v hvk)
  -- Submatrix entries = E₈ entries via CartanEquiv
  have hsub : ∀ i j : Fin 8, A (v.succAbove i) (v.succAbove j) =
      CartanMatrix.E₈ (e' i) (e' j) := fun i j => (he' i j).symm
  -- D-value equality on E₈ subgraph: E₈ is symmetric + connected → all d equal
  have hedge : ∀ p q : Fin 8, p ≠ q → CartanMatrix.E₈ p q ≠ 0 →
      hSym.d (v.succAbove (e'.symm p)) = hSym.d (v.succAbove (e'.symm q)) := by
    intro p q _ hE
    have h := hSym.sym (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))
    have hA_pq : A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q)) =
        CartanMatrix.E₈ p q := by rw [hsub]; simp [Equiv.apply_symm_apply]
    have hA_qp : A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p)) =
        CartanMatrix.E₈ q p := by rw [hsub]; simp [Equiv.apply_symm_apply]
    have hEsym : CartanMatrix.E₈ q p = CartanMatrix.E₈ p q := by
      have := congr_fun (congr_fun CartanMatrix.E₈_isSymm p) q
      rwa [Matrix.transpose_apply] at this
    rw [show (↑(A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))) : ℚ)
        = ↑(CartanMatrix.E₈ p q) from by rw [hA_pq],
      show (↑(A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p))) : ℚ)
        = ↑(CartanMatrix.E₈ p q) from by rw [hA_qp, hEsym]] at h
    exact mul_right_cancel₀ (by exact_mod_cast hE : (↑(CartanMatrix.E₈ p q) : ℚ) ≠ 0) h
  -- Chain along E₈ edges: 0↔2, 1↔3, 2↔3, 3↔4, 4↔5, 5↔6, 6↔7
  have h02 := hedge 0 2 (by decide) (by decide)
  have h23 := hedge 2 3 (by decide) (by decide)
  have h13 := hedge 1 3 (by decide) (by decide)
  have h34 := hedge 3 4 (by decide) (by decide)
  have h45 := hedge 4 5 (by decide) (by decide)
  have h56 := hedge 5 6 (by decide) (by decide)
  have h67 := hedge 6 7 (by decide) (by decide)
  -- All d values equal (chain to vertex 3, which connects to 0,1,2,4 directly/transitively)
  have hD_all : ∀ p : Fin 8,
      hSym.d (v.succAbove (e'.symm p)) = hSym.d (v.succAbove (e'.symm 3)) := by
    intro p; fin_cases p
    · exact h02.trans h23                                          -- 0→2→3
    · exact h13                                                     -- 1→3
    · exact h23                                                     -- 2→3
    · rfl                                                           -- 3
    · exact h34.symm                                                -- 4→3
    · exact h45.symm.trans h34.symm                                 -- 5→4→3
    · exact h56.symm.trans (h45.symm.trans h34.symm)                -- 6→5→4→3
    · exact h67.symm.trans (h56.symm.trans (h45.symm.trans h34.symm)) -- 7→6→5→4→3
  -- Key: d at vertex mapping to E₈-7 = d at u
  have hd7_eq_u : hSym.d (v.succAbove (e'.symm 7)) = hSym.d u := by
    have h1 := hD_all 7
    have h2 := hD_all (e' u_idx)
    rw [Equiv.symm_apply_apply] at h2
    rw [hu_idx] at h2
    exact h1.trans h2.symm
  -- Test vector: x(v) = -A(v,u), x(sA k) = marks(e' k)
  set c : ℚ := -(↑(A v u) : ℚ)
  have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
  have hc_pos : 0 < c := by simp only [c]; linarith
  set x : Fin 9 → ℚ := fun i =>
    if h : ∃ k : Fin 8, v.succAbove k = i then ↑(marksE8 (e' h.choose))
    else c
  have hx_sub : ∀ k : Fin 8, x (v.succAbove k) = ↑(marksE8 (e' k)) := by
    intro k; simp only [x]
    have hex : ∃ k' : Fin 8, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
    rw [dif_pos hex]
    have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
    rw [heq]
  have hx_v : x v = c := by
    simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
  have hx : x ≠ 0 := by
    intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
  -- Inner sum at leaf row v
  set mj : ℤ := marksE8 (e' u_idx)
  have hmj : (2 : ℤ) ≤ mj := marksE8_ge_two _
  have inner_v : ∑ j, (↑(A v j) : ℚ) * x j =
      2 * c + ↑(A v u) * ↑mj := by
    rw [Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hGCM.diag v, hx_sub]
    have hsum : ∑ k : Fin 8, (↑(A v (v.succAbove k)) : ℚ) * ↑(marksE8 (e' k)) =
        ↑(A v u) * ↑mj := by
      have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksE8 (e' u_idx)) =
          ↑(A v u) * ↑mj := by rw [hu_idx]
      rw [← hval]
      exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
    rw [hsum]; push_cast; ring
  -- E₈·marks reindexing
  have e8marks_sum : ∀ k : Fin 8,
      ∑ l : Fin 8, (↑(CartanMatrix.E₈ (e' k) (e' l)) : ℚ) * ↑(marksE8 (e' l)) =
      if e' k = 7 then 1 else 0 := by
    intro k
    have hreindex : ∑ l, (↑(CartanMatrix.E₈ (e' k) (e' l)) : ℚ) * ↑(marksE8 (e' l))
        = ∑ p, (↑(CartanMatrix.E₈ (e' k) p) : ℚ) * ↑(marksE8 p) := by
      exact Equiv.sum_comp e' (fun p => (↑(CartanMatrix.E₈ (e' k) p) : ℚ) * ↑(marksE8 p))
    rw [hreindex]
    have h := congr_fun E8_mulVec_marks (e' k)
    simp only [mulVec, dotProduct] at h
    have hcast : ∑ p, (↑(CartanMatrix.E₈ (e' k) p) : ℚ) * ↑(marksE8 p)
        = (↑(∑ p, CartanMatrix.E₈ (e' k) p * marksE8 p) : ℚ) := by push_cast; rfl
    rw [hcast, h]; push_cast; split_ifs <;> simp
  -- Inner sum at non-v vertex k
  have inner_sub : ∀ k : Fin 8, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
      ↑(A (v.succAbove k) v) * c +
      (if e' k = 7 then 1 else 0) := by
    intro k
    rw [Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hx_sub]; congr 1
    -- Rewrite A entries as E₈ entries, then use e8marks_sum
    have : ∀ l : Fin 8, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(marksE8 (e' l))
        = (↑(CartanMatrix.E₈ (e' k) (e' l)) : ℚ) * ↑(marksE8 (e' l)) := by
      intro l; rw [hsub]
    simp_rw [this]
    exact e8marks_sum k
  -- Symmetrizability trick: d(sA k)*A(sA k, v) = d(v)*A(v, sA k)
  have sym_trick : ∀ k : Fin 8,
      hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ) =
      hSym.d v * (↑(A v (v.succAbove k)) : ℚ) := by
    intro k; have := hSym.sym (v.succAbove k) v; linarith
  -- Show qform ≤ 0
  apply absurd hPD
  apply not_posDef_of_nonpos hSym x hx
  rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
  simp only [hx_v, hx_sub, inner_v, inner_sub]
  -- Split non-v sum: cross-terms + residual
  have hsplit : ∀ k : Fin 8,
      hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) *
      (↑(A (v.succAbove k) v) * c + if e' k = (7 : Fin 8) then (1 : ℚ) else 0) =
      c * (hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ)) * ↑(marksE8 (e' k)) +
      hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) *
      (if e' k = (7 : Fin 8) then (1 : ℚ) else 0) := by intro k; ring
  simp_rw [hsplit, sym_trick]
  rw [Finset.sum_add_distrib]
  -- Cross-term sum = c*d(v)*A(v,u)*mj (only u_idx term nonzero)
  have hcross : ∑ k : Fin 8, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
      ↑(marksE8 (e' k)) = c * hSym.d v * (↑(A v u) * ↑mj) := by
    simp_rw [show ∀ k : Fin 8, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
        ↑(marksE8 (e' k)) = c * hSym.d v * ((↑(A v (v.succAbove k)) : ℚ) *
        ↑(marksE8 (e' k))) from fun k => by ring]
    rw [← Finset.mul_sum]
    congr 1
    have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksE8 (e' u_idx)) =
        ↑(A v u) * ↑mj := by rw [hu_idx]
    rw [← hval]
    exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
  -- Residual sum = d(u)*2 (only vertex 7 contributes, via D-equality)
  have hresid : ∑ k : Fin 8, hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) *
      (if e' k = (7 : Fin 8) then (1 : ℚ) else 0) =
      2 * hSym.d u := by
    simp_rw [show ∀ k : Fin 8, hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) *
        (if e' k = (7 : Fin 8) then (1 : ℚ) else 0) =
        if e' k = 7 then hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) else 0 from
      fun k => by split_ifs <;> ring]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hmem : Finset.univ.filter (fun k : Fin 8 => e' k = 7) = {e'.symm 7} := by
      ext k; simp [Finset.mem_filter, Equiv.eq_symm_apply]
    rw [hmem, Finset.sum_singleton, Equiv.apply_symm_apply]
    show hSym.d (v.succAbove (e'.symm 7)) * ↑(marksE8 7) = 2 * hSym.d u
    rw [hd7_eq_u]; simp [marksE8]; ring
  rw [hcross, hresid]
  -- Total: d(v)*c*(2c + A(v,u)*mj) + c*d(v)*A(v,u)*mj + 2*d(u) ≤ 0
  have hsym_vu := hSym.sym v u
  have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
  have hdv : 0 < hSym.d v := hSym.d_pos v
  have hdu : 0 < hSym.d u := hSym.d_pos u
  have hmj_q : (2 : ℚ) ≤ ↑mj := by exact_mod_cast hmj
  -- Algebraic simplification: unfold c = -↑(A v u) and rearrange
  have htotal : hSym.d v * c * (2 * c + ↑(A v u) * ↑mj) +
      (c * hSym.d v * (↑(A v u) * ↑mj) + 2 * hSym.d u) =
      2 * (hSym.d u + hSym.d v * (↑(A v u) : ℚ) ^ 2 * (1 - (↑mj : ℚ))) := by
    simp only [c]; ring
  rw [htotal]
  -- Symmetrizability: d(v)*A(v,u) = d(u)*A(u,v)
  have hsym_vu' : hSym.d v * (↑(A v u) : ℚ) = hSym.d u * (↑(A u v) : ℚ) := by
    linarith [hsym_vu]
  -- d(v)*A(v,u)² = d(u)*A(u,v)*A(v,u)
  have hkey : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
      hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) := by
    have : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
        (hSym.d v * (↑(A v u) : ℚ)) * (↑(A v u) : ℚ) := by ring
    rw [this, hsym_vu']; ring
  rw [hkey]
  -- Goal: 2*du + 2*(du*(auv*avu))*(1-mj) ≤ 0
  -- A(u,v)*A(v,u) ≥ 1 (product of two ≤ -1 values)
  have hab : 1 ≤ (↑(A u v) : ℚ) * (↑(A v u) : ℚ) := by
    have := mul_le_mul_of_nonpos_left hAuv_q (show (↑(A v u) : ℚ) ≤ 0 by linarith)
    linarith
  -- du ≤ du*(auv*avu) since auv*avu ≥ 1
  have hdu_ab : hSym.d u ≤ hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) :=
    le_mul_of_one_le_right (le_of_lt hdu) hab
  -- (du*(auv*avu))*(1-mj) ≤ du*(1-mj) since du*(auv*avu) ≥ du and 1-mj ≤ 0
  have hbound := mul_le_mul_of_nonpos_right hdu_ab
    (show (1 : ℚ) - (↑mj : ℚ) ≤ 0 by linarith)
  -- du*(1-mj) ≤ -du since mj ≥ 2
  have hdu_mj : 0 ≤ hSym.d u * ((↑mj : ℚ) - 2) :=
    mul_nonneg (le_of_lt hdu) (by linarith)
  linarith

end BLD.Lie.Cartan
