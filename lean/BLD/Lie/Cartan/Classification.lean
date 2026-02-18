/- BLD Calculus — Cartan Classification: Main Theorem

   The extend_dynkin_type theorem (combinatorial heart) and
   the cartan_classification theorem (main result).
-/


import BLD.Lie.Cartan.ClassificationB
import BLD.Lie.Cartan.ClassificationC
import BLD.Lie.Cartan.ClassificationD
import BLD.Lie.Cartan.ClassificationE7

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

set_option maxHeartbeats 2000000 in
/-- Given a sub-matrix matching DynkinType t' and a leaf vertex v,
    determine the full DynkinType of the extended matrix.
    This is the combinatorial heart of the Cartan classification. -/
theorem extend_dynkin_type {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (hConn : IsConnected A hGCM)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1)
    (t' : DynkinType) (ht' : CartanEquiv (deleteVertex A v) t'.cartanMatrix.2) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  -- Extract the unique neighbor u of leaf v
  have hleaf' := hleaf
  unfold gcmDegree at hleaf'
  obtain ⟨u, hu_set⟩ := Finset.card_eq_one.mp hleaf'
  have hu_mem : u ∈ Finset.univ.filter (fun j : Fin (n+3) => j ≠ v ∧ A v j ≠ 0) :=
    hu_set ▸ Finset.mem_singleton_self u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu_mem
  have huv : u ≠ v := hu_mem.1
  have hAvu : A v u ≠ 0 := hu_mem.2
  have hAuv : A u v ≠ 0 := fun h => hAvu ((hGCM.zero_iff u v huv).mp h)
  have huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u := by
    intro j hjv hjA
    have : j ∈ Finset.univ.filter (fun j : Fin (n+3) => j ≠ v ∧ A v j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjv, hjA⟩
    rw [hu_set] at this; exact Finset.mem_singleton.mp this
  -- Rank equation
  have hrank : n + 2 = t'.cartanMatrix.1 := cartanEquiv_rank_eq ht'
  -- Get u's preimage in the submatrix
  obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
  -- u has a neighbor w in the connected subdiagram (rank ≥ 2)
  have hsubConn := deleteVertex_connected_of_leaf hGCM hConn v hleaf
  obtain ⟨w_sub, hw_ne, hBuw⟩ := exists_neighbor_of_connected
    (deleteVertex_isGCM hGCM v) hsubConn u_idx
  -- Translate to full matrix
  set w := v.succAbove w_sub with hw_def
  have hwv : w ≠ v := Fin.succAbove_ne v w_sub
  have hwu : w ≠ u := fun h => hw_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
  have hAuw : A u w ≠ 0 := by rw [← hu_idx]; exact hBuw
  -- Weight of the new edge (v, u) is ≤ 2: weight 3 → contradiction
  have hcw_lt : A v u * A u v < 4 :=
    coxeter_weight_lt_four hGCM hSym hPD v u huv.symm
  have hAvu_neg : A v u ≤ -1 := by
    have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_neg : A u v ≤ -1 := by
    have := hGCM.off_diag_nonpos u v huv; omega
  have hcw_pos : 1 ≤ A v u * A u v := by nlinarith
  have hcw_le2 : A v u * A u v ≤ 2 := by
    by_contra h; push_neg at h
    have hcw3 : A v u * A u v = 3 := by omega
    exact weight3_impossible hGCM hSym hPD v hleaf u huv hAvu
      w hwu hwv hAuw hcw3
  -- Case split on Dynkin type
  -- Zero entries: v only connects to u (leaf property)
  have hAv0 : ∀ m : Fin (n+2), m ≠ u_idx → A v (v.succAbove m) = 0 := by
    intro m hm; by_contra h
    exact hm (Fin.succAbove_right_injective (hu_idx ▸ huniq _ (Fin.succAbove_ne v m) h))
  have hAv0' : ∀ m : Fin (n+2), m ≠ u_idx → A (v.succAbove m) v = 0 := by
    intro m hm
    exact (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v m))).mp (hAv0 m hm)
  cases t' with
  | G₂ =>
    exfalso
    -- G₂ has rank 2: n + 2 = 2, so n = 0. A is 3×3.
    simp only [DynkinType.cartanMatrix] at hrank
    have hn : n = 0 := by omega
    subst hn
    obtain ⟨e', he'⟩ := ht'
    -- Get u's preimage in the 2-element submatrix
    obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
    -- The other submatrix vertex
    let w_idx : Fin 2 := if u_idx = 0 then 1 else 0
    have hw_ne : w_idx ≠ u_idx := by
      fin_cases u_idx <;> simp [w_idx]
    set w := v.succAbove w_idx with hw_def
    have hwu : w ≠ u := fun h => hw_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
    have hwv : w ≠ v := Fin.succAbove_ne v w_idx
    -- The G₂ Coxeter weight is 3 in the submatrix
    have hw3_sub : (deleteVertex A v) w_idx u_idx * (deleteVertex A v) u_idx w_idx = 3 := by
      rw [show (deleteVertex A v) w_idx u_idx = CartanMatrix.G₂ (e' w_idx) (e' u_idx) from
            (he' w_idx u_idx).symm,
          show (deleteVertex A v) u_idx w_idx = CartanMatrix.G₂ (e' u_idx) (e' w_idx) from
            (he' u_idx w_idx).symm]
      have hne : e' w_idx ≠ e' u_idx := e'.injective.ne hw_ne
      have key : ∀ (i j : Fin 2), i ≠ j →
          CartanMatrix.G₂ i j * CartanMatrix.G₂ j i = 3 := by decide
      exact key (e' w_idx) (e' u_idx) hne
    -- Translate to full matrix
    have hw3 : A w u * A u w = 3 := by rw [← hu_idx]; exact hw3_sub
    have hAwu : A w u ≠ 0 := by intro h; rw [h] at hw3; simp at hw3
    -- w is a leaf in the full matrix (connects only to u)
    have hleaf_w : gcmDegree A w = 1 := by
      unfold gcmDegree
      have hAvw : A v w = 0 := by
        by_contra h; exact hwu (huniq w hwv h)
      have hAwv : A w v = 0 := (hGCM.zero_iff v w (Ne.symm hwv)).mp hAvw
      suffices Finset.univ.filter (fun j : Fin 3 => j ≠ w ∧ A w j ≠ 0) = {u} by
        rw [this]; simp
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ⟨hjw, hjA⟩
        by_contra hju
        have hjv : j ≠ v := fun h => hjA (h ▸ hAwv)
        obtain ⟨j_idx, hj_idx⟩ := Fin.exists_succAbove_eq hjv
        have : j_idx ≠ u_idx := by intro h; exact hju (by rw [← hj_idx, h, hu_idx])
        have : j_idx ≠ w_idx := by intro h; exact hjw (by rw [← hj_idx, h])
        fin_cases j_idx <;> fin_cases u_idx <;> simp_all [w_idx]
      · intro hju; subst hju; exact ⟨hwu.symm, hAwu⟩
    -- Apply weight3_impossible: w is leaf, u is neighbor, v is third vertex
    exact weight3_impossible hGCM hSym hPD w hleaf_w u (Ne.symm hwu) hAwu
      v (Ne.symm huv) (Ne.symm hwv) hAuv hw3
  | A k hk =>
    simp only [DynkinType.cartanMatrix] at hrank ht'
    subst hrank -- k = n + 2
    exact a_extension hGCM hSym hPD v u huv hAvu hAuv huniq hcw_le2 ht'
  | B k hk =>
    simp only [DynkinType.cartanMatrix] at hrank ht'
    subst hrank
    exact extend_B hGCM hSym hPD v u huv hAvu hAuv huniq u_idx hu_idx
      hcw_le2 hcw_pos hAvu_neg hAuv_neg hAv0 hAv0' ht'
  | C k hk =>
    simp only [DynkinType.cartanMatrix] at hrank ht'
    subst hrank
    exact extend_C hGCM hSym hPD v u huv hAvu hAuv huniq u_idx hu_idx
      hcw_le2 hcw_pos hAvu_neg hAuv_neg hAv0 hAv0' ht'
  | D k hk =>
    simp only [DynkinType.cartanMatrix] at hrank ht'
    subst hrank
    exact extend_D hGCM hSym hPD v u huv hAvu hAuv huniq u_idx hu_idx
      hk hcw_le2 hcw_pos hAvu_neg hAuv_neg hAv0 hAv0' ht'
  | E₆ =>
    simp only [DynkinType.cartanMatrix] at hrank
    change CartanEquiv (deleteVertex A v) CartanMatrix.E₆ at ht'
    exact e6_extension hGCM hSym hPD v u huv hAvu hAuv huniq hcw_le2 ht'
  | E₇ =>
    simp only [DynkinType.cartanMatrix] at hrank
    change CartanEquiv (deleteVertex A v) CartanMatrix.E₇ at ht'
    have hn : n = 5 := by omega
    subst hn
    exact extend_E₇ hGCM hSym hPD v u huv hAvu hAuv huniq
      hcw_le2 hcw_pos hAvu_neg hAuv_neg ht'
  | E₈ => exact (e8_no_extension hGCM hSym hPD v hleaf ht').elim
  | F₄ => exact (f4_no_extension hGCM hSym hPD v hleaf ht').elim

-- ═══════════════════════════════════════════════════════════
-- Cartan classification theorem
-- ═══════════════════════════════════════════════════════════

/-- The Cartan classification: every indecomposable positive-definite
    generalized Cartan matrix is equivalent to one of the 9 Dynkin types
    (A_n, B_n, C_n, D_n, E₆, E₇, E₈, F₄, G₂).

    The proof uses strong induction on n with leaf removal.
    1. The graph is a tree (not_posDef_of_cycle)
    2. Coxeter weights < 4 (coxeter_weight_lt_four)
    3. Each vertex has degree ≤ 3 (gcmDegree_le_three)
    4. Delete a leaf, classify the submatrix by IH
    5. Classify how the leaf re-attaches

    Reference: Humphreys, Introduction to Lie Algebras, Chapter 11. -/
theorem cartan_classification {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A)
    (hConn : IsConnected A hGCM) (hPD : IsPosDef A hSym) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  -- Case split on matrix size
  match n with
  | 0 =>
    -- Fin 0 is empty, so Connected requires Nonempty (Fin 0) which is false
    exact absurd hConn.nonempty (not_nonempty_iff.mpr inferInstance)
  | 1 =>
    -- The only 1×1 GCM is [[2]] = A₁
    refine ⟨.A 1 (by omega), Equiv.refl _, fun i j => ?_⟩
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    subst hi; subst hj
    simp only [DynkinType.cartanMatrix, Equiv.refl_apply]
    rw [hGCM.diag 0]; decide
  | 2 =>
    -- Connectivity: the two vertices must be adjacent
    have h01 : A 0 1 ≠ 0 := by
      intro h
      have h10 := (hGCM.zero_iff 0 1 (by decide)).mp h
      have hnoedge : ∀ i j : Fin 2, ¬(toGraph A hGCM).Adj i j := by
        intro i j ⟨_, hA⟩; fin_cases i <;> fin_cases j <;> simp_all
      have ⟨w⟩ := hConn.preconnected (0 : Fin 2) 1
      exact w.rec (motive := fun u v _ => u ≠ v → False)
        (fun h => absurd rfl h)
        (fun hadj _ _ _ => absurd hadj (hnoedge _ _))
        (by decide)
    have h10 : A 1 0 ≠ 0 := fun h => h01 ((hGCM.zero_iff 1 0 (by decide)).mp h)
    -- Off-diagonal entries ≤ -1
    have ha1 : A 0 1 ≤ -1 := by
      have := hGCM.off_diag_nonpos 0 1 (by decide); omega
    have hb1 : A 1 0 ≤ -1 := by
      have := hGCM.off_diag_nonpos 1 0 (by decide); omega
    -- Coxeter weight in {1, 2, 3}
    have hw := coxeter_weight_lt_four hGCM hSym hPD 0 1 (by decide)
    unfold coxeterWeight at hw
    have hp_lo : 1 ≤ A 0 1 * A 1 0 := by nlinarith
    have hp_hi : A 0 1 * A 1 0 ≤ 3 := by omega
    -- Case split on the Coxeter weight (1, 2, or 3)
    have hcases : A 0 1 * A 1 0 = 1 ∨ A 0 1 * A 1 0 = 2 ∨ A 0 1 * A 1 0 = 3 := by omega
    rcases hcases with hw1 | hw2 | hw3
    · -- weight 1: a = b = -1 → A₂
      have ha : A 0 1 = -1 := by nlinarith
      have hb : A 1 0 = -1 := by nlinarith
      refine ⟨.A 2 (by omega), Equiv.refl _, fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;>
        simp only [DynkinType.cartanMatrix, Equiv.refl_apply, CartanMatrix.A_two] <;>
        first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
    · -- weight 2: (a,b) ∈ {(-2,-1), (-1,-2)} → B₂ or C₂
      have hab : (A 0 1 = -2 ∧ A 1 0 = -1) ∨ (A 0 1 = -1 ∧ A 1 0 = -2) := by
        have : -2 ≤ A 0 1 := by nlinarith
        have : -2 ≤ A 1 0 := by nlinarith
        have h1 : A 0 1 = -2 ∨ A 0 1 = -1 := by omega
        have h2 : A 1 0 = -2 ∨ A 1 0 = -1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; rw [h1, h2] at hw2; norm_num at hw2
        · exact .inl ⟨h1, h2⟩
        · exact .inr ⟨h1, h2⟩
        · exfalso; rw [h1, h2] at hw2; norm_num at hw2
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · refine ⟨.B 2 (by omega), Equiv.refl _, fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, Equiv.refl_apply, CartanMatrix.B_two] <;>
          first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
      · -- A 0 1 = -1, A 1 0 = -2: this is B₂ with swapped indices
        refine ⟨.B 2 (by omega), Equiv.swap 0 1, fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, CartanMatrix.B_two] <;>
          first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
    · -- weight 3: (a,b) ∈ {(-3,-1), (-1,-3)} → G₂
      have hab : (A 0 1 = -3 ∧ A 1 0 = -1) ∨ (A 0 1 = -1 ∧ A 1 0 = -3) := by
        have : -3 ≤ A 0 1 := by nlinarith
        have : -3 ≤ A 1 0 := by nlinarith
        have : A 0 1 ≠ -2 := fun h => by rw [h] at hw3; omega
        have : A 1 0 ≠ -2 := fun h => by rw [h] at hw3; omega
        have h1 : A 0 1 = -3 ∨ A 0 1 = -1 := by omega
        have h2 : A 1 0 = -3 ∨ A 1 0 = -1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; rw [h1, h2] at hw3; norm_num at hw3
        · exact .inl ⟨h1, h2⟩
        · exact .inr ⟨h1, h2⟩
        · exfalso; rw [h1, h2] at hw3; norm_num at hw3
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · refine ⟨.G₂, Equiv.refl _, fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, Equiv.refl_apply, CartanMatrix.G₂] <;>
          first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
      · refine ⟨.G₂, Equiv.swap 0 1, fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, CartanMatrix.G₂] <;>
          first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
  | n + 3 =>
    -- Find a leaf
    obtain ⟨v, hleaf⟩ := exists_leaf hGCM hSym hConn hPD
    -- Delete the leaf: gives (n+2) × (n+2) matrix
    -- Inductive hypothesis: sub-matrix is a Dynkin type
    obtain ⟨t', ht'⟩ := cartan_classification (deleteVertex A v)
      (deleteVertex_isGCM hGCM v) (deleteVertex_symmetrizable hSym v)
      (deleteVertex_connected_of_leaf hGCM hConn v hleaf)
      (deleteVertex_isPosDef hPD v)
    -- Classify the extension: leaf v connects to exactly one vertex u
    -- with Coxeter weight 1, 2, or 3. The extension determines the full type.
    exact extend_dynkin_type hGCM hSym hPD hConn v hleaf t' ht'
termination_by n

end BLD.Lie.Cartan
