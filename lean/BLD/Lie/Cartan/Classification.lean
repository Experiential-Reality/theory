/- BLD Calculus — Cartan Classification: Main Theorem

   The extend_dynkin_type theorem (combinatorial heart) and
   the cartan_classification theorem (main result).
-/

import BLD.Lie.Cartan.F4

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

set_option maxHeartbeats 1600000 in
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
    subst hrank -- k = n + 2
    obtain ⟨e', he'⟩ := ht'
    have hsub : ∀ i j : Fin (n+2), A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.B (n+2) (e' i) (e' j) := fun i j => (he' i j).symm
    have hAv0 : ∀ m : Fin (n+2), m ≠ u_idx → A v (v.succAbove m) = 0 := by
      intro m hm; by_contra h
      exact hm (Fin.succAbove_right_injective (hu_idx ▸ huniq _ (Fin.succAbove_ne v m) h))
    have hAv0' : ∀ m : Fin (n+2), m ≠ u_idx → A (v.succAbove m) v = 0 := by
      intro m hm
      exact (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v m))).mp (hAv0 m hm)
    by_cases h0 : e' u_idx = 0
    · -- Attachment at vertex 0 (simply-laced end), weight must be 1
      by_cases hw1 : A v u * A u v = 1
      · -- Weight 1 → B_{k+1} = B_{n+3}
        have hAvu_eq : A v u = -1 := by nlinarith
        have hAuv_eq : A u v = -1 := by nlinarith
        refine ⟨DynkinType.B (n+3) (by omega), ?_⟩
        simp only [DynkinType.cartanMatrix]
        exact extend_at_zero hGCM v e' (CartanMatrix.B (n+3))
          (by simp [CartanMatrix.B])
          (fun i j => by rw [B_succ_eq_B]; exact (hsub i j).symm)
          (fun m => by
            rw [B_first_row (n+2) (by omega)]
            split_ifs with h
            · have : e' m = e' u_idx := (Fin.ext h).trans h0.symm
              rw [show m = u_idx from e'.injective this, hu_idx, hAvu_eq]
            · rw [hAv0 m (fun heq => h (show (e' m).val = 0 from
                heq ▸ (congrArg Fin.val h0)))])
          (fun m => by
            rw [B_first_col (n+2) (by omega)]
            split_ifs with h
            · have : e' m = e' u_idx := (Fin.ext h).trans h0.symm
              rw [show m = u_idx from e'.injective this, hu_idx, hAuv_eq]
            · rw [hAv0' m (fun heq => h (show (e' m).val = 0 from
                heq ▸ (congrArg Fin.val h0)))])
      · -- Weight 2 at vertex 0 → contradiction
        exfalso
        have hcw2 : A v u * A u v = 2 := by omega
        -- Null vector: x(v) = -A(v,u), x(sub_m) = B_marks(e'(m))
        -- B·marks = (2,0,...,0) where marks = [2,...,2,1]
        apply absurd hPD (not_posDef_of_int_null hSym
          (fun i => if h : ∃ m, v.succAbove m = i then B_marks (n+2) (e' h.choose) else -A v u)
          (by intro h; have := congr_fun h v
              simp only [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k)),
                Pi.zero_apply] at this; omega)
          _)
        have hx_v : (fun i => if h : ∃ m, v.succAbove m = i then B_marks (n+2) (e' h.choose)
            else -A v u) v = -A v u := dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))
        have hx_sub : ∀ m, (fun i => if h : ∃ m, v.succAbove m = i then B_marks (n+2) (e' h.choose)
            else -A v u) (v.succAbove m) = B_marks (n+2) (e' m) := by
          intro m
          have hex : ∃ m', v.succAbove m' = v.succAbove m := ⟨m, rfl⟩
          simp only [dif_pos hex]
          exact congr_arg _ (congr_arg e' (Fin.succAbove_right_injective hex.choose_spec))
        ext i; simp only [mulVec, dotProduct, Pi.zero_apply]
        rw [Fin.sum_univ_succAbove _ v]
        simp only [hx_v, hx_sub]
        rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨m, hi⟩
        · -- Row v: 2*(-Avu) + ∑_m A(v,sAm)*marks(e'm) = 0
          rw [hi, hGCM.diag v]
          rw [show ∑ k, A v (v.succAbove k) * B_marks (n+2) (e' k) = A v u * B_marks (n+2) (e' u_idx)
            from Fintype.sum_eq_single u_idx (fun m hm => by
              rw [show A v (v.succAbove m) = 0 from by
                by_contra h; exact hm (Fin.succAbove_right_injective
                  (hu_idx ▸ huniq _ (Fin.succAbove_ne v m) h))]; ring) |>.trans (by rw [hu_idx])]
          rw [h0]; show 2 * -A v u + A v u * B_marks (n + 2) ⟨0, by omega⟩ = 0
          have : B_marks (n+2) ⟨0, by omega⟩ = 2 := by
            simp only [B_marks, show (⟨0, by omega⟩ : Fin (n+2)).val = 0 from rfl]
            split_ifs <;> omega
          rw [this]; ring
        · -- Row v.succAbove m
          rw [hi]
          -- Reindex: ∑_l A(sAm,sAl)*marks(e'l) = ∑_p B(e'm,p)*marks(p)
          have hsub_reindex : ∑ l, A (v.succAbove m) (v.succAbove l) * B_marks (n+2) (e' l) =
              ∑ p, CartanMatrix.B (n+2) (e' m) p * B_marks (n+2) p := by
            simp_rw [fun l => show A (v.succAbove m) (v.succAbove l) =
                CartanMatrix.B (n+2) (e' m) (e' l) from hsub m l]
            exact Equiv.sum_comp e' (fun p => CartanMatrix.B (n+2) (e' m) p * B_marks (n+2) p)
          rw [hsub_reindex, B_mulVec_marks (n+2) (by omega)]
          by_cases hm : m = u_idx
          · rw [hm, show (e' u_idx).val = 0 from congrArg Fin.val h0, if_pos rfl,
              hu_idx]; linarith
          · rw [if_neg (show (e' m).val ≠ 0 from fun h =>
              hm (e'.injective (Fin.ext (h ▸ (congrArg Fin.val h0).symm))))]
            rw [show A (v.succAbove m) v = 0 from hAv0' m hm]; ring
    · -- Attachment at vertex ≠ 0
      have hp_pos : 0 < (e' u_idx).val := Nat.pos_of_ne_zero (fun h => h0 (Fin.ext h))
      by_cases hw1 : A v u * A u v = 1
      · -- Weight 1
        have hAvu_eq : A v u = -1 := by nlinarith
        have hAuv_eq : A u v = -1 := by nlinarith
        by_cases hpk1 : (e' u_idx).val + 1 = n + 2
        · -- p = k-1 (short root endpoint)
          by_cases hn2 : 2 ≤ n
          · -- k ≥ 4 → contradiction via 5-vertex null subgraph
            exfalso
            have hu_val : (e' u_idx).val = n + 1 := by omega
            -- Define 3 new vertices: wl (=n), wl2 (=n-1), wl3 (=n-2) in B_{n+2}
            set wl_pos : Fin (n+2) := ⟨n, by omega⟩ with wl_pos_def
            set wl_idx := e'.symm wl_pos with wl_idx_def
            have he'wl : e' wl_idx = wl_pos := e'.apply_symm_apply wl_pos
            have hwl_ne_u_idx : wl_idx ≠ u_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl, wl_pos_def, Fin.ext_iff, Fin.val_mk] at h1; omega
            set wl := v.succAbove wl_idx with wl_def
            have hwl_ne_v : wl ≠ v := Fin.succAbove_ne v wl_idx
            have hwl_ne_u : wl ≠ u := fun h => hwl_ne_u_idx
              (Fin.succAbove_right_injective (hu_idx ▸ h))
            set wl2_pos : Fin (n+2) := ⟨n-1, by omega⟩ with wl2_pos_def
            set wl2_idx := e'.symm wl2_pos with wl2_idx_def
            have he'wl2 : e' wl2_idx = wl2_pos := e'.apply_symm_apply wl2_pos
            have hwl2_ne_u_idx : wl2_idx ≠ u_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl2, wl2_pos_def, Fin.ext_iff, Fin.val_mk] at h1; omega
            have hwl2_ne_wl_idx : wl2_idx ≠ wl_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl2, he'wl, wl2_pos_def, wl_pos_def,
                Fin.ext_iff, Fin.val_mk] at h1; omega
            set wl2 := v.succAbove wl2_idx with wl2_def
            have hwl2_ne_v : wl2 ≠ v := Fin.succAbove_ne v wl2_idx
            have hwl2_ne_u : wl2 ≠ u := fun h => hwl2_ne_u_idx
              (Fin.succAbove_right_injective (hu_idx ▸ h))
            have hwl2_ne_wl : wl2 ≠ wl := fun h => hwl2_ne_wl_idx
              (Fin.succAbove_right_injective h)
            set wl3_pos : Fin (n+2) := ⟨n-2, by omega⟩ with wl3_pos_def
            set wl3_idx := e'.symm wl3_pos with wl3_idx_def
            have he'wl3 : e' wl3_idx = wl3_pos := e'.apply_symm_apply wl3_pos
            have hwl3_ne_u_idx : wl3_idx ≠ u_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl3, wl3_pos_def, Fin.ext_iff, Fin.val_mk] at h1; omega
            have hwl3_ne_wl_idx : wl3_idx ≠ wl_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl3, he'wl, wl3_pos_def, wl_pos_def,
                Fin.ext_iff, Fin.val_mk] at h1; omega
            have hwl3_ne_wl2_idx : wl3_idx ≠ wl2_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl3, he'wl2, wl3_pos_def, wl2_pos_def,
                Fin.ext_iff, Fin.val_mk] at h1; omega
            set wl3 := v.succAbove wl3_idx with wl3_def
            have hwl3_ne_v : wl3 ≠ v := Fin.succAbove_ne v wl3_idx
            have hwl3_ne_u : wl3 ≠ u := fun h => hwl3_ne_u_idx
              (Fin.succAbove_right_injective (hu_idx ▸ h))
            have hwl3_ne_wl : wl3 ≠ wl := fun h => hwl3_ne_wl_idx
              (Fin.succAbove_right_injective h)
            have hwl3_ne_wl2 : wl3 ≠ wl2 := fun h => hwl3_ne_wl2_idx
              (Fin.succAbove_right_injective h)
            -- A-entries: v row/col
            have hAv_wl : A v wl = 0 := hAv0 wl_idx hwl_ne_u_idx
            have hAv_wl2 : A v wl2 = 0 := hAv0 wl2_idx hwl2_ne_u_idx
            have hAv_wl3 : A v wl3 = 0 := hAv0 wl3_idx hwl3_ne_u_idx
            -- A-entries: B submatrix (using hsub + simp [CartanMatrix.B])
            have hAu_wl : A u wl = -1 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove wl_idx) = -1
              rw [hsub, he'wl]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, wl_pos_def]
              split_ifs <;> omega
            have hAwl_u : A wl u = -2 := by
              rw [← hu_idx]; show A (v.succAbove wl_idx) (v.succAbove u_idx) = -2
              rw [hsub, he'wl]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, wl_pos_def]
              split_ifs <;> omega
            have hAwl_wl2 : A wl wl2 = -1 := by
              show A (v.succAbove wl_idx) (v.succAbove wl2_idx) = -1
              rw [hsub, he'wl, he'wl2]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl_pos_def, wl2_pos_def]; split_ifs <;> omega
            have hAwl2_wl : A wl2 wl = -1 := by
              show A (v.succAbove wl2_idx) (v.succAbove wl_idx) = -1
              rw [hsub, he'wl2, he'wl]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl2_pos_def, wl_pos_def]; split_ifs <;> omega
            have hAwl2_wl3 : A wl2 wl3 = -1 := by
              show A (v.succAbove wl2_idx) (v.succAbove wl3_idx) = -1
              rw [hsub, he'wl2, he'wl3]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl2_pos_def, wl3_pos_def]; split_ifs <;> omega
            have hAwl3_wl2 : A wl3 wl2 = -1 := by
              show A (v.succAbove wl3_idx) (v.succAbove wl2_idx) = -1
              rw [hsub, he'wl3, he'wl2]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl3_pos_def, wl2_pos_def]; split_ifs <;> omega
            -- Null vector x: {v↦1, u↦2, wl↦3, wl2↦2, wl3↦1}
            set x : Fin (n+3) → ℚ := fun i =>
              if i = v then 1 else if i = u then 2 else if i = wl then 3
              else if i = wl2 then 2 else if i = wl3 then 1 else 0
            have hx : x ≠ 0 := by
              intro h; have := congr_fun h v
              simp only [x, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
            have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ wl → k ≠ wl2 → k ≠ wl3 → x k = 0 :=
              fun k h1 h2 h3 h4 h5 => by simp [x, h1, h2, h3, h4, h5]
            -- Zero A-entries (named with vertex names for simp compatibility)
            have hAwl_v : A wl v = 0 := hAv0' wl_idx hwl_ne_u_idx
            have hAwl2_v : A wl2 v = 0 := hAv0' wl2_idx hwl2_ne_u_idx
            have hAwl3_v : A wl3 v = 0 := hAv0' wl3_idx hwl3_ne_u_idx
            have hAu_wl2 : A u wl2 = 0 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove wl2_idx) = 0
              rw [hsub, he'wl2]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl2_pos_def]; split_ifs <;> omega
            have hAu_wl3 : A u wl3 = 0 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove wl3_idx) = 0
              rw [hsub, he'wl3]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl3_pos_def]; split_ifs <;> omega
            have hAwl_wl3 : A wl wl3 = 0 := by
              show A (v.succAbove wl_idx) (v.succAbove wl3_idx) = 0
              rw [hsub, he'wl, he'wl3]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl_pos_def, wl3_pos_def]; split_ifs <;> omega
            have hAwl3_u : A wl3 u = 0 := by
              rw [← hu_idx]; show A (v.succAbove wl3_idx) (v.succAbove u_idx) = 0
              rw [hsub, he'wl3]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl3_pos_def]; split_ifs <;> omega
            have hAwl3_wl : A wl3 wl = 0 := by
              show A (v.succAbove wl3_idx) (v.succAbove wl_idx) = 0
              rw [hsub, he'wl3, he'wl]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl3_pos_def, wl_pos_def]; split_ifs <;> omega
            have hAwl2_u : A wl2 u = 0 := by
              rw [← hu_idx]; show A (v.succAbove wl2_idx) (v.succAbove u_idx) = 0
              rw [hsub, he'wl2]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl2_pos_def]; split_ifs <;> omega
            -- Inner products (each row of A·x restricted to support)
            -- Row v (leaf): only connects to u
            have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
              rw [sum_two huv.symm (fun m => (↑(A v m) : ℚ) * x m)
                (fun m h1 h2 => by
                  have : A v m = 0 := by
                    obtain ⟨m_idx, hm_eq⟩ := Fin.exists_succAbove_eq h1
                    rw [← hm_eq]
                    exact hAv0 m_idx (fun h => h2 (by rw [← hm_eq, h, hu_idx]))
                  simp [this])]
              simp only [x, ↓reduceIte, if_neg huv, hGCM.diag v, hAvu_eq]
              push_cast; ring
            -- Row u: connects to v and wl (= vertex n)
            have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
              rw [sum_three huv.symm hwl_ne_v.symm hwl_ne_u.symm
                (fun m => (↑(A u m) : ℚ) * x m)
                (fun m h1 h2 h3 => by
                  by_cases hm4 : m = wl2; · simp [hm4, hAu_wl2]
                  by_cases hm5 : m = wl3; · simp [hm5, hAu_wl3]
                  simp [x0 m h1 h2 h3 hm4 hm5])]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
                hGCM.diag u, hAuv_eq, hAu_wl]; push_cast; ring
            -- Row wl (= vertex n): connects to u and wl2
            have inner_wl : ∑ j, (↑(A wl j) : ℚ) * x j = 0 := by
              rw [sum_three (hwl_ne_u.symm) (hwl2_ne_u.symm) (hwl2_ne_wl.symm)
                (fun m => (↑(A wl m) : ℚ) * x m)
                (fun m h1 h2 h3 => by
                  by_cases hm1 : m = v
                  · subst hm1; simp [hAwl_v]
                  by_cases hm5 : m = wl3
                  · subst hm5; simp [hAwl_wl3]
                  simp [x0 m hm1 h1 h2 h3 hm5])]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_u, if_neg hwl_ne_v,
                if_neg hwl2_ne_u, if_neg hwl2_ne_wl, if_neg hwl2_ne_v,
                hGCM.diag wl, hAwl_u, hAwl_wl2]; push_cast; ring
            -- Row wl2 (= vertex n-1): connects to wl and wl3
            have inner_wl2 : ∑ j, (↑(A wl2 j) : ℚ) * x j = 0 := by
              rw [sum_three (hwl2_ne_wl.symm) (hwl3_ne_wl.symm) (hwl3_ne_wl2.symm)
                (fun m => (↑(A wl2 m) : ℚ) * x m)
                (fun m h1 h2 h3 => by
                  by_cases hm1 : m = v
                  · subst hm1; simp [hAwl2_v]
                  by_cases hm2 : m = u
                  · subst hm2; simp [hAwl2_u]
                  simp [x0 m hm1 hm2 h1 h2 h3])]
              simp only [x, ↓reduceIte, if_neg hwl2_ne_wl, if_neg hwl_ne_v, if_neg hwl_ne_u,
                if_neg hwl3_ne_wl, if_neg hwl3_ne_wl2, if_neg hwl3_ne_v, if_neg hwl3_ne_u,
                if_neg hwl2_ne_v, if_neg hwl2_ne_u,
                hGCM.diag wl2, hAwl2_wl, hAwl2_wl3]; push_cast; ring
            -- Row wl3 (= vertex n-2): connects to wl2
            have inner_wl3 : ∑ j, (↑(A wl3 j) : ℚ) * x j = 0 := by
              rw [sum_two (hwl3_ne_wl2.symm)
                (fun m => (↑(A wl3 m) : ℚ) * x m)
                (fun m h1 h2 => by
                  by_cases hm1 : m = v
                  · subst hm1; simp [hAwl3_v]
                  by_cases hm2 : m = u
                  · subst hm2; simp [hAwl3_u]
                  by_cases hm3 : m = wl
                  · subst hm3; simp [hAwl3_wl]
                  simp [x0 m hm1 hm2 hm3 h1 h2])]
              simp only [x, ↓reduceIte, if_neg hwl2_ne_v, if_neg hwl2_ne_u,
                if_neg hwl2_ne_wl, if_neg hwl3_ne_v, if_neg hwl3_ne_u,
                if_neg hwl3_ne_wl, if_neg hwl3_ne_wl2,
                hGCM.diag wl3, hAwl3_wl2]; push_cast; ring
            -- Conclude
            have hq : qform hSym.d A x = 0 := by
              rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
              by_cases hiv : i = v; · subst hiv; simp [inner_v]
              by_cases hiu : i = u; · subst hiu; simp [inner_u]
              by_cases hiw : i = wl; · subst hiw; simp [inner_wl]
              by_cases hiw2 : i = wl2; · subst hiw2; simp [inner_wl2]
              by_cases hiw3 : i = wl3; · subst hiw3; simp [inner_wl3]
              simp [x0 i hiv hiu hiw hiw2 hiw3]
            exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
          · -- k ≤ 3: constructive
            push_neg at hn2
            rcases Nat.eq_zero_or_pos n with rfl | hn_pos
            · -- n = 0, k = 2 → C₃
              refine ⟨DynkinType.C 3 (by omega), ?_⟩
              simp only [DynkinType.cartanMatrix]
              have he'u_val : (e' u_idx).val = 1 := by have h := hpk1; omega
              have swap_zero_iff : ∀ x : Fin 2,
                  (Equiv.swap (0 : Fin 2) 1 x).val = 0 ↔ x.val = 1 := by decide
              exact extend_at_zero hGCM v (e'.trans (Equiv.swap (0 : Fin 2) 1)) (CartanMatrix.C 3)
                (by decide)
                (fun i j => by
                  simp only [Equiv.trans_apply, C_succ_eq_C]
                  have key : ∀ a b : Fin 2,
                      CartanMatrix.C 2 (Equiv.swap (0 : Fin 2) 1 a)
                        (Equiv.swap (0 : Fin 2) 1 b) =
                      CartanMatrix.B 2 a b := by decide
                  rw [key]; exact (hsub i j).symm)
                (fun m => by
                  simp only [Equiv.trans_apply, C_first_row 2 (by omega)]
                  split_ifs with h
                  · have hm_eq : m = u_idx := by
                      apply e'.injective; ext
                      exact ((swap_zero_iff _).mp h).trans he'u_val.symm
                    rw [hm_eq, hu_idx, hAvu_eq]
                  · have hm_ne : m ≠ u_idx := by
                      intro heq; subst heq
                      exact h ((swap_zero_iff _).mpr he'u_val)
                    rw [hAv0 m hm_ne])
                (fun m => by
                  simp only [Equiv.trans_apply, C_first_col 2 (by omega)]
                  split_ifs with h
                  · have hm_eq : m = u_idx := by
                      apply e'.injective; ext
                      exact ((swap_zero_iff _).mp h).trans he'u_val.symm
                    rw [hm_eq, hu_idx, hAuv_eq]
                  · have hm_ne : m ≠ u_idx := by
                      intro heq; subst heq
                      exact h ((swap_zero_iff _).mpr he'u_val)
                    rw [hAv0' m hm_ne])
            · -- n ≥ 1, and n < 2, so n = 1
              have hn1 : n = 1 := by omega
              subst hn1
              -- n = 1, k = 3 → F₄
              refine ⟨DynkinType.F₄, ?_⟩
              simp only [DynkinType.cartanMatrix]
              have he'u_val : (e' u_idx).val = 2 := by have h := hpk1; omega
              exact extend_at_last hGCM v e' CartanMatrix.F₄
                (by decide)
                (fun i j => by
                  have key : ∀ a b : Fin 3,
                      CartanMatrix.F₄ (Fin.castSucc a) (Fin.castSucc b) =
                      CartanMatrix.B 3 a b := by decide
                  rw [key]; exact (hsub i j).symm)
                (fun m => by
                  have hF_lr : ∀ j : Fin 3,
                      CartanMatrix.F₄ (Fin.last 3) (Fin.castSucc j) =
                      if j.val = 2 then -1 else 0 := by decide
                  rw [hF_lr]
                  split_ifs with h
                  · have hm_eq : m = u_idx :=
                      e'.injective (Fin.ext (h.trans he'u_val.symm))
                    rw [hm_eq, hu_idx, hAvu_eq]
                  · have hm_ne : m ≠ u_idx := by
                      intro heq; subst heq; exact h he'u_val
                    rw [hAv0 m hm_ne])
                (fun m => by
                  have hF_lc : ∀ j : Fin 3,
                      CartanMatrix.F₄ (Fin.castSucc j) (Fin.last 3) =
                      if j.val = 2 then -1 else 0 := by decide
                  rw [hF_lc]
                  split_ifs with h
                  · have hm_eq : m = u_idx :=
                      e'.injective (Fin.ext (h.trans he'u_val.symm))
                    rw [hm_eq, hu_idx, hAuv_eq]
                  · have hm_ne : m ≠ u_idx := by
                      intro heq; subst heq; exact h he'u_val
                    rw [hAv0' m hm_ne])
        · -- 1 ≤ p ≤ k-2 (interior) → contradiction via subgraph null vector
          exfalso
          push_neg at hpk1
          have hp_le : (e' u_idx).val ≤ n := by omega
          set p_val := (e' u_idx).val with p_val_def
          set rr := n + 2 - p_val with rr_def
          have hrr_ge : 2 ≤ rr := by omega
          -- Define support vector on B_{n+2}:
          --   fB(j) = 1 if j=p-1, B_marks(rr,j-p) if p≤j, 0 otherwise
          let fB : Fin (n+2) → ℤ := fun j =>
            if j.val + 1 = p_val then 1
            else if p_val ≤ j.val then B_marks rr ⟨j.val - p_val, by omega⟩
            else 0
          -- Full vector on Fin(n+3): x(v)=1, x(v.succAbove m)=fB(e' m)
          let x : Fin (n+3) → ℚ := fun i =>
            if h : ∃ m, v.succAbove m = i then ↑(fB (e' h.choose)) else 1
          have hx_v : x v = 1 := by
            simp only [x, dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
          have hx_sub : ∀ m, x (v.succAbove m) = ↑(fB (e' m)) := by
            intro m
            have hex : ∃ m', v.succAbove m' = v.succAbove m := ⟨m, rfl⟩
            simp only [x, dif_pos hex]
            exact congr_arg (fun z => (↑(fB (e' z)) : ℚ))
              (Fin.succAbove_right_injective hex.choose_spec)
          have hx_ne : x ≠ 0 := by
            intro h; have := congr_fun h v
            simp only [hx_v, Pi.zero_apply] at this; linarith
          -- fB values at key positions
          have hfB_u : fB (e' u_idx) = B_marks rr ⟨0, by omega⟩ := by
            simp only [fB, p_val_def]
            rw [if_neg (by omega), if_pos (le_refl _)]
            congr 1; ext; simp [Nat.sub_self]
          have hfB_marks : ∀ q : Fin (n+2), p_val ≤ q.val →
              fB q = B_marks rr ⟨q.val - p_val, by omega⟩ := by
            intro q hq; simp only [fB]; rw [if_neg (by omega), if_pos hq]
          have hfB_zero : ∀ q : Fin (n+2), q.val + 1 < p_val → q.val ≠ p_val - 1 → fB q = 0 := by
            intro q h1 h2; simp only [fB]; rw [if_neg (by omega), if_neg (by omega)]
          have hBm0 : B_marks rr ⟨0, by omega⟩ = 2 := by
            simp only [B_marks]; split_ifs <;> omega
          -- B-path sum helper: for row at B-position i_off+p in B_{n+2},
          -- ∑_q B(i_off+p, q) * fB(q) = (B_mulVec_marks shifted) + (left neighbor contribution)
          -- Specifically: = (if i_off=0 then 2 else 0) + (if i_off=0 then -1 else 0)
          -- because fB(p-1) = 1 and B(p, p-1) = -1 (only row 0 of the shifted path sees left)
          have hBpath_sum : ∀ i_off : Fin rr,
              ∑ q : Fin (n+2), (↑(CartanMatrix.B (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) * ↑(fB q) =
              (if i_off.val = 0 then (2 : ℚ) else 0) +
              (if i_off.val = 0 then (-1 : ℚ) else 0) := by
            intro i_off
            -- Decompose each term: B(row,q)*fB(q) = shifted_part(q) + left_part(q)
            have hterm : ∀ q : Fin (n+2),
                (↑(CartanMatrix.B (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) * ↑(fB q) =
                (if h : p_val ≤ q.val then
                  (↑(CartanMatrix.B rr i_off ⟨q.val - p_val, by omega⟩) : ℚ) *
                  ↑(B_marks rr ⟨q.val - p_val, by omega⟩)
                else 0) +
                (if q.val + 1 = p_val then
                  (if i_off.val = 0 then (-1 : ℚ) else 0)
                else 0) := by
              intro q
              by_cases hqp : p_val ≤ q.val
              · -- q ≥ p: B_shift + fB = B_marks
                rw [dif_pos hqp, if_neg (by omega)]
                simp only [add_zero]
                have hq_eq : q = ⟨(q.val - p_val) + p_val, by omega⟩ :=
                  Fin.ext (Nat.sub_add_cancel hqp).symm
                congr 1
                · conv_lhs => rw [hq_eq]
                  exact_mod_cast B_shift (n+2) p_val (by omega) i_off ⟨q.val - p_val, by omega⟩
                · exact_mod_cast hfB_marks q hqp
              · push_neg at hqp
                rw [dif_neg (by omega)]
                simp only [zero_add]
                by_cases hq1 : q.val + 1 = p_val
                · -- q = p-1 (left neighbor)
                  rw [if_pos hq1]
                  have hfq : fB q = 1 := by simp only [fB]; rw [if_pos hq1]
                  rw [hfq]; push_cast; simp only [mul_one]
                  -- B(i_off+p, p-1) = if i_off=0 then -1 else 0
                  have hBval : CartanMatrix.B (n+2) ⟨i_off.val + p_val, by omega⟩ q =
                      if i_off.val = 0 then -1 else 0 := by
                    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
                    have := q.isLt; have := i_off.isLt; split_ifs <;> omega
                  rw [hBval]; split_ifs <;> simp
                · -- q < p-1: fB(q) = 0
                  rw [if_neg hq1]
                  have hfq : fB q = 0 := by
                    simp only [fB]; rw [if_neg (by omega), if_neg (by omega)]
                  rw [hfq]; simp
            -- Sum both sides
            simp_rw [hterm]
            rw [Finset.sum_add_distrib]
            congr 1
            · -- Shifted part: ∑_q (if p ≤ q then B_rr*marks else 0) = if i_off=0 then 2 else 0
              trans ∑ j : Fin rr, (↑(CartanMatrix.B rr i_off j) : ℚ) * ↑(B_marks rr j)
              · exact sum_shift (by omega : p_val ≤ n + 2)
                  (fun j => (↑(CartanMatrix.B rr i_off j) : ℚ) * ↑(B_marks rr j))
              · have := B_mulVec_marks rr hrr_ge i_off
                push_cast at this ⊢; exact_mod_cast this
            · -- Left neighbor: single nonzero term at q = ⟨p-1, _⟩
              rw [Fintype.sum_eq_single ⟨p_val - 1, by omega⟩ (fun q hq => by
                rw [if_neg (fun h => hq (Fin.ext (by simp at h ⊢; omega)))])]
              simp only [Fin.val_mk]
              rw [if_pos (by omega)]
          -- qform = 0 via qform_zero_of_null
          have hq : qform hSym.d A x = 0 := by
            apply qform_zero_of_null
            intro k
            rcases Fin.eq_self_or_eq_succAbove v k with hkv | ⟨m, hkm⟩
            · -- Row v: inner product = 2 + (-1)*2 = 0
              right; rw [hkv]
              rw [Fin.sum_univ_succAbove _ v]
              simp only [hx_v, hx_sub, hGCM.diag v]
              rw [Fintype.sum_eq_single u_idx (fun m' hm' => by
                rw [show A v (v.succAbove m') = 0 from hAv0 m' (fun heq => hm' heq)]; ring)]
              rw [hu_idx, hAvu_eq, hfB_u, hBm0]; push_cast; ring
            · -- Row v.succAbove m
              rw [hkm, hx_sub m]
              by_cases hfm : fB (e' m) = 0
              · left; simp [hfm]
              · right; rw [Fin.sum_univ_succAbove _ v]
                simp only [hx_v, hx_sub, hGCM.diag (v.succAbove m)]
                -- Reindex the sum
                have hsub_reindex : ∑ l, (↑(A (v.succAbove m) (v.succAbove l)) : ℚ) * ↑(fB (e' l)) =
                    ∑ q, (↑(CartanMatrix.B (n+2) (e' m) q) : ℚ) * ↑(fB q) := by
                  simp_rw [fun l => show A (v.succAbove m) (v.succAbove l) =
                      CartanMatrix.B (n+2) (e' m) (e' l) from hsub m l]
                  push_cast
                  exact Equiv.sum_comp e' (fun q => (↑(CartanMatrix.B (n+2) (e' m) q) : ℚ) * ↑(fB q))
                rw [hsub_reindex]
                -- fB(e' m) ≠ 0 → (e' m).val = p-1 or (e' m).val ≥ p
                -- Show: 2*fB(e'm) + A(sAm,v) + ∑_q B(e'm,q)*fB(q) = 0
                -- equivalently: fB(e'm) * (2*fB(e'm) + A(sAm,v) + ∑_q) = 0
                -- We need: inner product = 0
                have hpos : (e' m).val + 1 = p_val ∨ p_val ≤ (e' m).val := by
                  simp only [fB] at hfm; split_ifs at hfm <;> [left; right; exact absurd rfl hfm] <;> omega
                rcases hpos with hpm1 | hpm
                · -- (e' m).val = p-1: the left neighbor row
                  have hm_ne_u : m ≠ u_idx := by
                    intro heq; rw [heq] at hpm1; omega
                  have hAmv : A (v.succAbove m) v = 0 := hAv0' m hm_ne_u
                  rw [hAmv]; push_cast; simp only [zero_mul, zero_add]
                  -- Goal: ∑_q B(p-1, q) * fB(q) = 0
                  -- Two nonzero terms: q=⟨p-1,_⟩ (B=2, fB=1) and q=⟨p,_⟩ (B=-1, fB=2)
                  set q1 : Fin (n+2) := ⟨p_val - 1, by omega⟩
                  set q2 : Fin (n+2) := ⟨p_val, by omega⟩
                  have hq12 : q1 ≠ q2 := by intro h; simp [q1, q2, Fin.ext_iff] at h; omega
                  rw [sum_two hq12
                    (fun q => (↑(CartanMatrix.B (n+2) (e' m) q) : ℚ) * ↑(fB q))
                    (fun q hq1' hq2' => by
                      have hBq : CartanMatrix.B (n+2) (e' m) q = 0 ∨ fB q = 0 := by
                        by_cases hqp : q.val + 1 = p_val
                        · -- q would be q1, contradiction
                          exact absurd (Fin.ext (by simp [q1]; omega)) hq1'
                        · by_cases hqp2 : p_val ≤ q.val
                          · -- q ≥ p, q ≠ q2: B(p-1, q) = 0 since q > p
                            left
                            have hq_ne : q.val ≠ p_val := fun h =>
                              hq2' (Fin.ext (by simp [q2]; exact h))
                            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
                            have := q.isLt; split_ifs <;> omega
                          · -- q < p-1: fB(q) = 0
                            right; show fB q = 0
                            simp only [fB]; rw [if_neg (by omega), if_neg (by omega)]
                      rcases hBq with h | h <;> simp [h])]
                  -- Now: B(p-1,p-1)*fB(p-1) + B(p-1,p)*fB(p)
                  -- = 2*1 + (-1)*2 = 0
                  have hBq1 : CartanMatrix.B (n+2) (e' m) q1 = 2 := by
                    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, q1]
                    have := hpm1; split_ifs <;> omega
                  have hBq2 : CartanMatrix.B (n+2) (e' m) q2 = -1 := by
                    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, q2]
                    have := hpm1; split_ifs <;> omega
                  have hfq1 : fB q1 = 1 := by
                    simp only [fB, q1]; rw [if_pos (by omega)]
                  have hfq2 : fB q2 = B_marks rr ⟨0, by omega⟩ := by
                    simp only [fB, q2]; rw [if_neg (by omega), if_pos (le_refl _)]
                    congr 1; ext; simp [Nat.sub_self]
                  rw [hBq1, hBq2, hfq1, hfq2, hBm0]; push_cast; ring
                · -- (e' m).val ≥ p: B sub-path vertex
                  set i_off : Fin rr := ⟨(e' m).val - p_val, by omega⟩
                  have hAmv : A (v.succAbove m) v =
                      if (e' m).val = p_val then -1 else 0 := by
                    by_cases he : (e' m).val = p_val
                    · rw [if_pos he]
                      have : m = u_idx := e'.injective (Fin.ext (he ▸ p_val_def.symm))
                      rw [this, hu_idx]; exact hAuv_eq
                    · rw [if_neg he]
                      exact hAv0' m (fun heq =>
                        he ((congr_arg (fun x => (e' x).val) heq).trans p_val_def.symm))
                  rw [hAmv]
                  have he'm_eq : e' m = ⟨i_off.val + p_val, by omega⟩ := by
                    ext; simp [i_off]; omega
                  rw [show ∑ q, (↑(CartanMatrix.B (n+2) (e' m) q) : ℚ) * ↑(fB q) =
                      ∑ q, (↑(CartanMatrix.B (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) * ↑(fB q)
                    from by rw [he'm_eq]]
                  rw [hBpath_sum i_off]
                  -- Goal is now purely arithmetic with if-then-else on i_off.val = 0 and (e' m).val = p_val
                  by_cases hi0 : i_off.val = 0
                  · -- i_off = 0, so (e' m) = p, row = u
                    have : (e' m).val = p_val := by simp [i_off, Fin.ext_iff] at hi0; omega
                    simp [hi0, this]; push_cast; ring
                  · -- i_off ≥ 1, row is interior B vertex
                    have : (e' m).val ≠ p_val := by
                      simp [i_off, Fin.ext_iff] at hi0; omega
                    simp [hi0, this]
          exact absurd hPD (not_posDef_of_nonpos hSym x hx_ne (le_of_eq hq))
      · -- Weight 2 → contradiction for all subcases
        exfalso
        have hcw2 : A v u * A u v = 2 := by omega
        -- Left neighbor at position p-1 (always exists since p ≥ 1)
        set left_pos : Fin (n+2) := ⟨(e' u_idx).val - 1, by omega⟩ with left_pos_def
        set left_idx := e'.symm left_pos with left_idx_def
        have hleft_ne : left_idx ≠ u_idx := by
          intro h; have h1 := congr_arg e' h; simp only [left_idx_def, e'.apply_symm_apply] at h1
          exact absurd (congr_arg Fin.val h1) (by simp [left_pos_def]; omega)
        set wl := v.succAbove left_idx with wl_def
        have hwl_ne_v : wl ≠ v := Fin.succAbove_ne v left_idx
        have hwl_ne_u : wl ≠ u := fun h => hleft_ne
          (Fin.succAbove_right_injective (hu_idx ▸ h))
        have hAvl : A v wl = 0 := hAv0 left_idx hleft_ne
        have hAlv : A wl v = 0 := hAv0' left_idx hleft_ne
        have he'l : e' left_idx = left_pos := e'.apply_symm_apply left_pos
        have hAul : A u wl = -1 := by
          rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove left_idx) = -1
          rw [hsub, he'l]
          simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, left_pos_def]
          split_ifs <;> omega
        by_cases hpn1 : (e' u_idx).val + 1 = n + 2
        · -- p = n+1 (short root): 3-vertex {v, u, wl}, null vec [-Avu, 2, 2]
          have hAlu : A wl u = -2 := by
            rw [← hu_idx]; show A (v.succAbove left_idx) (v.succAbove u_idx) = -2
            rw [hsub, he'l]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, left_pos_def]
            split_ifs <;> omega
          -- 3-vertex null test via qform: x(v) = -Avu, x(u) = 2, x(wl) = 2
          set x : Fin (n+3) → ℚ := fun i =>
            if i = v then -(↑(A v u : ℤ) : ℚ)
            else if i = u then 2
            else if i = wl then 2
            else 0
          have hx : x ≠ 0 := by
            intro h; have := congr_fun h u
            simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
          have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ wl → x k = 0 :=
            fun k h1 h2 h3 => by simp [x, h1, h2, h3]
          have hrest : ∀ (r : Fin (n+3) → ℚ) (m : Fin (n+3)),
              m ≠ v → m ≠ u → m ≠ wl → r m * x m = 0 := by
            intro r m h1 h2 h3; simp [x0 m h1 h2 h3]
          have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
            rw [sum_three huv.symm hwl_ne_v.symm hwl_ne_u.symm
              (fun m => (↑(A v m) : ℚ) * x m)
              (fun m h1 h2 h3 => hrest (fun j => ↑(A v j)) m h1 h2 h3)]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
              hGCM.diag v, hAvl]; push_cast; ring
          have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
            rw [sum_three huv.symm hwl_ne_v.symm hwl_ne_u.symm
              (fun m => (↑(A u m) : ℚ) * x m)
              (fun m h1 h2 h3 => hrest (fun j => ↑(A u j)) m h1 h2 h3)]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
              hGCM.diag u, hAul]; push_cast
            have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by rw [mul_comm]; exact_mod_cast hcw2
            linarith
          have inner_wl : ∑ j, (↑(A wl j) : ℚ) * x j = 0 := by
            rw [sum_three huv.symm hwl_ne_v.symm hwl_ne_u.symm
              (fun m => (↑(A wl m) : ℚ) * x m)
              (fun m h1 h2 h3 => hrest (fun j => ↑(A wl j)) m h1 h2 h3)]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
              hGCM.diag wl, hAlv, hAlu]; push_cast; ring
          have hq : qform hSym.d A x = 0 := by
            rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
            by_cases hiv : i = v; · subst hiv; simp [inner_v]
            by_cases hiu : i = u; · subst hiu; simp [inner_u]
            by_cases hiw : i = wl; · subst hiw; simp [inner_wl]
            simp [x0 i hiv hiu hiw]
          exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
        · -- p ≤ n: right neighbor at position p+1
          have hp_le_n : (e' u_idx).val ≤ n := by omega
          set right_pos : Fin (n+2) := ⟨(e' u_idx).val + 1, by omega⟩ with right_pos_def
          set right_idx := e'.symm right_pos with right_idx_def
          have hright_ne : right_idx ≠ u_idx := by
            intro h; have h1 := congr_arg e' h
            simp only [right_idx_def, e'.apply_symm_apply, right_pos_def, Fin.ext_iff,
              Fin.val_mk] at h1; omega
          have hrl_ne : right_idx ≠ left_idx := by
            intro h; have h1 := congr_arg e' h
            simp only [right_idx_def, left_idx_def, e'.apply_symm_apply, right_pos_def,
              left_pos_def, Fin.ext_iff, Fin.val_mk] at h1; omega
          set wr := v.succAbove right_idx with wr_def
          have hwr_ne_v : wr ≠ v := Fin.succAbove_ne v right_idx
          have hwr_ne_u : wr ≠ u := fun h => hright_ne
            (Fin.succAbove_right_injective (hu_idx ▸ h))
          have hwr_ne_wl : wr ≠ wl := fun h => hrl_ne
            (Fin.succAbove_right_injective h)
          have hAvr : A v wr = 0 := hAv0 right_idx hright_ne
          have hArv : A wr v = 0 := hAv0' right_idx hright_ne
          have he'r : e' right_idx = right_pos := e'.apply_symm_apply right_pos
          have hAru : A wr u = -1 := by
            rw [← hu_idx]; show A (v.succAbove right_idx) (v.succAbove u_idx) = -1
            rw [hsub, he'r]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, right_pos_def]
            split_ifs <;> omega
          have hAlr : A wl wr = 0 := by
            show A (v.succAbove left_idx) (v.succAbove right_idx) = 0
            rw [hsub, he'l, he'r]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
              left_pos_def, right_pos_def]; split_ifs <;> omega
          have hArl : A wr wl = 0 := by
            show A (v.succAbove right_idx) (v.succAbove left_idx) = 0
            rw [hsub, he'r, he'l]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
              right_pos_def, left_pos_def]; split_ifs <;> omega
          have hAlu : A wl u = -1 := by
            rw [← hu_idx]; show A (v.succAbove left_idx) (v.succAbove u_idx) = -1
            rw [hsub, he'l]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, left_pos_def]
            split_ifs <;> omega
          by_cases hpn : (e' u_idx).val = n
          · -- p = n: A(u,right) = -2, 3-vertex {v, u, wr}, null vec [-Avu, 2, 1]
            have hAur : A u wr = -2 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove right_idx) = -2
              rw [hsub, he'r]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, right_pos_def]
              split_ifs <;> omega
            -- 3-vertex null test via qform: x(v) = -Avu, x(u) = 2, x(wr) = 1
            set x : Fin (n+3) → ℚ := fun i =>
              if i = v then -(↑(A v u : ℤ) : ℚ)
              else if i = u then 2
              else if i = wr then 1
              else 0
            have hx : x ≠ 0 := by
              intro h; have := congr_fun h u
              simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
            have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ wr → x k = 0 :=
              fun k h1 h2 h3 => by simp [x, h1, h2, h3]
            have hrest : ∀ (r : Fin (n+3) → ℚ) (m : Fin (n+3)),
                m ≠ v → m ≠ u → m ≠ wr → r m * x m = 0 := by
              intro r m h1 h2 h3; simp [x0 m h1 h2 h3]
            have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
              rw [sum_three huv.symm hwr_ne_v.symm hwr_ne_u.symm
                (fun m => (↑(A v m) : ℚ) * x m)
                (fun m h1 h2 h3 => hrest (fun j => ↑(A v j)) m h1 h2 h3)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwr_ne_v, if_neg hwr_ne_u,
                hGCM.diag v, hAvr]; push_cast; ring
            have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
              rw [sum_three huv.symm hwr_ne_v.symm hwr_ne_u.symm
                (fun m => (↑(A u m) : ℚ) * x m)
                (fun m h1 h2 h3 => hrest (fun j => ↑(A u j)) m h1 h2 h3)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwr_ne_v, if_neg hwr_ne_u,
                hGCM.diag u, hAur]; push_cast
              have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by rw [mul_comm]; exact_mod_cast hcw2
              linarith
            have inner_wr : ∑ j, (↑(A wr j) : ℚ) * x j = 0 := by
              rw [sum_three huv.symm hwr_ne_v.symm hwr_ne_u.symm
                (fun m => (↑(A wr m) : ℚ) * x m)
                (fun m h1 h2 h3 => hrest (fun j => ↑(A wr j)) m h1 h2 h3)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwr_ne_v, if_neg hwr_ne_u,
                hGCM.diag wr, hArv, hAru]; push_cast; ring
            have hq : qform hSym.d A x = 0 := by
              rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
              by_cases hiv : i = v; · subst hiv; simp [inner_v]
              by_cases hiu : i = u; · subst hiu; simp [inner_u]
              by_cases hiw : i = wr; · subst hiw; simp [inner_wr]
              simp [x0 i hiv hiu hiw]
            exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
          · -- 1 ≤ p ≤ n-1: A(u,right) = -1, 4-vertex {v, u, wl, wr}, null vec [-Avu, 2, 1, 1]
            have hAur : A u wr = -1 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove right_idx) = -1
              rw [hsub, he'r]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, right_pos_def]
              split_ifs <;> omega
            -- 4-vertex null test: x(v) = -Avu, x(u) = 2, x(wl) = 1, x(wr) = 1
            set x : Fin (n+3) → ℚ := fun i =>
              if i = v then -(↑(A v u : ℤ) : ℚ)
              else if i = u then 2
              else if i = wl then 1
              else if i = wr then 1
              else 0
            have hx : x ≠ 0 := by
              intro h; have := congr_fun h u
              simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
            have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ wl → k ≠ wr → x k = 0 :=
              fun k h1 h2 h3 h4 => by simp [x, h1, h2, h3, h4]
            have hrest : ∀ (r : Fin (n+3) → ℚ) (m : Fin (n+3)),
                m ≠ v → m ≠ u → m ≠ wl → m ≠ wr → r m * x m = 0 := by
              intro r m h1 h2 h3 h4; simp [x0 m h1 h2 h3 h4]
            have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
              rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
                hwr_ne_wl.symm (fun m => (↑(A v m) : ℚ) * x m)
                (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A v j)) m h1 h2 h3 h4)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwr_ne_v,
                if_neg hwl_ne_u, if_neg hwr_ne_u, if_neg hwr_ne_wl,
                hGCM.diag v, hAvl, hAvr]; push_cast; ring
            have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
              rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
                hwr_ne_wl.symm (fun m => (↑(A u m) : ℚ) * x m)
                (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A u j)) m h1 h2 h3 h4)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwr_ne_v,
                if_neg hwl_ne_u, if_neg hwr_ne_u, if_neg hwr_ne_wl, if_neg hwr_ne_wl.symm,
                hGCM.diag u, hAul, hAur]; push_cast
              have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by rw [mul_comm]; exact_mod_cast hcw2
              linarith
            have inner_wl : ∑ j, (↑(A wl j) : ℚ) * x j = 0 := by
              rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
                hwr_ne_wl.symm (fun m => (↑(A wl m) : ℚ) * x m)
                (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A wl j)) m h1 h2 h3 h4)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
                if_neg hwr_ne_v, if_neg hwr_ne_u, if_neg hwr_ne_wl, if_neg hwr_ne_wl.symm,
                hGCM.diag wl, hAlv, hAlu, hAlr]; push_cast; ring
            have inner_wr : ∑ j, (↑(A wr j) : ℚ) * x j = 0 := by
              rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
                hwr_ne_wl.symm (fun m => (↑(A wr m) : ℚ) * x m)
                (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A wr j)) m h1 h2 h3 h4)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
                if_neg hwr_ne_v, if_neg hwr_ne_u, if_neg hwr_ne_wl, if_neg hwr_ne_wl.symm,
                hGCM.diag wr, hArv, hAru, hArl]; push_cast; ring
            have hq : qform hSym.d A x = 0 := by
              rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
              by_cases hiv : i = v; · subst hiv; simp [inner_v]
              by_cases hiu : i = u; · subst hiu; simp [inner_u]
              by_cases hiw1 : i = wl; · subst hiw1; simp [inner_wl]
              by_cases hiw2 : i = wr; · subst hiw2; simp [inner_wr]
              simp [x0 i hiv hiu hiw1 hiw2]
            exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
  | C k hk =>
    simp only [DynkinType.cartanMatrix] at hrank ht'
    subst hrank -- k = n + 2
    obtain ⟨e', he'⟩ := ht'
    have hsub : ∀ i j : Fin (n+2), A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.C (n+2) (e' i) (e' j) := fun i j => (he' i j).symm
    have hAv0 : ∀ m : Fin (n+2), m ≠ u_idx → A v (v.succAbove m) = 0 := by
      intro m hm; by_contra h
      exact hm (Fin.succAbove_right_injective (hu_idx ▸ huniq _ (Fin.succAbove_ne v m) h))
    have hAv0' : ∀ m : Fin (n+2), m ≠ u_idx → A (v.succAbove m) v = 0 := by
      intro m hm
      exact (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v m))).mp (hAv0 m hm)
    by_cases h0 : e' u_idx = 0
    · -- Attachment at vertex 0 (simply-laced end), weight must be 1
      by_cases hw1 : A v u * A u v = 1
      · -- Weight 1 → C_{k+1} = C_{n+3}
        have hAvu_eq : A v u = -1 := by nlinarith
        have hAuv_eq : A u v = -1 := by nlinarith
        refine ⟨DynkinType.C (n+3) (by omega), ?_⟩
        simp only [DynkinType.cartanMatrix]
        exact extend_at_zero hGCM v e' (CartanMatrix.C (n+3))
          (by simp [CartanMatrix.C])
          (fun i j => by rw [C_succ_eq_C]; exact (hsub i j).symm)
          (fun m => by
            rw [C_first_row (n+2) (by omega)]
            split_ifs with h
            · have : e' m = e' u_idx := (Fin.ext h).trans h0.symm
              rw [show m = u_idx from e'.injective this, hu_idx, hAvu_eq]
            · rw [hAv0 m (fun heq => h (show (e' m).val = 0 from
                heq ▸ (congrArg Fin.val h0)))])
          (fun m => by
            rw [C_first_col (n+2) (by omega)]
            split_ifs with h
            · have : e' m = e' u_idx := (Fin.ext h).trans h0.symm
              rw [show m = u_idx from e'.injective this, hu_idx, hAuv_eq]
            · rw [hAv0' m (fun heq => h (show (e' m).val = 0 from
                heq ▸ (congrArg Fin.val h0)))])
      · -- Weight 2 at vertex 0 → contradiction
        exfalso
        have hcw2 : A v u * A u v = 2 := by omega
        -- Null vector: x(v) = -A(v,u), x(other) = 2
        apply absurd hPD (not_posDef_of_int_null hSym
          (fun i => if i = v then -A v u else 2)
          (by intro h; have := congr_fun h v; simp at this; omega)
          _)
        ext i; simp only [mulVec, dotProduct, Pi.zero_apply]
        rw [Fin.sum_univ_succAbove _ v]
        simp only [ite_true]
        simp_rw [show ∀ m, (if v.succAbove m = v then -A v u else 2) = 2 from
          fun m => if_neg (Fin.succAbove_ne v m)]
        -- Goal: A i v * (-A v u) + ∑ m, A i (v.succAbove m) * 2 = 0
        rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨m, hi⟩
        · -- Row v
          rw [hi, hGCM.diag v]
          have : ∑ k, A v (v.succAbove k) * 2 = A v u * 2 := by
            rw [Fintype.sum_eq_single u_idx (fun m hm => by
              have : A v (v.succAbove m) = 0 := by
                by_contra h; exact hm (Fin.succAbove_right_injective
                  (hu_idx ▸ huniq _ (Fin.succAbove_ne v m) h))
              rw [this]; ring)]
            rw [hu_idx]
          rw [this]; ring
        · -- Row v.succAbove m: A(sAm,v)*(-Avu) + ∑_l A(sAm,sAl)*2 = 0
          rw [hi]
          -- Rewrite submatrix entries and factor out 2
          have hsub_eq : ∀ l, A (v.succAbove m) (v.succAbove l) =
              CartanMatrix.C (n+2) (e' m) (e' l) := fun l => hsub m l
          simp_rw [hsub_eq]
          rw [← Finset.sum_mul, Equiv.sum_comp e' (fun p => CartanMatrix.C (n+2) (e' m) p),
            C_rowSum (n+2) (by omega)]
          by_cases hm : m = u_idx
          · rw [hm, show (e' u_idx).val = 0 from congrArg Fin.val h0, if_pos rfl,
              hu_idx]; linarith
          · rw [if_neg (show (e' m).val ≠ 0 from fun h =>
              hm (e'.injective (Fin.ext (h ▸ (congrArg Fin.val h0).symm))))]
            rw [show A (v.succAbove m) v = 0 from hAv0' m hm]; ring
    · -- Attachment at vertex ≠ 0
      have hp_pos : 0 < (e' u_idx).val := Nat.pos_of_ne_zero (fun h => h0 (Fin.ext h))
      by_cases hw1 : A v u * A u v = 1
      · -- Weight 1
        have hAvu_eq : A v u = -1 := by nlinarith
        have hAuv_eq : A u v = -1 := by nlinarith
        by_cases hpk1 : (e' u_idx).val + 1 = n + 2
        · -- p = k-1 (double-bond endpoint)
          by_cases hn2 : 2 ≤ n
          · -- k ≥ 4 → contradiction via 5-vertex null subgraph [2,4,3,2,1]
            exfalso
            have hu_val : (e' u_idx).val = n + 1 := by omega
            set wl_pos : Fin (n+2) := ⟨n, by omega⟩ with wl_pos_def
            set wl_idx := e'.symm wl_pos with wl_idx_def
            have he'wl : e' wl_idx = wl_pos := e'.apply_symm_apply wl_pos
            have hwl_ne_u_idx : wl_idx ≠ u_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl, wl_pos_def, Fin.ext_iff, Fin.val_mk] at h1; omega
            set wl2_pos : Fin (n+2) := ⟨n-1, by omega⟩ with wl2_pos_def
            set wl2_idx := e'.symm wl2_pos with wl2_idx_def
            have he'wl2 : e' wl2_idx = wl2_pos := e'.apply_symm_apply wl2_pos
            have hwl2_ne_u_idx : wl2_idx ≠ u_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl2, wl2_pos_def, Fin.ext_iff, Fin.val_mk] at h1; omega
            have hwl2_ne_wl_idx : wl2_idx ≠ wl_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl2, he'wl, wl2_pos_def, wl_pos_def,
                Fin.ext_iff, Fin.val_mk] at h1; omega
            set wl3_pos : Fin (n+2) := ⟨n-2, by omega⟩ with wl3_pos_def
            set wl3_idx := e'.symm wl3_pos with wl3_idx_def
            have he'wl3 : e' wl3_idx = wl3_pos := e'.apply_symm_apply wl3_pos
            have hwl3_ne_u_idx : wl3_idx ≠ u_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl3, wl3_pos_def, Fin.ext_iff, Fin.val_mk] at h1; omega
            have hwl3_ne_wl_idx : wl3_idx ≠ wl_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl3, he'wl, wl3_pos_def, wl_pos_def,
                Fin.ext_iff, Fin.val_mk] at h1; omega
            have hwl3_ne_wl2_idx : wl3_idx ≠ wl2_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [he'wl3, he'wl2, wl3_pos_def, wl2_pos_def,
                Fin.ext_iff, Fin.val_mk] at h1; omega
            -- A-entry proofs
            have hAvu : A v u = -1 := hAvu_eq
            have hAuv : A u v = -1 := hAuv_eq
            have hAvwl : A v (v.succAbove wl_idx) = 0 := hAv0 wl_idx hwl_ne_u_idx
            have hAlv : A (v.succAbove wl_idx) v = 0 := hAv0' wl_idx hwl_ne_u_idx
            have hAvwl2 : A v (v.succAbove wl2_idx) = 0 := hAv0 wl2_idx hwl2_ne_u_idx
            have hAl2v : A (v.succAbove wl2_idx) v = 0 := hAv0' wl2_idx hwl2_ne_u_idx
            have hAvwl3 : A v (v.succAbove wl3_idx) = 0 := hAv0 wl3_idx hwl3_ne_u_idx
            have hAl3v : A (v.succAbove wl3_idx) v = 0 := hAv0' wl3_idx hwl3_ne_u_idx
            -- C entries via hsub
            have hCul : CartanMatrix.C (n+2) (e' u_idx) (e' wl_idx) = -2 := by
              rw [he'wl]; simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
                Fin.val_mk, wl_pos_def]; split_ifs <;> omega
            have hClu : CartanMatrix.C (n+2) (e' wl_idx) (e' u_idx) = -1 := by
              rw [he'wl]; simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
                Fin.val_mk, wl_pos_def]; split_ifs <;> omega
            have hCll2 : CartanMatrix.C (n+2) (e' wl_idx) (e' wl2_idx) = -1 := by
              rw [he'wl, he'wl2]; simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
                Fin.val_mk, wl_pos_def, wl2_pos_def]; split_ifs <;> omega
            have hCl2l : CartanMatrix.C (n+2) (e' wl2_idx) (e' wl_idx) = -1 := by
              rw [he'wl, he'wl2]; simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
                Fin.val_mk, wl_pos_def, wl2_pos_def]; split_ifs <;> omega
            have hCl2l3 : CartanMatrix.C (n+2) (e' wl2_idx) (e' wl3_idx) = -1 := by
              rw [he'wl2, he'wl3]; simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
                Fin.val_mk, wl2_pos_def, wl3_pos_def]; split_ifs <;> omega
            have hCl3l2 : CartanMatrix.C (n+2) (e' wl3_idx) (e' wl2_idx) = -1 := by
              rw [he'wl2, he'wl3]; simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
                Fin.val_mk, wl2_pos_def, wl3_pos_def]; split_ifs <;> omega
            -- Null test: x = [2, 4, 3, 2, 1] on {v, u, wl, wl2, wl3}
            set wl := v.succAbove wl_idx
            set wl2 := v.succAbove wl2_idx
            set wl3 := v.succAbove wl3_idx
            let x : Fin (n+3) → ℚ := fun i =>
              if i = v then 2 else if i = u then 4
              else if i = wl then 3 else if i = wl2 then 2
              else if i = wl3 then 1 else 0
            have hx : x ≠ 0 := by
              intro h; have := congr_fun h v; simp only [x, if_pos rfl, Pi.zero_apply] at this
              exact absurd this (by norm_num)
            have hwl_ne_v : wl ≠ v := Fin.succAbove_ne v wl_idx
            have hwl_ne_u : wl ≠ u := fun h => hwl_ne_u_idx
              (Fin.succAbove_right_injective (hu_idx ▸ h))
            have hwl2_ne_v : wl2 ≠ v := Fin.succAbove_ne v wl2_idx
            have hwl2_ne_u : wl2 ≠ u := fun h => hwl2_ne_u_idx
              (Fin.succAbove_right_injective (hu_idx ▸ h))
            have hwl2_ne_wl : wl2 ≠ wl := fun h => hwl2_ne_wl_idx
              (Fin.succAbove_right_injective h)
            have hwl3_ne_v : wl3 ≠ v := Fin.succAbove_ne v wl3_idx
            have hwl3_ne_u : wl3 ≠ u := fun h => hwl3_ne_u_idx
              (Fin.succAbove_right_injective (hu_idx ▸ h))
            have hwl3_ne_wl : wl3 ≠ wl := fun h => hwl3_ne_wl_idx
              (Fin.succAbove_right_injective h)
            have hwl3_ne_wl2 : wl3 ≠ wl2 := fun h => hwl3_ne_wl2_idx
              (Fin.succAbove_right_injective h)
            have hAul : A u wl = -2 := by rw [← hu_idx]; exact (hsub u_idx wl_idx).symm ▸ hCul
            have hAlu : A wl u = -1 := by rw [← hu_idx]; exact (hsub wl_idx u_idx).symm ▸ hClu
            have hAll2 : A wl wl2 = -1 := (hsub wl_idx wl2_idx).symm ▸ hCll2
            have hAl2l : A wl2 wl = -1 := (hsub wl2_idx wl_idx).symm ▸ hCl2l
            have hAl2l3 : A wl2 wl3 = -1 := (hsub wl2_idx wl3_idx).symm ▸ hCl2l3
            have hAl3l2 : A wl3 wl2 = -1 := (hsub wl3_idx wl2_idx).symm ▸ hCl3l2
            -- Zero A-entries for non-adjacent pairs
            have hAu_wl2 : A u wl2 = 0 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove wl2_idx) = 0
              rw [hsub, he'wl2]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl2_pos_def]; split_ifs <;> omega
            have hAu_wl3 : A u wl3 = 0 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove wl3_idx) = 0
              rw [hsub, he'wl3]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl3_pos_def]; split_ifs <;> omega
            have hAwl_wl3 : A wl wl3 = 0 := by
              show A (v.succAbove wl_idx) (v.succAbove wl3_idx) = 0
              rw [hsub, he'wl, he'wl3]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl_pos_def, wl3_pos_def]; split_ifs <;> omega
            have hAwl3_u : A wl3 u = 0 := by
              rw [← hu_idx]; show A (v.succAbove wl3_idx) (v.succAbove u_idx) = 0
              rw [hsub, he'wl3]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl3_pos_def]; split_ifs <;> omega
            have hAwl3_wl : A wl3 wl = 0 := by
              show A (v.succAbove wl3_idx) (v.succAbove wl_idx) = 0
              rw [hsub, he'wl3, he'wl]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl3_pos_def, wl_pos_def]; split_ifs <;> omega
            have hAwl2_u : A wl2 u = 0 := by
              rw [← hu_idx]; show A (v.succAbove wl2_idx) (v.succAbove u_idx) = 0
              rw [hsub, he'wl2]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                wl2_pos_def]; split_ifs <;> omega
            have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ wl → k ≠ wl2 → k ≠ wl3 → x k = 0 :=
              fun k h1 h2 h3 h4 h5 => by simp [x, h1, h2, h3, h4, h5]
            -- Inner products
            have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
              rw [sum_two huv.symm (fun m => (↑(A v m) : ℚ) * x m)
                (fun m h1 h2 => by
                  have : A v m = 0 := by
                    obtain ⟨m_idx, hm_eq⟩ := Fin.exists_succAbove_eq h1
                    rw [← hm_eq]
                    exact hAv0 m_idx (fun h => h2 (by rw [← hm_eq, h, hu_idx]))
                  simp [this])]
              simp only [x, ↓reduceIte, if_neg huv, hGCM.diag v, hAvu_eq]
              push_cast; ring
            have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
              rw [sum_three huv.symm hwl_ne_v.symm hwl_ne_u.symm
                (fun m => (↑(A u m) : ℚ) * x m)
                (fun m h1 h2 h3 => by
                  by_cases hm4 : m = wl2; · simp [hm4, hAu_wl2]
                  by_cases hm5 : m = wl3; · simp [hm5, hAu_wl3]
                  simp [x0 m h1 h2 h3 hm4 hm5])]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
                hGCM.diag u, hAuv_eq, hAul]; push_cast; ring
            have inner_wl : ∑ j, (↑(A wl j) : ℚ) * x j = 0 := by
              rw [sum_three (hwl_ne_u.symm) (hwl2_ne_u.symm) (hwl2_ne_wl.symm)
                (fun m => (↑(A wl m) : ℚ) * x m)
                (fun m h1 h2 h3 => by
                  by_cases hm1 : m = v; · subst hm1; simp [hAlv]
                  by_cases hm5 : m = wl3; · subst hm5; simp [hAwl_wl3]
                  simp [x0 m hm1 h1 h2 h3 hm5])]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_u, if_neg hwl_ne_v,
                if_neg hwl2_ne_u, if_neg hwl2_ne_wl, if_neg hwl2_ne_v,
                hGCM.diag wl, hAlu, hAll2]; push_cast; ring
            have inner_wl2 : ∑ j, (↑(A wl2 j) : ℚ) * x j = 0 := by
              rw [sum_three (hwl2_ne_wl.symm) (hwl3_ne_wl.symm) (hwl3_ne_wl2.symm)
                (fun m => (↑(A wl2 m) : ℚ) * x m)
                (fun m h1 h2 h3 => by
                  by_cases hm1 : m = v; · subst hm1; simp [hAl2v]
                  by_cases hm2 : m = u; · subst hm2; simp [hAwl2_u]
                  simp [x0 m hm1 hm2 h1 h2 h3])]
              simp only [x, ↓reduceIte, if_neg hwl2_ne_wl, if_neg hwl_ne_v, if_neg hwl_ne_u,
                if_neg hwl3_ne_wl, if_neg hwl3_ne_wl2, if_neg hwl3_ne_v, if_neg hwl3_ne_u,
                if_neg hwl2_ne_v, if_neg hwl2_ne_u,
                hGCM.diag wl2, hAl2l, hAl2l3]; push_cast; ring
            have inner_wl3 : ∑ j, (↑(A wl3 j) : ℚ) * x j = 0 := by
              rw [sum_two (hwl3_ne_wl2.symm)
                (fun m => (↑(A wl3 m) : ℚ) * x m)
                (fun m h1 h2 => by
                  by_cases hm1 : m = v; · subst hm1; simp [hAl3v]
                  by_cases hm2 : m = u; · subst hm2; simp [hAwl3_u]
                  by_cases hm3 : m = wl; · subst hm3; simp [hAwl3_wl]
                  simp [x0 m hm1 hm2 hm3 h1 h2])]
              simp only [x, ↓reduceIte, if_neg hwl2_ne_v, if_neg hwl2_ne_u,
                if_neg hwl2_ne_wl, if_neg hwl3_ne_v, if_neg hwl3_ne_u,
                if_neg hwl3_ne_wl, if_neg hwl3_ne_wl2,
                hGCM.diag wl3, hAl3l2]; push_cast; ring
            have hq : qform hSym.d A x = 0 := by
              rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
              by_cases hiv : i = v; · subst hiv; simp [inner_v]
              by_cases hiu : i = u; · subst hiu; simp [inner_u]
              by_cases hiw : i = wl; · subst hiw; simp [inner_wl]
              by_cases hiw2 : i = wl2; · subst hiw2; simp [inner_wl2]
              by_cases hiw3 : i = wl3; · subst hiw3; simp [inner_wl3]
              simp [x0 i hiv hiu hiw hiw2 hiw3]
            exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
          · -- k = 2 or k = 3 (n < 2)
            push_neg at hn2
            rcases Nat.eq_zero_or_pos n with rfl | hn_pos
            · -- n = 0, k = 2 → C₂ + leaf at vertex 1 = B₃
              refine ⟨DynkinType.B 3 (by omega), ?_⟩
              simp only [DynkinType.cartanMatrix]
              have he'u_val : (e' u_idx).val = 1 := by omega
              have swap_zero_iff : ∀ x : Fin 2,
                  (Equiv.swap (0 : Fin 2) 1 x).val = 0 ↔ x.val = 1 := by decide
              exact extend_at_zero hGCM v (e'.trans (Equiv.swap (0 : Fin 2) 1))
                (CartanMatrix.B 3)
                (by decide)
                (fun i j => by
                  simp only [Equiv.trans_apply, B_succ_eq_B]
                  have key : ∀ a b : Fin 2,
                      CartanMatrix.B 2 (Equiv.swap (0 : Fin 2) 1 a)
                        (Equiv.swap (0 : Fin 2) 1 b) =
                      CartanMatrix.C 2 a b := by decide
                  rw [key]; exact (hsub i j).symm)
                (fun m => by
                  simp only [Equiv.trans_apply, B_first_row 2 (by omega)]
                  split_ifs with h
                  · have hm_eq : m = u_idx := by
                      apply e'.injective; ext
                      exact ((swap_zero_iff _).mp h).trans he'u_val.symm
                    rw [hm_eq, hu_idx, hAvu_eq]
                  · have hm_ne : m ≠ u_idx := by
                      intro heq; subst heq
                      exact h ((swap_zero_iff _).mpr he'u_val)
                    rw [hAv0 m hm_ne])
                (fun m => by
                  simp only [Equiv.trans_apply, B_first_col 2 (by omega)]
                  split_ifs with h
                  · have hm_eq : m = u_idx := by
                      apply e'.injective; ext
                      exact ((swap_zero_iff _).mp h).trans he'u_val.symm
                    rw [hm_eq, hu_idx, hAuv_eq]
                  · have hm_ne : m ≠ u_idx := by
                      intro heq; subst heq
                      exact h ((swap_zero_iff _).mpr he'u_val)
                    rw [hAv0' m hm_ne])
            · -- n = 1, k = 3 → C₃ + leaf at vertex 2 = F₄
              have hn1 : n = 1 := by omega
              subst hn1
              refine ⟨DynkinType.F₄, ?_⟩
              simp only [DynkinType.cartanMatrix]
              have he'u_val : (e' u_idx).val = 2 := by omega
              have swap_zero_iff : ∀ x : Fin 3,
                  (Equiv.swap (0 : Fin 3) 2 x).val = 0 ↔ x.val = 2 := by decide
              exact extend_at_zero hGCM v (e'.trans (Equiv.swap (0 : Fin 3) 2))
                CartanMatrix.F₄
                (by decide)
                (fun i j => by
                  simp only [Equiv.trans_apply]
                  have key : ∀ a b : Fin 3,
                      CartanMatrix.F₄ (Fin.succ (Equiv.swap (0 : Fin 3) 2 a))
                        (Fin.succ (Equiv.swap (0 : Fin 3) 2 b)) =
                      CartanMatrix.C 3 a b := by decide
                  rw [key]; exact (hsub i j).symm)
                (fun m => by
                  simp only [Equiv.trans_apply]
                  have hF_row : ∀ j : Fin 3,
                      CartanMatrix.F₄ 0 (Fin.succ (Equiv.swap (0 : Fin 3) 2 j)) =
                      if j.val = 2 then -1 else 0 := by decide
                  rw [hF_row]
                  split_ifs with h
                  · have hm_eq : m = u_idx :=
                      e'.injective (Fin.ext (h.trans he'u_val.symm))
                    rw [hm_eq, hu_idx, hAvu_eq]
                  · have hm_ne : m ≠ u_idx := by
                      intro heq; subst heq; exact h he'u_val
                    rw [hAv0 m hm_ne])
                (fun m => by
                  simp only [Equiv.trans_apply]
                  have hF_col : ∀ j : Fin 3,
                      CartanMatrix.F₄ (Fin.succ (Equiv.swap (0 : Fin 3) 2 j)) 0 =
                      if j.val = 2 then -1 else 0 := by decide
                  rw [hF_col]
                  split_ifs with h
                  · have hm_eq : m = u_idx :=
                      e'.injective (Fin.ext (h.trans he'u_val.symm))
                    rw [hm_eq, hu_idx, hAuv_eq]
                  · have hm_ne : m ≠ u_idx := by
                      intro heq; subst heq; exact h he'u_val
                    rw [hAv0' m hm_ne])
        · -- 1 ≤ p ≤ k-2 (interior) → contradiction via subgraph null vector
          exfalso
          push_neg at hpk1
          have hp_le : (e' u_idx).val ≤ n := by omega
          set p_val := (e' u_idx).val with p_val_def
          set rr := n + 2 - p_val with rr_def
          have hrr_ge : 2 ≤ rr := by omega
          let fC : Fin (n+2) → ℤ := fun j =>
            if j.val + 1 = p_val then 1
            else if p_val ≤ j.val then 2
            else 0
          let x : Fin (n+3) → ℚ := fun i =>
            if h : ∃ m, v.succAbove m = i then ↑(fC (e' h.choose)) else 1
          have hx_v : x v = 1 := by
            simp only [x, dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
          have hx_sub : ∀ m, x (v.succAbove m) = ↑(fC (e' m)) := by
            intro m
            have hex : ∃ m', v.succAbove m' = v.succAbove m := ⟨m, rfl⟩
            simp only [x, dif_pos hex]
            exact congr_arg (fun z => (↑(fC (e' z)) : ℚ))
              (Fin.succAbove_right_injective hex.choose_spec)
          have hx_ne : x ≠ 0 := by
            intro h; have := congr_fun h v
            simp only [hx_v, Pi.zero_apply] at this; linarith
          have hfC_marks : ∀ q : Fin (n+2), p_val ≤ q.val → fC q = 2 := by
            intro q hq; simp only [fC]; rw [if_neg (by omega), if_pos hq]
          have hfC_u : fC (e' u_idx) = 2 := hfC_marks (e' u_idx) (le_refl _)
          -- C-path sum helper (same formula as B case)
          have hCpath_sum : ∀ i_off : Fin rr,
              ∑ q : Fin (n+2), (↑(CartanMatrix.C (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) * ↑(fC q) =
              (if i_off.val = 0 then (2 : ℚ) else 0) +
              (if i_off.val = 0 then (-1 : ℚ) else 0) := by
            intro i_off
            have hterm : ∀ q : Fin (n+2),
                (↑(CartanMatrix.C (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) * ↑(fC q) =
                (if h : p_val ≤ q.val then
                  (↑(CartanMatrix.C rr i_off ⟨q.val - p_val, by omega⟩) : ℚ) * 2
                else 0) +
                (if q.val + 1 = p_val then
                  (if i_off.val = 0 then (-1 : ℚ) else 0)
                else 0) := by
              intro q
              by_cases hqp : p_val ≤ q.val
              · rw [dif_pos hqp, if_neg (by omega)]
                simp only [add_zero]
                have hq_eq : q = ⟨(q.val - p_val) + p_val, by omega⟩ :=
                  Fin.ext (Nat.sub_add_cancel hqp).symm
                congr 1
                · conv_lhs => rw [hq_eq]
                  exact_mod_cast C_shift (n+2) p_val (by omega) i_off ⟨q.val - p_val, by omega⟩
                · exact_mod_cast hfC_marks q hqp
              · push_neg at hqp
                rw [dif_neg (by omega)]
                simp only [zero_add]
                by_cases hq1 : q.val + 1 = p_val
                · rw [if_pos hq1]
                  have hfq : fC q = 1 := by simp only [fC]; rw [if_pos hq1]
                  rw [hfq]; push_cast; simp only [mul_one]
                  have hCval : CartanMatrix.C (n+2) ⟨i_off.val + p_val, by omega⟩ q =
                      if i_off.val = 0 then -1 else 0 := by
                    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
                    have := q.isLt; have := i_off.isLt; split_ifs <;> omega
                  rw [hCval]; split_ifs <;> simp
                · rw [if_neg hq1]
                  have hfq : fC q = 0 := by
                    simp only [fC]; rw [if_neg (by omega), if_neg (by omega)]
                  rw [hfq]; simp
            simp_rw [hterm]
            rw [Finset.sum_add_distrib]
            congr 1
            · -- Shifted part: use sum_shift + C_rowSum
              trans ∑ j : Fin rr, (↑(CartanMatrix.C rr i_off j) : ℚ) * 2
              · exact sum_shift (by omega : p_val ≤ n + 2)
                  (fun j => (↑(CartanMatrix.C rr i_off j) : ℚ) * 2)
              · rw [← Finset.sum_mul]
                have hcr := C_rowSum rr hrr_ge i_off
                have : (∑ j : Fin rr, (↑(CartanMatrix.C rr i_off j) : ℚ)) =
                    if i_off.val = 0 then 1 else 0 := by exact_mod_cast hcr
                rw [this]; split_ifs <;> ring
            · rw [Fintype.sum_eq_single ⟨p_val - 1, by omega⟩ (fun q hq => by
                rw [if_neg (fun h => hq (Fin.ext (by simp at h ⊢; omega)))])]
              simp only [Fin.val_mk]
              rw [if_pos (by omega)]
          -- qform = 0 via qform_zero_of_null
          have hq : qform hSym.d A x = 0 := by
            apply qform_zero_of_null
            intro k
            rcases Fin.eq_self_or_eq_succAbove v k with hkv | ⟨m, hkm⟩
            · right; rw [hkv]
              rw [Fin.sum_univ_succAbove _ v]
              simp only [hx_v, hx_sub, hGCM.diag v]
              rw [Fintype.sum_eq_single u_idx (fun m' hm' => by
                rw [show A v (v.succAbove m') = 0 from hAv0 m' (fun heq => hm' heq)]; ring)]
              rw [hu_idx, hAvu_eq, hfC_u]; push_cast; ring
            · rw [hkm, hx_sub m]
              by_cases hfm : fC (e' m) = 0
              · left; simp [hfm]
              · right; rw [Fin.sum_univ_succAbove _ v]
                simp only [hx_v, hx_sub, hGCM.diag (v.succAbove m)]
                have hsub_reindex : ∑ l, (↑(A (v.succAbove m) (v.succAbove l)) : ℚ) * ↑(fC (e' l)) =
                    ∑ q, (↑(CartanMatrix.C (n+2) (e' m) q) : ℚ) * ↑(fC q) := by
                  simp_rw [fun l => show A (v.succAbove m) (v.succAbove l) =
                      CartanMatrix.C (n+2) (e' m) (e' l) from hsub m l]
                  push_cast
                  exact Equiv.sum_comp e' (fun q => (↑(CartanMatrix.C (n+2) (e' m) q) : ℚ) * ↑(fC q))
                rw [hsub_reindex]
                have hpos : (e' m).val + 1 = p_val ∨ p_val ≤ (e' m).val := by
                  simp only [fC] at hfm; split_ifs at hfm <;> [left; right; exact absurd rfl hfm] <;> omega
                rcases hpos with hpm1 | hpm
                · -- Left neighbor
                  have hm_ne_u : m ≠ u_idx := by intro heq; rw [heq] at hpm1; omega
                  have hAmv : A (v.succAbove m) v = 0 := hAv0' m hm_ne_u
                  rw [hAmv]; push_cast; simp only [zero_mul, zero_add]
                  set q1 : Fin (n+2) := ⟨p_val - 1, by omega⟩
                  set q2 : Fin (n+2) := ⟨p_val, by omega⟩
                  have hq12 : q1 ≠ q2 := by intro h; simp [q1, q2, Fin.ext_iff] at h; omega
                  rw [sum_two hq12
                    (fun q => (↑(CartanMatrix.C (n+2) (e' m) q) : ℚ) * ↑(fC q))
                    (fun q hq1' hq2' => by
                      have hCq : CartanMatrix.C (n+2) (e' m) q = 0 ∨ fC q = 0 := by
                        by_cases hqp : q.val + 1 = p_val
                        · exact absurd (Fin.ext (by simp [q1]; omega)) hq1'
                        · by_cases hqp2 : p_val ≤ q.val
                          · left
                            have hq_ne : q.val ≠ p_val := fun h =>
                              hq2' (Fin.ext (by simp [q2]; exact h))
                            simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk]
                            have := q.isLt; split_ifs <;> omega
                          · right; show fC q = 0
                            simp only [fC]; rw [if_neg (by omega), if_neg (by omega)]
                      rcases hCq with h | h <;> simp [h])]
                  have hCq1 : CartanMatrix.C (n+2) (e' m) q1 = 2 := by
                    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, q1]
                    have := hpm1; split_ifs <;> omega
                  have hCq2 : CartanMatrix.C (n+2) (e' m) q2 = -1 := by
                    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, q2]
                    have := hpm1; split_ifs <;> omega
                  have hfq1 : fC q1 = 1 := by simp only [fC, q1]; rw [if_pos (by omega)]
                  have hfq2 : fC q2 = 2 := hfC_marks q2 (le_refl _)
                  rw [hCq1, hCq2, hfq1, hfq2]; push_cast; ring
                · -- C sub-path vertex
                  set i_off : Fin rr := ⟨(e' m).val - p_val, by omega⟩
                  have hAmv : A (v.succAbove m) v =
                      if (e' m).val = p_val then -1 else 0 := by
                    by_cases he : (e' m).val = p_val
                    · rw [if_pos he]
                      have : m = u_idx := e'.injective (Fin.ext (he ▸ p_val_def.symm))
                      rw [this, hu_idx]; exact hAuv_eq
                    · rw [if_neg he]
                      exact hAv0' m (fun heq =>
                        he ((congr_arg (fun x => (e' x).val) heq).trans p_val_def.symm))
                  rw [hAmv]
                  have he'm_eq : e' m = ⟨i_off.val + p_val, by omega⟩ := by
                    ext; simp [i_off]; omega
                  rw [show ∑ q, (↑(CartanMatrix.C (n+2) (e' m) q) : ℚ) * ↑(fC q) =
                      ∑ q, (↑(CartanMatrix.C (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) * ↑(fC q)
                    from by rw [he'm_eq]]
                  rw [hCpath_sum i_off]
                  by_cases hi0 : i_off.val = 0
                  · have : (e' m).val = p_val := by simp [i_off, Fin.ext_iff] at hi0; omega
                    simp [hi0, this]; push_cast; ring
                  · have : (e' m).val ≠ p_val := by
                      simp [i_off, Fin.ext_iff] at hi0; omega
                    simp [hi0, this]
          exact absurd hPD (not_posDef_of_nonpos hSym x hx_ne (le_of_eq hq))
      · -- Weight 2 → contradiction for all subcases
        exfalso
        have hcw2 : A v u * A u v = 2 := by omega
        set left_pos : Fin (n+2) := ⟨(e' u_idx).val - 1, by omega⟩ with left_pos_def
        set left_idx := e'.symm left_pos with left_idx_def
        have hleft_ne : left_idx ≠ u_idx := by
          intro h; have h1 := congr_arg e' h; simp only [left_idx_def, e'.apply_symm_apply] at h1
          exact absurd (congr_arg Fin.val h1) (by simp [left_pos_def]; omega)
        set wl := v.succAbove left_idx with wl_def
        have hwl_ne_v : wl ≠ v := Fin.succAbove_ne v left_idx
        have hwl_ne_u : wl ≠ u := fun h => hleft_ne
          (Fin.succAbove_right_injective (hu_idx ▸ h))
        have hAvl : A v wl = 0 := hAv0 left_idx hleft_ne
        have hAlv : A wl v = 0 := hAv0' left_idx hleft_ne
        have he'l : e' left_idx = left_pos := e'.apply_symm_apply left_pos
        by_cases hpk1 : (e' u_idx).val + 1 = n + 2
        · -- p = k-1 (double-bond end): {v, u, wl}, vec [-Avu, 2, 1]
          -- C(k-1, k-2) = -2 (double bond), C(k-2, k-1) = -1
          have hAul : A u wl = -2 := by
            rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove left_idx) = -2
            rw [hsub, he'l]
            simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, left_pos_def]
            split_ifs <;> omega
          have hAlu : A wl u = -1 := by
            rw [← hu_idx]; show A (v.succAbove left_idx) (v.succAbove u_idx) = -1
            rw [hsub, he'l]
            simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, left_pos_def]
            split_ifs <;> omega
          set x : Fin (n+3) → ℚ := fun i =>
            if i = v then -(↑(A v u : ℤ) : ℚ) else if i = u then 2 else if i = wl then 1 else 0
          have hx : x ≠ 0 := by
            intro h; have := congr_fun h u
            simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
          have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ wl → x k = 0 :=
            fun k h1 h2 h3 => by simp [x, h1, h2, h3]
          have hrest : ∀ (r : Fin (n+3) → ℚ) (m : Fin (n+3)),
              m ≠ v → m ≠ u → m ≠ wl → r m * x m = 0 := by
            intro r m h1 h2 h3; simp [x0 m h1 h2 h3]
          have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
            rw [sum_three huv.symm hwl_ne_v.symm hwl_ne_u.symm
              (fun m => (↑(A v m) : ℚ) * x m)
              (fun m h1 h2 h3 => hrest (fun j => ↑(A v j)) m h1 h2 h3)]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
              hGCM.diag v, hAvl]; push_cast; ring
          have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
            rw [sum_three huv.symm hwl_ne_v.symm hwl_ne_u.symm
              (fun m => (↑(A u m) : ℚ) * x m)
              (fun m h1 h2 h3 => hrest (fun j => ↑(A u j)) m h1 h2 h3)]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
              hGCM.diag u, hAul]; push_cast
            have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by rw [mul_comm]; exact_mod_cast hcw2
            linarith
          have inner_wl : ∑ j, (↑(A wl j) : ℚ) * x j = 0 := by
            rw [sum_three huv.symm hwl_ne_v.symm hwl_ne_u.symm
              (fun m => (↑(A wl m) : ℚ) * x m)
              (fun m h1 h2 h3 => hrest (fun j => ↑(A wl j)) m h1 h2 h3)]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
              hGCM.diag wl, hAlv, hAlu]; push_cast; ring
          have hq : qform hSym.d A x = 0 := by
            rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
            by_cases hiv : i = v; · subst hiv; simp [inner_v]
            by_cases hiu : i = u; · subst hiu; simp [inner_u]
            by_cases hiw : i = wl; · subst hiw; simp [inner_wl]
            simp [x0 i hiv hiu hiw]
          exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
        · push_neg at hpk1
          -- Here p < k-1, so C(p, p-1) = -1 (not the double bond)
          have hAul : A u wl = -1 := by
            rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove left_idx) = -1
            rw [hsub, he'l]
            simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, left_pos_def]
            split_ifs <;> omega
          have hAlu : A wl u = -1 := by
            rw [← hu_idx]; show A (v.succAbove left_idx) (v.succAbove u_idx) = -1
            rw [hsub, he'l]
            simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, left_pos_def]
            split_ifs <;> omega
          by_cases hpk2 : (e' u_idx).val + 2 = n + 2
          · -- p = k-2 (next to double bond): {v, u, right(=k-1)}, vec [-Avu, 2, 2]
            set right_pos : Fin (n+2) := ⟨(e' u_idx).val + 1, by omega⟩ with right_pos_def
            set right_idx := e'.symm right_pos with right_idx_def
            have hright_ne : right_idx ≠ u_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [right_idx_def, e'.apply_symm_apply, right_pos_def,
                Fin.ext_iff, Fin.val_mk] at h1; omega
            set wr := v.succAbove right_idx
            have hwr_ne_v : wr ≠ v := Fin.succAbove_ne v right_idx
            have hwr_ne_u : wr ≠ u := fun h => hright_ne
              (Fin.succAbove_right_injective (hu_idx ▸ h))
            have he'r : e' right_idx = right_pos := e'.apply_symm_apply right_pos
            have hAur : A u wr = -1 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove right_idx) = -1
              rw [hsub, he'r]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, right_pos_def]
              split_ifs <;> omega
            have hAru : A wr u = -2 := by
              rw [← hu_idx]; show A (v.succAbove right_idx) (v.succAbove u_idx) = -2
              rw [hsub, he'r]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, right_pos_def]
              split_ifs <;> omega
            have hAvr : A v wr = 0 := hAv0 right_idx hright_ne
            have hArv : A wr v = 0 := hAv0' right_idx hright_ne
            have hwr_ne_wl : wr ≠ wl := fun h =>
              (show right_idx ≠ left_idx from by
                intro h'; have h1 := congr_arg e' h'
                simp only [right_idx_def, left_idx_def, e'.apply_symm_apply, right_pos_def,
                  left_pos_def, Fin.ext_iff, Fin.val_mk] at h1; omega)
              (Fin.succAbove_right_injective h)
            set x : Fin (n+3) → ℚ := fun i =>
              if i = v then -(↑(A v u : ℤ) : ℚ) else if i = u then 2 else if i = wr then 2 else 0
            have hx : x ≠ 0 := by
              intro h; have := congr_fun h u
              simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
            have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ wr → x k = 0 :=
              fun k h1 h2 h3 => by simp [x, h1, h2, h3]
            have hrest : ∀ (r : Fin (n+3) → ℚ) (m : Fin (n+3)),
                m ≠ v → m ≠ u → m ≠ wr → r m * x m = 0 := by
              intro r m h1 h2 h3; simp [x0 m h1 h2 h3]
            have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
              rw [sum_three huv.symm hwr_ne_v.symm hwr_ne_u.symm
                (fun m => (↑(A v m) : ℚ) * x m)
                (fun m h1 h2 h3 => hrest (fun j => ↑(A v j)) m h1 h2 h3)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwr_ne_v, if_neg hwr_ne_u,
                hGCM.diag v, hAvr]; push_cast; ring
            have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
              rw [sum_three huv.symm hwr_ne_v.symm hwr_ne_u.symm
                (fun m => (↑(A u m) : ℚ) * x m)
                (fun m h1 h2 h3 => hrest (fun j => ↑(A u j)) m h1 h2 h3)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwr_ne_v, if_neg hwr_ne_u,
                hGCM.diag u, hAur]; push_cast
              have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by rw [mul_comm]; exact_mod_cast hcw2
              linarith
            have inner_wr : ∑ j, (↑(A wr j) : ℚ) * x j = 0 := by
              rw [sum_three huv.symm hwr_ne_v.symm hwr_ne_u.symm
                (fun m => (↑(A wr m) : ℚ) * x m)
                (fun m h1 h2 h3 => hrest (fun j => ↑(A wr j)) m h1 h2 h3)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwr_ne_v, if_neg hwr_ne_u,
                hGCM.diag wr, hArv, hAru]; push_cast; ring
            have hq : qform hSym.d A x = 0 := by
              rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
              by_cases hiv : i = v; · subst hiv; simp [inner_v]
              by_cases hiu : i = u; · subst hiu; simp [inner_u]
              by_cases hiw : i = wr; · subst hiw; simp [inner_wr]
              simp [x0 i hiv hiu hiw]
            exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
          · -- 1 ≤ p ≤ k-3 (interior): {v, u, left, right}, vec [-Avu, 2, 1, 1]
            set right_pos : Fin (n+2) := ⟨(e' u_idx).val + 1, by omega⟩ with right_pos_def
            set right_idx := e'.symm right_pos with right_idx_def
            have hright_ne : right_idx ≠ u_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [right_idx_def, e'.apply_symm_apply, right_pos_def,
                Fin.ext_iff, Fin.val_mk] at h1; omega
            have hright_ne_left : right_idx ≠ left_idx := by
              intro h; have h1 := congr_arg e' h
              simp only [right_idx_def, left_idx_def, e'.apply_symm_apply] at h1
              exact absurd (congr_arg Fin.val h1) (by simp [right_pos_def, left_pos_def]; omega)
            set wr := v.succAbove right_idx
            have hwr_ne_v : wr ≠ v := Fin.succAbove_ne v right_idx
            have hwr_ne_u : wr ≠ u := fun h => hright_ne
              (Fin.succAbove_right_injective (hu_idx ▸ h))
            have hwr_ne_wl : wr ≠ wl := fun h => hright_ne_left
              (Fin.succAbove_right_injective h)
            have he'r : e' right_idx = right_pos := e'.apply_symm_apply right_pos
            have hAur : A u wr = -1 := by
              rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove right_idx) = -1
              rw [hsub, he'r]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, right_pos_def]
              split_ifs <;> omega
            have hAru : A wr u = -1 := by
              rw [← hu_idx]; show A (v.succAbove right_idx) (v.succAbove u_idx) = -1
              rw [hsub, he'r]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk, right_pos_def]
              split_ifs <;> omega
            have hAvr : A v wr = 0 := hAv0 right_idx hright_ne
            have hArv : A wr v = 0 := hAv0' right_idx hright_ne
            have hAlr : A wl wr = 0 := by
              show A (v.succAbove left_idx) (v.succAbove right_idx) = 0
              rw [hsub, he'l, he'r]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                left_pos_def, right_pos_def]; split_ifs <;> omega
            have hArl : A wr wl = 0 := by
              show A (v.succAbove right_idx) (v.succAbove left_idx) = 0
              rw [hsub, he'r, he'l]
              simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff, Fin.val_mk,
                right_pos_def, left_pos_def]; split_ifs <;> omega
            set x : Fin (n+3) → ℚ := fun i =>
              if i = v then -(↑(A v u : ℤ) : ℚ) else if i = u then 2
              else if i = wl then 1 else if i = wr then 1 else 0
            have hx : x ≠ 0 := by
              intro h; have := congr_fun h u
              simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
            have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ wl → k ≠ wr → x k = 0 :=
              fun k h1 h2 h3 h4 => by simp [x, h1, h2, h3, h4]
            have hrest : ∀ (r : Fin (n+3) → ℚ) (m : Fin (n+3)),
                m ≠ v → m ≠ u → m ≠ wl → m ≠ wr → r m * x m = 0 := by
              intro r m h1 h2 h3 h4; simp [x0 m h1 h2 h3 h4]
            have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
              rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
                hwr_ne_wl.symm
                (fun m => (↑(A v m) : ℚ) * x m)
                (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A v j)) m h1 h2 h3 h4)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
                if_neg hwr_ne_v, if_neg hwr_ne_u, if_neg hwr_ne_wl,
                hGCM.diag v, hAvl, hAvr]; push_cast; ring
            have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
              rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
                hwr_ne_wl.symm
                (fun m => (↑(A u m) : ℚ) * x m)
                (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A u j)) m h1 h2 h3 h4)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
                if_neg hwr_ne_v, if_neg hwr_ne_u, if_neg hwr_ne_wl,
                hGCM.diag u, hAul, hAur]; push_cast
              have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by rw [mul_comm]; exact_mod_cast hcw2
              linarith
            have inner_wl : ∑ j, (↑(A wl j) : ℚ) * x j = 0 := by
              rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
                hwr_ne_wl.symm
                (fun m => (↑(A wl m) : ℚ) * x m)
                (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A wl j)) m h1 h2 h3 h4)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
                if_neg hwr_ne_v, if_neg hwr_ne_u, if_neg hwr_ne_wl,
                hGCM.diag wl, hAlv, hAlu, hAlr]; push_cast; ring
            have inner_wr : ∑ j, (↑(A wr j) : ℚ) * x j = 0 := by
              rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
                hwr_ne_wl.symm
                (fun m => (↑(A wr m) : ℚ) * x m)
                (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A wr j)) m h1 h2 h3 h4)]
              simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
                if_neg hwr_ne_v, if_neg hwr_ne_u, if_neg hwr_ne_wl,
                hGCM.diag wr, hArv, hAru, hArl]; push_cast; ring
            have hq : qform hSym.d A x = 0 := by
              rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
              by_cases hiv : i = v; · subst hiv; simp [inner_v]
              by_cases hiu : i = u; · subst hiu; simp [inner_u]
              by_cases hiw : i = wl; · subst hiw; simp [inner_wl]
              by_cases hiwr : i = wr; · subst hiwr; simp [inner_wr]
              simp [x0 i hiv hiu hiw hiwr]
            exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
  | D k hk =>
    simp only [DynkinType.cartanMatrix] at hrank ht'
    subst hrank -- k = n + 2
    obtain ⟨e', he'⟩ := ht'
    have hsub : ∀ i j : Fin (n+2), A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.D (n+2) (e' i) (e' j) := fun i j => (he' i j).symm
    have hAv0 : ∀ m : Fin (n+2), m ≠ u_idx → A v (v.succAbove m) = 0 := by
      intro m hm; by_contra h
      exact hm (Fin.succAbove_right_injective (hu_idx ▸ huniq _ (Fin.succAbove_ne v m) h))
    have hAv0' : ∀ m : Fin (n+2), m ≠ u_idx → A (v.succAbove m) v = 0 := by
      intro m hm
      exact (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v m))).mp (hAv0 m hm)
    by_cases h0 : (e' u_idx).val = 0
    · -- Attachment at vertex 0 (path leaf), weight must be 1
      by_cases hw1 : A v u * A u v = 1
      · -- Weight 1 → D_{k+1} = D_{n+3}
        have hAvu_eq : A v u = -1 := by nlinarith
        have hAuv_eq : A u v = -1 := by nlinarith
        refine ⟨DynkinType.D (n+3) (by omega), ?_⟩
        simp only [DynkinType.cartanMatrix]
        exact extend_at_zero hGCM v e' (CartanMatrix.D (n+3))
          (by simp [CartanMatrix.D])
          (fun i j => by rw [D_succ_eq_D (n+2) (by omega)]; exact (hsub i j).symm)
          (fun m => by
            rw [D_first_row (n+2) (by omega)]
            split_ifs with h
            · have : e' m = e' u_idx := by
                ext; rw [show (e' m).val = 0 from h, show (e' u_idx).val = 0 from h0]
              rw [show m = u_idx from e'.injective this, hu_idx, hAvu_eq]
            · rw [hAv0 m (fun heq => h (show (e' m).val = 0 from heq ▸ h0))])
          (fun m => by
            rw [D_first_col (n+2) (by omega)]
            split_ifs with h
            · have : e' m = e' u_idx := by
                ext; rw [show (e' m).val = 0 from h, show (e' u_idx).val = 0 from h0]
              rw [show m = u_idx from e'.injective this, hu_idx, hAuv_eq]
            · rw [hAv0' m (fun heq => h (show (e' m).val = 0 from heq ▸ h0))])
      · -- Weight 2 at vertex 0 → contradiction
        exfalso
        have hcw2 : A v u * A u v = 2 := by omega
        apply absurd hPD (not_posDef_of_int_null hSym
          (fun i => if h : ∃ m, v.succAbove m = i then D_marks (n+2) (e' h.choose) else -A v u)
          (by intro h; have := congr_fun h v
              simp only [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k)),
                Pi.zero_apply] at this; omega)
          _)
        have hx_v : (fun i => if h : ∃ m, v.succAbove m = i then D_marks (n+2) (e' h.choose)
            else -A v u) v = -A v u := dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))
        have hx_sub : ∀ m, (fun i => if h : ∃ m, v.succAbove m = i then D_marks (n+2) (e' h.choose)
            else -A v u) (v.succAbove m) = D_marks (n+2) (e' m) := by
          intro m
          have hex : ∃ m', v.succAbove m' = v.succAbove m := ⟨m, rfl⟩
          simp only [dif_pos hex]
          exact congr_arg _ (congr_arg e' (Fin.succAbove_right_injective hex.choose_spec))
        ext i; simp only [mulVec, dotProduct, Pi.zero_apply]
        rw [Fin.sum_univ_succAbove _ v]
        simp only [hx_v, hx_sub]
        rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨m, hi⟩
        · -- Row v
          rw [hi, hGCM.diag v]
          rw [show ∑ k, A v (v.succAbove k) * D_marks (n+2) (e' k) = A v u * D_marks (n+2) (e' u_idx)
            from Fintype.sum_eq_single u_idx (fun m hm => by
              rw [show A v (v.succAbove m) = 0 from by
                by_contra h; exact hm (Fin.succAbove_right_injective
                  (hu_idx ▸ huniq _ (Fin.succAbove_ne v m) h))]; ring) |>.trans (by rw [hu_idx])]
          rw [show e' u_idx = ⟨0, by omega⟩ from Fin.ext h0]
          have : D_marks (n+2) ⟨0, by omega⟩ = 2 := by
            simp only [D_marks, show (⟨0, by omega⟩ : Fin (n+2)).val = 0 from rfl]
            split_ifs <;> omega
          rw [this]; ring
        · -- Row v.succAbove m
          rw [hi]
          have hsub_reindex : ∑ l, A (v.succAbove m) (v.succAbove l) * D_marks (n+2) (e' l) =
              ∑ p, CartanMatrix.D (n+2) (e' m) p * D_marks (n+2) p := by
            simp_rw [fun l => show A (v.succAbove m) (v.succAbove l) =
                CartanMatrix.D (n+2) (e' m) (e' l) from hsub m l]
            exact Equiv.sum_comp e' (fun p => CartanMatrix.D (n+2) (e' m) p * D_marks (n+2) p)
          rw [hsub_reindex, D_mulVec_marks (n+2) (by omega)]
          by_cases hm : m = u_idx
          · rw [hm, show (e' u_idx).val = 0 from h0, if_pos rfl, hu_idx]; linarith
          · rw [if_neg (show (e' m).val ≠ 0 from fun h =>
              hm (e'.injective (Fin.ext (h ▸ h0.symm))))]
            rw [show A (v.succAbove m) v = 0 from hAv0' m hm]; ring
    · -- Attachment at vertex ≠ 0 → further case analysis needed
      sorry
  | E₆ =>
    simp only [DynkinType.cartanMatrix] at hrank
    change CartanEquiv (deleteVertex A v) CartanMatrix.E₆ at ht'
    exact e6_extension hGCM hSym hPD v u huv hAvu hAuv huniq hcw_le2 ht'
  | E₇ =>
    -- Rank: n + 2 = 7, so n = 5, A is 8×8.
    simp only [DynkinType.cartanMatrix] at hrank
    change CartanEquiv (deleteVertex A v) CartanMatrix.E₇ at ht'
    have hn : n = 5 := by omega
    subst hn
    obtain ⟨e', he'⟩ := ht'
    obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
    have hsub : ∀ i j : Fin 7, A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.E₇ (e' i) (e' j) := fun i j => (he' i j).symm
    have hAv0 : ∀ k : Fin 7, k ≠ u_idx → A v (v.succAbove k) = 0 := by
      intro k hk
      have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
      have hne_u : v.succAbove k ≠ u := fun h =>
        hk (Fin.succAbove_right_injective (hu_idx ▸ h))
      by_contra hvk; exact hne_u (huniq _ hne_v hvk)
    by_cases h6 : e' u_idx = 6
    · -- Attachment at E₇ vertex 6 (marks = 1)
      by_cases hw1 : A v u * A u v = 1
      · -- Weight 1: both entries = -1. Construct E₈.
        have hAvu_eq : A v u = -1 := by nlinarith
        have hAuv_eq : A u v = -1 := by nlinarith
        -- Build CartanEquiv A E₈
        -- Map: v ↦ 7, v.succAbove k ↦ castSucc (e' k)
        refine ⟨DynkinType.E₈, ?_⟩
        -- For i : Fin 8, either i = v or i = v.succAbove k for unique k
        let f : Fin 8 → Fin 8 := fun i =>
          if h : ∃ k : Fin 7, v.succAbove k = i then Fin.castSucc (e' h.choose) else 7
        have hf_v : f v = 7 := by
          simp only [f]; rw [dif_neg]; push_neg
          exact fun k => Fin.succAbove_ne v k
        have hf_sub : ∀ k : Fin 7, f (v.succAbove k) = Fin.castSucc (e' k) := by
          intro k; simp only [f]
          have hex : ∃ k' : Fin 7, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
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
        -- Verify: E₈ (σ i) (σ j) = A i j
        show CartanMatrix.E₈ (f i) (f j) = A i j
        rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
        · -- i = v
          rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
          · -- j = v: E₈(7,7) = 2 = A(v,v)
            rw [hi, hj]; simp only [hf_v, hGCM.diag]; decide
          · -- j = sA kj: E₈(7, castSucc(e' kj)) vs A(v, sA kj)
            rw [hi, hj, hf_v, hf_sub, E8_last_row]
            by_cases hkj : kj = u_idx
            · subst hkj; rw [h6]; simp [hu_idx, hAvu_eq]
            · rw [if_neg (show e' kj ≠ 6 from fun h => hkj (e'.injective (h.trans h6.symm)))]
              simp [hAv0 kj hkj]
        · -- i = sA ki
          rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
          · -- j = v: E₈(castSucc(e' ki), 7) vs A(sA ki, v)
            rw [hi, hj, hf_sub, hf_v]
            have hE8_sym : CartanMatrix.E₈ (Fin.castSucc (e' ki)) 7 =
                CartanMatrix.E₈ 7 (Fin.castSucc (e' ki)) := by
              have : ∀ a b : Fin 8, CartanMatrix.E₈ a b = CartanMatrix.E₈ b a := by decide
              exact this _ _
            rw [hE8_sym, E8_last_row]
            by_cases hki : ki = u_idx
            · subst hki; rw [h6]; simp [hu_idx, hAuv_eq]
            · rw [if_neg (show e' ki ≠ 6 from fun h => hki (e'.injective (h.trans h6.symm)))]
              simp
              have hne_v : v.succAbove ki ≠ v := Fin.succAbove_ne v ki
              have hAvk : A v (v.succAbove ki) = 0 := hAv0 ki hki
              exact ((hGCM.zero_iff v _ (Ne.symm hne_v)).mp hAvk).symm
          · -- Both submatrix: E₈(castSucc(e' ki), castSucc(e' kj)) = A(sA ki, sA kj)
            rw [hi, hj, hf_sub, hf_sub, E8_castSucc_eq_E7, ← hsub]
      · -- Weight 2 at vertex 6: contradiction
        exfalso
        have hw2 : A v u * A u v = 2 := by omega
        -- Case split on which entry is -2
        have hcases : (A v u = -1 ∧ A u v = -2) ∨ (A v u = -2 ∧ A u v = -1) := by
          have : A v u = -1 ∨ A v u = -2 := by
            have hAvu_ge : -2 ≤ A v u := by
              by_contra hlt; push_neg at hlt
              have h3 : A v u ≤ -3 := by omega
              nlinarith [mul_nonneg_of_nonpos_of_nonpos (show A v u + 2 ≤ 0 by omega)
                (show A u v + 1 ≤ 0 by omega)]
            omega
          rcases this with h | h <;> [left; right] <;> constructor <;> [exact h; nlinarith; exact h; nlinarith]
        -- Embedding: φ(k) = v.succAbove(e'⁻¹(k+1)) for k<6, φ(6) = v
        let g : Fin 6 → Fin 8 := fun k => v.succAbove (e'.symm (Fin.succ k))
        let φ : Fin 7 → Fin 8 := fun i =>
          if h : (i : ℕ) < 6 then g ⟨i, h⟩ else v
        have hφ_lt : ∀ (i : Fin 7) (hi : (i : ℕ) < 6), φ i = g ⟨i, hi⟩ := by
          intro i hi; simp only [φ, hi, ↓reduceDIte]
        have hφ6 : ∀ (i : Fin 7), ¬ (i : ℕ) < 6 → φ i = v := by
          intro i hi; simp only [φ, hi, ↓reduceDIte]
        have he'symm6 : e'.symm 6 = u_idx := by rw [← h6, e'.symm_apply_apply]
        -- φ is injective
        have hφ_inj : Function.Injective φ := by
          intro i j hij; simp only [φ] at hij
          by_cases hi : (i : ℕ) < 6 <;> by_cases hj : (j : ℕ) < 6 <;>
            simp only [hi, hj, ↓reduceDIte] at hij
          · exact Fin.ext (show (i : ℕ) = j from by
              have := Fin.ext_iff.mp (Fin.succ_injective _
                (e'.symm.injective (Fin.succAbove_right_injective hij)))
              simpa using this)
          · exact absurd hij (Fin.succAbove_ne v _)
          · exact absurd hij.symm (Fin.succAbove_ne v _)
          · exact Fin.ext (by omega)
        let φ_emb : Fin 7 ↪ Fin 8 := ⟨φ, hφ_inj⟩
        -- Key: e'.symm (Fin.succ k) ≠ u_idx when k ≠ 5
        have hk_ne_u : ∀ k : Fin 6, k ≠ 5 → e'.symm (Fin.succ k) ≠ u_idx := by
          intro k hk heq; apply hk
          have h1 := e'.symm.injective (heq.trans he'symm6.symm)
          exact Fin.ext (by have := Fin.ext_iff.mp h1; simp at this; omega)
        -- Entry proof helper: A(g k, v) and A(v, g k)
        have hAg_v : ∀ k : Fin 6, k ≠ 5 → A (g k) v = 0 := by
          intro k hk; show A (v.succAbove _) v = 0
          have h0 := hAv0 _ (hk_ne_u k hk)
          exact (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v _))).mp h0
        have hAv_g : ∀ k : Fin 6, k ≠ 5 → A v (g k) = 0 := by
          intro k hk; show A v (v.succAbove _) = 0; exact hAv0 _ (hk_ne_u k hk)
        have hsucc5_eq_6 : Fin.succ (5 : Fin 6) = (6 : Fin 7) := by decide
        have hg5_eq : g 5 = u := by
          show v.succAbove (e'.symm (Fin.succ 5)) = u
          rw [hsucc5_eq_6, he'symm6, hu_idx]
        -- Submatrix entries = E₇ subblock
        have hgg : ∀ ki kj : Fin 6, A (g ki) (g kj) =
            CartanMatrix.E₇ (Fin.succ ki) (Fin.succ kj) := by
          intro ki kj; simp only [g]
          rw [hsub, e'.apply_symm_apply, e'.apply_symm_apply]
        -- Entry proof: A(φ i, φ j) = M i j (for given M, Avu, Auv)
        -- 4 cases: (g-g) submatrix, (g-v)/(v-g) leaf, (v-v) diagonal
        have hentry : ∀ (Avu Auv : ℤ) (hAvu : A v u = Avu) (hAuv : A u v = Auv)
            (M : Matrix (Fin 7) (Fin 7) ℤ)
            (hM1 : ∀ ki kj : Fin 6,
              M (Fin.castSucc ki) (Fin.castSucc kj) =
              CartanMatrix.E₇ (Fin.succ ki) (Fin.succ kj))
            (hM2 : M 6 6 = 2) (hM3 : M 5 6 = Auv) (hM4 : M 6 5 = Avu)
            (hM5 : ∀ k : Fin 6, k ≠ 5 → M (Fin.castSucc k) 6 = 0)
            (hM6 : ∀ k : Fin 6, k ≠ 5 → M 6 (Fin.castSucc k) = 0),
            ∀ i j : Fin 7, A (φ i) (φ j) = M i j := by
          intro Avu Auv hAvu hAuv M hM1 hM2 hM3 hM4 hM5 hM6 i j
          have hcs : ∀ (k : Fin 7) (hk : (k : ℕ) < 6),
              Fin.castSucc (⟨k, hk⟩ : Fin 6) = k := fun _ _ => Fin.ext rfl
          by_cases hi : (i : ℕ) < 6 <;> by_cases hj : (j : ℕ) < 6
          · -- Both in submatrix
            rw [hφ_lt i hi, hφ_lt j hj, hgg, ← hM1, hcs i hi, hcs j hj]
          · -- i in submatrix, j = v
            have hj6 : j = 6 := Fin.ext (by omega)
            subst hj6; rw [hφ_lt i hi, hφ6 6 (by omega)]
            by_cases hki5 : (⟨(i : ℕ), hi⟩ : Fin 6) = 5
            · rw [show g ⟨i, hi⟩ = u from by
                rw [show (⟨(i : ℕ), hi⟩ : Fin 6) = 5 from hki5]; exact hg5_eq]
              rw [hAuv, ← hM3]; congr 1; exact Fin.ext (by simp [Fin.ext_iff] at hki5; omega)
            · rw [hAg_v _ hki5, ← hM5 _ hki5, hcs i hi]
          · -- i = v, j in submatrix
            have hi6 : i = 6 := Fin.ext (by omega)
            subst hi6; rw [hφ6 6 (by omega), hφ_lt j hj]
            by_cases hkj5 : (⟨(j : ℕ), hj⟩ : Fin 6) = 5
            · rw [show g ⟨j, hj⟩ = u from by
                rw [show (⟨(j : ℕ), hj⟩ : Fin 6) = 5 from hkj5]; exact hg5_eq]
              rw [hAvu, ← hM4]; congr 1; exact Fin.ext (by simp [Fin.ext_iff] at hkj5; omega)
            · rw [hAv_g _ hkj5, ← hM6 _ hkj5, hcs j hj]
          · -- Both = v
            have hi6 : i = 6 := Fin.ext (by omega)
            have hj6 : j = 6 := Fin.ext (by omega)
            subst hi6; subst hj6
            rw [hGCM.diag, ← hM2]
        rcases hcases with ⟨hvu_eq, huv_eq⟩ | ⟨hvu_eq, huv_eq⟩
        · apply absurd hPD
          exact not_posDef_of_submatrix_int_null hSym φ_emb e7w2c1
            (hentry (-1) (-2) hvu_eq huv_eq e7w2c1
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide))
            _ (by decide) e7w2c1_null
        · apply absurd hPD
          exact not_posDef_of_submatrix_int_null hSym φ_emb e7w2c2
            (hentry (-2) (-1) hvu_eq huv_eq e7w2c2
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide))
            _ (by decide) e7w2c2_null
    · -- Attachment at E₇ vertex ≠ 6 (marks ≥ 2): contradiction
      exfalso
      -- Same marks approach as E₈/F₄
      set mj : ℤ := marksE7 (e' u_idx)
      have hmj : (2 : ℤ) ≤ mj := by
        have : ∀ i : Fin 7, i ≠ 6 → 2 ≤ marksE7 i := by decide
        exact this _ h6
      set c : ℚ := -(↑(A v u) : ℚ)
      have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
      have hc_pos : 0 < c := by simp only [c]; linarith
      set x : Fin 8 → ℚ := fun i =>
        if h : ∃ k : Fin 7, v.succAbove k = i then ↑(marksE7 (e' h.choose))
        else c
      have hx_sub : ∀ k : Fin 7, x (v.succAbove k) = ↑(marksE7 (e' k)) := by
        intro k; simp only [x]
        have hex : ∃ k' : Fin 7, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
        rw [dif_pos hex]
        have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
        rw [heq]
      have hx_v : x v = c := by
        simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
      have hx : x ≠ 0 := by
        intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
      have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 2 * c + ↑(A v u) * ↑mj := by
        rw [Fin.sum_univ_succAbove _ v]
        simp only [hx_v, hGCM.diag v, hx_sub]
        have hsum : ∑ k : Fin 7, (↑(A v (v.succAbove k)) : ℚ) * ↑(marksE7 (e' k)) =
            ↑(A v u) * ↑mj := by
          have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksE7 (e' u_idx)) =
              ↑(A v u) * ↑mj := by rw [hu_idx]
          rw [← hval]
          exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
        rw [hsum]; push_cast; ring
      have e7marks_sum : ∀ k : Fin 7,
          ∑ l : Fin 7, (↑(CartanMatrix.E₇ (e' k) (e' l)) : ℚ) * ↑(marksE7 (e' l)) =
          if e' k = 0 then 1 else 0 := by
        intro k
        have hreindex := Equiv.sum_comp e'
          (fun p => (↑(CartanMatrix.E₇ (e' k) p) : ℚ) * ↑(marksE7 p))
        rw [hreindex]
        have h := congr_fun E7_mulVec_marks (e' k)
        simp only [mulVec, dotProduct] at h
        have hcast : ∑ p, (↑(CartanMatrix.E₇ (e' k) p) : ℚ) * ↑(marksE7 p)
            = (↑(∑ p, CartanMatrix.E₇ (e' k) p * marksE7 p) : ℚ) := by push_cast; rfl
        rw [hcast, h]; push_cast; split_ifs <;> simp
      have inner_sub : ∀ k : Fin 7, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
          ↑(A (v.succAbove k) v) * c +
          (if e' k = 0 then 1 else 0) := by
        intro k
        rw [Fin.sum_univ_succAbove _ v]
        simp only [hx_v, hx_sub]; congr 1
        have : ∀ l : Fin 7, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(marksE7 (e' l))
            = (↑(CartanMatrix.E₇ (e' k) (e' l)) : ℚ) * ↑(marksE7 (e' l)) := by
          intro l; rw [hsub]
        simp_rw [this]
        exact e7marks_sum k
      have sym_trick : ∀ k : Fin 7,
          hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ) =
          hSym.d v * (↑(A v (v.succAbove k)) : ℚ) := by
        intro k; have := hSym.sym (v.succAbove k) v; linarith
      apply absurd hPD
      apply not_posDef_of_nonpos hSym x hx
      rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hx_sub, inner_v, inner_sub]
      have hsplit : ∀ k : Fin 7,
          hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) *
          (↑(A (v.succAbove k) v) * c + if e' k = (0 : Fin 7) then (1 : ℚ) else 0) =
          c * (hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ)) * ↑(marksE7 (e' k)) +
          hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) *
          (if e' k = (0 : Fin 7) then (1 : ℚ) else 0) := by intro k; ring
      simp_rw [hsplit, sym_trick]
      rw [Finset.sum_add_distrib]
      have hcross : ∑ k : Fin 7, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
          ↑(marksE7 (e' k)) = c * hSym.d v * (↑(A v u) * ↑mj) := by
        simp_rw [show ∀ k : Fin 7, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
            ↑(marksE7 (e' k)) = c * hSym.d v * ((↑(A v (v.succAbove k)) : ℚ) *
            ↑(marksE7 (e' k))) from fun k => by ring]
        rw [← Finset.mul_sum]
        congr 1
        have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksE7 (e' u_idx)) =
            ↑(A v u) * ↑mj := by rw [hu_idx]
        rw [← hval]
        exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
      have hresid : ∑ k : Fin 7, hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) *
          (if e' k = (0 : Fin 7) then (1 : ℚ) else 0) =
          2 * hSym.d (v.succAbove (e'.symm 0)) := by
        simp_rw [show ∀ k : Fin 7, hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) *
            (if e' k = (0 : Fin 7) then (1 : ℚ) else 0) =
            if e' k = 0 then hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) else 0 from
          fun k => by split_ifs <;> ring]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        have hmem : Finset.univ.filter (fun k : Fin 7 => e' k = 0) = {e'.symm 0} := by
          ext k; simp [Finset.mem_filter, Equiv.eq_symm_apply]
        rw [hmem, Finset.sum_singleton, Equiv.apply_symm_apply]
        simp [marksE7]; ring
      rw [hcross, hresid]
      -- Need d(e'⁻¹(0)) ≤ d(u). E₇ is symmetric so all d-values on subgraph equal.
      have hedge : ∀ p q : Fin 7, p ≠ q → CartanMatrix.E₇ p q ≠ 0 →
          hSym.d (v.succAbove (e'.symm p)) = hSym.d (v.succAbove (e'.symm q)) := by
        intro p q hpq hE
        have h := hSym.sym (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))
        have hApq : A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q)) =
            CartanMatrix.E₇ p q := by rw [hsub]; simp [Equiv.apply_symm_apply]
        have hAqp : A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p)) =
            CartanMatrix.E₇ q p := by rw [hsub]; simp [Equiv.apply_symm_apply]
        have hE_sym : CartanMatrix.E₇ p q = CartanMatrix.E₇ q p := by
          have : ∀ a b : Fin 7, CartanMatrix.E₇ a b = CartanMatrix.E₇ b a := by decide
          exact this _ _
        rw [show (↑(A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))) : ℚ) =
            ↑(CartanMatrix.E₇ p q) from by push_cast; rw [hApq],
          show (↑(A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p))) : ℚ) =
            ↑(CartanMatrix.E₇ q p) from by push_cast; rw [hAqp],
          ← hE_sym] at h
        have hne : (↑(CartanMatrix.E₇ p q) : ℚ) ≠ 0 := by exact_mod_cast hE
        exact mul_right_cancel₀ hne h
      -- Chain along E₇ edges to get all d-values equal
      have h02 := hedge 0 2 (by decide) (by decide)
      have h13 := hedge 1 3 (by decide) (by decide)
      have h23 := hedge 2 3 (by decide) (by decide)
      have h34 := hedge 3 4 (by decide) (by decide)
      have h45 := hedge 4 5 (by decide) (by decide)
      have h56 := hedge 5 6 (by decide) (by decide)
      have hD_all : ∀ p : Fin 7, hSym.d (v.succAbove (e'.symm p)) =
          hSym.d (v.succAbove (e'.symm 3)) := by
        intro p; fin_cases p
        · exact h02.trans h23
        · exact h13
        · exact h23
        · rfl
        · exact h34.symm
        · exact h45.symm.trans h34.symm
        · exact h56.symm.trans (h45.symm.trans h34.symm)
      have hd0_eq_u : hSym.d (v.succAbove (e'.symm 0)) = hSym.d u := by
        rw [hD_all 0, ← hD_all (e' u_idx), e'.symm_apply_apply, hu_idx]
      -- Final algebraic bound (same structure as E₈)
      have hsym_vu := hSym.sym v u
      have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
      have hdu : 0 < hSym.d u := hSym.d_pos u
      have hdv : 0 < hSym.d v := hSym.d_pos v
      have hmj_q : (2 : ℚ) ≤ ↑mj := by exact_mod_cast hmj
      have hd0 := hSym.d_pos (v.succAbove (e'.symm 0))
      have htotal : hSym.d v * c * (2 * c + ↑(A v u) * ↑mj) +
          (c * hSym.d v * (↑(A v u) * ↑mj) + 2 * hSym.d (v.succAbove (e'.symm 0))) =
          2 * (hSym.d (v.succAbove (e'.symm 0)) +
          hSym.d v * (↑(A v u) : ℚ) ^ 2 * (1 - (↑mj : ℚ))) := by
        simp only [c]; ring
      rw [htotal]
      have hsym_vu' : hSym.d v * (↑(A v u) : ℚ) = hSym.d u * (↑(A u v) : ℚ) := by
        linarith [hsym_vu]
      have hkey : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
          hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) := by
        have : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
            (hSym.d v * (↑(A v u) : ℚ)) * (↑(A v u) : ℚ) := by ring
        rw [this, hsym_vu']; ring
      rw [hkey, hd0_eq_u]
      have hab : 1 ≤ (↑(A u v) : ℚ) * (↑(A v u) : ℚ) := by
        have := mul_le_mul_of_nonpos_left hAuv_q (show (↑(A v u) : ℚ) ≤ 0 by linarith)
        linarith
      have hdu_ab : hSym.d u ≤
          hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) :=
        le_mul_of_one_le_right (le_of_lt hdu) hab
      have hbound := mul_le_mul_of_nonpos_right hdu_ab
        (show (1 : ℚ) - (↑mj : ℚ) ≤ 0 by linarith)
      have hdu_mj : 0 ≤ hSym.d u * ((↑mj : ℚ) - 2) :=
        mul_nonneg (le_of_lt hdu) (by linarith)
      linarith
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
        have s01 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by decide
        have s10 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by decide
        refine ⟨.B 2 (by omega), Equiv.swap 0 1, fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, CartanMatrix.B_two, s01, s10] <;>
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
        have s01 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by decide
        have s10 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by decide
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, CartanMatrix.G₂, s01, s10] <;>
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
