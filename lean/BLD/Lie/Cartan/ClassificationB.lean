/- BLD Calculus — Cartan Classification: B_k extension case -/

import BLD.Lie.Cartan.F4

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

set_option maxHeartbeats 6400000 in
theorem extend_B {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3)) (u : Fin (n+3)) (huv : u ≠ v)
    (hAvu : A v u ≠ 0) (hAuv : A u v ≠ 0)
    (huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u)
    (u_idx : Fin (n+2)) (hu_idx : v.succAbove u_idx = u)
    (hcw_le2 : A v u * A u v ≤ 2) (hcw_pos : 1 ≤ A v u * A u v)
    (hAvu_neg : A v u ≤ -1) (hAuv_neg : A u v ≤ -1)
    (hAv0 : ∀ m : Fin (n+2), m ≠ u_idx → A v (v.succAbove m) = 0)
    (hAv0' : ∀ m : Fin (n+2), m ≠ u_idx → A (v.succAbove m) v = 0)
    (ht' : CartanEquiv (deleteVertex A v) (CartanMatrix.B (n+2))) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  obtain ⟨e', he'⟩ := ht'
  have hsub : ∀ i j : Fin (n+2), A (v.succAbove i) (v.succAbove j) =
      CartanMatrix.B (n+2) (e' i) (e' j) := fun i j => (he' i j).symm
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
          simp only [B_marks]
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
            simp only [he'wl, wl_pos_def, Fin.ext_iff] at h1; omega
          set wl := v.succAbove wl_idx with wl_def
          have hwl_ne_v : wl ≠ v := Fin.succAbove_ne v wl_idx
          have hwl_ne_u : wl ≠ u := fun h => hwl_ne_u_idx
            (Fin.succAbove_right_injective (hu_idx ▸ h))
          set wl2_pos : Fin (n+2) := ⟨n-1, by omega⟩ with wl2_pos_def
          set wl2_idx := e'.symm wl2_pos with wl2_idx_def
          have he'wl2 : e' wl2_idx = wl2_pos := e'.apply_symm_apply wl2_pos
          have hwl2_ne_u_idx : wl2_idx ≠ u_idx := by
            intro h; have h1 := congr_arg e' h
            simp only [he'wl2, wl2_pos_def, Fin.ext_iff] at h1; omega
          have hwl2_ne_wl_idx : wl2_idx ≠ wl_idx := by
            intro h; have h1 := congr_arg e' h
            simp only [he'wl2, he'wl, wl2_pos_def, wl_pos_def,
              Fin.ext_iff] at h1; omega
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
            simp only [he'wl3, wl3_pos_def, Fin.ext_iff] at h1; omega
          have hwl3_ne_wl_idx : wl3_idx ≠ wl_idx := by
            intro h; have h1 := congr_arg e' h
            simp only [he'wl3, he'wl, wl3_pos_def, wl_pos_def,
              Fin.ext_iff] at h1; omega
          have hwl3_ne_wl2_idx : wl3_idx ≠ wl2_idx := by
            intro h; have h1 := congr_arg e' h
            simp only [he'wl3, he'wl2, wl3_pos_def, wl2_pos_def,
              Fin.ext_iff] at h1; omega
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
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  wl_pos_def]
            split_ifs <;> omega
          have hAwl_u : A wl u = -2 := by
            rw [← hu_idx]; show A (v.succAbove wl_idx) (v.succAbove u_idx) = -2
            rw [hsub, he'wl]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  wl_pos_def]
            split_ifs <;> omega
          have hAwl_wl2 : A wl wl2 = -1 := by
            show A (v.succAbove wl_idx) (v.succAbove wl2_idx) = -1
            rw [hsub, he'wl, he'wl2]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
              wl_pos_def, wl2_pos_def]; split_ifs <;> omega
          have hAwl2_wl : A wl2 wl = -1 := by
            show A (v.succAbove wl2_idx) (v.succAbove wl_idx) = -1
            rw [hsub, he'wl2, he'wl]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
              wl2_pos_def, wl_pos_def]; split_ifs <;> omega
          have hAwl2_wl3 : A wl2 wl3 = -1 := by
            show A (v.succAbove wl2_idx) (v.succAbove wl3_idx) = -1
            rw [hsub, he'wl2, he'wl3]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
              wl2_pos_def, wl3_pos_def]; split_ifs <;> omega
          have hAwl3_wl2 : A wl3 wl2 = -1 := by
            show A (v.succAbove wl3_idx) (v.succAbove wl2_idx) = -1
            rw [hsub, he'wl3, he'wl2]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
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
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
              wl2_pos_def]; split_ifs <;> omega
          have hAu_wl3 : A u wl3 = 0 := by
            rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove wl3_idx) = 0
            rw [hsub, he'wl3]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
              wl3_pos_def]; split_ifs <;> omega
          have hAwl_wl3 : A wl wl3 = 0 := by
            show A (v.succAbove wl_idx) (v.succAbove wl3_idx) = 0
            rw [hsub, he'wl, he'wl3]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
              wl_pos_def, wl3_pos_def]; split_ifs <;> omega
          have hAwl3_u : A wl3 u = 0 := by
            rw [← hu_idx]; show A (v.succAbove wl3_idx) (v.succAbove u_idx) = 0
            rw [hsub, he'wl3]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
              wl3_pos_def]; split_ifs <;> omega
          have hAwl3_wl : A wl3 wl = 0 := by
            show A (v.succAbove wl3_idx) (v.succAbove wl_idx) = 0
            rw [hsub, he'wl3, he'wl]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
              wl3_pos_def, wl_pos_def]; split_ifs <;> omega
          have hAwl2_u : A wl2 u = 0 := by
            rw [← hu_idx]; show A (v.succAbove wl2_idx) (v.succAbove u_idx) = 0
            rw [hsub, he'wl2]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
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
          congr 1; ext; simp
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
                  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
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
            simp; omega
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
              simp only [hx_v, hx_sub]
              -- Reindex the sum
              have hsub_reindex : ∑ l, (↑(A (v.succAbove m) (v.succAbove l)) : ℚ) * ↑(fB (e' l)) =
                  ∑ q, (↑(CartanMatrix.B (n+2) (e' m) q) : ℚ) * ↑(fB q) := by
                simp_rw [fun l => show A (v.succAbove m) (v.succAbove l) =
                    CartanMatrix.B (n+2) (e' m) (e' l) from hsub m l]
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
                          simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
                          have := q.isLt; split_ifs <;> omega
                        · -- q < p-1: fB(q) = 0
                          right; show fB q = 0
                          simp only [fB]; rw [if_neg (by omega), if_neg (by omega)]
                    rcases hBq with h | h <;> simp [h])]
                -- Now: B(p-1,p-1)*fB(p-1) + B(p-1,p)*fB(p)
                -- = 2*1 + (-1)*2 = 0
                have hBq1 : CartanMatrix.B (n+2) (e' m) q1 = 2 := by
                  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  q1]
                  have := hpm1; split_ifs <;> omega
                have hBq2 : CartanMatrix.B (n+2) (e' m) q2 = -1 := by
                  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  q2]
                  have := hpm1; split_ifs <;> omega
                have hfq1 : fB q1 = 1 := by
                  simp only [fB, q1]; rw [if_pos (by omega)]
                have hfq2 : fB q2 = B_marks rr ⟨0, by omega⟩ := by
                  simp only [fB, q2]; rw [if_neg (by omega), if_pos (le_refl _)]
                  congr 1; ext; simp
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
                  have : (e' m).val = p_val := by simp [i_off] at hi0; omega
                  simp [hi0, this]; ring
                · -- i_off ≥ 1, row is interior B vertex
                  have : (e' m).val ≠ p_val := by
                    simp [i_off] at hi0; omega
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
        simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  left_pos_def]
        split_ifs <;> omega
      by_cases hpn1 : (e' u_idx).val + 1 = n + 2
      · -- p = n+1 (short root): 3-vertex {v, u, wl}, null vec [-Avu, 2, 2]
        have hAlu : A wl u = -2 := by
          rw [← hu_idx]; show A (v.succAbove left_idx) (v.succAbove u_idx) = -2
          rw [hsub, he'l]
          simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  left_pos_def]
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
          simp only [right_idx_def, e'.apply_symm_apply, right_pos_def, Fin.ext_iff] at h1; omega
        have hrl_ne : right_idx ≠ left_idx := by
          intro h; have h1 := congr_arg e' h
          simp only [right_idx_def, left_idx_def, e'.apply_symm_apply, right_pos_def,
            left_pos_def, Fin.ext_iff] at h1; omega
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
          simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  right_pos_def]
          split_ifs <;> omega
        have hAlr : A wl wr = 0 := by
          show A (v.succAbove left_idx) (v.succAbove right_idx) = 0
          rw [hsub, he'l, he'r]
          simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
            left_pos_def, right_pos_def]; split_ifs <;> omega
        have hArl : A wr wl = 0 := by
          show A (v.succAbove right_idx) (v.succAbove left_idx) = 0
          rw [hsub, he'r, he'l]
          simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, 
            right_pos_def, left_pos_def]; split_ifs <;> omega
        have hAlu : A wl u = -1 := by
          rw [← hu_idx]; show A (v.succAbove left_idx) (v.succAbove u_idx) = -1
          rw [hsub, he'l]
          simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  left_pos_def]
          split_ifs <;> omega
        by_cases hpn : (e' u_idx).val = n
        · -- p = n: A(u,right) = -2, 3-vertex {v, u, wr}, null vec [-Avu, 2, 1]
          have hAur : A u wr = -2 := by
            rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove right_idx) = -2
            rw [hsub, he'r]
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  right_pos_def]
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
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,  right_pos_def]
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
              if_neg hwl_ne_u, if_neg hwr_ne_u, if_neg hwr_ne_wl, 
              hGCM.diag u, hAul, hAur]; push_cast
            have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by rw [mul_comm]; exact_mod_cast hcw2
            linarith
          have inner_wl : ∑ j, (↑(A wl j) : ℚ) * x j = 0 := by
            rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
              hwr_ne_wl.symm (fun m => (↑(A wl m) : ℚ) * x m)
              (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A wl j)) m h1 h2 h3 h4)]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
              if_neg hwr_ne_v, if_neg hwr_ne_u, if_neg hwr_ne_wl, 
              hGCM.diag wl, hAlv, hAlu, hAlr]; push_cast; ring
          have inner_wr : ∑ j, (↑(A wr j) : ℚ) * x j = 0 := by
            rw [sum_four huv.symm hwl_ne_v.symm hwr_ne_v.symm hwl_ne_u.symm hwr_ne_u.symm
              hwr_ne_wl.symm (fun m => (↑(A wr m) : ℚ) * x m)
              (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A wr j)) m h1 h2 h3 h4)]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hwl_ne_v, if_neg hwl_ne_u,
              if_neg hwr_ne_v, if_neg hwr_ne_u, if_neg hwr_ne_wl, 
              hGCM.diag wr, hArv, hAru, hArl]; push_cast; ring
          have hq : qform hSym.d A x = 0 := by
            rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
            by_cases hiv : i = v; · subst hiv; simp [inner_v]
            by_cases hiu : i = u; · subst hiu; simp [inner_u]
            by_cases hiw1 : i = wl; · subst hiw1; simp [inner_wl]
            by_cases hiw2 : i = wr; · subst hiw2; simp [inner_wr]
            simp [x0 i hiv hiu hiw1 hiw2]
          exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))

end BLD.Lie.Cartan
