/- BLD Calculus — Cartan Classification: D_k extension case -/

import BLD.Lie.Cartan.F4

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

-- azz_zero: prove A(v.succAbove a)(v.succAbove b) = 0 for non-adjacent D_{n+2} positions.
-- Uses Dz (proved once) via convert, then discharges numeric conditions with simp+omega.
-- Expects `hu_idx`, `hsub''`, `Dz`, and `he_*` in local context.
local syntax "azz_zero" ident ident : tactic
set_option hygiene false in
macro_rules
  | `(tactic| azz_zero $a $b) => `(tactic| (
      try rw [← hu_idx]
      show A (v.succAbove $a) (v.succAbove $b) = 0
      rw [hsub'']
      convert Dz (e'' $a).val (e'' $b).val
        (by simp only [he_fv, he_ol, he_u, he_w2, he_w3, he_w4, he_w5, he_w6]; omega)
        (e'' $a).isLt (e'' $b).isLt
        (by simp only [he_fv, he_ol, he_u, he_w2, he_w3, he_w4, he_w5, he_w6]; omega)
        (by simp only [he_fv, he_ol, he_u, he_w2, he_w3, he_w4, he_w5, he_w6]; omega)
        (by simp only [he_fv, he_ol, he_u, he_w2, he_w3, he_w4, he_w5, he_w6]; omega)
        (by simp only [he_fv, he_ol, he_u, he_w2, he_w3, he_w4, he_w5, he_w6]; omega) using 2))

set_option maxHeartbeats 16000000 in
theorem extend_D {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3)) (u : Fin (n+3)) (huv : u ≠ v)
    (hAvu : A v u ≠ 0) (hAuv : A u v ≠ 0)
    (huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u)
    (u_idx : Fin (n+2)) (hu_idx : v.succAbove u_idx = u)
    (hk : 4 ≤ n + 2)
    (hcw_le2 : A v u * A u v ≤ 2) (hcw_pos : 1 ≤ A v u * A u v)
    (hAvu_neg : A v u ≤ -1) (hAuv_neg : A u v ≤ -1)
    (hAv0 : ∀ m : Fin (n+2), m ≠ u_idx → A v (v.succAbove m) = 0)
    (hAv0' : ∀ m : Fin (n+2), m ≠ u_idx → A (v.succAbove m) v = 0)
    (ht' : CartanEquiv (deleteVertex A v) (CartanMatrix.D (n+2))) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  obtain ⟨e', he'⟩ := ht'
  have hsub : ∀ i j : Fin (n+2), A (v.succAbove i) (v.succAbove j) =
      CartanMatrix.D (n+2) (e' i) (e' j) := fun i j => (he' i j).symm
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
          simp only [D_marks]
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
    -- D_{n+2} structure: path 0-1-...(n-1), fork at (n-1) to n and (n+1)
    -- Case 1: Fork vertex ((e' u_idx).val + 3 = n + 2, i.e., at position n - 1)
    by_cases hfork : (e' u_idx).val + 3 = n + 2
    · -- u maps to the fork vertex of D_{n+2}
      -- u has 3 neighbors in D: positions p-1, p+1 (=n), p+2 (=n+1)
      -- Plus v outside → degree 4 → contradiction via qform ≤ 0
      exfalso
      -- Define the 3 D-neighbors of u using concrete indices (not p)
      -- Define D-neighbors of u via inverse of e'
      let pp_idx := e'.symm (⟨n - 2, by omega⟩ : Fin (n+2))
      let fl1_idx := e'.symm (⟨n, by omega⟩ : Fin (n+2))
      let fl2_idx := e'.symm (⟨n + 1, by omega⟩ : Fin (n+2))
      let pp := v.succAbove pp_idx
      let fl1 := v.succAbove fl1_idx
      let fl2 := v.succAbove fl2_idx
      -- Entry facts: concrete Fin.mk values for equiv images
      have he_pp : e' pp_idx = ⟨n - 2, by omega⟩ := e'.apply_symm_apply _
      have he_fl1 : e' fl1_idx = ⟨n, by omega⟩ := e'.apply_symm_apply _
      have he_fl2 : e' fl2_idx = ⟨n + 1, by omega⟩ := e'.apply_symm_apply _
      have he_u : e' u_idx = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
      -- D entry proofs via D_fork_entry
      have hn2 : 2 ≤ n := by omega
      have hAu_pp : A u pp = -1 := by
        show A u (v.succAbove pp_idx) = -1; rw [← hu_idx, hsub, he_pp, he_u]
        exact D_fork_entry n hn2 _ _ (by omega) (by omega) (Or.inl ⟨rfl, Or.inl rfl⟩)
      have hAu_fl1 : A u fl1 = -1 := by
        show A u (v.succAbove fl1_idx) = -1; rw [← hu_idx, hsub, he_fl1, he_u]
        exact D_fork_entry n hn2 _ _ (by omega) (by omega) (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)
      have hAu_fl2 : A u fl2 = -1 := by
        show A u (v.succAbove fl2_idx) = -1; rw [← hu_idx, hsub, he_fl2, he_u]
        exact D_fork_entry n hn2 _ _ (by omega) (by omega) (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩)
      have hApp_u : A pp u = -1 := by
        show A (v.succAbove pp_idx) u = -1; rw [← hu_idx, hsub, he_pp, he_u]
        exact D_fork_entry n hn2 _ _ (by omega) (by omega) (Or.inr ⟨rfl, Or.inl rfl⟩)
      have hAfl1_u : A fl1 u = -1 := by
        show A (v.succAbove fl1_idx) u = -1; rw [← hu_idx, hsub, he_fl1, he_u]
        exact D_fork_entry n hn2 _ _ (by omega) (by omega) (Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩)
      have hAfl2_u : A fl2 u = -1 := by
        show A (v.succAbove fl2_idx) u = -1; rw [← hu_idx, hsub, he_fl2, he_u]
        exact D_fork_entry n hn2 _ _ (by omega) (by omega) (Or.inr ⟨rfl, Or.inr (Or.inr rfl)⟩)
      -- Distinctness of all 5 vertices {v, u, pp, fl1, fl2}
      have hppu_ne : pp_idx ≠ u_idx := by
        intro h; have := congr_arg (fun x => (e' x).val) h
        simp only [he_pp, he_u, Fin.val_mk] at this; omega
      have hfl1u_ne : fl1_idx ≠ u_idx := by
        intro h; have := congr_arg (fun x => (e' x).val) h
        simp only [he_fl1, he_u, Fin.val_mk] at this; omega
      have hfl2u_ne : fl2_idx ≠ u_idx := by
        intro h; have := congr_arg (fun x => (e' x).val) h
        simp only [he_fl2, he_u, Fin.val_mk] at this; omega
      have hpp_fl1_ne : pp_idx ≠ fl1_idx := by
        intro h; have := congr_arg (fun x => (e' x).val) h
        simp only [he_pp, he_fl1, Fin.val_mk] at this; omega
      have hpp_fl2_ne : pp_idx ≠ fl2_idx := by
        intro h; have := congr_arg (fun x => (e' x).val) h
        simp only [he_pp, he_fl2, Fin.val_mk] at this; omega
      have hfl1_fl2_ne : fl1_idx ≠ fl2_idx := by
        intro h; have := congr_arg (fun x => (e' x).val) h
        simp only [he_fl1, he_fl2, Fin.val_mk] at this; omega
      have hppv : pp ≠ v := Fin.succAbove_ne v pp_idx
      have hfl1v : fl1 ≠ v := Fin.succAbove_ne v fl1_idx
      have hfl2v : fl2 ≠ v := Fin.succAbove_ne v fl2_idx
      have hppu : pp ≠ u := fun h => hppu_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
      have hfl1u : fl1 ≠ u := fun h => hfl1u_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
      have hfl2u : fl2 ≠ u := fun h => hfl2u_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
      have hpp_fl1 : pp ≠ fl1 := fun h => hpp_fl1_ne (Fin.succAbove_right_injective h)
      have hpp_fl2 : pp ≠ fl2 := fun h => hpp_fl2_ne (Fin.succAbove_right_injective h)
      have hfl1_fl2 : fl1 ≠ fl2 := fun h => hfl1_fl2_ne (Fin.succAbove_right_injective h)
      -- v connects only to u
      have hAvpp : A v pp = 0 := by
        by_contra h; exact hppu (huniq pp hppv h)
      have hAvfl1 : A v fl1 = 0 := by
        by_contra h; exact hfl1u (huniq fl1 hfl1v h)
      have hAvfl2 : A v fl2 = 0 := by
        by_contra h; exact hfl2u (huniq fl2 hfl2v h)
      have hAppv : A pp v = 0 := (hGCM.zero_iff v pp hppv.symm).mp hAvpp
      have hAfl1v : A fl1 v = 0 := (hGCM.zero_iff v fl1 hfl1v.symm).mp hAvfl1
      have hAfl2v : A fl2 v = 0 := (hGCM.zero_iff v fl2 hfl2v.symm).mp hAvfl2
      -- Test vector: x(u) = 2, x(v) = x(pp) = x(fl1) = x(fl2) = 1, rest = 0
      set x : Fin (n+3) → ℚ := fun i =>
        if i = v then 1
        else if i = u then 2
        else if i = pp then 1
        else if i = fl1 then 1
        else if i = fl2 then 1
        else 0
      have hx : x ≠ 0 := by
        intro h; have := congr_fun h v
        simp only [x, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
      have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ pp → k ≠ fl1 → k ≠ fl2 → x k = 0 :=
        fun k h1 h2 h3 h4 h5 => by simp [x, h1, h2, h3, h4, h5]
      have hrest : ∀ (r : Fin (n+3) → ℚ) (m : Fin (n+3)),
          m ≠ v → m ≠ u → m ≠ pp → m ≠ fl1 → m ≠ fl2 → r m * x m = 0 := by
        intro r m h1 h2 h3 h4 h5; simp [x0 m h1 h2 h3 h4 h5]
      -- Inner products at each vertex
      have inner_pp : ∑ j, (↑(A pp j) : ℚ) * x j = 0 := by
        rw [sum_five huv.symm hppv.symm hfl1v.symm hfl2v.symm hppu.symm hfl1u.symm hfl2u.symm
          hpp_fl1 hpp_fl2 hfl1_fl2
          (fun m => (↑(A pp m) : ℚ) * x m)
          (fun m h1 h2 h3 h4 h5 => hrest (fun j => ↑(A pp j)) m h1 h2 h3 h4 h5)]
        simp only [x, ↓reduceIte, if_neg huv, if_neg hppv, if_neg hfl1v, if_neg hfl2v,
          if_neg hppu, if_neg hfl1u, if_neg hfl2u,  
           hGCM.diag pp, hAppv, hApp_u]; push_cast
        -- A(pp, fl1) and A(pp, fl2): pp is at position p-1, fl1 at n, fl2 at n+1
        -- Since p-1 = n-2 and n ≥ 2 (from hfork), pp is on path far from fork
        have hApp_fl1 : A pp fl1 = 0 := by
          show A (v.succAbove pp_idx) (v.succAbove fl1_idx) = 0
          rw [hsub, he_pp, he_fl1]
          exact D_fork_zero n hn2 _ _ (by omega) (by omega) (Or.inl ⟨rfl, Or.inl rfl⟩)
        have hApp_fl2 : A pp fl2 = 0 := by
          show A (v.succAbove pp_idx) (v.succAbove fl2_idx) = 0
          rw [hsub, he_pp, he_fl2]
          exact D_fork_zero n hn2 _ _ (by omega) (by omega) (Or.inl ⟨rfl, Or.inr rfl⟩)
        rw [hApp_fl1, hApp_fl2]; ring
      have inner_fl1 : ∑ j, (↑(A fl1 j) : ℚ) * x j = 0 := by
        rw [sum_five huv.symm hppv.symm hfl1v.symm hfl2v.symm hppu.symm hfl1u.symm hfl2u.symm
          hpp_fl1 hpp_fl2 hfl1_fl2
          (fun m => (↑(A fl1 m) : ℚ) * x m)
          (fun m h1 h2 h3 h4 h5 => hrest (fun j => ↑(A fl1 j)) m h1 h2 h3 h4 h5)]
        simp only [x, ↓reduceIte, if_neg huv, if_neg hppv, if_neg hfl1v, if_neg hfl2v,
          if_neg hppu, if_neg hfl1u, if_neg hfl2u,  
           if_neg hfl1_fl2.symm, if_neg hpp_fl1.symm,
          hGCM.diag fl1, hAfl1v, hAfl1_u]; push_cast
        have hAfl1_pp : A fl1 pp = 0 := by
          show A (v.succAbove fl1_idx) (v.succAbove pp_idx) = 0
          rw [hsub, he_fl1, he_pp]
          exact D_fork_zero n hn2 _ _ (by omega) (by omega) (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))
        have hAfl1_fl2 : A fl1 fl2 = 0 := by
          show A (v.succAbove fl1_idx) (v.succAbove fl2_idx) = 0
          rw [hsub, he_fl1, he_fl2]
          exact D_fork_zero n hn2 _ _ (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        rw [hAfl1_pp, hAfl1_fl2]; ring
      have inner_fl2 : ∑ j, (↑(A fl2 j) : ℚ) * x j = 0 := by
        rw [sum_five huv.symm hppv.symm hfl1v.symm hfl2v.symm hppu.symm hfl1u.symm hfl2u.symm
          hpp_fl1 hpp_fl2 hfl1_fl2
          (fun m => (↑(A fl2 m) : ℚ) * x m)
          (fun m h1 h2 h3 h4 h5 => hrest (fun j => ↑(A fl2 j)) m h1 h2 h3 h4 h5)]
        simp only [x, ↓reduceIte, if_neg huv, if_neg hppv, if_neg hfl1v, if_neg hfl2v,
          if_neg hppu, if_neg hfl1u, if_neg hfl2u,  
           if_neg hpp_fl2.symm, if_neg hfl1_fl2.symm,
          hGCM.diag fl2, hAfl2v, hAfl2_u]; push_cast
        have hAfl2_pp : A fl2 pp = 0 := by
          show A (v.succAbove fl2_idx) (v.succAbove pp_idx) = 0
          rw [hsub, he_fl2, he_pp]
          exact D_fork_zero n hn2 _ _ (by omega) (by omega) (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
        have hAfl2_fl1 : A fl2 fl1 = 0 := by
          show A (v.succAbove fl2_idx) (v.succAbove fl1_idx) = 0
          rw [hsub, he_fl2, he_fl1]
          exact D_fork_zero n hn2 _ _ (by omega) (by omega) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
        rw [hAfl2_pp, hAfl2_fl1]; ring
      -- inner_v ≤ 0: ∑ j A(v,j)*x(j) = 2 + 2*A(v,u) ≤ 0
      have inner_v_le : ∑ j, (↑(A v j) : ℚ) * x j ≤ 0 := by
        rw [sum_five huv.symm hppv.symm hfl1v.symm hfl2v.symm hppu.symm hfl1u.symm hfl2u.symm
          hpp_fl1 hpp_fl2 hfl1_fl2
          (fun m => (↑(A v m) : ℚ) * x m)
          (fun m h1 h2 h3 h4 h5 => hrest (fun j => ↑(A v j)) m h1 h2 h3 h4 h5)]
        simp only [x, ↓reduceIte, if_neg huv,
          hGCM.diag v, hAvpp, hAvfl1, hAvfl2]; push_cast
        have : (A v u : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
        linarith
      -- inner_u ≤ 0: ∑ j A(u,j)*x(j) = 1*A(u,v) + 4 - 1 - 1 - 1 = A(u,v) + 1 ≤ 0
      have inner_u_le : ∑ j, (↑(A u j) : ℚ) * x j ≤ 0 := by
        rw [sum_five huv.symm hppv.symm hfl1v.symm hfl2v.symm hppu.symm hfl1u.symm hfl2u.symm
          hpp_fl1 hpp_fl2 hfl1_fl2
          (fun m => (↑(A u m) : ℚ) * x m)
          (fun m h1 h2 h3 h4 h5 => hrest (fun j => ↑(A u j)) m h1 h2 h3 h4 h5)]
        simp only [x, ↓reduceIte, if_neg huv, if_neg hppv, if_neg hfl1v, if_neg hfl2v,
          if_neg hppu, if_neg hfl1u, if_neg hfl2u,
          if_neg hpp_fl1.symm, if_neg hpp_fl2.symm, if_neg hfl1_fl2.symm,
          hGCM.diag u, hAu_pp, hAu_fl1, hAu_fl2]; push_cast
        have : (A u v : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
        linarith
      -- qform ≤ 0 via Finset.sum_nonpos: each term d(i)*x(i)*inner(i) ≤ 0
      have hq : qform hSym.d A x ≤ 0 := by
        rw [qform_eq_sum_mul]
        apply Finset.sum_nonpos; intro i _
        rcases eq_or_ne i v with rfl | hiv
        · exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (le_of_lt (hSym.d_pos _))
              (by simp only [x, ↓reduceIte]; positivity)) inner_v_le
        rcases eq_or_ne i u with rfl | hiu
        · exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (le_of_lt (hSym.d_pos _))
              (by simp only [x, ↓reduceIte, if_neg huv]; positivity)) inner_u_le
        rcases eq_or_ne i pp with rfl | hipp
        · simp [inner_pp]
        rcases eq_or_ne i fl1 with rfl | hifl1
        · simp [inner_fl1]
        rcases eq_or_ne i fl2 with rfl | hifl2
        · simp [inner_fl2]
        · simp [x0 i hiv hiu hipp hifl1 hifl2]
      exact absurd hPD (not_posDef_of_nonpos hSym x hx hq)
    · -- Case 2 & 3: Not fork vertex, not vertex 0
      -- p := (e' u_idx).val satisfies: 1 ≤ p, p ≠ n-1, p < n+2
      by_cases hfl : n ≤ (e' u_idx).val
      · -- Fork leaf case (p = n or n+1)
        by_cases hw1 : A v u * A u v = 1
        · -- Weight 1: D₄→D₅, D₅→E₆, D₆→E₇, D₇→E₈, n≥6 contradiction
          have hAvu_eq : A v u = -1 := by nlinarith
          have hAuv_eq : A u v = -1 := by nlinarith
          -- Reduce to the case where u maps to position n (fork leaf n)
          suffices hE : ∀ e'' : Fin (n+2) ≃ Fin (n+2),
              (∀ i j, A (v.succAbove i) (v.succAbove j) =
                CartanMatrix.D (n+2) (e'' i) (e'' j)) →
              (e'' u_idx).val = n →
              ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 by
            by_cases hpn : (e' u_idx).val = n
            · exact hE e' hsub hpn
            · have hpn1 : (e' u_idx).val = n + 1 := by omega
              let sw : Fin (n+2) ≃ Fin (n+2) := Equiv.swap ⟨n, by omega⟩ ⟨n+1, by omega⟩
              have hDsw : ∀ i j : Fin (n+2),
                  CartanMatrix.D (n+2) (sw i) (sw j) = CartanMatrix.D (n+2) i j := by
                intro i j
                simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, sw]
                have hi := i.isLt; have hj := j.isLt
                by_cases hin : i = ⟨n, by omega⟩ <;>
                by_cases hin1 : i = ⟨n+1, by omega⟩ <;>
                by_cases hjn : j = ⟨n, by omega⟩ <;>
                by_cases hjn1 : j = ⟨n+1, by omega⟩ <;>
                simp_all [Equiv.swap_apply_def, Fin.ext_iff, Fin.val_mk] <;>
                split_ifs <;> omega
              exact hE (e'.trans sw)
                (fun i j => by simp only [Equiv.trans_apply]; rw [hDsw]; exact hsub i j)
                (by simp only [Equiv.trans_apply, sw, Equiv.swap_apply_def]
                    have : e' u_idx = ⟨n+1, by omega⟩ := Fin.ext hpn1
                    rw [this]; simp [Fin.ext_iff])
          intro e'' hsub'' hpn
          by_cases hn2 : n = 2
          · -- D_4 → D_5
            subst hn2
            let σ : Fin 4 ≃ Fin 4 := ⟨![2, 1, 0, 3], ![2, 1, 0, 3],
              by decide, by decide⟩
            have hDσ : ∀ i j : Fin 4,
                CartanMatrix.D 4 (σ i) (σ j) = CartanMatrix.D 4 i j := by decide
            let e3 := e''.trans σ
            have he3_u : (e3 u_idx).val = 0 := by
              simp only [e3, Equiv.trans_apply]
              have : e'' u_idx = ⟨2, by omega⟩ := Fin.ext hpn
              rw [this]; rfl
            refine ⟨DynkinType.D 5 (by omega), ?_⟩
            simp only [DynkinType.cartanMatrix]
            exact extend_at_zero hGCM v e3 (CartanMatrix.D 5)
              (by simp [CartanMatrix.D])
              (fun i j => by
                rw [D_succ_eq_D 4 (by omega)]
                simp only [e3, Equiv.trans_apply]; rw [hDσ]; exact (hsub'' i j).symm)
              (fun m => by
                rw [D_first_row 4 (by omega)]
                split_ifs with h
                · rw [show m = u_idx from
                    e3.injective (Fin.ext (by omega : (e3 m).val = (e3 u_idx).val)),
                    hu_idx, hAvu_eq]
                · rw [hAv0 m (fun heq => h (heq ▸ he3_u))])
              (fun m => by
                rw [D_first_col 4 (by omega)]
                split_ifs with h
                · rw [show m = u_idx from
                    e3.injective (Fin.ext (by omega : (e3 m).val = (e3 u_idx).val)),
                    hu_idx, hAuv_eq]
                · rw [hAv0' m (fun heq => h (heq ▸ he3_u))])
          · by_cases hn3 : n = 3
            · -- D_5 → E_6
              subst hn3
              let σ : Fin 5 ≃ Fin 5 := ⟨![4, 3, 2, 1, 0], ![4, 3, 2, 1, 0],
                by decide, by decide⟩
              have hDσ : ∀ i j : Fin 5,
                  CartanMatrix.E₆ (Fin.succ (σ i)) (Fin.succ (σ j)) =
                  CartanMatrix.D 5 i j := by decide
              let e3 := e''.trans σ
              have he3_u : (e3 u_idx).val = 1 := by
                simp only [e3, Equiv.trans_apply]
                have : e'' u_idx = ⟨3, by omega⟩ := Fin.ext hpn
                rw [this]; rfl
              have hrow : ∀ j : Fin 5, CartanMatrix.E₆ 0 (Fin.succ j) =
                  if j.val = 1 then -1 else 0 := by decide
              have hcol : ∀ j : Fin 5, CartanMatrix.E₆ (Fin.succ j) 0 =
                  if j.val = 1 then -1 else 0 := by decide
              refine ⟨DynkinType.E₆, ?_⟩
              simp only [DynkinType.cartanMatrix]
              exact extend_at_zero hGCM v e3 CartanMatrix.E₆
                (by decide)
                (fun i j => by
                  simp only [e3, Equiv.trans_apply]; rw [hDσ]; exact (hsub'' i j).symm)
                (fun m => by
                  rw [hrow]; split_ifs with h
                  · rw [show m = u_idx from
                      e3.injective (Fin.ext (by omega : (e3 m).val = (e3 u_idx).val)),
                      hu_idx, hAvu_eq]
                  · rw [hAv0 m (fun heq => h (heq ▸ he3_u))])
                (fun m => by
                  rw [hcol]; split_ifs with h
                  · rw [show m = u_idx from
                      e3.injective (Fin.ext (by omega : (e3 m).val = (e3 u_idx).val)),
                      hu_idx, hAuv_eq]
                  · rw [hAv0' m (fun heq => h (heq ▸ he3_u))])
            · by_cases hn4 : n = 4
              · -- D_6 → E_7
                subst hn4
                let σ : Fin 6 ≃ Fin 6 := ⟨![5, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0],
                  by decide, by decide⟩
                have hDσ : ∀ i j : Fin 6,
                    CartanMatrix.E₇ (Fin.succ (σ i)) (Fin.succ (σ j)) =
                    CartanMatrix.D 6 i j := by decide
                let e3 := e''.trans σ
                have he3_u : (e3 u_idx).val = 1 := by
                  simp only [e3, Equiv.trans_apply]
                  have : e'' u_idx = ⟨4, by omega⟩ := Fin.ext hpn
                  rw [this]; rfl
                have hrow : ∀ j : Fin 6, CartanMatrix.E₇ 0 (Fin.succ j) =
                    if j.val = 1 then -1 else 0 := by decide
                have hcol : ∀ j : Fin 6, CartanMatrix.E₇ (Fin.succ j) 0 =
                    if j.val = 1 then -1 else 0 := by decide
                refine ⟨DynkinType.E₇, ?_⟩
                simp only [DynkinType.cartanMatrix]
                exact extend_at_zero hGCM v e3 CartanMatrix.E₇
                  (by decide)
                  (fun i j => by
                  simp only [e3, Equiv.trans_apply]; rw [hDσ]; exact (hsub'' i j).symm)
                  (fun m => by
                    rw [hrow]; split_ifs with h
                    · rw [show m = u_idx from
                        e3.injective (Fin.ext (by omega : (e3 m).val = (e3 u_idx).val)),
                        hu_idx, hAvu_eq]
                    · rw [hAv0 m (fun heq => h (heq ▸ he3_u))])
                  (fun m => by
                    rw [hcol]; split_ifs with h
                    · rw [show m = u_idx from
                        e3.injective (Fin.ext (by omega : (e3 m).val = (e3 u_idx).val)),
                        hu_idx, hAuv_eq]
                    · rw [hAv0' m (fun heq => h (heq ▸ he3_u))])
              · by_cases hn5 : n = 5
                · -- D_7 → E_8
                  subst hn5
                  let σ : Fin 7 ≃ Fin 7 := ⟨![6, 5, 4, 3, 2, 1, 0], ![6, 5, 4, 3, 2, 1, 0],
                    by decide, by decide⟩
                  have hDσ : ∀ i j : Fin 7,
                      CartanMatrix.E₈ (Fin.succ (σ i)) (Fin.succ (σ j)) =
                      CartanMatrix.D 7 i j := by decide
                  let e3 := e''.trans σ
                  have he3_u : (e3 u_idx).val = 1 := by
                    simp only [e3, Equiv.trans_apply]
                    have : e'' u_idx = ⟨5, by omega⟩ := Fin.ext hpn
                    rw [this]; rfl
                  have hrow : ∀ j : Fin 7, CartanMatrix.E₈ 0 (Fin.succ j) =
                      if j.val = 1 then -1 else 0 := by decide
                  have hcol : ∀ j : Fin 7, CartanMatrix.E₈ (Fin.succ j) 0 =
                      if j.val = 1 then -1 else 0 := by decide
                  refine ⟨DynkinType.E₈, ?_⟩
                  simp only [DynkinType.cartanMatrix]
                  exact extend_at_zero hGCM v e3 CartanMatrix.E₈
                    (by decide)
                    (fun i j => by
                  simp only [e3, Equiv.trans_apply]; rw [hDσ]; exact (hsub'' i j).symm)
                    (fun m => by
                      rw [hrow]; split_ifs with h
                      · rw [show m = u_idx from
                          e3.injective (Fin.ext (by omega : (e3 m).val = (e3 u_idx).val)),
                          hu_idx, hAvu_eq]
                      · rw [hAv0 m (fun heq => h (heq ▸ he3_u))])
                    (fun m => by
                      rw [hcol]; split_ifs with h
                      · rw [show m = u_idx from
                          e3.injective (Fin.ext (by omega : (e3 m).val = (e3 u_idx).val)),
                          hu_idx, hAuv_eq]
                      · rw [hAv0' m (fun heq => h (heq ▸ he3_u))])
                · -- n ≥ 6: Ẽ₈ subgraph → contradiction
                  exfalso
                  have hn6 : 6 ≤ n := by omega
                  -- Define key vertex indices in D_{n+2}
                  let fv_idx := e''.symm ⟨n - 1, by omega⟩
                  let ol_idx := e''.symm ⟨n + 1, by omega⟩
                  let w2_idx := e''.symm ⟨n - 2, by omega⟩
                  let w3_idx := e''.symm ⟨n - 3, by omega⟩
                  let w4_idx := e''.symm ⟨n - 4, by omega⟩
                  let w5_idx := e''.symm ⟨n - 5, by omega⟩
                  let w6_idx := e''.symm ⟨n - 6, by omega⟩
                  let fv := v.succAbove fv_idx; let ol := v.succAbove ol_idx
                  let w2 := v.succAbove w2_idx; let w3 := v.succAbove w3_idx
                  let w4 := v.succAbove w4_idx; let w5 := v.succAbove w5_idx
                  let w6 := v.succAbove w6_idx
                  -- e'' round-trip facts
                  have he_fv : e'' fv_idx = ⟨n - 1, by omega⟩ := e''.apply_symm_apply _
                  have he_ol : e'' ol_idx = ⟨n + 1, by omega⟩ := e''.apply_symm_apply _
                  have he_w2 : e'' w2_idx = ⟨n - 2, by omega⟩ := e''.apply_symm_apply _
                  have he_w3 : e'' w3_idx = ⟨n - 3, by omega⟩ := e''.apply_symm_apply _
                  have he_w4 : e'' w4_idx = ⟨n - 4, by omega⟩ := e''.apply_symm_apply _
                  have he_w5 : e'' w5_idx = ⟨n - 5, by omega⟩ := e''.apply_symm_apply _
                  have he_w6 : e'' w6_idx = ⟨n - 6, by omega⟩ := e''.apply_symm_apply _
                  have he_u : e'' u_idx = ⟨n, by omega⟩ := Fin.ext hpn
                  -- D-zero helper: D(n+2)(p,q) = 0 when non-adjacent (proved once)
                  have Dz : ∀ (p q : ℕ) (_ : p ≠ q) (hp : p < n + 2) (hq : q < n + 2),
                      ¬(p + 1 = q ∧ q + 2 < n + 2) → ¬(q + 1 = p ∧ p + 2 < n + 2) →
                      ¬(p + 3 = n + 2 ∧ (q + 2 = n + 2 ∨ q + 1 = n + 2)) →
                      ¬(q + 3 = n + 2 ∧ (p + 2 = n + 2 ∨ p + 1 = n + 2)) →
                      CartanMatrix.D (n + 2) ⟨p, hp⟩ ⟨q, hq⟩ = 0 := by
                    intro p q h1 hp hq h2 h3 h4 h5
                    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
                    split_ifs <;> omega
                  -- Idx distinctness helper
                  have dns : ∀ (a b : Fin (n+2)), (e'' a).val ≠ (e'' b).val → a ≠ b :=
                    fun a b h hab => absurd (congrArg (fun x => (e'' x).val) hab) h
                  -- Idx-level distinctness
                  have hfvu_ne : fv_idx ≠ u_idx := dns _ _ (by simp [he_fv, he_u]; omega)
                  have holu_ne : ol_idx ≠ u_idx := dns _ _ (by simp [he_ol, he_u])
                  have hw2u_ne : w2_idx ≠ u_idx := dns _ _ (by simp [he_w2, he_u]; omega)
                  have hw3u_ne : w3_idx ≠ u_idx := dns _ _ (by simp [he_w3, he_u]; omega)
                  have hw4u_ne : w4_idx ≠ u_idx := dns _ _ (by simp [he_w4, he_u]; omega)
                  have hw5u_ne : w5_idx ≠ u_idx := dns _ _ (by simp [he_w5, he_u]; omega)
                  have hw6u_ne : w6_idx ≠ u_idx := dns _ _ (by simp [he_w6, he_u]; omega)
                  -- Vertex ≠ v
                  have hfvv : fv ≠ v := Fin.succAbove_ne v fv_idx
                  have holv : ol ≠ v := Fin.succAbove_ne v ol_idx
                  have hw2v : w2 ≠ v := Fin.succAbove_ne v w2_idx
                  have hw3v : w3 ≠ v := Fin.succAbove_ne v w3_idx
                  have hw4v : w4 ≠ v := Fin.succAbove_ne v w4_idx
                  have hw5v : w5 ≠ v := Fin.succAbove_ne v w5_idx
                  have hw6v : w6 ≠ v := Fin.succAbove_ne v w6_idx
                  -- Vertex ≠ u
                  have hfvu : fv ≠ u := fun h => hfvu_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
                  have holu : ol ≠ u := fun h => holu_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
                  have hw2u : w2 ≠ u := fun h => hw2u_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
                  have hw3u : w3 ≠ u := fun h => hw3u_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
                  have hw4u : w4 ≠ u := fun h => hw4u_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
                  have hw5u : w5 ≠ u := fun h => hw5u_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
                  have hw6u : w6 ≠ u := fun h => hw6u_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
                  -- Vertex-vertex helper
                  have vne : ∀ (a b : Fin (n+2)), (e'' a).val ≠ (e'' b).val →
                      v.succAbove a ≠ v.succAbove b :=
                    fun a b h hab => absurd (congrArg (fun x => (e'' x).val)
                      (Fin.succAbove_right_injective hab)) h
                  -- Key vertex distinctness (for sum_N calls)
                  have hfv_ol : fv ≠ ol := vne _ _ (by simp [he_fv, he_ol])
                  have hfv_w2 : fv ≠ w2 := vne _ _ (by simp [he_fv, he_w2]; omega)
                  have hfv_w3 : fv ≠ w3 := vne _ _ (by simp [he_fv, he_w3]; omega)
                  have hol_w2 : ol ≠ w2 := vne _ _ (by simp [he_ol, he_w2]; omega)
                  have hw2_w3 : w2 ≠ w3 := vne _ _ (by simp [he_w2, he_w3]; omega)
                  have hw2_w4 : w2 ≠ w4 := vne _ _ (by simp [he_w2, he_w4]; omega)
                  have hw3_w4 : w3 ≠ w4 := vne _ _ (by simp [he_w3, he_w4]; omega)
                  have hw3_w5 : w3 ≠ w5 := vne _ _ (by simp [he_w3, he_w5]; omega)
                  have hw4_w5 : w4 ≠ w5 := vne _ _ (by simp [he_w4, he_w5]; omega)
                  have hw4_w6 : w4 ≠ w6 := vne _ _ (by simp [he_w4, he_w6]; omega)
                  have hw5_w6 : w5 ≠ w6 := vne _ _ (by simp [he_w5, he_w6]; omega)
                  have hfv_w4 : fv ≠ w4 := vne _ _ (by simp [he_fv, he_w4]; omega)
                  have hfv_w5 : fv ≠ w5 := vne _ _ (by simp [he_fv, he_w5]; omega)
                  have hfv_w6 : fv ≠ w6 := vne _ _ (by simp [he_fv, he_w6]; omega)
                  have hol_w3 : ol ≠ w3 := vne _ _ (by simp [he_ol, he_w3]; omega)
                  have hol_w4 : ol ≠ w4 := vne _ _ (by simp [he_ol, he_w4]; omega)
                  have hol_w5 : ol ≠ w5 := vne _ _ (by simp [he_ol, he_w5]; omega)
                  have hol_w6 : ol ≠ w6 := vne _ _ (by simp [he_ol, he_w6]; omega)
                  have hw2_w5 : w2 ≠ w5 := vne _ _ (by simp [he_w2, he_w5]; omega)
                  have hw2_w6 : w2 ≠ w6 := vne _ _ (by simp [he_w2, he_w6]; omega)
                  have hw3_w6 : w3 ≠ w6 := vne _ _ (by simp [he_w3, he_w6]; omega)
                  -- Adjacency facts (A = -1)
                  have hAu_fv : A u fv = -1 := by
                    rw [← hu_idx]
                    show A (v.succAbove u_idx) (v.succAbove fv_idx) = -1
                    rw [hsub'', he_u, he_fv]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAfv_u : A fv u = -1 := by
                    rw [← hu_idx]
                    show A (v.succAbove fv_idx) (v.succAbove u_idx) = -1
                    rw [hsub'', he_fv, he_u]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAfv_w2 : A fv w2 = -1 := by
                    show A (v.succAbove fv_idx) (v.succAbove w2_idx) = -1
                    rw [hsub'', he_fv, he_w2]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAfv_ol : A fv ol = -1 := by
                    show A (v.succAbove fv_idx) (v.succAbove ol_idx) = -1
                    rw [hsub'', he_fv, he_ol]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw2_fv : A w2 fv = -1 := by
                    show A (v.succAbove w2_idx) (v.succAbove fv_idx) = -1
                    rw [hsub'', he_w2, he_fv]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw2_w3 : A w2 w3 = -1 := by
                    show A (v.succAbove w2_idx) (v.succAbove w3_idx) = -1
                    rw [hsub'', he_w2, he_w3]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw3_w2 : A w3 w2 = -1 := by
                    show A (v.succAbove w3_idx) (v.succAbove w2_idx) = -1
                    rw [hsub'', he_w3, he_w2]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw3_w4 : A w3 w4 = -1 := by
                    show A (v.succAbove w3_idx) (v.succAbove w4_idx) = -1
                    rw [hsub'', he_w3, he_w4]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw4_w3 : A w4 w3 = -1 := by
                    show A (v.succAbove w4_idx) (v.succAbove w3_idx) = -1
                    rw [hsub'', he_w4, he_w3]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw4_w5 : A w4 w5 = -1 := by
                    show A (v.succAbove w4_idx) (v.succAbove w5_idx) = -1
                    rw [hsub'', he_w4, he_w5]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw5_w4 : A w5 w4 = -1 := by
                    show A (v.succAbove w5_idx) (v.succAbove w4_idx) = -1
                    rw [hsub'', he_w5, he_w4]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw5_w6 : A w5 w6 = -1 := by
                    show A (v.succAbove w5_idx) (v.succAbove w6_idx) = -1
                    rw [hsub'', he_w5, he_w6]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAw6_w5 : A w6 w5 = -1 := by
                    show A (v.succAbove w6_idx) (v.succAbove w5_idx) = -1
                    rw [hsub'', he_w6, he_w5]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  have hAol_fv : A ol fv = -1 := by
                    show A (v.succAbove ol_idx) (v.succAbove fv_idx) = -1
                    rw [hsub'', he_ol, he_fv]
                    simp [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
                  -- A(v, X) = 0 for X ≠ u, and A(X, v) = 0 for X ≠ u
                  have hAvfv : A v fv = 0 := hAv0 fv_idx hfvu_ne
                  have hAvol : A v ol = 0 := hAv0 ol_idx holu_ne
                  have hAvw2 : A v w2 = 0 := hAv0 w2_idx hw2u_ne
                  have hAvw3 : A v w3 = 0 := hAv0 w3_idx hw3u_ne
                  have hAvw4 : A v w4 = 0 := hAv0 w4_idx hw4u_ne
                  have hAvw5 : A v w5 = 0 := hAv0 w5_idx hw5u_ne
                  have hAvw6 : A v w6 = 0 := hAv0 w6_idx hw6u_ne
                  have hAfvv : A fv v = 0 := hAv0' fv_idx hfvu_ne
                  have hAolv : A ol v = 0 := hAv0' ol_idx holu_ne
                  have hAw2v : A w2 v = 0 := hAv0' w2_idx hw2u_ne
                  have hAw3v : A w3 v = 0 := hAv0' w3_idx hw3u_ne
                  have hAw4v : A w4 v = 0 := hAv0' w4_idx hw4u_ne
                  have hAw5v : A w5 v = 0 := hAv0' w5_idx hw5u_ne
                  have hAw6v : A w6 v = 0 := hAv0' w6_idx hw6u_ne
                  -- Non-adjacent zero entries (via azz_zero)
                  -- u non-adjacent pairs (u at pos n, only connects to fv at n-1)
                  have hAu_ol : A u ol = 0 := by azz_zero u_idx ol_idx
                  have hAu_w2 : A u w2 = 0 := by azz_zero u_idx w2_idx
                  have hAu_w3 : A u w3 = 0 := by azz_zero u_idx w3_idx
                  have hAu_w4 : A u w4 = 0 := by azz_zero u_idx w4_idx
                  have hAu_w5 : A u w5 = 0 := by azz_zero u_idx w5_idx
                  have hAu_w6 : A u w6 = 0 := by azz_zero u_idx w6_idx
                  -- fv non-adjacent pairs (fv at n-1, connects to u, w2, ol)
                  have hAfv_w3 : A fv w3 = 0 := by azz_zero fv_idx w3_idx
                  have hAfv_w4 : A fv w4 = 0 := by azz_zero fv_idx w4_idx
                  have hAfv_w5 : A fv w5 = 0 := by azz_zero fv_idx w5_idx
                  have hAfv_w6 : A fv w6 = 0 := by azz_zero fv_idx w6_idx
                  -- ol non-adjacent pairs (ol at n+1, connects to fv)
                  have hAol_u : A ol u = 0 := by azz_zero ol_idx u_idx
                  have hAol_w2 : A ol w2 = 0 := by azz_zero ol_idx w2_idx
                  have hAol_w3 : A ol w3 = 0 := by azz_zero ol_idx w3_idx
                  have hAol_w4 : A ol w4 = 0 := by azz_zero ol_idx w4_idx
                  have hAol_w5 : A ol w5 = 0 := by azz_zero ol_idx w5_idx
                  have hAol_w6 : A ol w6 = 0 := by azz_zero ol_idx w6_idx
                  -- w2 non-adjacent pairs (w2 at n-2, connects to fv, w3)
                  have hAw2_u : A w2 u = 0 := by azz_zero w2_idx u_idx
                  have hAw2_ol : A w2 ol = 0 := by azz_zero w2_idx ol_idx
                  have hAw2_w4 : A w2 w4 = 0 := by azz_zero w2_idx w4_idx
                  have hAw2_w5 : A w2 w5 = 0 := by azz_zero w2_idx w5_idx
                  have hAw2_w6 : A w2 w6 = 0 := by azz_zero w2_idx w6_idx
                  -- w3 non-adjacent pairs (w3 at n-3, connects to w2, w4)
                  have hAw3_u : A w3 u = 0 := by azz_zero w3_idx u_idx
                  have hAw3_fv : A w3 fv = 0 := by azz_zero w3_idx fv_idx
                  have hAw3_ol : A w3 ol = 0 := by azz_zero w3_idx ol_idx
                  have hAw3_w5 : A w3 w5 = 0 := by azz_zero w3_idx w5_idx
                  have hAw3_w6 : A w3 w6 = 0 := by azz_zero w3_idx w6_idx
                  -- w4 non-adjacent pairs (w4 at n-4, connects to w3, w5)
                  have hAw4_u : A w4 u = 0 := by azz_zero w4_idx u_idx
                  have hAw4_fv : A w4 fv = 0 := by azz_zero w4_idx fv_idx
                  have hAw4_ol : A w4 ol = 0 := by azz_zero w4_idx ol_idx
                  have hAw4_w2 : A w4 w2 = 0 := by azz_zero w4_idx w2_idx
                  have hAw4_w6 : A w4 w6 = 0 := by azz_zero w4_idx w6_idx
                  -- w5 non-adjacent pairs (w5 at n-5, connects to w4, w6)
                  have hAw5_u : A w5 u = 0 := by azz_zero w5_idx u_idx
                  have hAw5_fv : A w5 fv = 0 := by azz_zero w5_idx fv_idx
                  have hAw5_ol : A w5 ol = 0 := by azz_zero w5_idx ol_idx
                  have hAw5_w2 : A w5 w2 = 0 := by azz_zero w5_idx w2_idx
                  have hAw5_w3 : A w5 w3 = 0 := by azz_zero w5_idx w3_idx
                  -- w6 non-adjacent pairs (w6 at n-6, connects to w5)
                  have hAw6_u : A w6 u = 0 := by azz_zero w6_idx u_idx
                  have hAw6_fv : A w6 fv = 0 := by azz_zero w6_idx fv_idx
                  have hAw6_ol : A w6 ol = 0 := by azz_zero w6_idx ol_idx
                  have hAw6_w2 : A w6 w2 = 0 := by azz_zero w6_idx w2_idx
                  have hAw6_w3 : A w6 w3 = 0 := by azz_zero w6_idx w3_idx
                  have hAw6_w4 : A w6 w4 = 0 := by azz_zero w6_idx w4_idx
                  -- Test vector
                  set x : Fin (n+3) → ℚ := fun j =>
                    if j = v then 2 else if j = u then 4 else if j = fv then 6
                    else if j = ol then 3 else if j = w2 then 5 else if j = w3 then 4
                    else if j = w4 then 3 else if j = w5 then 2 else if j = w6 then 1 else 0
                  have hx : x ≠ 0 := by
                    intro h; have := congr_fun h u
                    simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
                  have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ fv → k ≠ ol → k ≠ w2 → k ≠ w3 →
                      k ≠ w4 → k ≠ w5 → k ≠ w6 → x k = 0 :=
                    fun k h1 h2 h3 h4 h5 h6 h7 h8 h9 => by simp [x, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                  -- Per-vertex product-zero
                  have hPv : ∀ m, m ≠ v → m ≠ u → (↑(A v m) : ℚ) * x m = 0 := by
                    intro m hv' hu'
                    rcases Fin.eq_self_or_eq_succAbove v m with rfl | ⟨m', rfl⟩
                    · exact absurd rfl hv'
                    · by_cases hm : m' = u_idx
                      · exact absurd (hm ▸ hu_idx) hu'
                      · simp [hAv0 m' hm]
                  have hPu : ∀ m, m ≠ v → m ≠ u → m ≠ fv → (↑(A u m) : ℚ) * x m = 0 := by
                    intro m hv' hu' hfv'
                    by_cases hol' : m = ol; · simp [hol', hAu_ol]
                    by_cases hw2' : m = w2; · simp [hw2', hAu_w2]
                    by_cases hw3' : m = w3; · simp [hw3', hAu_w3]
                    by_cases hw4' : m = w4; · simp [hw4', hAu_w4]
                    by_cases hw5' : m = w5; · simp [hw5', hAu_w5]
                    by_cases hw6' : m = w6; · simp [hw6', hAu_w6]
                    simp [x0 m hv' hu' hfv' hol' hw2' hw3' hw4' hw5' hw6']
                  have hPfv : ∀ m, m ≠ fv → m ≠ u → m ≠ w2 → m ≠ ol →
                      (↑(A fv m) : ℚ) * x m = 0 := by
                    intro m hfv' hu' hw2' hol'
                    by_cases hv' : m = v; · simp [hv', hAfvv]
                    by_cases hw3' : m = w3; · simp [hw3', hAfv_w3]
                    by_cases hw4' : m = w4; · simp [hw4', hAfv_w4]
                    by_cases hw5' : m = w5; · simp [hw5', hAfv_w5]
                    by_cases hw6' : m = w6; · simp [hw6', hAfv_w6]
                    simp [x0 m hv' hu' hfv' hol' hw2' hw3' hw4' hw5' hw6']
                  have hPol : ∀ m, m ≠ ol → m ≠ fv → (↑(A ol m) : ℚ) * x m = 0 := by
                    intro m hol' hfv'
                    by_cases hv' : m = v; · simp [hv', hAolv]
                    by_cases hu' : m = u; · simp [hu', hAol_u]
                    by_cases hw2' : m = w2; · simp [hw2', hAol_w2]
                    by_cases hw3' : m = w3; · simp [hw3', hAol_w3]
                    by_cases hw4' : m = w4; · simp [hw4', hAol_w4]
                    by_cases hw5' : m = w5; · simp [hw5', hAol_w5]
                    by_cases hw6' : m = w6; · simp [hw6', hAol_w6]
                    simp [x0 m hv' hu' hfv' hol' hw2' hw3' hw4' hw5' hw6']
                  -- w2's product-zero (connects to fv, w3)
                  have hPw2 : ∀ m, m ≠ w2 → m ≠ fv → m ≠ w3 → (↑(A w2 m) : ℚ) * x m = 0 := by
                    intro m hw2' hfv' hw3'
                    by_cases hv' : m = v; · simp [hv', hAw2v]
                    by_cases hu' : m = u; · simp [hu', hAw2_u]
                    by_cases hol' : m = ol; · simp [hol', hAw2_ol]
                    by_cases hw4' : m = w4; · simp [hw4', hAw2_w4]
                    by_cases hw5' : m = w5; · simp [hw5', hAw2_w5]
                    by_cases hw6' : m = w6; · simp [hw6', hAw2_w6]
                    simp [x0 m hv' hu' hfv' hol' hw2' hw3' hw4' hw5' hw6']
                  -- w3 product-zero (connects to w2, w4)
                  have hPw3 : ∀ m, m ≠ w3 → m ≠ w2 → m ≠ w4 → (↑(A w3 m) : ℚ) * x m = 0 := by
                    intro m hw3' hw2' hw4'
                    by_cases hv' : m = v; · simp [hv', hAw3v]
                    by_cases hu' : m = u; · simp [hu', hAw3_u]
                    by_cases hfv' : m = fv; · simp [hfv', hAw3_fv]
                    by_cases hol' : m = ol; · simp [hol', hAw3_ol]
                    by_cases hw5' : m = w5; · simp [hw5', hAw3_w5]
                    by_cases hw6' : m = w6; · simp [hw6', hAw3_w6]
                    simp [x0 m hv' hu' hfv' hol' hw2' hw3' hw4' hw5' hw6']
                  -- w4 product-zero (connects to w3, w5)
                  have hPw4 : ∀ m, m ≠ w4 → m ≠ w3 → m ≠ w5 → (↑(A w4 m) : ℚ) * x m = 0 := by
                    intro m hw4' hw3' hw5'
                    by_cases hv' : m = v; · simp [hv', hAw4v]
                    by_cases hu' : m = u; · simp [hu', hAw4_u]
                    by_cases hfv' : m = fv; · simp [hfv', hAw4_fv]
                    by_cases hol' : m = ol; · simp [hol', hAw4_ol]
                    by_cases hw2' : m = w2; · simp [hw2', hAw4_w2]
                    by_cases hw6' : m = w6; · simp [hw6', hAw4_w6]
                    simp [x0 m hv' hu' hfv' hol' hw2' hw3' hw4' hw5' hw6']
                  -- w5 product-zero (connects to w4, w6)
                  have hPw5 : ∀ m, m ≠ w5 → m ≠ w4 → m ≠ w6 → (↑(A w5 m) : ℚ) * x m = 0 := by
                    intro m hw5' hw4' hw6'
                    by_cases hv' : m = v; · simp [hv', hAw5v]
                    by_cases hu' : m = u; · simp [hu', hAw5_u]
                    by_cases hfv' : m = fv; · simp [hfv', hAw5_fv]
                    by_cases hol' : m = ol; · simp [hol', hAw5_ol]
                    by_cases hw2' : m = w2; · simp [hw2', hAw5_w2]
                    by_cases hw3' : m = w3; · simp [hw3', hAw5_w3]
                    simp [x0 m hv' hu' hfv' hol' hw2' hw3' hw4' hw5' hw6']
                  -- w6 product-zero (connects to w5; w7 unnamed but x(w7)=0)
                  have hPw6 : ∀ m, m ≠ w6 → m ≠ w5 → (↑(A w6 m) : ℚ) * x m = 0 := by
                    intro m hw6' hw5'
                    by_cases hv' : m = v; · simp [hv', hAw6v]
                    by_cases hu' : m = u; · simp [hu', hAw6_u]
                    by_cases hfv' : m = fv; · simp [hfv', hAw6_fv]
                    by_cases hol' : m = ol; · simp [hol', hAw6_ol]
                    by_cases hw2' : m = w2; · simp [hw2', hAw6_w2]
                    by_cases hw3' : m = w3; · simp [hw3', hAw6_w3]
                    by_cases hw4' : m = w4; · simp [hw4', hAw6_w4]
                    simp [x0 m hv' hu' hfv' hol' hw2' hw3' hw4' hw5' hw6']
                  -- Inner products via sum_two/sum_three/sum_four
                  have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
                    rw [sum_two huv.symm (fun m => (↑(A v m) : ℚ) * x m) hPv]
                    simp [x, hGCM.diag, hAvu_eq, if_neg huv]; ring
                  have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
                    rw [sum_three huv.symm hfvv.symm hfvu.symm
                      (fun m => (↑(A u m) : ℚ) * x m) hPu]
                    simp [x, hGCM.diag, hAuv_eq, hAu_fv,
                      if_neg huv, if_neg hfvv, if_neg hfvu]; ring
                  have inner_fv : ∑ j, (↑(A fv j) : ℚ) * x j = 0 := by
                    rw [sum_four hfvu hfv_w2 hfv_ol hw2u.symm holu.symm hol_w2.symm
                      (fun m => (↑(A fv m) : ℚ) * x m) hPfv]
                    simp [x, hGCM.diag, hAfv_u, hAfv_w2, hAfv_ol,
                      if_neg huv, if_neg hfvv, if_neg hfvu,
                      if_neg holv, if_neg holu, if_neg hfv_ol.symm,
                      if_neg hw2v, if_neg hw2u, if_neg hfv_w2.symm,
                      if_neg hol_w2.symm]; ring
                  have inner_ol : ∑ j, (↑(A ol j) : ℚ) * x j = 0 := by
                    rw [sum_two hfv_ol.symm (fun m => (↑(A ol m) : ℚ) * x m) hPol]
                    simp [x, hGCM.diag, hAol_fv,
                      if_neg holv, if_neg holu, if_neg hfv_ol.symm,
                      if_neg hfvv, if_neg hfvu]; ring
                  have inner_w2 : ∑ j, (↑(A w2 j) : ℚ) * x j = 0 := by
                    rw [sum_three hfv_w2.symm hw2_w3 hfv_w3
                      (fun m => (↑(A w2 m) : ℚ) * x m) hPw2]
                    simp [x, hGCM.diag, hAw2_fv, hAw2_w3,
                      if_neg hw2v, if_neg hw2u, if_neg hfv_w2.symm, if_neg hol_w2.symm,
                      if_neg hfvv, if_neg hfvu,
                      if_neg hw3v,  if_neg hfv_w3.symm,
                      if_neg hol_w3.symm, if_neg hw2_w3.symm]; ring
                  have inner_w3 : ∑ j, (↑(A w3 j) : ℚ) * x j = 0 := by
                    rw [sum_three hw2_w3.symm hw3_w4 hw2_w4
                      (fun m => (↑(A w3 m) : ℚ) * x m) hPw3]
                    simp [x, hGCM.diag, hAw3_w2, hAw3_w4,
                      if_neg hw3v,  if_neg hfv_w3.symm,
                      if_neg hol_w3.symm, if_neg hw2_w3.symm,
                      if_neg hw2v, if_neg hw2u, if_neg hfv_w2.symm, if_neg hol_w2.symm,
                      if_neg hw4v, if_neg hw4u, if_neg hfv_w4.symm,
                       if_neg hw2_w4.symm,
                      if_neg hw3_w4.symm]; ring
                  have inner_w4 : ∑ j, (↑(A w4 j) : ℚ) * x j = 0 := by
                    rw [sum_three hw3_w4.symm hw4_w5 hw3_w5
                      (fun m => (↑(A w4 m) : ℚ) * x m) hPw4]
                    simp [x, hGCM.diag, hAw4_w3, hAw4_w5,
                      if_neg hw4v, if_neg hw4u, if_neg hfv_w4.symm,
                       if_neg hw2_w4.symm, if_neg hw3_w4.symm,
                      if_neg hw3v,  if_neg hfv_w3.symm,
                      if_neg hol_w3.symm, if_neg hw2_w3.symm,
                      if_neg hw5v, if_neg hw5u, if_neg hfv_w5.symm,
                      if_neg hol_w5.symm, if_neg hw2_w5.symm,
                      if_neg hw3_w5.symm, if_neg hw4_w5.symm]; ring
                  have inner_w5 : ∑ j, (↑(A w5 j) : ℚ) * x j = 0 := by
                    rw [sum_three hw4_w5.symm hw5_w6 hw4_w6
                      (fun m => (↑(A w5 m) : ℚ) * x m) hPw5]
                    simp [x, hGCM.diag, hAw5_w4, hAw5_w6,
                      if_neg hw5v, if_neg hw5u, if_neg hfv_w5.symm,
                      if_neg hol_w5.symm, if_neg hw2_w5.symm,
                      if_neg hw3_w5.symm, if_neg hw4_w5.symm,
                      if_neg hw4v, if_neg hw4u, if_neg hfv_w4.symm,
                       if_neg hw2_w4.symm, if_neg hw3_w4.symm,
                      if_neg hw6v, if_neg hw6u, if_neg hfv_w6.symm,
                      if_neg hol_w6.symm, if_neg hw2_w6.symm,
                      if_neg hw3_w6.symm, if_neg hw4_w6.symm,
                      if_neg hw5_w6.symm]; ring
                  have inner_w6 : ∑ j, (↑(A w6 j) : ℚ) * x j = 0 := by
                    rw [sum_two hw5_w6.symm (fun m => (↑(A w6 m) : ℚ) * x m) hPw6]
                    simp [x, hGCM.diag, hAw6_w5,
                      if_neg hw6v, if_neg hw6u, if_neg hfv_w6.symm,
                      if_neg hol_w6.symm, if_neg hw2_w6.symm,
                      if_neg hw3_w6.symm, if_neg hw4_w6.symm, if_neg hw5_w6.symm,
                      if_neg hw5v, if_neg hw5u, if_neg hfv_w5.symm,
                      if_neg hol_w5.symm, if_neg hw2_w5.symm,
                      if_neg hw3_w5.symm, if_neg hw4_w5.symm]
                  -- Combine: qform = 0 → contradiction
                  have hq : qform hSym.d A x = 0 := by
                    apply qform_zero_of_null; intro k
                    rcases Fin.eq_self_or_eq_succAbove v k with rfl | ⟨m, rfl⟩
                    · right; exact inner_v
                    · by_cases hmu : v.succAbove m = u; · right; rw [hmu]; exact inner_u
                      by_cases hmfv : v.succAbove m = fv; · right; rw [hmfv]; exact inner_fv
                      by_cases hmol : v.succAbove m = ol; · right; rw [hmol]; exact inner_ol
                      by_cases hmw2 : v.succAbove m = w2; · right; rw [hmw2]; exact inner_w2
                      by_cases hmw3 : v.succAbove m = w3; · right; rw [hmw3]; exact inner_w3
                      by_cases hmw4 : v.succAbove m = w4; · right; rw [hmw4]; exact inner_w4
                      by_cases hmw5 : v.succAbove m = w5; · right; rw [hmw5]; exact inner_w5
                      by_cases hmw6 : v.succAbove m = w6; · right; rw [hmw6]; exact inner_w6
                      left; exact x0 _ (Fin.succAbove_ne v m) hmu hmfv hmol hmw2 hmw3 hmw4 hmw5 hmw6
                  exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
        · -- Weight 2 at fork leaf → contradiction
          exfalso
          have hcw2 : A v u * A u v = 2 := by omega
          have hpn : (e' u_idx).val = n ∨ (e' u_idx).val = n + 1 := by omega
          -- Fork vertex (n-1), other fork leaf, path predecessor (n-2)
          let fv_idx := e'.symm ⟨n - 1, by omega⟩
          let ol_idx := e'.symm ⟨if (e' u_idx).val = n then n + 1 else n,
            by split_ifs <;> omega⟩
          let pp_idx := e'.symm ⟨n - 2, by omega⟩
          let fv := v.succAbove fv_idx
          let ol := v.succAbove ol_idx
          let pp := v.succAbove pp_idx
          have he_fv : e' fv_idx = ⟨n - 1, by omega⟩ := e'.apply_symm_apply _
          have he_ol : e' ol_idx = ⟨if (e' u_idx).val = n then n + 1 else n,
              by split_ifs <;> omega⟩ :=
            e'.apply_symm_apply _
          have he_pp : e' pp_idx = ⟨n - 2, by omega⟩ := e'.apply_symm_apply _
          -- Index distinctness
          have hfv_ne : fv_idx ≠ u_idx := by
            intro h; have := congr_arg (fun x => (e' x).val) h
            simp only [he_fv, Fin.val_mk] at this
            rcases hpn with hp | hp <;> omega
          have hol_ne : ol_idx ≠ u_idx := by
            intro h; have := congr_arg (fun x => (e' x).val) h
            simp only [he_ol, Fin.val_mk] at this
            split_ifs at this <;> omega
          have hol_ne_fv : ol_idx ≠ fv_idx := by
            intro h; have := congr_arg (fun x => (e' x).val) h
            simp only [he_ol, he_fv, Fin.val_mk] at this
            split_ifs at this <;> omega
          have hpp_ne : pp_idx ≠ u_idx := by
            intro h; have := congr_arg (fun x => (e' x).val) h
            simp only [he_pp, Fin.val_mk] at this
            rcases hpn with hp | hp <;> omega
          have hpp_ne_fv : pp_idx ≠ fv_idx := by
            intro h; have := congr_arg (fun x => (e' x).val) h
            simp only [he_pp, he_fv, Fin.val_mk] at this; omega
          have hpp_ne_ol : pp_idx ≠ ol_idx := by
            intro h; have := congr_arg (fun x => (e' x).val) h
            simp only [he_pp, he_ol, Fin.val_mk] at this
            split_ifs at this <;> omega
          -- Vertex distinctness
          have hfv_v : fv ≠ v := Fin.succAbove_ne v fv_idx
          have hfv_u : fv ≠ u := fun h => hfv_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
          have hol_v : ol ≠ v := Fin.succAbove_ne v ol_idx
          have hol_u : ol ≠ u := fun h => hol_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
          have hol_fv : ol ≠ fv := fun h => hol_ne_fv (Fin.succAbove_right_injective h)
          have hpp_v : pp ≠ v := Fin.succAbove_ne v pp_idx
          have hpp_u : pp ≠ u := fun h => hpp_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
          have hpp_fv : pp ≠ fv := fun h => hpp_ne_fv (Fin.succAbove_right_injective h)
          have hpp_ol : pp ≠ ol := fun h => hpp_ne_ol (Fin.succAbove_right_injective h)
          -- Adjacency: fork edges (all -1 in D)
          have hAu_fv : A u fv = -1 := by
            rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove fv_idx) = -1
            rw [hsub, he_fv]; simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> rw [hp] <;> split_ifs <;> omega
          have hAfv_u : A fv u = -1 := by
            rw [← hu_idx]; show A (v.succAbove fv_idx) (v.succAbove u_idx) = -1
            rw [hsub, he_fv]; simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> rw [hp] <;> split_ifs <;> omega
          have hAfv_ol : A fv ol = -1 := by
            show A (v.succAbove fv_idx) (v.succAbove ol_idx) = -1
            rw [hsub, he_fv, he_ol]
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> simp [hp] <;> split_ifs <;> omega
          have hAol_fv : A ol fv = -1 := by
            show A (v.succAbove ol_idx) (v.succAbove fv_idx) = -1
            rw [hsub, he_ol, he_fv]
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> simp [hp] <;> split_ifs <;> omega
          have hAfv_pp : A fv pp = -1 := by
            show A (v.succAbove fv_idx) (v.succAbove pp_idx) = -1
            rw [hsub, he_fv, he_pp]
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            split_ifs <;> omega
          have hApp_fv : A pp fv = -1 := by
            show A (v.succAbove pp_idx) (v.succAbove fv_idx) = -1
            rw [hsub, he_pp, he_fv]
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            split_ifs <;> omega
          -- Zero entries
          have hAvfv : A v fv = 0 := hAv0 fv_idx hfv_ne
          have hAvol : A v ol = 0 := hAv0 ol_idx hol_ne
          have hAvpp : A v pp = 0 := hAv0 pp_idx hpp_ne
          have hAfvv : A fv v = 0 := hAv0' fv_idx hfv_ne
          have hAolv : A ol v = 0 := hAv0' ol_idx hol_ne
          have hAppv : A pp v = 0 := hAv0' pp_idx hpp_ne
          have hAu_ol : A u ol = 0 := by
            rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove ol_idx) = 0
            rw [hsub, he_ol]; simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> simp [hp]
          have hAu_pp : A u pp = 0 := by
            rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove pp_idx) = 0
            rw [hsub, he_pp]; simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> rw [hp] <;> split_ifs <;> omega
          have hAol_u : A ol u = 0 := by
            rw [← hu_idx]; show A (v.succAbove ol_idx) (v.succAbove u_idx) = 0
            rw [hsub, he_ol]; simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> simp [hp]
          have hAol_pp : A ol pp = 0 := by
            show A (v.succAbove ol_idx) (v.succAbove pp_idx) = 0
            rw [hsub, he_ol, he_pp]
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> simp [hp] <;> split_ifs <;> omega
          have hApp_u : A pp u = 0 := by
            rw [← hu_idx]; show A (v.succAbove pp_idx) (v.succAbove u_idx) = 0
            rw [hsub, he_pp]; simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> rw [hp] <;> split_ifs <;> omega
          have hApp_ol : A pp ol = 0 := by
            show A (v.succAbove pp_idx) (v.succAbove ol_idx) = 0
            rw [hsub, he_pp, he_ol]
            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
            rcases hpn with hp | hp <;> simp [hp] <;> split_ifs <;> omega
          -- Test vector: [-A(v,u), 2, 2, 1, 1] on {v, u, fv, ol, pp}
          set x : Fin (n+3) → ℚ := fun i =>
            if i = v then -(↑(A v u : ℤ) : ℚ) else if i = u then 2
            else if i = fv then 2 else if i = ol then 1 else if i = pp then 1 else 0
          have hx : x ≠ 0 := by
            intro h; have := congr_fun h u
            simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
          have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ fv → k ≠ ol → k ≠ pp → x k = 0 :=
            fun k h1 h2 h3 h4 h5 => by simp [x, h1, h2, h3, h4, h5]
          -- Inner products
          have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
            rw [sum_two huv.symm (fun m => (↑(A v m) : ℚ) * x m)
              (fun m h1 h2 => by
                have : A v m = 0 := by
                  obtain ⟨m_idx, hm_eq⟩ := Fin.exists_succAbove_eq h1
                  rw [← hm_eq]; exact hAv0 m_idx (fun h => h2 (by rw [← hm_eq, h, hu_idx]))
                simp [this])]
            simp only [x, ↓reduceIte, if_neg huv, hGCM.diag v]; push_cast; ring
          have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
            rw [sum_three huv.symm hfv_v.symm hfv_u.symm
              (fun m => (↑(A u m) : ℚ) * x m)
              (fun m h1 h2 h3 => by
                by_cases hm4 : m = ol; · simp [hm4, hAu_ol]
                by_cases hm5 : m = pp; · simp [hm5, hAu_pp]
                simp [x0 m h1 h2 h3 hm4 hm5])]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hfv_v, if_neg hfv_u,
              hGCM.diag u, hAu_fv]; push_cast
            have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by rw [mul_comm]; exact_mod_cast hcw2
            linarith
          have inner_fv : ∑ j, (↑(A fv j) : ℚ) * x j = 0 := by
            rw [sum_four hfv_u.symm hol_u.symm hpp_u.symm hol_fv.symm hpp_fv.symm hpp_ol.symm
              (fun m => (↑(A fv m) : ℚ) * x m)
              (fun m h1 h2 h3 h4 => by
                by_cases hm : m = v; · simp [hm, hAfvv]
                simp [x0 m hm h1 h2 h3 h4])]
            simp only [x, ↓reduceIte, if_neg huv, if_neg hfv_v, if_neg hfv_u,
              if_neg hol_v, if_neg hol_u, if_neg hol_fv,
              if_neg hpp_v, if_neg hpp_u, if_neg hpp_fv, if_neg hpp_ol,
              hGCM.diag fv, hAfv_u, hAfv_ol, hAfv_pp]; push_cast; ring
          have inner_ol : ∑ j, (↑(A ol j) : ℚ) * x j = 0 := by
            rw [sum_two hol_fv.symm (fun m => (↑(A ol m) : ℚ) * x m)
              (fun m h1 h2 => by
                by_cases hm : m = v; · simp [hm, hAolv]
                by_cases hm2 : m = u; · simp [hm2, hAol_u]
                by_cases hm3 : m = pp; · simp [hm3, hAol_pp]
                simp [x0 m hm hm2 h1 h2 hm3])]
            simp only [x, ↓reduceIte, if_neg hfv_v, if_neg hfv_u,
              if_neg hol_v, if_neg hol_u, if_neg hol_fv,
              hGCM.diag ol, hAol_fv]; push_cast; ring
          have inner_pp : ∑ j, (↑(A pp j) : ℚ) * x j = 0 := by
            rw [sum_two hpp_fv.symm (fun m => (↑(A pp m) : ℚ) * x m)
              (fun m h1 h2 => by
                by_cases hm : m = v; · simp [hm, hAppv]
                by_cases hm2 : m = u; · simp [hm2, hApp_u]
                by_cases hm3 : m = ol; · simp [hm3, hApp_ol]
                simp [x0 m hm hm2 h1 hm3 h2])]
            simp only [x, ↓reduceIte, if_neg hfv_v, if_neg hfv_u,
              if_neg hpp_v, if_neg hpp_u, if_neg hpp_fv, if_neg hpp_ol,
              hGCM.diag pp, hApp_fv]; push_cast; ring
          have hq : qform hSym.d A x = 0 := by
            apply qform_zero_of_null; intro k
            rcases Fin.eq_self_or_eq_succAbove v k with rfl | ⟨m, rfl⟩
            · right; exact inner_v
            · by_cases hmu : v.succAbove m = u; · right; rw [hmu]; exact inner_u
              by_cases hmfv : v.succAbove m = fv; · right; rw [hmfv]; exact inner_fv
              by_cases hmol : v.succAbove m = ol; · right; rw [hmol]; exact inner_ol
              by_cases hmpp : v.succAbove m = pp; · right; rw [hmpp]; exact inner_pp
              left; exact_mod_cast x0 (v.succAbove m) (Fin.succAbove_ne v m) hmu hmfv hmol hmpp
          exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))
      · -- Interior path (1 ≤ p ≤ n-2) → contradiction
        exfalso
        push_neg at hfl
        -- p := (e' u_idx).val satisfies: 1 ≤ p (from h0), p ≤ n-2 (from hfl+hfork), p < n+2
        -- u sits on the D-path with two D-neighbors: left (p-1) and right (p+1)
        -- Test vector: x(v) = -A(v,u), x(u) = 2, x(left) = 1
        --   x(j) = 2 for p ≤ j ≤ n-1, x(n) = x(n+1) = 1, rest = 0
        -- (This is D_marks shifted to start at position p, extended with -A(v,u) at v)
        set p_val := (e' u_idx).val with p_val_def
        set rr := n + 2 - p_val with rr_def
        have hrr4 : 4 ≤ rr := by omega
        -- Define the D-marks function for the shifted sub-D region
        let fD : Fin (n+2) → ℤ := fun q =>
          if q.val + 1 = p_val then 1
          else if p_val ≤ q.val then D_marks rr ⟨q.val - p_val, by omega⟩
          else 0
        let x : Fin (n+3) → ℚ := fun i =>
          if h : ∃ m, v.succAbove m = i then ↑(fD (e' h.choose)) else ↑(-A v u)
        have hx_v : x v = ↑(-A v u) := by
          simp only [x, dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
        have hx_sub : ∀ m, x (v.succAbove m) = ↑(fD (e' m)) := by
          intro m
          have hex : ∃ m', v.succAbove m' = v.succAbove m := ⟨m, rfl⟩
          simp only [x, dif_pos hex]
          exact congr_arg (fun z => (↑(fD (e' z)) : ℚ))
            (Fin.succAbove_right_injective hex.choose_spec)
        have hx_ne : x ≠ 0 := by
          intro h; have := congr_fun h v
          simp only [hx_v, Pi.zero_apply] at this; norm_cast at this; omega
        have hfD_u : fD (e' u_idx) = 2 := by
          simp only [fD, D_marks]; rw [if_neg (by omega), if_pos (le_refl _)]
          split_ifs <;> omega
        have hfD_marks : ∀ q : Fin (n+2), p_val ≤ q.val →
            fD q = D_marks rr ⟨q.val - p_val, by omega⟩ := by
          intro q hq; simp only [fD]; rw [if_neg (by omega), if_pos hq]
        -- The key computation: for D-vertices at positions ≥ p,
        -- the sum ∑_q D(⟨i+p,_⟩, q)*fD(q) = D_mulVec_marks contribution + left neighbor term
        have hDpath_sum : ∀ i_off : Fin rr,
            ∑ q : Fin (n+2), (↑(CartanMatrix.D (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) *
              ↑(fD q) =
            (if i_off.val = 0 then (2 : ℚ) else 0) +
            (if i_off.val = 0 then (-1 : ℚ) else 0) := by
          intro i_off
          have hterm : ∀ q : Fin (n+2),
              (↑(CartanMatrix.D (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) * ↑(fD q) =
              (if h : p_val ≤ q.val then
                (↑(CartanMatrix.D rr i_off ⟨q.val - p_val, by omega⟩) : ℚ) *
                  ↑(D_marks rr ⟨q.val - p_val, by omega⟩)
              else 0) +
              (if q.val + 1 = p_val then
                (if i_off.val = 0 then (-1 : ℚ) else 0)
              else 0) := by
            intro q
            by_cases hqp : p_val ≤ q.val
            · rw [dif_pos hqp, if_neg (by omega)]
              simp only [add_zero]
              congr 1
              · have hq_eq : q = ⟨(q.val - p_val) + p_val, by omega⟩ :=
                  Fin.ext (Nat.sub_add_cancel hqp).symm
                conv_lhs => rw [hq_eq]
                norm_cast
                simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
                split_ifs <;> omega
              · exact_mod_cast hfD_marks q hqp
            · push_neg at hqp
              rw [dif_neg (by omega)]
              simp only [zero_add]
              by_cases hq1 : q.val + 1 = p_val
              · rw [if_pos hq1]
                have hfq : fD q = 1 := by simp only [fD]; rw [if_pos hq1]
                rw [hfq]; push_cast; simp only [mul_one]
                have hDval : CartanMatrix.D (n+2) ⟨i_off.val + p_val, by omega⟩ q =
                    if i_off.val = 0 then -1 else 0 := by
                  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
                  have := q.isLt; have := i_off.isLt
                  split_ifs <;> omega
                rw [hDval]; split_ifs <;> simp
              · rw [if_neg hq1]
                have hfq : fD q = 0 := by
                  simp only [fD]; rw [if_neg (by omega), if_neg (by omega)]
                rw [hfq]; simp
          simp_rw [hterm]
          rw [Finset.sum_add_distrib]
          congr 1
          · -- Shifted D part: reindex and use D_mulVec_marks
            trans ∑ j : Fin rr,
                (↑(CartanMatrix.D rr i_off j) : ℚ) * ↑(D_marks rr j)
            · exact sum_shift (by omega : p_val ≤ n + 2)
                (fun j => (↑(CartanMatrix.D rr i_off j) : ℚ) * ↑(D_marks rr j))
            · have hdm := D_mulVec_marks rr hrr4 i_off
              have : (∑ j : Fin rr, (↑(CartanMatrix.D rr i_off j) : ℚ) * ↑(D_marks rr j)) =
                  if i_off.val = 0 then 2 else 0 := by exact_mod_cast hdm
              rw [this]
          · rw [Fintype.sum_eq_single ⟨p_val - 1, by omega⟩ (fun q hq => by
              rw [if_neg (fun h => hq (Fin.ext (by simp at h ⊢; omega)))])]
            simp; omega
        -- Now prove qform ≤ 0
        have hq : qform hSym.d A x ≤ 0 := by
          rw [qform_eq_sum_mul]
          apply Finset.sum_nonpos; intro i _
          by_cases hiv : i = v
          · -- Term at v: d(v)*(-A(v,u))*inner(v) where inner(v) = 0
            rw [show i = v from hiv]
            suffices inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 by simp [inner_v]
            rw [Fin.sum_univ_succAbove _ v]
            simp only [hx_v, hx_sub, hGCM.diag v]
            rw [Fintype.sum_eq_single u_idx (fun m' hm' => by
              rw [show A v (v.succAbove m') = 0 from hAv0 m' (fun heq => hm' heq)]; ring)]
            rw [hu_idx, hfD_u]; push_cast; ring
          · -- Terms at D-vertices
            rcases Fin.eq_self_or_eq_succAbove v i with hkv | ⟨m, hkm⟩
            · exact absurd hkv hiv
            · rw [hkm, hx_sub m]
              by_cases hfm : fD (e' m) = 0
              · simp [hfm]
              · -- fD(e' m) ≠ 0 means e'(m) is at position ≥ p-1
                have hfD_nonneg : (0 : ℤ) ≤ fD (e' m) := by
                  simp only [fD, D_marks] at hfm ⊢; split_ifs <;> omega
                suffices inner_m : ∑ j, (↑(A (v.succAbove m) j) : ℚ) * x j ≤ 0 by
                  exact mul_nonpos_of_nonneg_of_nonpos
                    (mul_nonneg (le_of_lt (hSym.d_pos _)) (by exact_mod_cast hfD_nonneg))
                    inner_m
                rw [Fin.sum_univ_succAbove _ v]
                simp only [hx_v, hx_sub]
                have hsub_reindex : ∑ l, (↑(A (v.succAbove m) (v.succAbove l)) : ℚ) * ↑(fD (e' l)) =
                    ∑ q, (↑(CartanMatrix.D (n+2) (e' m) q) : ℚ) * ↑(fD q) := by
                  simp_rw [fun l => show A (v.succAbove m) (v.succAbove l) =
                      CartanMatrix.D (n+2) (e' m) (e' l) from hsub m l]
                  exact Equiv.sum_comp e' (fun q => (↑(CartanMatrix.D (n+2) (e' m) q) : ℚ) * ↑(fD q))
                rw [hsub_reindex]
                have hpos : (e' m).val + 1 = p_val ∨ p_val ≤ (e' m).val := by
                  simp only [fD, D_marks] at hfm
                  split_ifs at hfm <;> [left; right; right; exact absurd rfl hfm] <;> omega
                rcases hpos with hpm1 | hpm
                · -- Left neighbor (position p-1): inner = 0
                  have hm_ne_u : m ≠ u_idx := by intro heq; rw [heq] at hpm1; omega
                  have hAmv : A (v.succAbove m) v = 0 := hAv0' m hm_ne_u
                  rw [hAmv]; push_cast; simp only [zero_mul, zero_add]
                  set q1 : Fin (n+2) := ⟨p_val - 1, by omega⟩
                  set q2 : Fin (n+2) := ⟨p_val, by omega⟩
                  have hq12 : q1 ≠ q2 := by intro h; simp [q1, q2, Fin.ext_iff] at h; omega
                  rw [sum_two hq12
                    (fun q => (↑(CartanMatrix.D (n+2) (e' m) q) : ℚ) * ↑(fD q))
                    (fun q hq1' hq2' => by
                      have hDq : CartanMatrix.D (n+2) (e' m) q = 0 ∨ fD q = 0 := by
                        by_cases hqp1 : q.val + 1 = p_val
                        · exact absurd (Fin.ext (by simp [q1]; omega)) hq1'
                        · by_cases hqp2 : p_val ≤ q.val
                          · left
                            have hq_ne : q.val ≠ p_val := fun h =>
                              hq2' (Fin.ext (by simp [q2]; exact h))
                            simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
                            have := q.isLt; have := hpm1
                            split_ifs <;> omega
                          · right; show fD q = 0
                            simp only [fD]; rw [if_neg (by omega), if_neg (by omega)]
                      rcases hDq with h | h <;> simp [h])]
                  have hDq1 : CartanMatrix.D (n+2) (e' m) q1 = 2 := by
                    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,  q1]
                    have := hpm1; split_ifs <;> omega
                  have hDq2 : CartanMatrix.D (n+2) (e' m) q2 = -1 := by
                    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,  q2]
                    have := hpm1; split_ifs <;> omega
                  have hfq1 : fD q1 = 1 := by simp only [fD, q1]; rw [if_pos (by omega)]
                  have hfq2 : fD q2 = 2 := by
                    simp only [fD, D_marks, q2]
                    rw [if_neg (by omega), if_pos (le_refl _)]
                    split_ifs <;> omega
                  rw [hDq1, hDq2, hfq1, hfq2]; push_cast; linarith
                · -- D sub-path vertex (position ≥ p)
                  set i_off : Fin rr := ⟨(e' m).val - p_val, by omega⟩
                  have hAmv : A (v.succAbove m) v =
                      if (e' m).val = p_val then A u v else 0 := by
                    by_cases he : (e' m).val = p_val
                    · rw [if_pos he]
                      have : m = u_idx := e'.injective (Fin.ext (he ▸ p_val_def.symm))
                      rw [this, hu_idx]
                    · rw [if_neg he]
                      exact hAv0' m (fun heq =>
                        he ((congr_arg (fun x => (e' x).val) heq).trans p_val_def.symm))
                  rw [hAmv]
                  have he'm_eq : e' m = ⟨i_off.val + p_val, by omega⟩ := by
                    ext; simp [i_off]; omega
                  rw [show ∑ q, (↑(CartanMatrix.D (n+2) (e' m) q) : ℚ) * ↑(fD q) =
                      ∑ q, (↑(CartanMatrix.D (n+2) ⟨i_off.val + p_val, by omega⟩ q) : ℚ) * ↑(fD q)
                    from by rw [he'm_eq]]
                  rw [hDpath_sum i_off]
                  by_cases hi0 : i_off.val = 0
                  · -- At position p (= u): inner(u) = A(u,v)*(-A(v,u)) + 2 - 1
                    --   = -weight + 1 ≤ 0 (weight ≥ 1)
                    have : (e' m).val = p_val := by simp [i_off] at hi0; omega
                    simp [hi0, this]
                    have : (A u v : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
                    have : (A v u : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
                    nlinarith
                  · -- At positions > p: inner = 0
                    have : (e' m).val ≠ p_val := by
                      simp [i_off] at hi0; omega
                    simp [hi0, this]
        exact absurd hPD (not_posDef_of_nonpos hSym x hx_ne hq)

end BLD.Lie.Cartan
