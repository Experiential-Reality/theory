/- BLD Calculus — Cartan Classification: E₇ extension case -/

import BLD.Lie.Cartan.F4

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

set_option maxHeartbeats 6400000 in
theorem extend_E₇ {A : Matrix (Fin 8) (Fin 8) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin 8) (u : Fin 8) (huv : u ≠ v)
    (_hAvu : A v u ≠ 0) (_hAuv : A u v ≠ 0)
    (huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u)
    (hcw_le2 : A v u * A u v ≤ 2) (hcw_pos : 1 ≤ A v u * A u v)
    (hAvu_neg : A v u ≤ -1) (hAuv_neg : A u v ≤ -1)
    (ht' : CartanEquiv (deleteVertex A v) CartanMatrix.E₇) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
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
            try simp
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
          ↑(CartanMatrix.E₇ p q) from by rw [hApq],
        show (↑(A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p))) : ℚ) =
          ↑(CartanMatrix.E₇ q p) from by rw [hAqp],
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

end BLD.Lie.Cartan
