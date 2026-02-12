/- BLD Calculus — Cartan Classification: F₄ and A_k Cases

   F₄ no-extension theorem and A_k extension analysis.
-/

import BLD.Lie.Cartan.Exceptional

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

/-- F₄ cannot be extended: any pos-def GCM whose principal submatrix is
    CartanEquiv to F₄ yields a contradiction.
    Proof: for attachment vertices 0,1,2 (marks ≥ 2), the marksF4 test vector
    gives qform ≤ 0. For vertex 3 (marks = 1), the affine F₄ test vector gives
    qform ≤ 0. -/
theorem f4_no_extension {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1)
    (ht' : CartanEquiv (deleteVertex A v) CartanMatrix.F₄) : False := by
  -- Rank: n + 2 = 4
  have hn : n = 2 := by
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
    have hmem : j ∈ Finset.univ.filter (fun j : Fin 5 => j ≠ v ∧ A v j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjv, hjA⟩
    rw [hu_set] at hmem; exact Finset.mem_singleton.mp hmem
  obtain ⟨e', he'⟩ := ht'
  obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
  have hAvu_neg : A v u ≤ -1 := by
    have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_ne : A u v ≠ 0 := fun h => hAvu ((hGCM.zero_iff u v huv).mp h)
  have hAuv_neg : A u v ≤ -1 := by
    have := hGCM.off_diag_nonpos u v huv; omega
  have hAv0 : ∀ k : Fin 4, k ≠ u_idx → A v (v.succAbove k) = 0 := by
    intro k hk
    have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
    have hne_u : v.succAbove k ≠ u := fun h =>
      hk (Fin.succAbove_right_injective (hu_idx ▸ h))
    by_contra hvk; exact hne_u (huniq _ hne_v hvk)
  have hsub : ∀ i j : Fin 4, A (v.succAbove i) (v.succAbove j) =
      CartanMatrix.F₄ (e' i) (e' j) := fun i j => (he' i j).symm
  -- Case split on attachment vertex
  -- Vertex 3: use affmarksF4 test vector [2,4,3,2] on F₄ subgraph, 1 on v
  -- Vertices 0,1,2: use marksF4 test vector [2,3,2,1] with c = -A(v,u)
  by_cases h3 : e' u_idx = 3
  · -- Vertex 3: affmarksF4 approach
    -- Test vector: x(v) = 1, x(sA k) = affmarksF4(e' k)
    set x : Fin 5 → ℚ := fun i =>
      if h : ∃ k : Fin 4, v.succAbove k = i then ↑(affmarksF4 (e' h.choose))
      else 1
    have hx_sub : ∀ k : Fin 4, x (v.succAbove k) = ↑(affmarksF4 (e' k)) := by
      intro k; simp only [x]
      have hex : ∃ k' : Fin 4, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
      rw [dif_pos hex]
      have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
      rw [heq]
    have hx_v : x v = 1 := by
      simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
    have hx : x ≠ 0 := by
      intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
    -- qform ≤ 0: each term d(i)*x(i)*inner(i) ≤ 0
    apply absurd hPD
    apply not_posDef_of_nonpos hSym x hx
    rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hx_sub]
    -- Inner sum at v: 2*1 + A(v,u)*affmarksF4(3) = 2 + 2*A(v,u)
    have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 2 + 2 * ↑(A v u) := by
      rw [Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hGCM.diag v, hx_sub]
      have hsum : ∑ k : Fin 4, (↑(A v (v.succAbove k)) : ℚ) * ↑(affmarksF4 (e' k)) =
          ↑(A v u) * ↑(affmarksF4 (e' u_idx)) := by
        have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(affmarksF4 (e' u_idx)) =
            ↑(A v u) * ↑(affmarksF4 (e' u_idx)) := by rw [hu_idx]
        rw [← hval]
        exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
      rw [hsum, h3]; simp [affmarksF4]; push_cast; ring
    -- Inner sum at u (vertex mapping to F₄-3):
    -- A(u,v)*1 + (F₄·affmarks)(3) = A(u,v) + 1
    have f4_affmarks_sum : ∀ k : Fin 4,
        ∑ l : Fin 4, (↑(CartanMatrix.F₄ (e' k) (e' l)) : ℚ) * ↑(affmarksF4 (e' l)) =
        if e' k = 3 then 1 else 0 := by
      intro k
      have hreindex := Equiv.sum_comp e'
        (fun p => (↑(CartanMatrix.F₄ (e' k) p) : ℚ) * ↑(affmarksF4 p))
      rw [hreindex]
      have h := congr_fun F4_mulVec_affmarks (e' k)
      simp only [mulVec, dotProduct] at h
      have hcast : ∑ p, (↑(CartanMatrix.F₄ (e' k) p) : ℚ) * ↑(affmarksF4 p)
          = (↑(∑ p, CartanMatrix.F₄ (e' k) p * affmarksF4 p) : ℚ) := by push_cast; rfl
      rw [hcast, h]; push_cast; split_ifs <;> simp
    have inner_sub : ∀ k : Fin 4, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
        ↑(A (v.succAbove k) v) * 1 +
        (if e' k = 3 then 1 else 0) := by
      intro k
      rw [Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hx_sub]; congr 1
      have : ∀ l : Fin 4, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(affmarksF4 (e' l))
          = (↑(CartanMatrix.F₄ (e' k) (e' l)) : ℚ) * ↑(affmarksF4 (e' l)) := by
        intro l; rw [hsub]
      simp_rw [this]
      exact f4_affmarks_sum k
    simp only [inner_v, inner_sub, mul_one]
    -- Total: d(v)*(2+2A(v,u)) + ∑_k d(sA k)*affmarks(e'k)*(A(sA k,v) + if_3)
    -- Non-v: only k with e'(k)=3 (i.e., u_idx) has nonzero inner. Others have inner=0.
    -- The term at u_idx: d(u)*2*(A(u,v)+1) ≤ 0
    -- All other terms: d(sA k)*affmarks(e'k)*0 = 0 (if e'k≠3 and k≠u_idx)
    --                  or d(sA k)*affmarks(e'k)*A(sA k,v) where A(sA k,v)=0 (leaf)
    have hsplit : ∀ k : Fin 4,
        hSym.d (v.succAbove k) * ↑(affmarksF4 (e' k)) *
        (↑(A (v.succAbove k) v) + if e' k = (3 : Fin 4) then (1 : ℚ) else 0) =
        if k = u_idx then hSym.d u * ↑(affmarksF4 (e' u_idx)) *
          (↑(A u v) + 1)
        else 0 := by
      intro k
      by_cases hku : k = u_idx
      · subst hku; simp [hu_idx, h3]
      · have hAkv : A (v.succAbove k) v = 0 := by
          have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
          have hAvk : A v (v.succAbove k) = 0 := hAv0 k hku
          exact (hGCM.zero_iff v _ (Ne.symm hne_v)).mp hAvk
        have hek3 : e' k ≠ 3 := by
          intro hek; exact hku (e'.injective (hek.trans h3.symm))
        simp [hAkv, hek3, hku]
    simp_rw [hsplit]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hmem : Finset.univ.filter (fun k : Fin 4 => k = u_idx) = {u_idx} := by
      ext k; simp
    rw [hmem, Finset.sum_singleton, h3]
    simp [affmarksF4]
    -- Goal: 1 * (2 + 2 * ↑(A v u)) + hSym.d u * 2 * (↑(A u v) + 1) ≤ 0
    -- = 2*(d(v)*(1+A(v,u)) + d(u)*(1+A(u,v)))
    -- Both d(v)*(1+A(v,u)) ≤ 0 and d(u)*(1+A(u,v)) ≤ 0 since A(v,u),A(u,v) ≤ -1
    have hdv : 0 < hSym.d v := hSym.d_pos v
    have hdu : 0 < hSym.d u := hSym.d_pos u
    have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
    have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
    nlinarith [mul_nonneg (le_of_lt hdv) (show (0 : ℚ) ≤ -(1 + ↑(A v u)) by linarith),
               mul_nonneg (le_of_lt hdu) (show (0 : ℚ) ≤ -(1 + ↑(A u v)) by linarith)]
  · -- Vertices 0,1,2: marksF4 approach (same structure as E₈)
    -- marksF4(e'(u_idx)) ≥ 2 since e'(u_idx) ≠ 3
    set mj : ℤ := marksF4 (e' u_idx)
    have hmj : (2 : ℤ) ≤ mj := by
      have : ∀ i : Fin 4, i ≠ 3 → 2 ≤ marksF4 i := by decide
      exact this _ h3
    set c : ℚ := -(↑(A v u) : ℚ)
    have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
    have hc_pos : 0 < c := by simp only [c]; linarith
    set x : Fin 5 → ℚ := fun i =>
      if h : ∃ k : Fin 4, v.succAbove k = i then ↑(marksF4 (e' h.choose))
      else c
    have hx_sub : ∀ k : Fin 4, x (v.succAbove k) = ↑(marksF4 (e' k)) := by
      intro k; simp only [x]
      have hex : ∃ k' : Fin 4, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
      rw [dif_pos hex]
      have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
      rw [heq]
    have hx_v : x v = c := by
      simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
    have hx : x ≠ 0 := by
      intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
    -- Inner sum at v: 2c + A(v,u)*mj
    have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 2 * c + ↑(A v u) * ↑mj := by
      rw [Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hGCM.diag v, hx_sub]
      have hsum : ∑ k : Fin 4, (↑(A v (v.succAbove k)) : ℚ) * ↑(marksF4 (e' k)) =
          ↑(A v u) * ↑mj := by
        have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksF4 (e' u_idx)) =
            ↑(A v u) * ↑mj := by rw [hu_idx]
        rw [← hval]
        exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
      rw [hsum]; push_cast; ring
    -- F₄·marks reindexing
    have f4marks_sum : ∀ k : Fin 4,
        ∑ l : Fin 4, (↑(CartanMatrix.F₄ (e' k) (e' l)) : ℚ) * ↑(marksF4 (e' l)) =
        if e' k = 0 then 1 else 0 := by
      intro k
      have hreindex := Equiv.sum_comp e'
        (fun p => (↑(CartanMatrix.F₄ (e' k) p) : ℚ) * ↑(marksF4 p))
      rw [hreindex]
      have h := congr_fun F4_mulVec_marks (e' k)
      simp only [mulVec, dotProduct] at h
      have hcast : ∑ p, (↑(CartanMatrix.F₄ (e' k) p) : ℚ) * ↑(marksF4 p)
          = (↑(∑ p, CartanMatrix.F₄ (e' k) p * marksF4 p) : ℚ) := by push_cast; rfl
      rw [hcast, h]; push_cast; split_ifs <;> simp
    -- Inner sum at non-v vertex k
    have inner_sub : ∀ k : Fin 4, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
        ↑(A (v.succAbove k) v) * c +
        (if e' k = 0 then 1 else 0) := by
      intro k
      rw [Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hx_sub]; congr 1
      have : ∀ l : Fin 4, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(marksF4 (e' l))
          = (↑(CartanMatrix.F₄ (e' k) (e' l)) : ℚ) * ↑(marksF4 (e' l)) := by
        intro l; rw [hsub]
      simp_rw [this]
      exact f4marks_sum k
    -- Symmetrizability trick
    have sym_trick : ∀ k : Fin 4,
        hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ) =
        hSym.d v * (↑(A v (v.succAbove k)) : ℚ) := by
      intro k; have := hSym.sym (v.succAbove k) v; linarith
    -- Show qform ≤ 0
    apply absurd hPD
    apply not_posDef_of_nonpos hSym x hx
    rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hx_sub, inner_v, inner_sub]
    -- Split non-v sum: cross-terms + residual (same structure as E₈)
    have hsplit : ∀ k : Fin 4,
        hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) *
        (↑(A (v.succAbove k) v) * c + if e' k = (0 : Fin 4) then (1 : ℚ) else 0) =
        c * (hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ)) * ↑(marksF4 (e' k)) +
        hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) *
        (if e' k = (0 : Fin 4) then (1 : ℚ) else 0) := by intro k; ring
    simp_rw [hsplit, sym_trick]
    rw [Finset.sum_add_distrib]
    -- Cross-term sum = c*d(v)*A(v,u)*mj
    have hcross : ∑ k : Fin 4, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
        ↑(marksF4 (e' k)) = c * hSym.d v * (↑(A v u) * ↑mj) := by
      simp_rw [show ∀ k : Fin 4, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
          ↑(marksF4 (e' k)) = c * hSym.d v * ((↑(A v (v.succAbove k)) : ℚ) *
          ↑(marksF4 (e' k))) from fun k => by ring]
      rw [← Finset.mul_sum]
      congr 1
      have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksF4 (e' u_idx)) =
          ↑(A v u) * ↑mj := by rw [hu_idx]
      rw [← hval]
      exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
    -- Residual sum: only vertex 0 contributes. Need d(sA(e'⁻¹(0))) relationship.
    have hresid : ∑ k : Fin 4, hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) *
        (if e' k = (0 : Fin 4) then (1 : ℚ) else 0) =
        2 * hSym.d (v.succAbove (e'.symm 0)) := by
      simp_rw [show ∀ k : Fin 4, hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) *
          (if e' k = (0 : Fin 4) then (1 : ℚ) else 0) =
          if e' k = 0 then hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) else 0 from
        fun k => by split_ifs <;> ring]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      have hmem : Finset.univ.filter (fun k : Fin 4 => e' k = 0) = {e'.symm 0} := by
        ext k; simp [Finset.mem_filter, Equiv.eq_symm_apply]
      rw [hmem, Finset.sum_singleton, Equiv.apply_symm_apply]
      simp [marksF4]; ring
    rw [hcross, hresid]
    -- Need: d(sA(e'⁻¹(0))) ≤ d(u)
    -- This follows from the F₄ d-value chain:
    -- Edge 0↔1: d₀=d₁ (symmetric). Edge 1↔2: d₂=2d₁.
    -- So d₀ ≤ d₂ ≤ d(u) depending on which vertex u maps to.
    have hd0_le_du : hSym.d (v.succAbove (e'.symm 0)) ≤ hSym.d u := by
      have hsub_sym := fun p q => hSym.sym (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))
      -- Edge 0↔1 is symmetric: d₀ = d₁
      have h01 : hSym.d (v.succAbove (e'.symm 0)) = hSym.d (v.succAbove (e'.symm 1)) := by
        have h := hsub_sym 0 1
        have hA01 : A (v.succAbove (e'.symm 0)) (v.succAbove (e'.symm 1)) = CartanMatrix.F₄ 0 1 := by
          rw [hsub]; simp [Equiv.apply_symm_apply]
        have hA10 : A (v.succAbove (e'.symm 1)) (v.succAbove (e'.symm 0)) = CartanMatrix.F₄ 1 0 := by
          rw [hsub]; simp [Equiv.apply_symm_apply]
        rw [show (↑(A (v.succAbove (e'.symm 0)) (v.succAbove (e'.symm 1))) : ℚ)
            = ↑(CartanMatrix.F₄ 0 1) from by rw [hA01],
          show (↑(A (v.succAbove (e'.symm 1)) (v.succAbove (e'.symm 0))) : ℚ)
            = ↑(CartanMatrix.F₄ 1 0) from by rw [hA10]] at h
        -- F₄(0,1) = F₄(1,0) = -1, so cancel
        have hf01 : (↑(CartanMatrix.F₄ 0 1) : ℚ) = -1 := by decide
        have hf10 : (↑(CartanMatrix.F₄ 1 0) : ℚ) = -1 := by decide
        rw [hf01, hf10] at h; linarith
      -- Edge 1↔2: d₁*(-2) = d₂*(-1), so d₂ = 2*d₁
      have h12 : hSym.d (v.succAbove (e'.symm 2)) =
          2 * hSym.d (v.succAbove (e'.symm 1)) := by
        have h := hsub_sym 1 2
        have hA12 : A (v.succAbove (e'.symm 1)) (v.succAbove (e'.symm 2)) = CartanMatrix.F₄ 1 2 := by
          rw [hsub]; simp [Equiv.apply_symm_apply]
        have hA21 : A (v.succAbove (e'.symm 2)) (v.succAbove (e'.symm 1)) = CartanMatrix.F₄ 2 1 := by
          rw [hsub]; simp [Equiv.apply_symm_apply]
        rw [show (↑(A (v.succAbove (e'.symm 1)) (v.succAbove (e'.symm 2))) : ℚ)
            = ↑(CartanMatrix.F₄ 1 2) from by rw [hA12],
          show (↑(A (v.succAbove (e'.symm 2)) (v.succAbove (e'.symm 1))) : ℚ)
            = ↑(CartanMatrix.F₄ 2 1) from by rw [hA21]] at h
        -- F₄(1,2) = -2, F₄(2,1) = -1
        have hf12 : (↑(CartanMatrix.F₄ 1 2) : ℚ) = -2 := by decide
        have hf21 : (↑(CartanMatrix.F₄ 2 1) : ℚ) = -1 := by decide
        rw [hf12, hf21] at h; linarith
      -- Now case on e'(u_idx) to relate d₀ to d(u)
      have hkey : e'.symm (e' u_idx) = u_idx := e'.symm_apply_apply u_idx
      have heu_cases : e' u_idx = 0 ∨ e' u_idx = 1 ∨ e' u_idx = 2 := by
        have : ∀ i : Fin 4, i ≠ 3 → (i = 0 ∨ i = 1 ∨ i = 2) := by decide
        exact this _ h3
      rcases heu_cases with h0 | h1 | h2
      · -- e'(u_idx) = 0: d₀ = d(u)
        rw [show e'.symm 0 = u_idx from h0 ▸ hkey, hu_idx]
      · -- e'(u_idx) = 1: d₀ = d₁ = d(u)
        rw [h01, show e'.symm 1 = u_idx from h1 ▸ hkey, hu_idx]
      · -- e'(u_idx) = 2: d₀ ≤ 2*d₁ = d(u)
        have hd1_pos : 0 < hSym.d (v.succAbove (e'.symm 1)) := hSym.d_pos _
        have : e'.symm 2 = u_idx := h2 ▸ hkey
        rw [this, hu_idx] at h12; linarith [h01]
    -- Final bound: d(v)*c*(2c+A(v,u)*mj) + c*d(v)*A(v,u)*mj + 2*d(sA(e'⁻¹0)) ≤ 0
    have hsym_vu := hSym.sym v u
    have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
    have hdu : 0 < hSym.d u := hSym.d_pos u
    have hdv : 0 < hSym.d v := hSym.d_pos v
    have hmj_q : (2 : ℚ) ≤ ↑mj := by exact_mod_cast hmj
    have hd0 := hSym.d_pos (v.succAbove (e'.symm 0))
    -- Algebraic simplification
    have htotal : hSym.d v * c * (2 * c + ↑(A v u) * ↑mj) +
        (c * hSym.d v * (↑(A v u) * ↑mj) + 2 * hSym.d (v.succAbove (e'.symm 0))) =
        2 * (hSym.d (v.succAbove (e'.symm 0)) +
        hSym.d v * (↑(A v u) : ℚ) ^ 2 * (1 - (↑mj : ℚ))) := by
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
    -- Goal: 2*(d₀ + d(u)*auv*avu*(1-mj)) ≤ 0
    have hab : 1 ≤ (↑(A u v) : ℚ) * (↑(A v u) : ℚ) := by
      have := mul_le_mul_of_nonpos_left hAuv_q (show (↑(A v u) : ℚ) ≤ 0 by linarith)
      linarith
    -- d(u)*auv*avu ≥ d(u) ≥ d₀
    have hdu_ab : hSym.d (v.succAbove (e'.symm 0)) ≤
        hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) :=
      le_trans hd0_le_du (le_mul_of_one_le_right (le_of_lt hdu) hab)
    have hbound := mul_le_mul_of_nonpos_right hdu_ab
      (show (1 : ℚ) - (↑mj : ℚ) ≤ 0 by linarith)
    -- d₀ + d(u)*auv*avu*(1-mj) ≤ d₀ + d₀*(1-mj) = d₀*(2-mj) ≤ 0
    linarith [mul_nonneg (le_of_lt hd0) (show (0 : ℚ) ≤ (↑mj : ℚ) - 2 by linarith)]

-- ═══════════════════════════════════════════════════════════
-- Affine subgraph contradictions for A_k interior extension
-- ═══════════════════════════════════════════════════════════

/-- Generic affine subgraph contradiction: given path vertices g and branch v,
    with the submatrix matching an affine diagram M, derive ¬IsPosDef. -/
private theorem affine_subgraph_contradiction {n m : ℕ}
    {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hSym : IsSymmetrizable A)
    (v : Fin (n+3))
    (g : Fin m → Fin (n+2))
    (hg_inj : Function.Injective g)
    (M : Matrix (Fin (m+1)) (Fin (m+1)) ℤ)
    (hpath : ∀ k l : Fin m,
      A (v.succAbove (g k)) (v.succAbove (g l)) = M (Fin.castSucc k) (Fin.castSucc l))
    (hrow : ∀ k : Fin m,
      A v (v.succAbove (g k)) = M (Fin.last m) (Fin.castSucc k))
    (hcol : ∀ k : Fin m,
      A (v.succAbove (g k)) v = M (Fin.castSucc k) (Fin.last m))
    (hdiag : A v v = M (Fin.last m) (Fin.last m))
    (nullvec : Fin (m+1) → ℤ) (hnz : nullvec ≠ 0) (hnull : M.mulVec nullvec = 0)
    : ¬ IsPosDef A hSym := by
  let emb : Fin (m+1) → Fin (n+3) := fun i =>
    if h : i.val < m then v.succAbove (g ⟨i.val, h⟩) else v
  have emb_inj : Function.Injective emb := by
    intro a b hab
    simp only [emb] at hab
    by_cases ha : a.val < m <;> by_cases hb : b.val < m
    · rw [dif_pos ha, dif_pos hb] at hab
      have h1 := hg_inj (Fin.succAbove_right_injective hab)
      have h2 : a.val = b.val := by rw [Fin.ext_iff] at h1; exact h1
      exact Fin.ext h2
    · rw [dif_pos ha, dif_neg hb] at hab
      exact absurd hab (Fin.succAbove_ne v _)
    · rw [dif_neg ha, dif_pos hb] at hab
      exact absurd hab.symm (Fin.succAbove_ne v _)
    · have := Nat.le_of_not_lt ha; have := Nat.le_of_not_lt hb
      exact Fin.ext (by have := a.isLt; have := b.isLt; omega)
  apply not_posDef_of_submatrix_int_null hSym ⟨emb, emb_inj⟩ M
  · intro i j
    simp only [Function.Embedding.coeFn_mk, emb]
    by_cases hi : i.val < m <;> by_cases hj : j.val < m
    · rw [dif_pos hi, dif_pos hj]
      rw [hpath]
      congr 1 <;> exact Fin.ext rfl
    · rw [dif_pos hi, dif_neg hj]
      have : j = Fin.last m := by
        apply Fin.ext; simp only [Fin.val_last]
        have := Nat.le_of_not_lt hj; have := j.isLt; omega
      subst this; rw [hcol]; congr 1
    · rw [dif_neg hi, dif_pos hj]
      have : i = Fin.last m := by
        apply Fin.ext; simp only [Fin.val_last]
        have := Nat.le_of_not_lt hi; have := i.isLt; omega
      subst this; rw [hrow]; congr 1
    · rw [dif_neg hi, dif_neg hj]
      have : i = Fin.last m := by
        apply Fin.ext; simp only [Fin.val_last]
        have := Nat.le_of_not_lt hi; have := i.isLt; omega
      have : j = Fin.last m := by
        apply Fin.ext; simp only [Fin.val_last]
        have := Nat.le_of_not_lt hj; have := j.isLt; omega
      subst_vars; exact hdiag
  · exact hnz
  · exact hnull

-- ═══════════════════════════════════════════════════════════
-- A_k extension helper
-- ═══════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- When the submatrix is type A_{n+2}, determine the full DynkinType. -/
theorem a_extension {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v u : Fin (n+3)) (huv : u ≠ v)
    (hAvu : A v u ≠ 0) (hAuv : A u v ≠ 0)
    (huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u)
    (hcw_le2 : A v u * A u v ≤ 2)
    (ht' : CartanEquiv (deleteVertex A v) (CartanMatrix.A (n+2))) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  obtain ⟨e', he'⟩ := ht'
  obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
  have hsub : ∀ i j : Fin (n+2), A (v.succAbove i) (v.succAbove j) =
      CartanMatrix.A (n+2) (e' i) (e' j) := fun i j => (he' i j).symm
  have hAv0 : ∀ m : Fin (n+2), m ≠ u_idx → A v (v.succAbove m) = 0 := by
    intro m hm; by_contra h
    exact hm (Fin.succAbove_right_injective (hu_idx ▸ huniq _ (Fin.succAbove_ne v m) h))
  have hAv0' : ∀ m : Fin (n+2), m ≠ u_idx → A (v.succAbove m) v = 0 := by
    intro m hm
    exact (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v m))).mp (hAv0 m hm)
  have hAvu_neg : A v u ≤ -1 := by
    have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_neg : A u v ≤ -1 := by
    have := hGCM.off_diag_nonpos u v huv; omega
  have hcw_pos : 1 ≤ A v u * A u v := by nlinarith
  -- Case: weight 1 (A v u = -1, A u v = -1)
  by_cases hw1 : A v u * A u v = 1
  · have hAvu_eq : A v u = -1 := by nlinarith
    have hAuv_eq : A u v = -1 := by nlinarith
    by_cases h_last : (e' u_idx).val = n + 1
    · -- Endpoint at last vertex of A_{n+2}, weight 1 → A_{n+3}
      refine ⟨DynkinType.A (n+3) (by omega), ?_⟩
      simp only [DynkinType.cartanMatrix]
      exact extend_at_last hGCM v e' (CartanMatrix.A (n+3))
        (by simp [CartanMatrix.A])
        (fun i j => by rw [A_castSucc_eq]; exact (hsub i j).symm)
        (fun m => by
          rw [A_last_row]; split_ifs with h
          · have : e' m = e' u_idx := by
              ext; simp only [Fin.val_castSucc] at h; omega
            rw [show m = u_idx from e'.injective this, hu_idx, hAvu_eq]
          · rw [hAv0 m (fun heq => h (by rw [heq]; exact h_last))])
        (fun m => by
          rw [A_last_col]; split_ifs with h
          · have : e' m = e' u_idx := by ext; omega
            rw [show m = u_idx from e'.injective this, hu_idx, hAuv_eq]
          · rw [hAv0' m (fun heq => h (by rw [heq]; exact h_last))])
    · by_cases h_first : (e' u_idx).val = 0
      · -- Endpoint at first vertex of A_{n+2}, weight 1 → A_{n+3}
        refine ⟨DynkinType.A (n+3) (by omega), ?_⟩
        simp only [DynkinType.cartanMatrix]
        exact extend_at_zero hGCM v e' (CartanMatrix.A (n+3))
          (by simp [CartanMatrix.A])
          (fun i j => by rw [A_succ_eq]; exact (hsub i j).symm)
          (fun m => by
            rw [A_first_row]; split_ifs with h
            · have : e' m = e' u_idx := by
                ext; simp only [Fin.val_succ] at h; omega
              rw [show m = u_idx from e'.injective this, hu_idx, hAvu_eq]
            · rw [hAv0 m (fun heq => h (by rw [heq]; exact h_first))])
          (fun m => by
            rw [A_first_col]; split_ifs with h
            · have : e' m = e' u_idx := by ext; omega
              rw [show m = u_idx from e'.injective this, hu_idx, hAuv_eq]
            · rw [hAv0' m (fun heq => h (by rw [heq]; exact h_first))])
      · -- Interior attachment, weight 1 → D or E type
        have hp_ge : 1 ≤ (e' u_idx).val := by omega
        have hp_le : (e' u_idx).val ≤ n := by
          have := (e' u_idx).isLt; omega
        by_cases hp1 : (e' u_idx).val = 1
        · -- p = 1 → D_{n+3} via finRev
          refine ⟨DynkinType.D (n+3) (by omega), ?_⟩
          simp only [DynkinType.cartanMatrix]
          exact extend_at_last hGCM v (e'.trans (finRev (n+1))) (CartanMatrix.D (n+3))
            (by simp [CartanMatrix.D])
            (fun i j => by
              simp only [Equiv.trans_apply]
              rw [D_castSucc_eq_A (n+2) (by omega), A_finRev_eq]
              exact (hsub i j).symm)
            (fun m => by
              simp only [Equiv.trans_apply]
              rw [D_last_row (n+2) (by omega), finRev_val]
              split_ifs with h
              · have : e' m = e' u_idx := by ext; have := (e' m).isLt; omega
                rw [show m = u_idx from e'.injective this, hu_idx, hAvu_eq]
              · rw [hAv0 m (fun heq => h (by subst heq; rw [hp1]; omega))])
            (fun m => by
              simp only [Equiv.trans_apply]
              rw [D_last_col (n+2) (by omega), finRev_val]
              split_ifs with h
              · have : e' m = e' u_idx := by ext; have := (e' m).isLt; omega
                rw [show m = u_idx from e'.injective this, hu_idx, hAuv_eq]
              · rw [hAv0' m (fun heq => h (by subst heq; rw [hp1]; omega))])
        · by_cases hpn : (e' u_idx).val = n
          · -- p = n → D_{n+3}
            refine ⟨DynkinType.D (n+3) (by omega), ?_⟩
            simp only [DynkinType.cartanMatrix]
            exact extend_at_last hGCM v e' (CartanMatrix.D (n+3))
              (by simp [CartanMatrix.D])
              (fun i j => by
                rw [D_castSucc_eq_A (n+2) (by omega)]; exact (hsub i j).symm)
              (fun m => by
                rw [D_last_row (n+2) (by omega)]
                split_ifs with h
                · have : e' m = e' u_idx := by ext; omega
                  rw [show m = u_idx from e'.injective this, hu_idx, hAvu_eq]
                · rw [hAv0 m (fun heq => h (by subst heq; omega))])
              (fun m => by
                rw [D_last_col (n+2) (by omega)]
                split_ifs with h
                · have : e' m = e' u_idx := by ext; omega
                  rw [show m = u_idx from e'.injective this, hu_idx, hAuv_eq]
                · rw [hAv0' m (fun heq => h (by subst heq; omega))])
          · -- 2 ≤ p ≤ n-1: E-type or contradiction
            have hp2 : 2 ≤ (e' u_idx).val := by omega
            have hpn1 : (e' u_idx).val + 1 ≤ n := by omega
            -- Helper for E-type at position 2 (shared by p=2 and p=n-1 via finRev)
            suffices hE : ∀ e'' : Fin (n+2) ≃ Fin (n+2),
                (∀ i j, A (v.succAbove i) (v.succAbove j) =
                  CartanMatrix.A (n+2) (e'' i) (e'' j)) →
                (e'' u_idx).val = 2 →
                ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 by
              by_cases hp2e : (e' u_idx).val = 2
              · exact hE e' hsub hp2e
              · by_cases hpn1e : (e' u_idx).val = n - 1
                · -- p = n-1: compose with finRev to get position 2
                  have hn3 : 3 ≤ n := by omega
                  apply hE (e'.trans (finRev (n+1)))
                  · intro i j
                    simp only [Equiv.trans_apply]
                    rw [A_finRev_eq]; exact hsub i j
                  · simp only [Equiv.trans_apply, finRev_val]
                    omega
                · -- 3 ≤ p ≤ n-2: Ẽ₇ subgraph → contradiction
                  exfalso
                  let c := (e' u_idx).val - 3
                  have hcp : 3 + c = (e' u_idx).val := by simp only [c]; omega
                  let g : Fin 7 → Fin (n+2) := fun k => e'.symm ⟨k.val + c, by omega⟩
                  have hg_eq : ∀ k : Fin 7, e' (g k) = ⟨k.val + c, by omega⟩ :=
                    fun k => e'.apply_symm_apply _
                  have hg_inj : Function.Injective g := by
                    intro a b hab
                    have := congr_arg (fun x => (e' x).val) hab
                    simp only [hg_eq] at this; exact Fin.ext (by omega)
                  have hgu : g ⟨3, by omega⟩ = u_idx :=
                    e'.symm_apply_eq.mpr (Fin.ext hcp)
                  have hg_ne : ∀ k : Fin 7, k.val ≠ 3 → g k ≠ u_idx := by
                    intro k hk3 h
                    have := congr_arg (fun x => (e' x).val) h
                    simp only [hg_eq] at this; omega
                  exact absurd hPD (affine_subgraph_contradiction hSym v g hg_inj affineE7
                    (fun k l => by
                      rw [hsub]; simp only [hg_eq]
                      rw [A_shift_submatrix 7 (n+2) c (by omega)]
                      exact (affineE7_path k l).symm)
                    (fun k => by
                      rw [affineE7_row_branch]; by_cases hk3 : k.val = 3
                      · rw [if_pos hk3]
                        have : g k = u_idx := by
                          rw [show k = ⟨3, by omega⟩ from Fin.ext hk3]; exact hgu
                        rw [this, hu_idx]; exact hAvu_eq
                      · rw [if_neg hk3]; exact hAv0 _ (hg_ne k hk3))
                    (fun k => by
                      rw [affineE7_col_branch]; by_cases hk3 : k.val = 3
                      · rw [if_pos hk3]
                        have : g k = u_idx := by
                          rw [show k = ⟨3, by omega⟩ from Fin.ext hk3]; exact hgu
                        rw [this, hu_idx]; exact hAuv_eq
                      · rw [if_neg hk3]; exact hAv0' _ (hg_ne k hk3))
                    (by rw [hGCM.diag]; decide)
                    ![1, 2, 3, 4, 3, 2, 1, 2] (by decide) affineE7_null)
            -- Prove the suffices: E-type from position 2
            intro e'' hsub'' hp2e
            by_cases hn3 : n = 3
            · -- E₆
              subst hn3
              refine ⟨DynkinType.E₆, ?_⟩
              simp only [DynkinType.cartanMatrix]
              exact extend_at hGCM v e'' CartanMatrix.E₆ 1
                (by decide)
                (fun i j => by rw [E6_succAbove_one_eq_A]; exact (hsub'' i j).symm)
                (fun m => by
                  rw [E6_at_one_row]; split_ifs with h
                  · have : e'' m = e'' u_idx := by ext; omega
                    rw [show m = u_idx from e''.injective this, hu_idx, hAvu_eq]
                  · rw [hAv0 m (fun heq => h (by subst heq; omega))])
                (fun m => by
                  rw [E6_at_one_col]; split_ifs with h
                  · have : e'' m = e'' u_idx := by ext; omega
                    rw [show m = u_idx from e''.injective this, hu_idx, hAuv_eq]
                  · rw [hAv0' m (fun heq => h (by subst heq; omega))])
            · by_cases hn4 : n = 4
              · -- E₇
                subst hn4
                refine ⟨DynkinType.E₇, ?_⟩
                simp only [DynkinType.cartanMatrix]
                exact extend_at hGCM v e'' CartanMatrix.E₇ 1
                  (by decide)
                  (fun i j => by rw [E7_succAbove_one_eq_A]; exact (hsub'' i j).symm)
                  (fun m => by
                    rw [E7_at_one_row]; split_ifs with h
                    · have : e'' m = e'' u_idx := by ext; omega
                      rw [show m = u_idx from e''.injective this, hu_idx, hAvu_eq]
                    · rw [hAv0 m (fun heq => h (by subst heq; omega))])
                  (fun m => by
                    rw [E7_at_one_col]; split_ifs with h
                    · have : e'' m = e'' u_idx := by ext; omega
                      rw [show m = u_idx from e''.injective this, hu_idx, hAuv_eq]
                    · rw [hAv0' m (fun heq => h (by subst heq; omega))])
              · by_cases hn5 : n = 5
                · -- E₈
                  subst hn5
                  refine ⟨DynkinType.E₈, ?_⟩
                  simp only [DynkinType.cartanMatrix]
                  exact extend_at hGCM v e'' CartanMatrix.E₈ 1
                    (by decide)
                    (fun i j => by rw [E8_succAbove_one_eq_A]; exact (hsub'' i j).symm)
                    (fun m => by
                      rw [E8_at_one_row]; split_ifs with h
                      · have : e'' m = e'' u_idx := by ext; omega
                        rw [show m = u_idx from e''.injective this, hu_idx, hAvu_eq]
                      · rw [hAv0 m (fun heq => h (by subst heq; omega))])
                    (fun m => by
                      rw [E8_at_one_col]; split_ifs with h
                      · have : e'' m = e'' u_idx := by ext; omega
                        rw [show m = u_idx from e''.injective this, hu_idx, hAuv_eq]
                      · rw [hAv0' m (fun heq => h (by subst heq; omega))])
                · -- n ≥ 6: Ẽ₈ subgraph → contradiction
                  exfalso
                  let g : Fin 8 → Fin (n+2) := fun k => e''.symm ⟨k.val, by omega⟩
                  have hg_eq : ∀ k : Fin 8, e'' (g k) = ⟨k.val, by omega⟩ :=
                    fun k => e''.apply_symm_apply _
                  have hg_inj : Function.Injective g := by
                    intro a b hab
                    have := congr_arg (fun x => (e'' x).val) hab
                    simp only [hg_eq] at this; exact Fin.ext this
                  have hgu : g ⟨2, by omega⟩ = u_idx :=
                    e''.symm_apply_eq.mpr (Fin.ext hp2e.symm)
                  have hg_ne : ∀ k : Fin 8, k.val ≠ 2 → g k ≠ u_idx := by
                    intro k hk2 h
                    have := congr_arg (fun x => (e'' x).val) h
                    simp only [hg_eq] at this; omega
                  exact absurd hPD (affine_subgraph_contradiction hSym v g hg_inj affineE8
                    (fun k l => by
                      rw [hsub'']; simp only [hg_eq]
                      exact (A_shift_submatrix 8 (n+2) 0 (by omega) k l).trans
                        (affineE8_path k l).symm)
                    (fun k => by
                      rw [affineE8_row_branch]; by_cases hk2 : k.val = 2
                      · rw [if_pos hk2]
                        have : g k = u_idx := by
                          rw [show k = ⟨2, by omega⟩ from Fin.ext hk2]; exact hgu
                        rw [this, hu_idx]; exact hAvu_eq
                      · rw [if_neg hk2]; exact hAv0 _ (hg_ne k hk2))
                    (fun k => by
                      rw [affineE8_col_branch]; by_cases hk2 : k.val = 2
                      · rw [if_pos hk2]
                        have : g k = u_idx := by
                          rw [show k = ⟨2, by omega⟩ from Fin.ext hk2]; exact hgu
                        rw [this, hu_idx]; exact hAuv_eq
                      · rw [if_neg hk2]; exact hAv0' _ (hg_ne k hk2))
                    (by rw [hGCM.diag]; decide)
                    ![2, 4, 6, 5, 4, 3, 2, 1, 3] (by decide) affineE8_null)
  · -- Weight 2
    have hw2 : A v u * A u v = 2 := by omega
    by_cases h_last : (e' u_idx).val = n + 1
    · -- Endpoint at last vertex, weight 2 → B or C
      -- Determine direction: (A v u, A u v) = (-1,-2) or (-2,-1)
      have havu_ge : -2 ≤ A v u := by
        have := le_mul_of_one_le_right (by omega : 0 ≤ -A v u) (by omega : 1 ≤ -A u v)
        nlinarith [neg_mul_neg (A v u) (A u v)]
      by_cases hvu1 : A v u = -1
      · -- A(v,u) = -1, A(u,v) = -2 → B_{n+3}
        have hAuv_eq : A u v = -2 := by nlinarith
        refine ⟨DynkinType.B (n+3) (by omega), ?_⟩
        simp only [DynkinType.cartanMatrix]
        exact extend_at_last hGCM v e' (CartanMatrix.B (n+3))
          (by simp [CartanMatrix.B])
          (fun i j => by rw [B_castSucc_eq_A]; exact (hsub i j).symm)
          (fun m => by
            rw [B_last_row]; split_ifs with h
            · have : e' m = e' u_idx := by ext; omega
              rw [show m = u_idx from e'.injective this, hu_idx]; exact hvu1.symm
            · rw [hAv0 m (fun heq => h (by rw [heq]; exact h_last))])
          (fun m => by
            rw [B_last_col]; split_ifs with h
            · have : e' m = e' u_idx := by ext; omega
              rw [show m = u_idx from e'.injective this, hu_idx]; exact hAuv_eq.symm
            · rw [hAv0' m (fun heq => h (by rw [heq]; exact h_last))])
      · -- A(v,u) = -2, A(u,v) = -1 → C_{n+3}
        have hAvu_eq : A v u = -2 := by omega
        have hAuv_eq : A u v = -1 := by nlinarith
        refine ⟨DynkinType.C (n+3) (by omega), ?_⟩
        simp only [DynkinType.cartanMatrix]
        exact extend_at_last hGCM v e' (CartanMatrix.C (n+3))
          (by simp [CartanMatrix.C])
          (fun i j => by rw [C_castSucc_eq_A]; exact (hsub i j).symm)
          (fun m => by
            rw [C_last_row]; split_ifs with h
            · have : e' m = e' u_idx := by ext; omega
              rw [show m = u_idx from e'.injective this, hu_idx]; exact hAvu_eq.symm
            · rw [hAv0 m (fun heq => h (by rw [heq]; exact h_last))])
          (fun m => by
            rw [C_last_col]; split_ifs with h
            · have : e' m = e' u_idx := by ext; omega
              rw [show m = u_idx from e'.injective this, hu_idx]; exact hAuv_eq.symm
            · rw [hAv0' m (fun heq => h (by rw [heq]; exact h_last))])
    · by_cases h_first : (e' u_idx).val = 0
      · -- Endpoint at first vertex, weight 2 → B or C
        -- Compose e' with path reversal to move u to last position
        let e'' := e'.trans (finRev (n+1))
        have hr_last : (e'' u_idx).val = n + 1 := by
          show ((finRev (n+1)) (e' u_idx)).val = n + 1
          simp only [finRev_val]; omega
        have hsub'' : ∀ i j : Fin (n+2),
            CartanMatrix.A (n+2) (e'' i) (e'' j) = A (v.succAbove i) (v.succAbove j) := by
          intro i j
          show CartanMatrix.A (n+2) ((finRev (n+1)) (e' i)) ((finRev (n+1)) (e' j)) = _
          rw [A_finRev_eq]; exact he' i j
        have havu_ge : -2 ≤ A v u := by
          have := le_mul_of_one_le_right (by omega : 0 ≤ -A v u) (by omega : 1 ≤ -A u v)
          nlinarith [neg_mul_neg (A v u) (A u v)]
        by_cases hvu1 : A v u = -1
        · -- A(v,u) = -1, A(u,v) = -2 → B_{n+3}
          have hAuv_eq : A u v = -2 := by nlinarith
          refine ⟨DynkinType.B (n+3) (by omega), ?_⟩
          simp only [DynkinType.cartanMatrix]
          exact extend_at_last hGCM v e'' (CartanMatrix.B (n+3))
            (by simp [CartanMatrix.B])
            (fun i j => by rw [B_castSucc_eq_A]; exact (hsub'' i j))
            (fun m => by
              rw [B_last_row]; split_ifs with h
              · have : e'' m = e'' u_idx := by ext; omega
                rw [show m = u_idx from e''.injective this, hu_idx]; exact hvu1.symm
              · rw [hAv0 m (fun heq => h (by rw [heq]; exact hr_last))])
            (fun m => by
              rw [B_last_col]; split_ifs with h
              · have : e'' m = e'' u_idx := by ext; omega
                rw [show m = u_idx from e''.injective this, hu_idx]; exact hAuv_eq.symm
              · rw [hAv0' m (fun heq => h (by rw [heq]; exact hr_last))])
        · -- A(v,u) = -2, A(u,v) = -1 → C_{n+3}
          have hAvu_eq : A v u = -2 := by omega
          have hAuv_eq : A u v = -1 := by nlinarith
          refine ⟨DynkinType.C (n+3) (by omega), ?_⟩
          simp only [DynkinType.cartanMatrix]
          exact extend_at_last hGCM v e'' (CartanMatrix.C (n+3))
            (by simp [CartanMatrix.C])
            (fun i j => by rw [C_castSucc_eq_A]; exact (hsub'' i j))
            (fun m => by
              rw [C_last_row]; split_ifs with h
              · have : e'' m = e'' u_idx := by ext; omega
                rw [show m = u_idx from e''.injective this, hu_idx]; exact hAvu_eq.symm
              · rw [hAv0 m (fun heq => h (by rw [heq]; exact hr_last))])
            (fun m => by
              rw [C_last_col]; split_ifs with h
              · have : e'' m = e'' u_idx := by ext; omega
                rw [show m = u_idx from e''.injective this, hu_idx]; exact hAuv_eq.symm
              · rw [hAv0' m (fun heq => h (by rw [heq]; exact hr_last))])
      · -- Interior attachment, weight 2 → contradiction
        -- u maps to interior of A_{n+2}: 1 ≤ p.val < n+1
        exfalso
        have hp_low : 1 ≤ (e' u_idx).val := by omega
        have hp_high : (e' u_idx).val < n + 1 := by omega
        -- Two A-type neighbors of u in the submatrix
        let left_pos : Fin (n+2) := ⟨(e' u_idx).val - 1, by omega⟩
        let right_pos : Fin (n+2) := ⟨(e' u_idx).val + 1, by omega⟩
        let idx1 := e'.symm left_pos
        let idx2 := e'.symm right_pos
        let w1 := v.succAbove idx1
        let w2 := v.succAbove idx2
        -- Distinctness
        have h_lr_ne : left_pos ≠ right_pos := by
          intro h; have := congr_arg Fin.val h; dsimp [left_pos, right_pos] at this; omega
        have h_u_ne_l : e' u_idx ≠ left_pos := by
          intro h; have := congr_arg Fin.val h; dsimp [left_pos] at this; omega
        have h_u_ne_r : e' u_idx ≠ right_pos := by
          intro h; have := congr_arg Fin.val h; dsimp [right_pos] at this; omega
        have h_idx1_ne : idx1 ≠ u_idx := by
          intro h; apply h_u_ne_l; show e' u_idx = left_pos
          rw [← h]; exact e'.apply_symm_apply left_pos
        have h_idx2_ne : idx2 ≠ u_idx := by
          intro h; apply h_u_ne_r; show e' u_idx = right_pos
          rw [← h]; exact e'.apply_symm_apply right_pos
        have h_idx12_ne : idx1 ≠ idx2 := by
          intro h; exact h_lr_ne (e'.symm.injective h)
        have hw1v : w1 ≠ v := Fin.succAbove_ne v idx1
        have hw2v : w2 ≠ v := Fin.succAbove_ne v idx2
        have hw1u : w1 ≠ u := fun h => h_idx1_ne
          (Fin.succAbove_right_injective (hu_idx ▸ h))
        have hw2u : w2 ≠ u := fun h => h_idx2_ne
          (Fin.succAbove_right_injective (hu_idx ▸ h))
        have hw12 : w1 ≠ w2 := fun h => h_idx12_ne
          (Fin.succAbove_right_injective h)
        -- A-type entry facts (use hu_idx to rewrite u = v.succAbove u_idx)
        have hAuw1 : A u w1 = -1 := by
          rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove idx1) = -1
          rw [hsub, show e' idx1 = left_pos from e'.apply_symm_apply left_pos]
          exact A_adj _ _ _ h_u_ne_l (Or.inr (by dsimp [left_pos]; omega))
        have hAuw2 : A u w2 = -1 := by
          rw [← hu_idx]; show A (v.succAbove u_idx) (v.succAbove idx2) = -1
          rw [hsub, show e' idx2 = right_pos from e'.apply_symm_apply right_pos]
          exact A_adj _ _ _ h_u_ne_r (Or.inl (by dsimp [right_pos]))
        have hAw1u : A w1 u = -1 := by
          rw [← hu_idx]; show A (v.succAbove idx1) (v.succAbove u_idx) = -1
          rw [hsub, show e' idx1 = left_pos from e'.apply_symm_apply left_pos]
          exact A_adj _ _ _ (Ne.symm h_u_ne_l) (Or.inl (by dsimp [left_pos]; omega))
        have hAw2u : A w2 u = -1 := by
          rw [← hu_idx]; show A (v.succAbove idx2) (v.succAbove u_idx) = -1
          rw [hsub, show e' idx2 = right_pos from e'.apply_symm_apply right_pos]
          exact A_adj _ _ _ (Ne.symm h_u_ne_r) (Or.inr (by dsimp [right_pos]))
        have hAw1w2 : A w1 w2 = 0 := by
          show A (v.succAbove idx1) (v.succAbove idx2) = 0
          rw [hsub, show e' idx1 = left_pos from e'.apply_symm_apply left_pos,
            show e' idx2 = right_pos from e'.apply_symm_apply right_pos]
          exact A_nonadj _ _ _ h_lr_ne (by push_neg; dsimp [left_pos, right_pos]; omega)
        have hAw2w1 : A w2 w1 = 0 := by
          show A (v.succAbove idx2) (v.succAbove idx1) = 0
          rw [hsub, show e' idx2 = right_pos from e'.apply_symm_apply right_pos,
            show e' idx1 = left_pos from e'.apply_symm_apply left_pos]
          exact A_nonadj _ _ _ (Ne.symm h_lr_ne) (by push_neg; dsimp [left_pos, right_pos]; omega)
        have hAvw1 : A v w1 = 0 := by
          by_contra h; exact hw1u (huniq w1 hw1v h)
        have hAvw2 : A v w2 = 0 := by
          by_contra h; exact hw2u (huniq w2 hw2v h)
        have hAw1v : A w1 v = 0 := (hGCM.zero_iff v w1 hw1v.symm).mp hAvw1
        have hAw2v : A w2 v = 0 := (hGCM.zero_iff v w2 hw2v.symm).mp hAvw2
        -- Test vector: x(v) = -A(v,u), x(u) = 2, x(w1) = 1, x(w2) = 1, rest = 0
        set x : Fin (n+3) → ℚ := fun i =>
          if i = v then -(↑(A v u : ℤ) : ℚ)
          else if i = u then 2
          else if i = w1 then 1
          else if i = w2 then 1
          else 0
        have hx : x ≠ 0 := by
          intro h; have := congr_fun h u
          simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
        have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ w1 → k ≠ w2 → x k = 0 :=
          fun k h1 h2 h3 h4 => by simp [x, h1, h2, h3, h4]
        -- The "rest is zero" fact for sum_four
        have hrest : ∀ (r : Fin (n+3) → ℚ) (m : Fin (n+3)),
            m ≠ v → m ≠ u → m ≠ w1 → m ≠ w2 → r m * x m = 0 := by
          intro r m h1 h2 h3 h4; simp [x0 m h1 h2 h3 h4]
        -- Inner sums all vanish (null vector on 4-vertex submatrix)
        have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
          rw [sum_four huv.symm hw1v.symm hw2v.symm hw1u.symm hw2u.symm hw12
            (fun m => (↑(A v m) : ℚ) * x m)
            (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A v j)) m h1 h2 h3 h4)]
          simp only [x, ↓reduceIte, if_neg huv, if_neg hw1v, if_neg hw2v,
            if_neg hw1u, if_neg hw2u, if_neg hw12, if_neg hw12.symm,
            hGCM.diag v, hAvw1, hAvw2]; push_cast; ring
        have inner_u : ∑ j, (↑(A u j) : ℚ) * x j = 0 := by
          rw [sum_four huv.symm hw1v.symm hw2v.symm hw1u.symm hw2u.symm hw12
            (fun m => (↑(A u m) : ℚ) * x m)
            (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A u j)) m h1 h2 h3 h4)]
          simp only [x, ↓reduceIte, if_neg huv, if_neg hw1v, if_neg hw2v,
            if_neg hw1u, if_neg hw2u, if_neg hw12.symm,
            hGCM.diag u, hAuw1, hAuw2]; push_cast
          have : (↑(A u v) : ℚ) * ↑(A v u) = 2 := by
            rw [mul_comm]; exact_mod_cast hw2
          linarith
        have inner_w1 : ∑ j, (↑(A w1 j) : ℚ) * x j = 0 := by
          rw [sum_four huv.symm hw1v.symm hw2v.symm hw1u.symm hw2u.symm hw12
            (fun m => (↑(A w1 m) : ℚ) * x m)
            (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A w1 j)) m h1 h2 h3 h4)]
          simp only [x, ↓reduceIte, if_neg hw1v, if_neg hw1u, if_neg hw12,
            if_neg huv, hGCM.diag w1, hAw1v, hAw1u, hAw1w2]; push_cast; ring
        have inner_w2 : ∑ j, (↑(A w2 j) : ℚ) * x j = 0 := by
          rw [sum_four huv.symm hw1v.symm hw2v.symm hw1u.symm hw2u.symm hw12
            (fun m => (↑(A w2 m) : ℚ) * x m)
            (fun m h1 h2 h3 h4 => hrest (fun j => ↑(A w2 j)) m h1 h2 h3 h4)]
          simp only [x, ↓reduceIte, if_neg hw2v, if_neg hw2u, if_neg hw12.symm,
            if_neg huv, hGCM.diag w2, hAw2v, hAw2u, hAw2w1]; push_cast; ring
        -- qform = 0: each term is 0 (either x(i)=0 or inner(i)=0)
        have hq : qform hSym.d A x = 0 := by
          rw [qform_eq_sum_mul]; apply Finset.sum_eq_zero; intro i _
          by_cases hiv : i = v; · subst hiv; simp [inner_v]
          by_cases hiu : i = u; · subst hiu; simp [inner_u]
          by_cases hiw1 : i = w1; · subst hiw1; simp [inner_w1]
          by_cases hiw2 : i = w2; · subst hiw2; simp [inner_w2]
          simp [x0 i hiv hiu hiw1 hiw2]
        exact absurd hPD (not_posDef_of_nonpos hSym x hx (le_of_eq hq))

end BLD.Lie.Cartan
