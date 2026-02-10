/- BLD Calculus — Strong Normalization

   Every well-typed closed term reduces to a value.
   Proof by Tait's method (logical relations / reducibility).

   Since Ty has no recursive types (no μ-binder) and no fixpoint
   combinator, the simply-typed BLD calculus is strongly normalizing.

   Reference: bld-calculus.md §6 (Theorem 6.1)
-/

import BLD.MultiStep

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- Substitution infrastructure
-- ═══════════════════════════════════════════════════════════

private theorem rename_congr {Γ Δ : Context} {a : Ty}
    {ρ₁ ρ₂ : {c : Ty} → Lookup Γ c → Lookup Δ c}
    (h : ∀ {c : Ty} (x : Lookup Γ c), ρ₁ x = ρ₂ x)
    (e : Term Γ a) : rename ρ₁ e = rename ρ₂ e := by
  induction e generalizing Δ with
  | unit => rfl
  | var x => simp only [rename]; congr 1; exact h x
  | inl _ ih => simp only [rename]; congr 1; exact ih @h
  | inr _ ih => simp only [rename]; congr 1; exact ih @h
  | case _ _ _ ihs ihl ihr =>
    simp only [rename]; congr 1
    · exact ihs @h
    · exact ihl (fun x => by cases x <;> simp [ext, h])
    · exact ihr (fun x => by cases x <;> simp [ext, h])
  | lam _ ih =>
    simp only [rename]; congr 1
    exact ih (fun x => by cases x <;> simp [ext, h])
  | app _ _ ihf ihx =>
    simp only [rename]; congr 1; exact ihf @h; exact ihx @h
  | tnil => rfl
  | tcons _ _ ihv ihvs =>
    simp only [rename]; congr 1; exact ihv @h; exact ihvs @h
  | head _ ih => simp only [rename]; congr 1; exact ih @h
  | tail _ ih => simp only [rename]; congr 1; exact ih @h

private theorem subst_congr {Γ Δ : Context} {a : Ty}
    {σ₁ σ₂ : {c : Ty} → Lookup Γ c → Term Δ c}
    (h : ∀ {c : Ty} (x : Lookup Γ c), σ₁ x = σ₂ x)
    (e : Term Γ a) : subst σ₁ e = subst σ₂ e := by
  induction e generalizing Δ with
  | unit => rfl
  | var x => exact h x
  | inl _ ih => simp only [subst]; congr 1; exact ih @h
  | inr _ ih => simp only [subst]; congr 1; exact ih @h
  | case _ _ _ ihs ihl ihr =>
    simp only [subst]; congr 1
    · exact ihs @h
    · exact ihl (fun x => by cases x <;> simp [exts, h])
    · exact ihr (fun x => by cases x <;> simp [exts, h])
  | lam _ ih =>
    simp only [subst]; congr 1
    exact ih (fun x => by cases x <;> simp [exts, h])
  | app _ _ ihf ihx =>
    simp only [subst]; congr 1; exact ihf @h; exact ihx @h
  | tnil => rfl
  | tcons _ _ ihv ihvs =>
    simp only [subst]; congr 1; exact ihv @h; exact ihvs @h
  | head _ ih => simp only [subst]; congr 1; exact ih @h
  | tail _ ih => simp only [subst]; congr 1; exact ih @h

private theorem subst_var {Γ : Context} {a : Ty} (e : Term Γ a) :
    subst (fun {c : Ty} (x : Lookup Γ c) => Term.var x) e = e := by
  induction e with
  | unit | var _ | tnil => rfl
  | inl _ ih => simp only [subst, ih]
  | inr _ ih => simp only [subst, ih]
  | head _ ih => simp only [subst, ih]
  | tail _ ih => simp only [subst, ih]
  | app _ _ ihf ihx => simp only [subst, ihf, ihx]
  | tcons _ _ ihv ihvs => simp only [subst, ihv, ihvs]
  | case _ _ _ ihs ihl ihr =>
    simp only [subst, ihs]; congr 1
    · exact (subst_congr (fun x => by cases x <;> rfl) _).trans ihl
    · exact (subst_congr (fun x => by cases x <;> rfl) _).trans ihr
  | lam _ ih =>
    simp only [subst]; congr 1
    exact (subst_congr (fun x => by cases x <;> rfl) _).trans ih

private theorem rename_subst {Γ Δ Ε : Context} {a : Ty}
    (σ : {c : Ty} → Lookup Δ c → Term Ε c)
    (ρ : {c : Ty} → Lookup Γ c → Lookup Δ c)
    (e : Term Γ a) :
    subst σ (rename ρ e) = subst (fun x => σ (ρ x)) e := by
  induction e generalizing Δ Ε with
  | unit => rfl
  | var x => simp only [rename, subst]
  | inl _ ih => simp only [rename, subst]; congr 1; exact ih σ ρ
  | inr _ ih => simp only [rename, subst]; congr 1; exact ih σ ρ
  | case _ _ _ ihs ihl ihr =>
    simp only [rename, subst]; congr 1
    · exact ihs σ ρ
    · rw [ihl (exts σ) (ext ρ)]
      exact subst_congr (fun x => by cases x <;> simp [ext, exts]) _
    · rw [ihr (exts σ) (ext ρ)]
      exact subst_congr (fun x => by cases x <;> simp [ext, exts]) _
  | lam _ ih =>
    simp only [rename, subst]; congr 1
    rw [ih (exts σ) (ext ρ)]
    exact subst_congr (fun x => by cases x <;> simp [ext, exts]) _
  | app _ _ ihf ihx =>
    simp only [rename, subst]; congr 1; exact ihf σ ρ; exact ihx σ ρ
  | tnil => rfl
  | tcons _ _ ihv ihvs =>
    simp only [rename, subst]; congr 1; exact ihv σ ρ; exact ihvs σ ρ
  | head _ ih => simp only [rename, subst]; congr 1; exact ih σ ρ
  | tail _ ih => simp only [rename, subst]; congr 1; exact ih σ ρ

private theorem rename_rename {Γ Δ Ε : Context} {a : Ty}
    (ρ : {c : Ty} → Lookup Δ c → Lookup Ε c)
    (ρ' : {c : Ty} → Lookup Γ c → Lookup Δ c)
    (e : Term Γ a) :
    rename ρ (rename ρ' e) = rename (fun x => ρ (ρ' x)) e := by
  induction e generalizing Δ Ε with
  | unit => rfl
  | var x => simp only [rename]
  | inl _ ih => simp only [rename]; congr 1; exact ih ρ ρ'
  | inr _ ih => simp only [rename]; congr 1; exact ih ρ ρ'
  | case _ _ _ ihs ihl ihr =>
    simp only [rename]; congr 1
    · exact ihs ρ ρ'
    · rw [ihl (ext ρ) (ext ρ')]
      exact rename_congr (fun x => by cases x <;> simp [ext]) _
    · rw [ihr (ext ρ) (ext ρ')]
      exact rename_congr (fun x => by cases x <;> simp [ext]) _
  | lam _ ih =>
    simp only [rename]; congr 1
    rw [ih (ext ρ) (ext ρ')]
    exact rename_congr (fun x => by cases x <;> simp [ext]) _
  | app _ _ ihf ihx =>
    simp only [rename]; congr 1; exact ihf ρ ρ'; exact ihx ρ ρ'
  | tnil => rfl
  | tcons _ _ ihv ihvs =>
    simp only [rename]; congr 1; exact ihv ρ ρ'; exact ihvs ρ ρ'
  | head _ ih => simp only [rename]; congr 1; exact ih ρ ρ'
  | tail _ ih => simp only [rename]; congr 1; exact ih ρ ρ'

private theorem subst_rename {Γ Δ Ε : Context} {a : Ty}
    (ρ : {c : Ty} → Lookup Δ c → Lookup Ε c)
    (σ : {c : Ty} → Lookup Γ c → Term Δ c)
    (e : Term Γ a) :
    rename ρ (subst σ e) = subst (fun x => rename ρ (σ x)) e := by
  induction e generalizing Δ Ε with
  | unit => rfl
  | var x => simp only [subst]
  | inl _ ih => simp only [subst, rename]; congr 1; exact ih ρ σ
  | inr _ ih => simp only [subst, rename]; congr 1; exact ih ρ σ
  | case _ _ _ ihs ihl ihr =>
    simp only [subst, rename]; congr 1
    · exact ihs ρ σ
    · rw [ihl (ext ρ) (exts σ)]
      exact subst_congr (fun x => by
        cases x with
        | here => simp [exts, ext, rename]
        | there y => simp [exts, rename_rename, ext]) _
    · rw [ihr (ext ρ) (exts σ)]
      exact subst_congr (fun x => by
        cases x with
        | here => simp [exts, ext, rename]
        | there y => simp [exts, rename_rename, ext]) _
  | lam _ ih =>
    simp only [subst, rename]; congr 1
    rw [ih (ext ρ) (exts σ)]
    exact subst_congr (fun x => by
      cases x with
      | here => simp [exts, ext, rename]
      | there y => simp [exts, rename_rename, ext]) _
  | app _ _ ihf ihx =>
    simp only [subst, rename]; congr 1; exact ihf ρ σ; exact ihx ρ σ
  | tnil => rfl
  | tcons _ _ ihv ihvs =>
    simp only [subst, rename]; congr 1; exact ihv ρ σ; exact ihvs ρ σ
  | head _ ih => simp only [subst, rename]; congr 1; exact ih ρ σ
  | tail _ ih => simp only [subst, rename]; congr 1; exact ih ρ σ

private theorem subst_subst {Γ Δ Ε : Context} {a : Ty}
    (τ : {c : Ty} → Lookup Δ c → Term Ε c)
    (σ : {c : Ty} → Lookup Γ c → Term Δ c)
    (e : Term Γ a) :
    subst τ (subst σ e) = subst (fun x => subst τ (σ x)) e := by
  induction e generalizing Δ Ε with
  | unit => rfl
  | var x => simp only [subst]
  | inl _ ih => simp only [subst]; congr 1; exact ih τ σ
  | inr _ ih => simp only [subst]; congr 1; exact ih τ σ
  | case _ _ _ ihs ihl ihr =>
    simp only [subst]; congr 1
    · exact ihs τ σ
    · rw [ihl (exts τ) (exts σ)]
      exact subst_congr (fun x => by
        cases x with
        | here => simp [exts, subst]
        | there y => simp [exts, rename_subst, subst_rename]) _
    · rw [ihr (exts τ) (exts σ)]
      exact subst_congr (fun x => by
        cases x with
        | here => simp [exts, subst]
        | there y => simp [exts, rename_subst, subst_rename]) _
  | lam _ ih =>
    simp only [subst]; congr 1
    rw [ih (exts τ) (exts σ)]
    exact subst_congr (fun x => by
      cases x with
      | here => simp [exts, subst]
      | there y => simp [exts, rename_subst, subst_rename]) _
  | app _ _ ihf ihx =>
    simp only [subst]; congr 1; exact ihf τ σ; exact ihx τ σ
  | tnil => rfl
  | tcons _ _ ihv ihvs =>
    simp only [subst]; congr 1; exact ihv τ σ; exact ihvs τ σ
  | head _ ih => simp only [subst]; congr 1; exact ih τ σ
  | tail _ ih => simp only [subst]; congr 1; exact ih τ σ

private theorem subst_cons {Γ : Context} {a b : Ty}
    (σ : {c : Ty} → Lookup Γ c → Term [] c)
    (v : Term [] a)
    (body : Term (a :: Γ) b) :
    subst₁ v (subst (exts σ) body) =
    subst (fun {c : Ty} (x : Lookup (a :: Γ) c) =>
      match x with
      | .here => v
      | .there y => σ y) body := by
  simp only [subst₁]
  rw [subst_subst]
  exact subst_congr (fun x => by
    cases x with
    | here => rfl
    | there y =>
      simp only [exts]
      rw [rename_subst]
      exact subst_var _) _

-- ═══════════════════════════════════════════════════════════
-- Reducibility (logical relation)
-- ═══════════════════════════════════════════════════════════

/-- The reducibility predicate. A closed term of type `a` is reducible
    if it halts at a value and satisfies a type-indexed structural condition. -/
def R : (a : Ty) → Term [] a → Prop
  | .unit, e => ∃ v, Steps e v ∧ Value v
  | .sum a b, e => ∃ v, Steps e v ∧ Value v ∧
      ((∃ v', v = .inl v' ∧ R a v') ∨ (∃ v', v = .inr v' ∧ R b v'))
  | .fn a b, e => ∃ v, Steps e v ∧ Value v ∧
      (∀ (e' : Term [] a), R a e' → R b (.app v e'))
  | .prod 0 _, e => ∃ v, Steps e v ∧ Value v
  | .prod (n + 1) a, e => ∃ v, Steps e v ∧ Value v ∧
      (∃ v' vs, v = .tcons v' vs ∧ R a v' ∧ R (.prod n a) vs)

/-- Reducible terms halt: they step to a value. -/
theorem R_halts {a : Ty} {e : Term [] a} (h : R a e) :
    ∃ v, Steps e v ∧ Value v := by
  match a with
  | .unit => simp only [R] at h; exact h
  | .sum _ _ => simp only [R] at h; let ⟨v, steps, val, _⟩ := h; exact ⟨v, steps, val⟩
  | .fn _ _ => simp only [R] at h; let ⟨v, steps, val, _⟩ := h; exact ⟨v, steps, val⟩
  | .prod 0 _ => simp only [R] at h; exact h
  | .prod (_ + 1) _ => simp only [R] at h; let ⟨v, steps, val, _⟩ := h; exact ⟨v, steps, val⟩

/-- Backward closure of R under a single step. -/
theorem R_step {a : Ty} {e e' : Term [] a}
    (hs : Step e e') (h : R a e') : R a e := by
  match a with
  | .unit =>
    simp only [R] at h ⊢
    let ⟨v, steps, val⟩ := h; exact ⟨v, .step hs steps, val⟩
  | .sum _ _ =>
    simp only [R] at h ⊢
    let ⟨v, steps, val, extra⟩ := h; exact ⟨v, .step hs steps, val, extra⟩
  | .fn _ _ =>
    simp only [R] at h ⊢
    let ⟨v, steps, val, extra⟩ := h; exact ⟨v, .step hs steps, val, extra⟩
  | .prod 0 _ =>
    simp only [R] at h ⊢
    let ⟨v, steps, val⟩ := h; exact ⟨v, .step hs steps, val⟩
  | .prod (_ + 1) _ =>
    simp only [R] at h ⊢
    let ⟨v, steps, val, extra⟩ := h; exact ⟨v, .step hs steps, val, extra⟩

/-- Backward closure of R under multi-step reduction. -/
theorem R_steps {a : Ty} {e e' : Term [] a}
    (hs : Steps e e') (h : R a e') : R a e := by
  induction hs with
  | refl => exact h
  | step hs _ ih => exact R_step hs (ih h)

/-- If `R a e` and `e` steps to value `v`, then `R a v`. -/
theorem R_of_value {a : Ty} {e v : Term [] a}
    (hr : R a e) (hs : Steps e v) (hv : Value v) : R a v := by
  match a with
  | .unit =>
    simp only [R] at hr ⊢
    exact ⟨v, .refl, hv⟩
  | .sum _ _ =>
    simp only [R] at hr ⊢
    obtain ⟨v', steps', val', extra⟩ := hr
    have heq : v = v' := steps_value_unique hs hv steps' val'
    subst heq
    exact ⟨v, .refl, val', extra⟩
  | .fn _ _ =>
    simp only [R] at hr ⊢
    obtain ⟨v', steps', val', extra⟩ := hr
    have heq : v = v' := steps_value_unique hs hv steps' val'
    subst heq
    exact ⟨v, .refl, val', extra⟩
  | .prod 0 _ =>
    simp only [R] at hr ⊢
    exact ⟨v, .refl, hv⟩
  | .prod (_ + 1) _ =>
    simp only [R] at hr ⊢
    obtain ⟨v', steps', val', extra⟩ := hr
    have heq : v = v' := steps_value_unique hs hv steps' val'
    subst heq
    exact ⟨v, .refl, val', extra⟩

-- ═══════════════════════════════════════════════════════════
-- Reducible closing substitutions
-- ═══════════════════════════════════════════════════════════

/-- A closing substitution is reducible if every image is a value satisfying R. -/
def RSub : (Γ : Context) → ({c : Ty} → Lookup Γ c → Term [] c) → Prop
  | [], _ => True
  | a :: Γ, σ => Value (σ .here) ∧ R a (σ .here) ∧ RSub Γ (fun x => σ (.there x))

/-- Extract reducibility from RSub by following a lookup. -/
theorem RSub_lookup {Γ : Context} {a : Ty}
    {σ : {c : Ty} → Lookup Γ c → Term [] c}
    (x : Lookup Γ a) (hσ : RSub Γ σ) : R a (σ x) := by
  induction x with
  | here =>
    simp only [RSub] at hσ
    exact hσ.2.1
  | there _ ih =>
    simp only [RSub] at hσ
    exact ih hσ.2.2

/-- Extend a reducible substitution with a new value. -/
theorem RSub_cons {Γ : Context} {a : Ty}
    {σ : {c : Ty} → Lookup Γ c → Term [] c}
    {v : Term [] a}
    (hv : Value v) (hrv : R a v) (hσ : RSub Γ σ) :
    RSub (a :: Γ) (fun {c : Ty} (x : Lookup (a :: Γ) c) =>
      match x with
      | .here => v
      | .there y => σ y) := by
  simp only [RSub]
  exact ⟨hv, hrv, hσ⟩

-- ═══════════════════════════════════════════════════════════
-- Fundamental theorem (Tait's method)
-- ═══════════════════════════════════════════════════════════

/-- **Fundamental Theorem.** If `σ` is a reducible closing substitution for `Γ`,
    then for every well-typed term `e : Term Γ a`, `subst σ e` is reducible. -/
theorem fundamental {Γ : Context} {a : Ty} (e : Term Γ a)
    (σ : {c : Ty} → Lookup Γ c → Term [] c) (hσ : RSub Γ σ) :
    R a (subst σ e) := by
  induction e with
  | var x => exact RSub_lookup x hσ
  | unit => simp only [subst, R]; exact ⟨.unit, .refl, .unit⟩
  | tnil => simp only [subst, R]; exact ⟨.tnil, .refl, .tnil⟩
  | inl e ih =>
    simp only [subst]
    have hre := ih σ hσ
    obtain ⟨v, steps, val⟩ := R_halts hre
    simp only [R]
    exact ⟨.inl v, steps_inl steps, .inl val, .inl ⟨v, rfl, R_of_value hre steps val⟩⟩
  | inr e ih =>
    simp only [subst]
    have hre := ih σ hσ
    obtain ⟨v, steps, val⟩ := R_halts hre
    simp only [R]
    exact ⟨.inr v, steps_inr steps, .inr val, .inr ⟨v, rfl, R_of_value hre steps val⟩⟩
  | tcons v vs ihv ihvs =>
    simp only [subst]
    have hrv := ihv σ hσ
    have hrvs := ihvs σ hσ
    obtain ⟨vv, stepsv, valv⟩ := R_halts hrv
    obtain ⟨vvs, stepsvs, valvs⟩ := R_halts hrvs
    simp only [R]
    exact ⟨.tcons vv vvs,
      steps_trans (steps_tcons₁ stepsv) (steps_tcons₂ valv stepsvs),
      .tcons valv valvs,
      vv, vvs, rfl,
      R_of_value hrv stepsv valv,
      R_of_value hrvs stepsvs valvs⟩
  | lam body ih =>
    simp only [subst, R]
    refine ⟨.lam (subst (exts σ) body), .refl, .lam, ?_⟩
    intro e' hre'
    obtain ⟨vx, steps_x, hvx⟩ := R_halts hre'
    have hre'v := R_of_value hre' steps_x hvx
    apply R_steps (steps_trans (steps_app₂ .lam steps_x) (steps_one (.appβ hvx)))
    rw [subst_cons]
    exact ih _ (RSub_cons hvx hre'v hσ)
  | app f x ihf ihx =>
    simp only [subst]
    have hrf := ihf σ hσ
    have hrx := ihx σ hσ
    simp only [R] at hrf
    obtain ⟨vf, steps_f, hvf, hfn⟩ := hrf
    have hrapp := hfn (subst σ x) hrx
    exact R_steps (steps_app₁ steps_f) hrapp
  | case s e₁ e₂ ihs ihl ihr =>
    simp only [subst]
    have hrs := ihs σ hσ
    simp only [R] at hrs
    obtain ⟨vs, steps_s, hvs, hsum⟩ := hrs
    cases hsum with
    | inl hl =>
      obtain ⟨v', heq, hrv'⟩ := hl
      subst heq
      have hvalv' : Value v' := by cases hvs with | inl hv => exact hv
      apply R_steps (steps_case steps_s)
      apply R_step (.caseL hvalv')
      rw [subst_cons]
      exact ihl _ (RSub_cons hvalv' (R_of_value hrv' .refl hvalv') hσ)
    | inr hr =>
      obtain ⟨v', heq, hrv'⟩ := hr
      subst heq
      have hvalv' : Value v' := by cases hvs with | inr hv => exact hv
      apply R_steps (steps_case steps_s)
      apply R_step (.caseR hvalv')
      rw [subst_cons]
      exact ihr _ (RSub_cons hvalv' (R_of_value hrv' .refl hvalv') hσ)
  | head e ih =>
    simp only [subst]
    have hre := ih σ hσ
    simp only [R] at hre
    obtain ⟨vs, steps, hvs, v', vs', heq, hrv', hrvs'⟩ := hre
    subst heq
    have hvalv' : Value v' := by cases hvs with | tcons hv _ => exact hv
    have hvalvs' : Value vs' := by cases hvs with | tcons _ hvs => exact hvs
    apply R_steps (steps_head steps)
    apply R_step (.headβ hvalv' hvalvs')
    exact R_of_value hrv' .refl hvalv'
  | tail e ih =>
    simp only [subst]
    have hre := ih σ hσ
    simp only [R] at hre
    obtain ⟨vs, steps, hvs, v', vs', heq, hrv', hrvs'⟩ := hre
    subst heq
    have hvalv' : Value v' := by cases hvs with | tcons hv _ => exact hv
    have hvalvs' : Value vs' := by cases hvs with | tcons _ hvs => exact hvs
    apply R_steps (steps_tail steps)
    apply R_step (.tailβ hvalv' hvalvs')
    exact R_of_value hrvs' .refl hvalvs'

-- ═══════════════════════════════════════════════════════════
-- Strong normalization
-- ═══════════════════════════════════════════════════════════

/-- **Theorem 6.1 (Strong Normalization).** Every well-typed closed term
    reduces to a value. The BLD calculus is strongly normalizing. -/
theorem normalization {a : Ty} (e : Term [] a) : ∃ v, Steps e v ∧ Value v := by
  have h : R a e := by
    have hsub : subst (fun {c : Ty} (x : Lookup [] c) => Term.var x) e = e :=
      subst_var e
    rw [← hsub]
    exact fundamental e (fun x => Term.var x) trivial
  exact R_halts h

end Ty
