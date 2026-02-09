/- BLD Calculus — Operational Semantics and Metatheory

   Small-step call-by-value reduction with:
   - Progress (Theorem 5.2)
   - Preservation (Theorem 5.4) — free from intrinsic typing
   - Type Safety (Corollary 5.5)
   - Determinism — CBV is deterministic
   - Values don't step — values are terminal

   Reference: bld-calculus.md §4 (Rules 4.1-4.8), §5 (Theorems 5.2-5.5)
-/

import BLD.Term
import BLD.Subst

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- Small-step call-by-value reduction
-- Reference: bld-calculus.md §4, Rules 4.1-4.8
-- ═══════════════════════════════════════════════════════════

/-- Small-step CBV reduction relation.
    Γ is a parameter. a is an index (varies across congruence rules).
    Within each constructor, source and target share the same a —
    this IS Preservation (Theorem 5.4). -/
inductive Step {Γ : Context} : {a : Ty} → Term Γ a → Term Γ a → Prop where
  -- β-reductions (Rules 4.1-4.4)
  | caseL {a b c : Ty} {v : Term Γ a} {e₁ : Term (a :: Γ) c} {e₂ : Term (b :: Γ) c} :
      Value v → Step (.case (.inl v) e₁ e₂) (subst₁ v e₁)
  | caseR {a b c : Ty} {v : Term Γ b} {e₁ : Term (a :: Γ) c} {e₂ : Term (b :: Γ) c} :
      Value v → Step (.case (.inr v) e₁ e₂) (subst₁ v e₂)
  | appβ {a b : Ty} {body : Term (a :: Γ) b} {w : Term Γ a} :
      Value w → Step (.app (.lam body) w) (subst₁ w body)
  | headβ {n : Nat} {a : Ty} {v : Term Γ a} {vs : Term Γ (.prod n a)} :
      Value v → Value vs → Step (.head (.tcons v vs)) v
  | tailβ {n : Nat} {a : Ty} {v : Term Γ a} {vs : Term Γ (.prod n a)} :
      Value v → Value vs → Step (.tail (.tcons v vs)) vs
  -- Congruence rules (Rules 4.5-4.8)
  | inlξ {a b : Ty} {e e' : Term Γ a} :
      Step e e' → Step (.inl (b := b) e) (.inl e')
  | inrξ {a b : Ty} {e e' : Term Γ b} :
      Step e e' → Step (.inr (a := a) e) (.inr e')
  | caseξ {a b c : Ty} {e e' : Term Γ (.sum a b)}
      {e₁ : Term (a :: Γ) c} {e₂ : Term (b :: Γ) c} :
      Step e e' → Step (.case e e₁ e₂) (.case e' e₁ e₂)
  | appξ₁ {a b : Ty} {e₁ e₁' : Term Γ (.fn a b)} {e₂ : Term Γ a} :
      Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | appξ₂ {a b : Ty} {v : Term Γ (.fn a b)} {e₂ e₂' : Term Γ a} :
      Value v → Step e₂ e₂' → Step (.app v e₂) (.app v e₂')
  | tconsξ₁ {n : Nat} {a : Ty} {e e' : Term Γ a} {es : Term Γ (.prod n a)} :
      Step e e' → Step (.tcons e es) (.tcons e' es)
  | tconsξ₂ {n : Nat} {a : Ty} {v : Term Γ a} {es es' : Term Γ (.prod n a)} :
      Value v → Step es es' → Step (.tcons v es) (.tcons v es')
  | headξ {n : Nat} {a : Ty} {e e' : Term Γ (.prod (n + 1) a)} :
      Step e e' → Step (.head e) (.head e')
  | tailξ {n : Nat} {a : Ty} {e e' : Term Γ (.prod (n + 1) a)} :
      Step e e' → Step (.tail e) (.tail e')

/-- Notation: `e ⟶ e'` for single-step reduction. -/
scoped infixl:50 " ⟶ " => Step

-- ═══════════════════════════════════════════════════════════
-- Values don't step (values are terminal)
-- ═══════════════════════════════════════════════════════════

/-- A value cannot take a step. -/
theorem value_no_step {Γ : Context} {a : Ty} {e e' : Term Γ a}
    (hv : Value e) (hs : Step e e') : False := by
  induction hv with
  | unit => nomatch hs
  | lam => nomatch hs
  | tnil => nomatch hs
  | inl _ ih =>
    cases hs with
    | inlξ hs' => exact ih hs'
  | inr _ ih =>
    cases hs with
    | inrξ hs' => exact ih hs'
  | tcons _ _ ihv ihvs =>
    cases hs with
    | tconsξ₁ hs' => exact ihv hs'
    | tconsξ₂ _ hs' => exact ihvs hs'

/-- Values are irreducible (existential form). -/
theorem value_irreducible {Γ : Context} {a : Ty} {e : Term Γ a}
    (hv : Value e) : ¬ ∃ e', Step e e' :=
  fun ⟨_, hs⟩ => value_no_step hv hs

-- ═══════════════════════════════════════════════════════════
-- Progress (Theorem 5.2)
-- Reference: bld-calculus.md §5.2
-- ═══════════════════════════════════════════════════════════

/-- **Theorem 5.2 (Progress).** If ⊢ e : τ then either e is a value
    or there exists e' such that e ⟶ e'. -/
theorem progress {a : Ty} (e : Term [] a) : Value e ∨ ∃ e', Step e e' := by
  match e with
  | .unit => exact Or.inl .unit
  | .var idx => exact nomatch idx
  | .lam _ => exact Or.inl .lam
  | .tnil => exact Or.inl .tnil
  | .inl e =>
    match progress e with
    | .inl hv => exact .inl (.inl hv)
    | .inr ⟨e', hs⟩ => exact .inr ⟨_, .inlξ hs⟩
  | .inr e =>
    match progress e with
    | .inl hv => exact .inl (.inr hv)
    | .inr ⟨e', hs⟩ => exact .inr ⟨_, .inrξ hs⟩
  | .case s l r =>
    match progress s with
    | .inr ⟨s', hs⟩ => exact .inr ⟨_, .caseξ hs⟩
    | .inl hv =>
      match s, hv with
      | .inl _, .inl hv => exact .inr ⟨_, .caseL hv⟩
      | .inr _, .inr hv => exact .inr ⟨_, .caseR hv⟩
  | .app f x =>
    match progress f with
    | .inr ⟨f', hs⟩ => exact .inr ⟨_, .appξ₁ hs⟩
    | .inl hvf =>
      match progress x with
      | .inr ⟨x', hs⟩ => exact .inr ⟨_, .appξ₂ hvf hs⟩
      | .inl hvx =>
        match f, hvf with
        | .lam _, .lam => exact .inr ⟨_, .appβ hvx⟩
  | .tcons v vs =>
    match progress v with
    | .inr ⟨v', hs⟩ => exact .inr ⟨_, .tconsξ₁ hs⟩
    | .inl hvv =>
      match progress vs with
      | .inr ⟨vs', hs⟩ => exact .inr ⟨_, .tconsξ₂ hvv hs⟩
      | .inl hvvs => exact .inl (.tcons hvv hvvs)
  | .head e =>
    match progress e with
    | .inr ⟨e', hs⟩ => exact .inr ⟨_, .headξ hs⟩
    | .inl hv =>
      match e, hv with
      | .tcons _ _, .tcons hvv hvvs => exact .inr ⟨_, .headβ hvv hvvs⟩
  | .tail e =>
    match progress e with
    | .inr ⟨e', hs⟩ => exact .inr ⟨_, .tailξ hs⟩
    | .inl hv =>
      match e, hv with
      | .tcons _ _, .tcons hvv hvvs => exact .inr ⟨_, .tailβ hvv hvvs⟩

-- ═══════════════════════════════════════════════════════════
-- Preservation (Theorem 5.4)
-- Reference: bld-calculus.md §5.4
-- ═══════════════════════════════════════════════════════════

/-- **Theorem 5.4 (Preservation).** If Γ ⊢ e : τ and e ⟶ e', then Γ ⊢ e' : τ.

    With intrinsic typing, this is trivially true: `Step` maps
    `Term Γ a → Term Γ a → Prop`, so both sides have the same type
    index `a` by construction. -/
theorem preservation {Γ : Context} {a : Ty} {e e' : Term Γ a}
    (_h : Step e e') : True := trivial

-- ═══════════════════════════════════════════════════════════
-- Type Safety (Corollary 5.5)
-- Reference: bld-calculus.md §5.5
-- ═══════════════════════════════════════════════════════════

/-- **Corollary 5.5 (Type Safety).** Well-typed closed terms don't get stuck. -/
theorem type_safety {a : Ty} (e : Term [] a) :
    Value e ∨ ∃ e', Step e e' :=
  progress e

-- ═══════════════════════════════════════════════════════════
-- Determinism
-- ═══════════════════════════════════════════════════════════

/-- **Determinism.** CBV reduction is deterministic:
    if e ⟶ e₁ and e ⟶ e₂ then e₁ = e₂. -/
theorem deterministic {Γ : Context} {a : Ty} {e e₁ e₂ : Term Γ a}
    (h₁ : Step e e₁) (h₂ : Step e e₂) : e₁ = e₂ := by
  induction h₁ with
  | caseL hv₁ =>
    cases h₂ with
    | caseL _ => rfl
    | caseξ hs => exact (value_no_step (.inl hv₁) hs).elim
  | caseR hv₁ =>
    cases h₂ with
    | caseR _ => rfl
    | caseξ hs => exact (value_no_step (.inr hv₁) hs).elim
  | appβ hw₁ =>
    cases h₂ with
    | appβ _ => rfl
    | appξ₁ hs => exact (value_no_step .lam hs).elim
    | appξ₂ _ hs => exact (value_no_step hw₁ hs).elim
  | headβ hv₁ hvs₁ =>
    cases h₂ with
    | headβ _ _ => rfl
    | headξ hs => exact (value_no_step (.tcons hv₁ hvs₁) hs).elim
  | tailβ hv₁ hvs₁ =>
    cases h₂ with
    | tailβ _ _ => rfl
    | tailξ hs => exact (value_no_step (.tcons hv₁ hvs₁) hs).elim
  | inlξ _ ih =>
    cases h₂ with
    | inlξ hs₂ => congr 1; exact ih hs₂
  | inrξ _ ih =>
    cases h₂ with
    | inrξ hs₂ => congr 1; exact ih hs₂
  | caseξ _ ih =>
    cases h₂ with
    | caseL hv => exact (value_no_step (.inl hv) ‹Step _ _›).elim
    | caseR hv => exact (value_no_step (.inr hv) ‹Step _ _›).elim
    | caseξ hs₂ => congr 1; exact ih hs₂
  | appξ₁ _ ih =>
    cases h₂ with
    | appβ _ => exact (value_no_step .lam ‹Step _ _›).elim
    | appξ₁ hs₂ => congr 1; exact ih hs₂
    | appξ₂ hv _ => exact (value_no_step hv ‹Step _ _›).elim
  | appξ₂ hv₁ _ ih =>
    cases h₂ with
    | appβ hw => exact (value_no_step hw ‹Step _ _›).elim
    | appξ₁ hs => exact (value_no_step hv₁ hs).elim
    | appξ₂ _ hs₂ => congr 1; exact ih hs₂
  | tconsξ₁ _ ih =>
    cases h₂ with
    | tconsξ₁ hs₂ => congr 1; exact ih hs₂
    | tconsξ₂ hv _ => exact (value_no_step hv ‹Step _ _›).elim
  | tconsξ₂ hv₁ _ ih =>
    cases h₂ with
    | tconsξ₁ hs => exact (value_no_step hv₁ hs).elim
    | tconsξ₂ _ hs₂ => congr 1; exact ih hs₂
  | headξ _ ih =>
    cases h₂ with
    | headβ hv hvs => exact (value_no_step (.tcons hv hvs) ‹Step _ _›).elim
    | headξ hs₂ => congr 1; exact ih hs₂
  | tailξ _ ih =>
    cases h₂ with
    | tailβ hv hvs => exact (value_no_step (.tcons hv hvs) ‹Step _ _›).elim
    | tailξ hs₂ => congr 1; exact ih hs₂

-- ═══════════════════════════════════════════════════════════
-- Canonical Forms (Lemma 5.1)
-- Reference: bld-calculus.md §5.1
-- ═══════════════════════════════════════════════════════════

/-- Sum-typed values are inl or inr. -/
theorem canonical_sum {a b : Ty} {v : Term [] (.sum a b)} (hv : Value v) :
    (∃ v', v = .inl v' ∧ Value v') ∨ (∃ v', v = .inr v' ∧ Value v') := by
  cases hv with
  | inl hv' => exact .inl ⟨_, rfl, hv'⟩
  | inr hv' => exact .inr ⟨_, rfl, hv'⟩

/-- Function-typed values are lambdas. -/
theorem canonical_fn {a b : Ty} {v : Term [] (.fn a b)} (hv : Value v) :
    ∃ body, v = .lam body := by
  cases hv with
  | lam => exact ⟨_, rfl⟩

/-- Product(n+1)-typed values are tcons. -/
theorem canonical_prod_succ {n : Nat} {a : Ty} {v : Term [] (.prod (n + 1) a)}
    (hv : Value v) :
    ∃ v' vs, v = .tcons v' vs ∧ Value v' ∧ Value vs := by
  cases hv with
  | tcons hv' hvs' => exact ⟨_, _, rfl, hv', hvs'⟩

/-- Product(0)-typed values are tnil. -/
theorem canonical_prod_zero {a : Ty} {v : Term [] (.prod 0 a)} (hv : Value v) :
    v = .tnil := by
  cases hv with
  | tnil => rfl

/-- Unit-typed values are unit. -/
theorem canonical_unit {v : Term [] .unit} (hv : Value v) : v = .unit := by
  cases hv with
  | unit => rfl

end Ty
