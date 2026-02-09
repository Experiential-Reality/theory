/- BLD Calculus — Multi-Step Reduction and Strengthened Type Safety

   Reflexive-transitive closure of single-step reduction with:
   - Transitivity, single-step embedding
   - Congruence lifting (9 rules)
   - Normal forms and their relationship to values
   - Strengthened type safety (multi-step)
   - Value uniqueness (determinism of evaluation)

   Reference: bld-calculus.md §5
-/

import BLD.Semantics

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- Multi-step reduction (reflexive-transitive closure)
-- ═══════════════════════════════════════════════════════════

/-- Reflexive-transitive closure of single-step reduction.
    `Steps e e'` means e reduces to e' in zero or more steps. -/
inductive Steps {Γ : Context} {a : Ty} : Term Γ a → Term Γ a → Prop where
  | refl {e : Term Γ a} : Steps e e
  | step {e e' e'' : Term Γ a} : Step e e' → Steps e' e'' → Steps e e''

/-- Notation: `e ⟶* e'` for multi-step reduction. -/
scoped infixl:50 " ⟶* " => Steps

-- ═══════════════════════════════════════════════════════════
-- Basic properties
-- ═══════════════════════════════════════════════════════════

/-- Multi-step reduction is transitive. -/
theorem steps_trans {Γ : Context} {a : Ty} {e e' e'' : Term Γ a}
    (h₁ : Steps e e') (h₂ : Steps e' e'') : Steps e e'' := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- A single step embeds into multi-step. -/
theorem steps_one {Γ : Context} {a : Ty} {e e' : Term Γ a}
    (h : Step e e') : Steps e e' :=
  .step h .refl

-- ═══════════════════════════════════════════════════════════
-- Congruence lifting
-- ═══════════════════════════════════════════════════════════

/-- Lift Steps through inl. -/
theorem steps_inl {Γ : Context} {a b : Ty} {e e' : Term Γ a}
    (h : Steps e e') : Steps (.inl (b := b) e) (.inl e') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.inlξ hs) ih

/-- Lift Steps through inr. -/
theorem steps_inr {Γ : Context} {a b : Ty} {e e' : Term Γ b}
    (h : Steps e e') : Steps (.inr (a := a) e) (.inr e') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.inrξ hs) ih

/-- Lift Steps through case (scrutinee). -/
theorem steps_case {Γ : Context} {a b c : Ty}
    {e e' : Term Γ (.sum a b)}
    {e₁ : Term (a :: Γ) c} {e₂ : Term (b :: Γ) c}
    (h : Steps e e') : Steps (.case e e₁ e₂) (.case e' e₁ e₂) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.caseξ hs) ih

/-- Lift Steps through app (function position). -/
theorem steps_app₁ {Γ : Context} {a b : Ty}
    {e₁ e₁' : Term Γ (.fn a b)} {e₂ : Term Γ a}
    (h : Steps e₁ e₁') : Steps (.app e₁ e₂) (.app e₁' e₂) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.appξ₁ hs) ih

/-- Lift Steps through app (argument, function is a value). -/
theorem steps_app₂ {Γ : Context} {a b : Ty}
    {v : Term Γ (.fn a b)} {e₂ e₂' : Term Γ a}
    (hv : Value v) (h : Steps e₂ e₂') : Steps (.app v e₂) (.app v e₂') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.appξ₂ hv hs) ih

/-- Lift Steps through tcons (first component). -/
theorem steps_tcons₁ {Γ : Context} {n : Nat} {a : Ty}
    {e e' : Term Γ a} {es : Term Γ (.prod n a)}
    (h : Steps e e') : Steps (.tcons e es) (.tcons e' es) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.tconsξ₁ hs) ih

/-- Lift Steps through tcons (second component, first is a value). -/
theorem steps_tcons₂ {Γ : Context} {n : Nat} {a : Ty}
    {v : Term Γ a} {es es' : Term Γ (.prod n a)}
    (hv : Value v) (h : Steps es es') : Steps (.tcons v es) (.tcons v es') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.tconsξ₂ hv hs) ih

/-- Lift Steps through head. -/
theorem steps_head {Γ : Context} {n : Nat} {a : Ty}
    {e e' : Term Γ (.prod (n + 1) a)}
    (h : Steps e e') : Steps (.head e) (.head e') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.headξ hs) ih

/-- Lift Steps through tail. -/
theorem steps_tail {Γ : Context} {n : Nat} {a : Ty}
    {e e' : Term Γ (.prod (n + 1) a)}
    (h : Steps e e') : Steps (.tail e) (.tail e') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.tailξ hs) ih

-- ═══════════════════════════════════════════════════════════
-- Normal forms
-- ═══════════════════════════════════════════════════════════

/-- A normal form is a term that can't step. -/
def NormalForm {Γ : Context} {a : Ty} (e : Term Γ a) : Prop :=
  ¬ ∃ e', Step e e'

/-- Values are normal forms. -/
theorem value_is_normal {Γ : Context} {a : Ty} {e : Term Γ a}
    (hv : Value e) : NormalForm e :=
  value_irreducible hv

/-- Closed normal forms are values.
    By Progress, a closed term is either a value or can step.
    If it's a normal form, it can't step, so it must be a value. -/
theorem normal_form_is_value {a : Ty} (e : Term [] a)
    (hn : NormalForm e) : Value e := by
  cases progress e with
  | inl hv => exact hv
  | inr hex => exact absurd hex hn

-- ═══════════════════════════════════════════════════════════
-- Strengthened type safety (multi-step)
-- Reference: bld-calculus.md §5.5
-- ═══════════════════════════════════════════════════════════

/-- **Strengthened Type Safety.** Closed terms that reach normal form
    reach values. Well-typed programs don't get stuck, even after
    arbitrary numbers of steps. -/
theorem type_safety_multi {a : Ty} {e e' : Term [] a}
    (_hs : Steps e e') (hn : NormalForm e') : Value e' :=
  normal_form_is_value e' hn

-- ═══════════════════════════════════════════════════════════
-- Value uniqueness (determinism of evaluation)
-- ═══════════════════════════════════════════════════════════

/-- **Value Uniqueness.** If a term multi-steps to two values,
    they are equal. CBV evaluation is deterministic. -/
theorem steps_value_unique {Γ : Context} {a : Ty} {e v₁ v₂ : Term Γ a}
    (h₁ : Steps e v₁) (hv₁ : Value v₁)
    (h₂ : Steps e v₂) (hv₂ : Value v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | refl =>
    cases h₂ with
    | refl => rfl
    | step hs _ => exact absurd ⟨_, hs⟩ (value_irreducible hv₁)
  | step hs₁ _ ih =>
    cases h₂ with
    | refl => exact absurd ⟨_, hs₁⟩ (value_irreducible hv₂)
    | step hs₂ rest₂ =>
      have heq := deterministic hs₁ hs₂
      subst heq
      exact ih hv₁ rest₂ hv₂

end Ty
