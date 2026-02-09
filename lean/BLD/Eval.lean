/- BLD Calculus — Computable Evaluation

   A computable step function and fuel-bounded evaluator
   that makes BLD programs actually run.

   Includes example terms and verified evaluation results.
-/

import BLD.Semantics

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- Decidable value check
-- ═══════════════════════════════════════════════════════════

/-- Decide whether a term is a value (computable). -/
def isValue {Γ : Context} {a : Ty} : Term Γ a → _root_.Bool
  | .unit        => true
  | .var _       => false
  | .inl e       => isValue e
  | .inr e       => isValue e
  | .case _ _ _  => false
  | .lam _       => true
  | .app _ _     => false
  | .tnil        => true
  | .tcons v vs  => isValue v && isValue vs
  | .head _      => false
  | .tail _      => false

-- ═══════════════════════════════════════════════════════════
-- Computable single-step function
-- ═══════════════════════════════════════════════════════════

/-- Compute one CBV reduction step, if possible.
    Returns `none` for values (and stuck open terms, which can't
    exist for well-typed closed terms by Progress). -/
def step? {a : Ty} : Term [] a → Option (Term [] a)
  -- Values
  | .unit    => none
  | .lam _   => none
  | .tnil    => none
  | .var idx => nomatch idx
  -- inl: step the inner term
  | .inl e =>
    match step? e with
    | some e' => some (.inl e')
    | none => none
  -- inr: step the inner term
  | .inr e =>
    match step? e with
    | some e' => some (.inr e')
    | none => none
  -- case: β-reduce if scrutinee is a value, else step scrutinee
  | .case e e₁ e₂ =>
    match isValue e with
    | true =>
      match e with
      | .inl v => some (subst₁ v e₁)
      | .inr v => some (subst₁ v e₂)
      | _ => none
    | false =>
      match step? e with
      | some e' => some (.case e' e₁ e₂)
      | none => none
  -- app: step function first, then argument, then β-reduce
  | .app f x =>
    match isValue f with
    | true =>
      match isValue x with
      | true =>
        match f with
        | .lam body => some (subst₁ x body)
        | _ => none
      | false =>
        match step? x with
        | some x' => some (.app f x')
        | none => none
    | false =>
      match step? f with
      | some f' => some (.app f' x)
      | none => none
  -- tcons: step first component, then second
  | .tcons v vs =>
    match isValue v with
    | true =>
      match isValue vs with
      | true => none
      | false =>
        match step? vs with
        | some vs' => some (.tcons v vs')
        | none => none
    | false =>
      match step? v with
      | some v' => some (.tcons v' vs)
      | none => none
  -- head: β-reduce if argument is a tcons value, else step
  | .head e =>
    match isValue e with
    | true =>
      match e with
      | .tcons v _ => some v
      | _ => none
    | false =>
      match step? e with
      | some e' => some (.head e')
      | none => none
  -- tail: β-reduce if argument is a tcons value, else step
  | .tail e =>
    match isValue e with
    | true =>
      match e with
      | .tcons _ vs => some vs
      | _ => none
    | false =>
      match step? e with
      | some e' => some (.tail e')
      | none => none

-- ═══════════════════════════════════════════════════════════
-- Fuel-bounded evaluator
-- ═══════════════════════════════════════════════════════════

/-- Evaluate a closed term for up to `fuel` steps.
    Returns the term after reduction stops (either a value
    or the term when fuel runs out). -/
def eval (fuel : Nat) {a : Ty} (e : Term [] a) : Term [] a :=
  match fuel with
  | 0 => e
  | n + 1 =>
    match step? e with
    | none => e
    | some e' => eval n e'

-- ═══════════════════════════════════════════════════════════
-- Example terms
-- ═══════════════════════════════════════════════════════════

/-- Identity function: λx.x -/
def id_fn (a : Ty) : Term [] (.fn a a) := .lam (.var .here)

/-- Boolean negation: λb. case b of inl _ ⇒ inr (), inr _ ⇒ inl () -/
def not_fn : Term [] (.fn (.sum .unit .unit) (.sum .unit .unit)) :=
  .lam (.case (.var .here) (.inr .unit) (.inl .unit))

/-- A unit pair: ⟨(), ()⟩ -/
def unit_pair : Term [] (.prod 2 .unit) :=
  .tcons .unit (.tcons .unit .tnil)

-- ═══════════════════════════════════════════════════════════
-- Verified evaluation examples
-- ═══════════════════════════════════════════════════════════

/-- (λx.x) () = () -/
example : eval 2 (.app (id_fn .unit) .unit) = .unit := by native_decide

/-- not (inl ()) = inr () -/
example : eval 3 (.app not_fn (.inl .unit)) = .inr .unit := by native_decide

/-- not (inr ()) = inl () -/
example : eval 3 (.app not_fn (.inr .unit)) = .inl .unit := by native_decide

/-- head ⟨(), ()⟩ = () -/
example : eval 2 (.head unit_pair) = .unit := by native_decide

/-- tail ⟨(), ()⟩ = ⟨()⟩ -/
example : eval 2 (.tail unit_pair) = .tcons .unit .tnil := by native_decide

/-- Double negation: not (not (inl ())) = inl () -/
example : eval 10 (.app not_fn (.app not_fn (.inl .unit))) = .inl .unit := by native_decide

end Ty
