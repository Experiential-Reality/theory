/- BLD Calculus — Substitution

   Standard de Bruijn substitution machinery.
   With intrinsic typing, the Substitution Lemma (Lemma 5.3) is free:
   `subst₁ : Term Γ a → Term (a :: Γ) b → Term Γ b` is well-typed by construction.

   Reference: bld-calculus.md §5.3
-/

import BLD.Term

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- Renaming
-- ═══════════════════════════════════════════════════════════

/-- Extend a renaming under a binder. -/
def ext {Γ Δ : Context} {a b : Ty}
    (ρ : {c : Ty} → Lookup Γ c → Lookup Δ c) :
    Lookup (b :: Γ) a → Lookup (b :: Δ) a
  | .here      => .here
  | .there idx => .there (ρ idx)

/-- Apply a renaming to a term. -/
def rename {Γ Δ : Context} {a : Ty}
    (ρ : {c : Ty} → Lookup Γ c → Lookup Δ c) :
    Term Γ a → Term Δ a
  | .unit        => .unit
  | .var idx     => .var (ρ idx)
  | .inl e       => .inl (rename ρ e)
  | .inr e       => .inr (rename ρ e)
  | .case e l r  => .case (rename ρ e) (rename (ext ρ) l) (rename (ext ρ) r)
  | .lam body    => .lam (rename (ext ρ) body)
  | .app f x     => .app (rename ρ f) (rename ρ x)
  | .tnil        => .tnil
  | .tcons v vs  => .tcons (rename ρ v) (rename ρ vs)
  | .head e      => .head (rename ρ e)
  | .tail e      => .tail (rename ρ e)

-- ═══════════════════════════════════════════════════════════
-- Substitution
-- ═══════════════════════════════════════════════════════════

/-- Extend a substitution under a binder.
    The new variable (index 0) maps to itself;
    existing variables are renamed into the extended context. -/
def exts {Γ Δ : Context} {a b : Ty}
    (σ : {c : Ty} → Lookup Γ c → Term Δ c) :
    Lookup (b :: Γ) a → Term (b :: Δ) a
  | .here      => .var .here
  | .there idx => rename .there (σ idx)

/-- Simultaneous substitution. -/
def subst {Γ Δ : Context} {a : Ty}
    (σ : {c : Ty} → Lookup Γ c → Term Δ c) :
    Term Γ a → Term Δ a
  | .unit        => .unit
  | .var idx     => σ idx
  | .inl e       => .inl (subst σ e)
  | .inr e       => .inr (subst σ e)
  | .case e l r  => .case (subst σ e) (subst (exts σ) l) (subst (exts σ) r)
  | .lam body    => .lam (subst (exts σ) body)
  | .app f x     => .app (subst σ f) (subst σ x)
  | .tnil        => .tnil
  | .tcons v vs  => .tcons (subst σ v) (subst σ vs)
  | .head e      => .head (subst σ e)
  | .tail e      => .tail (subst σ e)

/-- Substitution that replaces variable 0 with `v` and shifts others down. -/
private def subst₁_σ {Γ : Context} {a : Ty} (v : Term Γ a) :
    {c : Ty} → Lookup (a :: Γ) c → Term Γ c
  | _, .here      => v
  | _, .there idx => .var idx

/-- Single-variable substitution (used in β-rules).
    Substitutes `v` for variable 0 in `body`. -/
def subst₁ {Γ : Context} {a b : Ty}
    (v : Term Γ a) (body : Term (a :: Γ) b) : Term Γ b :=
  subst (subst₁_σ v) body

-- ═══════════════════════════════════════════════════════════
-- Renaming preserves values
-- ═══════════════════════════════════════════════════════════

/-- Renaming preserves the Value predicate. -/
theorem rename_value {Γ Δ : Context} {a : Ty} {e : Term Γ a}
    (ρ : {c : Ty} → Lookup Γ c → Lookup Δ c)
    (hv : Value e) : Value (rename ρ e) := by
  induction hv with
  | unit => exact .unit
  | lam => exact .lam
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | tnil => exact .tnil
  | tcons _ _ ihv ihvs => exact .tcons ihv ihvs

/-- Weakening: add an unused variable to the context. -/
def weaken {Γ : Context} {a b : Ty} (e : Term Γ a) : Term (b :: Γ) a :=
  rename .there e

end Ty
