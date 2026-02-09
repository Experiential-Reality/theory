/- BLD Calculus — Term Language

   Intrinsically-typed terms with de Bruijn indices.
   Types are enforced by construction — no separate typing judgment needed.

   Reference: bld-calculus.md §2.2-2.4 (Definitions 2.3, 2.4)
              §3 (Typing Rules 3.2-3.10)
-/

import BLD.Basic

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- Contexts and variable lookup
-- ═══════════════════════════════════════════════════════════

/-- A typing context is a list of types (de Bruijn: rightmost = most recent). -/
abbrev Context := List Ty

/-- Proof that a type appears at a specific position in the context.
    De Bruijn index: `here` is index 0, `there here` is index 1, etc. -/
inductive Lookup : Context → Ty → Type where
  | here  {Γ : Context} {a : Ty} : Lookup (a :: Γ) a
  | there {Γ : Context} {a b : Ty} : Lookup Γ a → Lookup (b :: Γ) a
  deriving DecidableEq

-- ═══════════════════════════════════════════════════════════
-- Intrinsically-typed terms
-- Reference: bld-calculus.md §2.2 (Definition 2.3), §3 (Rules 3.2-3.10)
-- ═══════════════════════════════════════════════════════════

/-- Intrinsically-typed BLD terms.
    `Term Γ a` is a term of type `a` in context `Γ`.
    Typing rules are baked into the constructors — there is no
    separate typing judgment. Preservation is free. -/
inductive Term : Context → Ty → Type where
  -- Structural (Rules 3.2, 3.3)
  | unit {Γ : Context} : Term Γ .unit
  | var  {Γ : Context} {a : Ty} : Lookup Γ a → Term Γ a
  -- Sum / Boundary (Rules 3.4-3.6)
  | inl  {Γ : Context} {a b : Ty} : Term Γ a → Term Γ (.sum a b)
  | inr  {Γ : Context} {a b : Ty} : Term Γ b → Term Γ (.sum a b)
  | case {Γ : Context} {a b c : Ty} :
      Term Γ (.sum a b) → Term (a :: Γ) c → Term (b :: Γ) c → Term Γ c
  -- Function / Link (Rules 3.7-3.8)
  | lam  {Γ : Context} {a b : Ty} : Term (a :: Γ) b → Term Γ (.fn a b)
  | app  {Γ : Context} {a b : Ty} : Term Γ (.fn a b) → Term Γ a → Term Γ b
  -- Product / Dimension (Rules 3.9-3.10)
  -- tnil/tcons encode ⟨e₁,...,eₙ⟩; head/tail encode e.i via head(tail^i(...))
  | tnil  {Γ : Context} {a : Ty} : Term Γ (.prod 0 a)
  | tcons {Γ : Context} {n : Nat} {a : Ty} :
      Term Γ a → Term Γ (.prod n a) → Term Γ (.prod (n + 1) a)
  | head  {Γ : Context} {n : Nat} {a : Ty} :
      Term Γ (.prod (n + 1) a) → Term Γ a
  | tail  {Γ : Context} {n : Nat} {a : Ty} :
      Term Γ (.prod (n + 1) a) → Term Γ (.prod n a)
  deriving DecidableEq

-- ═══════════════════════════════════════════════════════════
-- Values
-- Reference: bld-calculus.md §2.3 (Definition 2.4)
-- ═══════════════════════════════════════════════════════════

/-- A value is a fully-evaluated term.
    Γ is a parameter (fixed). a is an index (varies across constructors).
    Lambda bodies are NOT required to be values. -/
inductive Value {Γ : Context} : {a : Ty} → Term Γ a → Prop where
  | unit : Value .unit
  | lam  {a b : Ty} {body : Term (a :: Γ) b} : Value (.lam body)
  | inl  {a b : Ty} {v : Term Γ a} : Value v → Value (.inl (b := b) v)
  | inr  {a b : Ty} {v : Term Γ b} : Value v → Value (.inr (a := a) v)
  | tnil {a : Ty} : Value (.tnil (a := a))
  | tcons {n : Nat} {a : Ty} {v : Term Γ a} {vs : Term Γ (.prod n a)} :
      Value v → Value vs → Value (.tcons v vs)

end Ty
