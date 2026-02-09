/- BLD Calculus — Term-Level Sublanguage Irreducibility

   Value-level consequences of sublanguage restrictions:

   Lemma 7.5 (BD is Data-Only):
     BD-typed values contain no lambdas → L is irreducible.
     This formalizes: "BD-calculus has no application construct."

   Lemma 7.7 (BL is Fixed-Arity):
     BL-typed values contain no tuples → D is irreducible.
     This formalizes: "BL-calculus cannot parameterize arity."

   Theorem 8.7 (Traverser Type Uniqueness):
     Any type with cardinality 1 is TypeEncoding-equivalent to unit.

   Reference: bld-calculus.md §7.3-7.4, §8.7
              irreducibility-categorical.md §4, §5
              (§9.2: "Machine verification... remains future work." — THIS IS IT.)
-/

import BLD.MultiStep
import BLD.Sublanguage
import BLD.Irreducibility

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- Data values: no lambdas (no deferred computation)
-- ═══════════════════════════════════════════════════════════

/-- A data value contains no lambdas. This characterizes
    the values reachable in the BD-calculus (no function types). -/
inductive DataValue {Γ : Context} : {a : Ty} → Term Γ a → Prop where
  | unit : DataValue .unit
  | inl  {a b : Ty} {v : Term Γ a} :
      DataValue v → DataValue (.inl (b := b) v)
  | inr  {a b : Ty} {v : Term Γ b} :
      DataValue v → DataValue (.inr (a := a) v)
  | tnil {a : Ty} : DataValue (.tnil (a := a))
  | tcons {n : Nat} {a : Ty} {v : Term Γ a} {vs : Term Γ (.prod n a)} :
      DataValue v → DataValue vs → DataValue (.tcons v vs)

/-- **Lemma 7.5 (BD is Data-Only).**
    If a type is in the BD fragment and v is a closed value of that type,
    then v contains no lambdas (v is a DataValue).

    Proof: by induction on Value v.
    The lam case produces type .fn, which contradicts IsBD (via bd_not_fn).
    The inl/inr/tcons cases recurse using the IH, decomposing IsBD. -/
theorem bd_values_are_data {a : Ty} {v : Term [] a}
    (hv : Value v) (hbd : IsBD a) : DataValue v := by
  induction hv with
  | unit => exact .unit
  | lam => exact absurd hbd bd_not_fn
  | inl _ ih =>
    cases hbd with
    | sum ha _ => exact .inl (ih ha)
  | inr _ ih =>
    cases hbd with
    | sum _ hb => exact .inr (ih hb)
  | tnil => exact .tnil
  | tcons _ _ ihv ihvs =>
    cases hbd with
    | prod ha => exact .tcons (ihv ha) (ihvs (.prod ha))

-- ═══════════════════════════════════════════════════════════
-- No-tuple values: no indexed repetition
-- ═══════════════════════════════════════════════════════════

/-- A value with no tuples. This characterizes
    the values reachable in the BL-calculus (no product types). -/
inductive NoTupleValue {Γ : Context} : {a : Ty} → Term Γ a → Prop where
  | unit : NoTupleValue .unit
  | lam  {a b : Ty} {body : Term (a :: Γ) b} : NoTupleValue (.lam body)
  | inl  {a b : Ty} {v : Term Γ a} :
      NoTupleValue v → NoTupleValue (.inl (b := b) v)
  | inr  {a b : Ty} {v : Term Γ b} :
      NoTupleValue v → NoTupleValue (.inr (a := a) v)

/-- **Lemma 7.7 (BL is Fixed-Arity).**
    If a type is in the BL fragment and v is a closed value of that type,
    then v contains no tuples (v is a NoTupleValue).

    Proof: by induction on Value v.
    The tnil/tcons cases produce type .prod, contradicting IsBL (via bl_not_prod).
    Simpler than bd_values_are_data — all tuple cases are contradictions. -/
theorem bl_values_no_tuples {a : Ty} {v : Term [] a}
    (hv : Value v) (hbl : IsBL a) : NoTupleValue v := by
  induction hv with
  | unit => exact .unit
  | lam => exact .lam
  | inl _ ih =>
    cases hbl with
    | sum ha _ => exact .inl (ih ha)
  | inr _ ih =>
    cases hbl with
    | sum _ hb => exact .inr (ih hb)
  | tnil => exact absurd hbl bl_not_prod
  | tcons _ _ _ _ => exact absurd hbl bl_not_prod

-- ═══════════════════════════════════════════════════════════
-- Traverser Type Uniqueness (Theorem 8.7)
-- Reference: bld-calculus.md §8.7
-- ═══════════════════════════════════════════════════════════

/-- **Theorem 8.7 (Traverser Type Uniqueness).**
    Any type with cardinality 1 is TypeEncoding-equivalent to unit.

    The traverser type τ_trav = 1 is the unique BLD type (up to isomorphism)
    satisfying: cardinality 1, inhabited, BLD-expressible.
    Since TypeEncoding requires only equal cardinality, and both sides
    have cardinality 1, this is immediate. -/
theorem trav_unique (t : Ty) (ht : t.cardinality = 1) :
    TypeEncoding t .unit :=
  ⟨by simp [cardinality]; exact ht⟩

-- ═══════════════════════════════════════════════════════════
-- Composed safety: sublanguage + multi-step
-- ═══════════════════════════════════════════════════════════

/-- BD terms that reach normal form produce DataValues (no lambdas). -/
theorem bd_safety_data {a : Ty} {e v : Term [] a}
    (hbd : IsBD a) (_hs : Steps e v) (hn : NormalForm v) : DataValue v :=
  bd_values_are_data (normal_form_is_value v hn) hbd

/-- BL terms that reach normal form produce NoTupleValues (no tuples). -/
theorem bl_safety_no_tuples {a : Ty} {e v : Term [] a}
    (hbl : IsBL a) (_hs : Steps e v) (hn : NormalForm v) : NoTupleValue v :=
  bl_values_no_tuples (normal_form_is_value v hn) hbl

end Ty
