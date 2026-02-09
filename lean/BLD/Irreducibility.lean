/- BLD Calculus — Irreducibility Proofs

   The crown jewel: machine-verified proofs that B, L, D are irreducible.

   Lemma 7.3 (LD Cardinality Collapse):
     Every type in the LD fragment has cardinality exactly 1.
     This replaces the depth-3 enumeration in
     tools/tests/test_structure.py::test_ld_cardinality_collapse
     with a UNIVERSAL proof for ALL LD types at ALL depths.

   Theorem 3.1 (Boundary Irreducibility):
     Sum cannot be encoded using only Link and Dimension.
     Witness: Bool = 1+1 has cardinality 2, but all LD types have cardinality 1.

   References:
     - bld-calculus.md Lemma 7.3, Corollary 7.4
     - irreducibility-categorical.md Section 3, Section 9.2
       ("Full machine verification (Coq/Agda/Lean) would provide
        the strongest guarantee. This remains future work.")
-/

import BLD.Basic
import BLD.Cardinality
import BLD.Sublanguage

namespace Ty

/-- **Lemma 7.3 (LD Cardinality Collapse).**
    Every type in the LD fragment has cardinality exactly 1.

    Proof by structural induction on the IsLD derivation:
    - Base: |1| = 1
    - Fn:   |a → b| = |b|^|a| = 1^1 = 1  (by IH on both a and b)
    - Prod: |Πₙ(t)| = |t|^n = 1^n = 1     (by IH on t)
-/
theorem ld_cardinality_one (t : Ty) (h : IsLD t) : t.cardinality = 1 := by
  induction h with
  | unit => rfl
  | fn _ _ iha ihb => simp [cardinality, iha, ihb]
  | prod _ iht => simp [cardinality, iht, Nat.one_pow]

/-- **Corollary 7.4.** Bool = 1 + 1 is not an LD type.

    Direct: Sum constructor is not in the LD grammar. -/
theorem bool_not_ld : ¬ IsLD Ty.Bool := by
  intro h; nomatch h

/-- **Theorem 3.1 (Boundary Irreducibility).**
    No LD type has the same cardinality as Bool (= 2).

    Any bijective encoding of Bool into LD types would require
    an LD type with cardinality 2. But ld_cardinality_one shows
    all LD types have cardinality 1. Contradiction. -/
theorem no_ld_encodes_bool (t : Ty) (h : IsLD t) :
    t.cardinality ≠ Ty.Bool.cardinality := by
  simp [Ty.Bool, cardinality, ld_cardinality_one t h]

/-- Generalization: no LD type has cardinality > 1.
    Sum is the ONLY way to get cardinality > 1 in the BLD calculus. -/
theorem ld_cardinality_le_one (t : Ty) (h : IsLD t) :
    t.cardinality ≤ 1 := by
  simp [ld_cardinality_one t h]

/-- LD types cannot encode any sum type with cardinality ≥ 2. -/
theorem ld_cannot_encode_sum (t : Ty) (h : IsLD t) (a b : Ty)
    (ha : a.cardinality ≥ 1) (hb : b.cardinality ≥ 1) :
    t.cardinality ≠ (Ty.sum a b).cardinality := by
  simp [cardinality, ld_cardinality_one t h]
  omega

end Ty
