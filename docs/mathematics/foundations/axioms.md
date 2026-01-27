---
status: PROVEN
layer: 0
depends_on: []
used_by:
  - definitions/bld-calculus.md
  - proofs/irreducibility-proof.md
  - proofs/completeness-proof.md
  - derivations/octonion-derivation.md
  - constants.md
---

# Axioms of BLD Theory

## Abstract

We present the axiomatic foundation of BLD theory, a structural framework built on three primitives: Boundary (B), Link (L), and Dimension (D). The axiom system consists of three existence axioms establishing the primitives, three closure axioms ensuring structural consistency, and one genesis axiom grounding the system in logical necessity. From these seven axioms, we derive the fundamental constants (B = 56, L = 20, n = 4, K = 2) and all subsequent results. The axioms are shown to be consistent and independent, forming a minimal foundation for the theory.

## 1. Introduction

Every formal theory requires explicit axioms from which all theorems derive. BLD theory is no exception. This document presents the complete axiomatic foundation, making explicit the assumptions that underlie all derivations in the codebase.

The axioms divide into three categories:
1. **Existence axioms** (A1-A3): Assert that the three primitives exist
2. **Closure axioms** (A4-A6): Ensure structural operations are well-defined
3. **Genesis axiom** (A7): Grounds the system in logical necessity

From these axioms, we derive the BLD calculus (see [bld-calculus.md](definitions/bld-calculus.md)), the irreducibility theorem (see [irreducibility-proof.md](proofs/irreducibility-proof.md)), and all physical constants (see [constants.md](constants.md)).

## 2. Primitive Notions

The following concepts are taken as undefined:

- **Structure**: That which can be described
- **Value**: A determinate content within structure
- **Traversal**: The act of moving through structure

## 3. The Axioms

### Existence Axioms

**Axiom 1** (Boundary Existence). *There exists a structural primitive B (Boundary) that partitions value space into disjoint regions based on a discriminator.*

Formally: For any value space V and discriminator function d, there exists B: V → {1, ..., k} such that V = ⨆ᵢBᵢ (disjoint union).

*Remark 1.1.* Boundary corresponds to Sum types in type theory, coproducts in category theory, and choice in computation.

---

**Axiom 2** (Link Existence). *There exists a structural primitive L (Link) that connects one value to another with direction.*

Formally: For any values v₁, v₂, there exists L: v₁ → v₂ establishing a directed reference from v₁ to v₂.

*Remark 2.1.* Link corresponds to Function types in type theory, morphisms in category theory, and reference in computation.

---

**Axiom 3** (Dimension Existence). *There exists a structural primitive D (Dimension) that enables homogeneous repetition of structure.*

Formally: For any structure S and natural number n ≥ 0, there exists Dₙ(S) representing n instances of S as a single structural unit.

*Remark 3.1.* Dimension corresponds to Product types in type theory, products in category theory, and arrays in computation.

### Closure Axioms

**Axiom 4** (Composition Closure). *Any finite combination of B, L, D applied to well-formed structure yields well-formed structure.*

Formally: If S is a well-formed structure, then B(S), L(S, S'), and Dₙ(S) are well-formed for all n ∈ ℕ.

*Remark 4.1.* This ensures the type system is closed under the three constructors.

---

**Axiom 5** (Traversal Closure). *Every well-formed structure can be traversed, and traversal incurs a finite cost.*

Formally: For any structure S, there exists a traversal operation traverse(S) with cost K(S) < ∞.

*Remark 5.1.* This is the observability axiom — structure exists to be traversed.

---

**Axiom 6** (Self-Reference Closure). *Structure can reference itself without paradox.*

Formally: If S is well-formed, then L(S, S) (self-reference) is well-formed and has finite traversal cost.

*Remark 6.1.* This enables recursive structures and self-observation. Combined with A5, it implies that self-observation has cost K > 0 (you cannot observe yourself for free).

### Genesis Axiom

**Axiom 7** (Genesis). *The existence of structure is logically necessary: "Nothing" is self-contradictory.*

Formally: ¬∃ empty state, because the assertion "nothing exists" is itself something.

*Corollary 7.1.* At minimum, Boundary must exist (the primordial distinction between existence and non-existence).

*Corollary 7.2.* The traversal from -B to B (non-existence to existence) must close on itself for consistency.

*Remark 7.1.* This axiom grounds BLD in logic rather than observation. The closure requirement (Corollary 7.2) leads to the derivation of all constants. See [octonion-necessity.md](derivations/octonion-necessity.md).

## 4. Derived Principles

The following principles are not axioms but immediate consequences:

**Principle 1** (Irreducibility). *B, L, and D are mutually irreducible: none can be expressed using the other two.*

*Proof.* See [irreducibility-proof.md](proofs/irreducibility-proof.md). ∎

**Principle 2** (Completeness). *B, L, and D are sufficient: any observable structure can be expressed using these three primitives.*

*Proof.* See [completeness-proof.md](proofs/completeness-proof.md). ∎

**Principle 3** (Observation Cost). *Every traversal incurs a cost of K/X where K is the Killing form (K = 2) and X is the structure traversed.*

*Derivation.* From A5 and A6, bidirectional observation requires K = 2. See [killing-form.md](../lie-theory/killing-form.md). ∎

## 5. Consistency

**Theorem 5.1** (Consistency). *The axiom system A1-A7 is consistent.*

*Proof sketch.* We exhibit a model: the BLD calculus (see [bld-calculus.md](definitions/bld-calculus.md)) with types and terms. Each axiom is satisfied:
- A1-A3: Sum, Function, Product types exist
- A4: Type constructors compose
- A5: Every well-typed term evaluates (Progress theorem)
- A6: Recursive types can be defined with finite cost
- A7: The unit type 1 exists (something rather than nothing)

The metatheory (Progress + Preservation) is proven in [bld-calculus.md](definitions/bld-calculus.md). ∎

## 6. Independence

**Theorem 6.1** (Independence). *Each axiom is independent of the others.*

*Proof sketch.* For each axiom Aᵢ, we exhibit a model satisfying all axioms except Aᵢ:

| Axiom | Model without it |
|-------|------------------|
| A1 (Boundary) | LD-calculus: functions and products only |
| A2 (Link) | BD-calculus: sums and products only |
| A3 (Dimension) | BL-calculus: sums and functions only |
| A4 (Composition) | Flat structures with no nesting |
| A5 (Traversal) | Unobservable structure (trivial model) |
| A6 (Self-Reference) | Acyclic structures only |
| A7 (Genesis) | Empty model (vacuously consistent) |

Full proof in [axiom-independence.md](proofs/axiom-independence.md). ∎

## 7. Discussion

### 7.1 Relationship to Other Foundations

The BLD axioms relate to existing mathematical foundations:

| BLD | Type Theory | Category Theory | Set Theory |
|-----|-------------|-----------------|------------|
| A1 (B) | Sum types | Coproducts | Disjoint union |
| A2 (L) | Function types | Morphisms | Functions |
| A3 (D) | Product types | Products | Cartesian product |
| A4 | Closure under constructors | Finite completeness | Closure under operations |
| A5 | Normalization | Evaluation | Well-foundedness |
| A6 | Recursive types | Fixed points | Non-well-founded sets |
| A7 | Existence of unit type | Terminal object | Non-empty universe |

### 7.2 Why These Axioms

The axiom set is minimal in the sense that:
1. Removing any existence axiom loses expressive power (Irreducibility)
2. Removing any closure axiom breaks the type system
3. Removing the genesis axiom leaves the system ungrounded

The axiom set is also complete in the sense that adding further axioms either:
1. Follows from A1-A7 (redundant)
2. Contradicts A1-A7 (inconsistent)
3. Restricts the models (a different theory)

## 8. Conclusion

The seven axioms A1-A7 provide the foundation for BLD theory. All results in this codebase derive from these axioms. When files contradict, the derivation closer to these axioms takes precedence.

## References

[Awodey, 2010] S. Awodey. *Category Theory*. Oxford University Press, 2010.

[Cartan, 1894] É. Cartan. "Sur la structure des groupes de transformations finis et continus." Thesis, Paris, 1894.

[Howard, 1980] W. A. Howard. "The formulae-as-types notion of construction." In *To H.B. Curry: Essays on Combinatory Logic*, Academic Press, 1980.

[Mac Lane, 1971] S. Mac Lane. *Categories for the Working Mathematician*. Springer, 1971.

[Martin-Löf, 1984] P. Martin-Löf. *Intuitionistic Type Theory*. Bibliopolis, 1984.

[Pierce, 2002] B. Pierce. *Types and Programming Languages*. MIT Press, 2002.
