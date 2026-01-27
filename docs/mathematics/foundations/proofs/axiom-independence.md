---
status: PROVEN
layer: 1
depends_on:
  - ../axioms.md
  - ../definitions/bld-calculus.md
used_by:
  - ../axioms.md
---

# Axiom Independence Proof

## Abstract

We prove that the seven axioms A1-A7 of BLD theory are mutually independent. For each axiom Aᵢ, we construct a model Mᵢ that satisfies all axioms except Aᵢ. This establishes that no axiom is redundant — removing any one genuinely changes the theory.

## 1. Introduction

The [axioms.md](../axioms.md) document presents seven axioms: three existence axioms (A1-A3), three closure axioms (A4-A6), and one genesis axiom (A7). This document proves each axiom is independent of the others.

**Proof Strategy.** For each axiom Aᵢ, we exhibit a model Mᵢ satisfying:
- All axioms Aⱼ for j ≠ i
- NOT axiom Aᵢ

The existence of such a model proves Aᵢ cannot be derived from the other axioms.

## 2. The Axioms (Summary)

| Axiom | Name | Content |
|-------|------|---------|
| A1 | Boundary Existence | Partitioning primitive B exists |
| A2 | Link Existence | Reference primitive L exists |
| A3 | Dimension Existence | Repetition primitive D exists |
| A4 | Composition Closure | B, L, D compose to form well-formed structures |
| A5 | Traversal Closure | All structures can be traversed with finite cost |
| A6 | Self-Reference Closure | Self-referential structures are permitted |
| A7 | Genesis | Existence is logically necessary (no empty model) |

## 3. Independence of A1 (Boundary)

### 3.1 Model M₁: LD-Calculus

**Definition.** The LD-calculus has types:
```
τ ::= 1 | τ → τ | Πₙτ
```
(See [bld-calculus.md](../definitions/bld-calculus.md) Definition 6.1)

### 3.2 Verification

| Axiom | Satisfied? | Reason |
|-------|------------|--------|
| A1 | **No** | No sum types — cannot partition |
| A2 | Yes | Function types exist (τ → τ) |
| A3 | Yes | Product types exist (Πₙτ) |
| A4 | Yes | Types compose (e.g., Π₃(τ → τ)) |
| A5 | Yes | All terms evaluate (Progress theorem holds) |
| A6 | Yes | Self-referential functions definable |
| A7 | Yes | Unit type 1 exists |

### 3.3 Key Property

By Lemma 7.3 of bld-calculus.md, every closed inhabited type in LD-calculus has cardinality 1. This means the LD-calculus cannot encode Bool = 1 + 1, which requires B.

**Conclusion.** M₁ satisfies A2-A7 but not A1. ∎

## 4. Independence of A2 (Link)

### 4.1 Model M₂: BD-Calculus

**Definition.** The BD-calculus has types:
```
τ ::= 1 | τ + τ | Πₙτ
```
(See [bld-calculus.md](../definitions/bld-calculus.md) Definition 6.2)

### 4.2 Verification

| Axiom | Satisfied? | Reason |
|-------|------------|--------|
| A1 | Yes | Sum types exist (τ + τ) |
| A2 | **No** | No function types — cannot reference |
| A3 | Yes | Product types exist (Πₙτ) |
| A4 | Yes | Types compose (e.g., (τ + τ) + Πₙσ) |
| A5 | Yes | All terms evaluate to canonical forms |
| A6 | Yes | Self-referential sums constructible |
| A7 | Yes | Unit type 1 exists |

### 4.3 Key Property

The BD-calculus has no application construct. Values are static data trees — they cannot compute or transform inputs.

**Conclusion.** M₂ satisfies A1, A3-A7 but not A2. ∎

## 5. Independence of A3 (Dimension)

### 5.1 Model M₃: BL-Calculus

**Definition.** The BL-calculus has types:
```
τ ::= 1 | τ + τ | τ → τ
```
(See [bld-calculus.md](../definitions/bld-calculus.md) Definition 6.3)

### 5.2 Verification

| Axiom | Satisfied? | Reason |
|-------|------------|--------|
| A1 | Yes | Sum types exist (τ + τ) |
| A2 | Yes | Function types exist (τ → τ) |
| A3 | **No** | No product types — cannot repeat |
| A4 | Yes | Types compose (e.g., (τ + τ) → σ) |
| A5 | Yes | All terms normalize (Progress holds) |
| A6 | Yes | Recursive functions definable via Y combinator |
| A7 | Yes | Unit type 1 exists |

### 5.3 Key Property

By Lemma 7.7 of bld-calculus.md, BL-calculus has fixed-arity structure. It cannot uniformly express the family {Πₙτ : n ∈ ℕ} — each arity requires a separate type definition.

**Conclusion.** M₃ satisfies A1, A2, A4-A7 but not A3. ∎

## 6. Independence of A4 (Composition Closure)

### 6.1 Model M₄: Flat Calculus

**Definition.** The Flat calculus permits only ground types:
```
τ ::= 1 | Bool | Nat
```
where Bool = 1 + 1 and Nat = μX.(1 + X).

No type constructors may be applied to non-ground types.

### 6.2 Verification

| Axiom | Satisfied? | Reason |
|-------|------------|--------|
| A1 | Yes | Bool = 1 + 1 exists (ground sum) |
| A2 | Yes | Nat → Bool exists (ground function) |
| A3 | Yes | Π₃Nat exists (ground product) |
| A4 | **No** | Cannot form (Bool → Nat) → Bool (nested) |
| A5 | Yes | Ground terms evaluate |
| A6 | Yes | Nat is self-referential (μ-type) |
| A7 | Yes | 1 exists |

### 6.3 Key Property

Nesting is forbidden: (τ₁ → τ₂) → τ₃ requires τ₁ → τ₂ as an argument type, which is not ground. The Flat calculus cannot express higher-order functions or nested structures.

**Conclusion.** M₄ satisfies A1-A3, A5-A7 but not A4. ∎

## 7. Independence of A5 (Traversal Closure)

### 7.1 Model M₅: Opaque Calculus

**Definition.** The Opaque calculus has full BLD types but no elimination forms:
- No `case` (cannot inspect sums)
- No application (cannot evaluate functions)
- No projection (cannot access tuple components)

Only introduction forms are permitted.

### 7.2 Verification

| Axiom | Satisfied? | Reason |
|-------|------------|--------|
| A1 | Yes | Sum types exist, can inject (inl, inr) |
| A2 | Yes | Function types exist, can abstract (λ) |
| A3 | Yes | Product types exist, can tuple (⟨...⟩) |
| A4 | Yes | Types compose normally |
| A5 | **No** | Cannot traverse — no elimination forms |
| A6 | Yes | Self-referential types constructible |
| A7 | Yes | Unit type exists |

### 7.3 Key Property

Structures exist but cannot be inspected. A value of type τ₁ + τ₂ exists but you cannot determine which branch it's in. This models "structure without observation."

**Conclusion.** M₅ satisfies A1-A4, A6-A7 but not A5. ∎

## 8. Independence of A6 (Self-Reference Closure)

### 8.1 Model M₆: Acyclic Calculus

**Definition.** The Acyclic calculus permits full BLD types but forbids:
- Recursive types (μX.τ)
- Self-application (f f)
- Any type T where T appears in its own definition

The type formation judgment Γ ⊢ τ ok includes a well-foundedness check: the dependency graph of type definitions must be acyclic.

### 8.2 Verification

| Axiom | Satisfied? | Reason |
|-------|------------|--------|
| A1 | Yes | Sum types exist (non-recursive) |
| A2 | Yes | Function types exist (non-recursive) |
| A3 | Yes | Product types exist (non-recursive) |
| A4 | Yes | Types compose (acyclically) |
| A5 | Yes | All terms terminate (strong normalization) |
| A6 | **No** | Self-reference forbidden |
| A7 | Yes | Unit type exists |

### 8.3 Key Property

The Acyclic calculus is strongly normalizing — every computation terminates. This is because without recursion, there's no way to create infinite loops. However, this also means natural numbers cannot be represented (Nat = μX.(1 + X) requires recursion).

**Conclusion.** M₆ satisfies A1-A5, A7 but not A6. ∎

## 9. Independence of A7 (Genesis)

### 9.1 Model M₇: Empty Calculus

**Definition.** The Empty calculus has:
- No types
- No terms
- No values

### 9.2 Verification

| Axiom | Satisfied? | Reason |
|-------|------------|--------|
| A1 | Yes (vacuously) | For all value spaces V, B exists... (no V exist) |
| A2 | Yes (vacuously) | For all values v₁, v₂, L exists... (no values exist) |
| A3 | Yes (vacuously) | For all structures S, Dₙ(S) exists... (no S exist) |
| A4 | Yes (vacuously) | All finite combinations preserve well-formedness (none exist) |
| A5 | Yes (vacuously) | All structures can be traversed (none exist) |
| A6 | Yes (vacuously) | Self-reference is well-formed (none exist) |
| A7 | **No** | Nothing exists — violates genesis |

### 9.3 Key Property

All universal statements ("for all X, P(X)") are vacuously true when the domain is empty. Genesis (A7) asserts existence, so it's the only axiom falsified by the empty model.

**Conclusion.** M₇ satisfies A1-A6 (vacuously) but not A7. ∎

## 10. Summary

| Model | Missing Axiom | Key Feature |
|-------|---------------|-------------|
| M₁ (LD) | A1 (Boundary) | No sums — cardinality always 1 |
| M₂ (BD) | A2 (Link) | No functions — no computation |
| M₃ (BL) | A3 (Dimension) | No products — fixed arity |
| M₄ (Flat) | A4 (Composition) | No nesting — ground types only |
| M₅ (Opaque) | A5 (Traversal) | No elimination — structure exists but can't be inspected |
| M₆ (Acyclic) | A6 (Self-Ref) | No recursion — all computations terminate |
| M₇ (Empty) | A7 (Genesis) | Nothing exists — vacuous truth |

## 11. Conclusion

Each of the seven axioms A1-A7 is independent of the others. No axiom is redundant, and removing any axiom yields a genuinely different (and weaker) theory.

## References

- [Axioms](../axioms.md) — The seven axioms
- [BLD Calculus](../definitions/bld-calculus.md) — Sublanguage definitions (Defs 6.1-6.3)
- [Irreducibility Categorical](irreducibility-categorical.md) — Type constructor irreducibility proofs
