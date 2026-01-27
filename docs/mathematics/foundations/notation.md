---
status: DERIVED
layer: 0
depends_on:
  - axioms.md
used_by:
  - definitions/bld-calculus.md
  - proofs/irreducibility-proof.md
  - proofs/completeness-proof.md
  - derivations/octonion-derivation.md
  - derivations/force-structure.md
  - constants.md
---

## Summary

**Standard notation used throughout BLD theory:**

1. Three primitives: B=56 (boundary), L=20 (link), n=4 (dimension) — [The Three Primitives](#2-the-three-primitives)
2. Derived constants: K=2 (Killing form), S=13 (structural intervals) — [Derived Constants](#3-derived-constants)
3. Type-theoretic notation: sum (+), function (->), product (Pn) — [Type-Theoretic Notation](#4-type-theoretic-notation)
4. Categorical notation: coproduct, morphism, product — [Categorical Notation](#5-categorical-notation)
5. Lie-theoretic notation: algebras, groups, brackets — [Lie-Theoretic Notation](#6-lie-theoretic-notation)
6. Physical quantities: coupling constants and masses — [Physical Quantities](#7-physical-quantities)
7. BLD-specific notation: traversal, K/X corrections — [BLD-Specific Notation](#10-bld-specific-notation)

# Notation and Conventions

## Abstract

This document establishes the standard notation used throughout BLD theory. We define symbols for the three primitives, derived constants, type-theoretic notation, categorical notation, and physical quantities. Consistent notation enables clear communication and reduces ambiguity in proofs and derivations.

## 1. Introduction

BLD theory uses notation from type theory, category theory, Lie theory, and physics. This document serves as the authoritative reference for symbol meanings. When notation in other files conflicts with this document, this document takes precedence.

## 2. The Three Primitives

| Symbol | Name | Meaning | Type-Theoretic | Categorical |
|--------|------|---------|----------------|-------------|
| **B** | Boundary | Partition/Choice | Sum type (τ₁ + τ₂) | Coproduct (⨿) |
| **L** | Link | Reference/Connection | Function type (τ₁ → τ₂) | Morphism (→) |
| **D** | Dimension | Repetition/Extent | Product type (Πₙτ) | Product (×) |

### 2.1 Primitive Values

When used as values (not operations):

| Symbol | Value | Derivation |
|--------|-------|------------|
| B | 56 | 2 × dim(Spin(8)) = 2 × 28 |
| L | 20 | n²(n²-1)/12 = 16×15/12 |
| n | 4 | Spacetime dimensions (octonion reference fixing) |

### 2.2 Operations

| Notation | Meaning |
|----------|---------|
| B(V) | Apply boundary to value space V |
| L(v₁, v₂) | Create link from v₁ to v₂ |
| Dₙ(S) | Create n-fold product of structure S |

## 3. Derived Constants

| Symbol | Value | Definition | Derivation Reference |
|--------|-------|------------|---------------------|
| **K** | 2 | Killing form (bidirectional observation cost) | [killing-form.md](../lie-theory/killing-form.md) |
| **S** | 13 | Structural intervals: (B - n)/n = 52/4 | [constants.md](constants.md) |
| **α⁻¹** | 137.036... | Fine structure constant inverse | [force-structure.md](derivations/force-structure.md) |

### 3.1 Key Combinations

| Expression | Value | Meaning |
|------------|-------|---------|
| n × L | 80 | Geometric structure |
| n × L + B | 136 | Structure without traverser |
| n × L + B + 1 | 137 | Full structure (α⁻¹ integer part) |
| K / B | 2/56 ≈ 0.036 | Boundary correction |
| K / X | varies | Observation cost (hidden structure) |

## 4. Type-Theoretic Notation

### 4.1 Types

| Notation | Meaning |
|----------|---------|
| τ, σ, ρ | Type variables |
| 1 | Unit type (single inhabitant) |
| 0 | Empty type (no inhabitants) |
| τ₁ + τ₂ | Sum type (B) |
| τ₁ → τ₂ | Function type (L) |
| Πₙτ | n-fold product type (D) |
| τ × τ | Binary product; shorthand for Π₂τ (homogeneous) |

### 4.2 Terms

| Notation | Meaning |
|----------|---------|
| () | Unit value |
| x, y, z | Variables |
| inl(e) | Left injection into sum |
| inr(e) | Right injection into sum |
| case e of {...} | Case analysis (B elimination) |
| λx:τ.e | Lambda abstraction (L introduction) |
| e₁ e₂ | Function application (L elimination) |
| ⟨e₁, ..., eₙ⟩ | n-tuple (D introduction) |
| e.i | Projection (D elimination) |

### 4.3 Typing Judgments

| Notation | Meaning |
|----------|---------|
| Γ | Typing context |
| Γ ⊢ e : τ | In context Γ, term e has type τ |
| e ⟶ e' | Term e reduces to e' |
| e ⟶* e' | Term e reduces to e' in zero or more steps |

## 5. Categorical Notation

| Notation | Meaning |
|----------|---------|
| C, D | Categories |
| Ob(C) | Objects of category C |
| Hom(A, B) | Morphisms from A to B |
| f: A → B | Morphism f from object A to object B |
| g ∘ f | Composition: first f, then g |
| idₐ | Identity morphism on object A |
| A ⨿ B | Coproduct (B) |
| A × B | Product (D) |
| A ⇒ B | Exponential object (L) |

## 6. Lie-Theoretic Notation

| Notation | Meaning |
|----------|---------|
| 𝔤 | Lie algebra |
| G | Lie group |
| [X, Y] | Lie bracket |
| fᵢⱼᵏ | Structure constants: [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ |
| dim(𝔤) | Dimension of Lie algebra |
| Spin(n) | Spin group |
| SU(n) | Special unitary group |
| SO(n) | Special orthogonal group |
| sl(n, 𝔽) | Special linear algebra over field 𝔽 |
| 𝕆 | Octonions |
| ℍ | Quaternions |
| ℂ | Complex numbers |
| ℝ | Real numbers |

## 7. Physical Quantities

### 7.1 Coupling Constants

| Symbol | Meaning | BLD Derivation |
|--------|---------|----------------|
| α | Fine structure constant (EM) | 1/(nL + B + 1 + K/B + ...) |
| α_W | Weak coupling | K/(nL) at weak scale |
| α_s | Strong coupling | From SU(3) structure |
| G_N | Gravitational constant | From dimensional analysis |

### 7.2 Masses

| Symbol | Meaning |
|--------|---------|
| mₑ | Electron mass |
| mμ | Muon mass |
| mτ | Tau mass |
| m_W | W boson mass |
| m_Z | Z boson mass |
| m_H | Higgs mass |

### 7.3 Other Physical Notation

| Symbol | Meaning |
|--------|---------|
| sin²θ_W | Weak mixing angle |
| θ_W | Weinberg angle |
| ℏ | Reduced Planck constant |
| c | Speed of light |
| G | Newton's gravitational constant |

## 8. Set-Theoretic Notation

| Notation | Meaning |
|----------|---------|
| ∈ | Element of |
| ⊆ | Subset |
| ∪ | Union |
| ∩ | Intersection |
| ⨆ | Disjoint union |
| ∅ | Empty set |
| ℕ | Natural numbers {0, 1, 2, ...} |
| ℤ | Integers |
| ℚ | Rationals |
| |S| | Cardinality of set S |

## 9. Proof Notation

| Symbol | Meaning |
|--------|---------|
| ∎ | End of proof (QED) |
| □ | End of proof (alternative) |
| ⊢ | Proves / Entails |
| ⊨ | Models / Satisfies |
| ≡ | Definitionally equal |
| ≅ | Isomorphic |
| ↔ | If and only if |
| → | Implies |
| ¬ | Not |
| ∀ | For all |
| ∃ | There exists |

## 10. BLD-Specific Notation

### 10.1 Traversal

| Notation | Meaning |
|----------|---------|
| traverse(S) | Traverse structure S |
| traverse(-B, B) | Traverse from non-existence to existence |
| K/X | Cost to traverse structure X |

### 10.2 Structural Formulas

| Formula | Meaning |
|---------|---------|
| E = K × Σ(1/Xᵢ) | Energy as accumulated traversal cost |
| α⁻¹ = nL + B + 1 + K/B + ... | Fine structure constant expansion |

### 10.3 Document References

| Notation | Meaning |
|----------|---------|
| [Author, Year] | Citation in academic format |
| [filename.md] | Internal document reference |

## 11. Conventions

### 11.1 Capitalization

- **B, L, D**: Uppercase when referring to primitives or their values
- **b, l, d**: Lowercase for variables ranging over boundaries, links, dimensions

### 11.2 Subscripts and Superscripts

- Subscript n: Dimension parameter (Πₙ, Dₙ)
- Subscript i, j, k: Index variables
- Superscript -1: Inverse (α⁻¹)
- Superscript n: Power (|τ|ⁿ)

### 11.3 Greek Letters

| Letter | Common Usage |
|--------|--------------|
| α | Fine structure constant |
| τ, σ, ρ | Type variables |
| λ | Lambda abstraction |
| Γ | Typing context |
| Π | Product type |
| Σ | Sum (sigma notation) |
| θ | Angle (Weinberg angle) |

## 12. Summary Table

| Domain | BLD Notation |
|--------|--------------|
| Primitives | B, L, D (or n for dimension value) |
| Constants | K, S, α, α⁻¹ |
| Types | τ + σ, τ → σ, Πₙτ |
| Terms | inl, inr, case, λ, ⟨...⟩, .i |
| Categories | ⨿, →, × |
| Lie theory | 𝔤, [X,Y], fᵢⱼᵏ |
| Traversal | traverse, K/X |

## References

[Harper, 2016] R. Harper. *Practical Foundations for Programming Languages*. Cambridge University Press, 2nd ed., 2016.

[Knuth, 1984] D. E. Knuth. *The TeXbook*. Addison-Wesley, 1984.

[Pierce, 2002] B. Pierce. *Types and Programming Languages*. MIT Press, 2002.
