# The BLD Calculus

> **Status**: Foundational

A typed lambda calculus with exactly three type constructors corresponding to Boundary, Link, and Dimension.

> **Dependency**: This document defines the formal system. The [Irreducibility Theorem](./irreducibility-categorical.md) uses these definitions to prove B/L/D independence.

---

## 1. Purpose

This calculus provides the formal foundation for proving B/L/D irreducibility. By defining a minimal type system with precisely these three constructors, we can rigorously prove that none can be expressed using the others.

---

## 2. Syntax

### 2.1 Types

```
τ ::= 1              -- Unit type (base case)
    | τ₁ + τ₂        -- Sum type (Boundary)
    | τ₁ → τ₂        -- Function type (Link)
    | Πₙτ            -- n-fold product (Dimension), where n ∈ ℕ
```

**Notation**:
- We write `Π₀τ = 1` (empty product is unit)
- We write `Π₁τ = τ` (singleton product is the type itself)
- We write `Πₙτ` for "n copies of τ" (an n-tuple)

### 2.2 Terms

```
e ::= ()                                              -- Unit value
    | x                                               -- Variable
    | inl(e)                                          -- Left injection (B)
    | inr(e)                                          -- Right injection (B)
    | case e of {inl(x) ⇒ e₁; inr(y) ⇒ e₂}           -- Case analysis (B)
    | λx:τ.e                                          -- Abstraction (L)
    | e₁ e₂                                           -- Application (L)
    | ⟨e₁, e₂, ..., eₙ⟩                               -- n-tuple (D)
    | e.i                                             -- Projection, i ∈ {1,...,n} (D)
```

### 2.3 Values

```
v ::= ()                        -- Unit value
    | inl(v)                    -- Left injection of value
    | inr(v)                    -- Right injection of value
    | λx:τ.e                    -- Function (body may not be reduced)
    | ⟨v₁, v₂, ..., vₙ⟩         -- Tuple of values
```

---

## 3. Typing Rules

### 3.1 Structural Rules

```
         x:τ ∈ Γ
    ─────────────── (Var)
       Γ ⊢ x : τ


    ─────────────── (Unit)
      Γ ⊢ () : 1
```

### 3.2 Sum Type (Boundary)

```
        Γ ⊢ e : τ₁
    ─────────────────────── (Inl)
     Γ ⊢ inl(e) : τ₁ + τ₂


        Γ ⊢ e : τ₂
    ─────────────────────── (Inr)
     Γ ⊢ inr(e) : τ₁ + τ₂


    Γ ⊢ e : τ₁ + τ₂    Γ,x:τ₁ ⊢ e₁ : τ    Γ,y:τ₂ ⊢ e₂ : τ
    ─────────────────────────────────────────────────────── (Case)
           Γ ⊢ case e of {inl(x) ⇒ e₁; inr(y) ⇒ e₂} : τ
```

### 3.3 Function Type (Link)

```
       Γ, x:τ₁ ⊢ e : τ₂
    ─────────────────────── (Abs)
      Γ ⊢ λx:τ₁.e : τ₁ → τ₂


     Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
    ─────────────────────────────────── (App)
              Γ ⊢ e₁ e₂ : τ₂
```

### 3.4 Product Type (Dimension)

```
     Γ ⊢ e₁ : τ    Γ ⊢ e₂ : τ    ...    Γ ⊢ eₙ : τ
    ─────────────────────────────────────────────────── (Tuple)
              Γ ⊢ ⟨e₁, e₂, ..., eₙ⟩ : Πₙτ


        Γ ⊢ e : Πₙτ    i ∈ {1, ..., n}
    ────────────────────────────────────── (Proj)
                 Γ ⊢ e.i : τ
```

---

## 4. Operational Semantics

Small-step call-by-value reduction:

### 4.1 Computation Rules

```
    case inl(v) of {inl(x) ⇒ e₁; inr(y) ⇒ e₂}  ⟶  e₁[v/x]     (β-Case-L)

    case inr(v) of {inl(x) ⇒ e₁; inr(y) ⇒ e₂}  ⟶  e₂[v/y]     (β-Case-R)

    (λx:τ.e) v  ⟶  e[v/x]                                       (β-App)

    ⟨v₁, ..., vₙ⟩.i  ⟶  vᵢ                                      (β-Proj)
```

### 4.2 Congruence Rules

```
         e ⟶ e'
    ─────────────────── (Cong-Inl)
     inl(e) ⟶ inl(e')


         e ⟶ e'
    ─────────────────── (Cong-Inr)
     inr(e) ⟶ inr(e')


                            e ⟶ e'
    ──────────────────────────────────────────────────────────── (Cong-Case)
     case e of {...} ⟶ case e' of {...}


      e₁ ⟶ e₁'                    e₂ ⟶ e₂'
    ────────────── (Cong-App-L)  ────────────── (Cong-App-R)
     e₁ e₂ ⟶ e₁' e₂              v e₂ ⟶ v e₂'


             eᵢ ⟶ eᵢ'
    ───────────────────────────────────────────── (Cong-Tuple)
     ⟨v₁,...,eᵢ,...⟩ ⟶ ⟨v₁,...,eᵢ',...⟩


       e ⟶ e'
    ──────────── (Cong-Proj)
     e.i ⟶ e'.i
```

---

## 5. Metatheory

### 5.1 Canonical Forms Lemma

**Lemma (Canonical Forms)**: If `⊢ v : τ` and `v` is a value, then:

1. If `τ = 1`, then `v = ()`
2. If `τ = τ₁ + τ₂`, then `v = inl(v')` with `⊢ v' : τ₁`, or `v = inr(v')` with `⊢ v' : τ₂`
3. If `τ = τ₁ → τ₂`, then `v = λx:τ₁.e` for some `e` with `x:τ₁ ⊢ e : τ₂`
4. If `τ = Πₙσ`, then `v = ⟨v₁, ..., vₙ⟩` with `⊢ vᵢ : σ` for all `i`

**Proof**: By induction on the typing derivation, using the definition of values. Each type constructor has a unique introduction form. ∎

### 5.2 Progress

**Theorem (Progress)**: If `⊢ e : τ`, then either:
- `e` is a value, or
- There exists `e'` such that `e ⟶ e'`

**Proof**: By induction on typing derivation. Each elimination form (case, application, projection) reduces when its principal argument is a value of the appropriate form (guaranteed by Canonical Forms). ∎

### 5.3 Preservation

**Theorem (Preservation)**: If `Γ ⊢ e : τ` and `e ⟶ e'`, then `Γ ⊢ e' : τ`.

**Proof**: By induction on the reduction derivation. Substitution lemma needed for β-rules. ∎

---

## 6. Sublanguages

### 6.1 Definitions

**LD-calculus**: The fragment with types `τ ::= 1 | τ → τ | Πₙτ` (no sums)

**BD-calculus**: The fragment with types `τ ::= 1 | τ + τ | Πₙτ` (no functions)

**BL-calculus**: The fragment with types `τ ::= 1 | τ + τ | τ → τ` (no Πₙ for n>1; Π₁τ ≅ τ is identity)

### 6.2 Inhabitance

**Definition**: A type `τ` is **inhabited** if there exists a closed value `v` with `⊢ v : τ`.

**Definition**: The **cardinality** `|τ|` of an inhabited type is the number of distinct closed values of that type (possibly infinite).

---

## 7. Cardinality Lemmas

> **Note**: These lemmas support the irreducibility proofs but are not the core arguments. See [irreducibility-categorical.md](./irreducibility-categorical.md) for the main theorems.

### 7.1 Full BLD Calculus

| Type | Cardinality |
|------|-------------|
| `1` | 1 |
| `τ₁ + τ₂` | `\|τ₁\| + \|τ₂\|` |
| `τ₁ → τ₂` | `\|τ₂\|^\|τ₁\|` |
| `Πₙτ` | `\|τ\|^n` |

### 7.2 LD-Calculus Cardinality

**Lemma**: In LD-calculus, every closed type has cardinality exactly 1.

**Proof**: By structural induction. The only base type is `1` (cardinality 1). Products and functions preserve cardinality 1:
- `|Πₙτ| = |τ|^n = 1^n = 1`
- `|τ₁ → τ₂| = |τ₂|^|τ₁| = 1^1 = 1`

Since LD-calculus has no sums, we cannot construct types with cardinality > 1. ∎

**Consequence**: LD-calculus cannot encode `Bool = 1 + 1` (which has cardinality 2).

### 7.3 BD-Calculus Cardinality

**Observation**: BD-calculus can express any finite cardinality:
- `|1| = 1`
- `|1 + 1| = 2`
- `|(1+1) + 1| = 3`
- `|Π₂(1+1)| = 4`

**Key limitation**: BD-calculus has no application construct. Values are pure data—they can be inspected via `case` and `project`, but cannot compute based on inputs.

**Consequence**: BD-calculus can represent function *graphs* but not functions as first-class values.

### 7.4 BL-Calculus Cardinality

**Observation**: In BL-calculus, each type has a fixed cardinality independent of any parameter n.

**Key limitation**: BL-calculus cannot express "n copies of τ" where n is a parameter. Every type has a fixed, finite description.

**Consequence**: BL-calculus cannot encode the family `{Πₙτ : n ∈ ℕ}` uniformly.

---

## 8. Connection to B/L/D Primitives

| Type Constructor | BLD Primitive | Traversal Operation |
|-----------------|---------------|---------------------|
| Sum (+) | Boundary | Case analysis (which partition?) |
| Function (→) | Link | Application (follow reference) |
| Product (Πₙ) | Dimension | Projection (access i-th element) |

The elimination forms correspond exactly to traverser capabilities:
- **case**: Discriminate based on tag (B capability)
- **apply**: Dereference a function at a point (L capability)
- **project**: Index into a tuple (D capability)

---

## 9. References

1. Pierce, B. "Types and Programming Languages." MIT Press, 2002.
2. Girard, J.-Y., Lafont, Y., Taylor, P. "Proofs and Types." Cambridge, 1989.
3. Harper, R. "Practical Foundations for Programming Languages." Cambridge, 2016.

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Irreducibility Theorem](./irreducibility-categorical.md) — Proof using this calculus
- [Irreducibility Proof](./irreducibility-proof.md) — Intuitive arguments
- [Structural Language](../../theory/structural-language.md) — B/L/D specification
