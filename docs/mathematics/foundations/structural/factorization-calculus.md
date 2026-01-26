---
status: DERIVED
layer: 1
depends_on:
  - ../definitions/bld-calculus.md
  - ../proofs/irreducibility-categorical.md
  - ../../lie-theory/lie-correspondence.md
used_by:
  - structural-cost-conservation.md
  - ../definitions/bld-calculus.md
  - ../../../applications/code/bld-driven-development.md
  - ../../../applications/code/refactoring.md
---

# Refactoring as Factorization (RF-Calculus)

Refactoring is factorization: decomposition of composite structures into smaller structures, terminating at irreducible BLD primitives.

---

## Quick Summary

**RF-Calculus in 7 steps:**

1. **FACTOR : S → S₁ × S₂ × ...** — decomposition into smaller structures
2. **Structural Terms** — s ::= b | l | d | s × s | s + s | s → s
3. **B-Factor** — scattered conditionals → explicit sum type (boundary)
4. **L-Factor** — cyclic dependencies → shared + directed (link acyclicity)
5. **D-Factor** — heterogeneous loops → homogeneous products (dimension purity)
6. **Termination** — stops at irreducible B × L × D (proven from BLD calculus)
7. **Isomorphism** — eval(S) = eval(FACTOR(S)) (behavior preserved)

| Rule | Input Pattern | Output Pattern | Reveals |
|------|---------------|----------------|---------|
| B-Factor | if/elif scattered | Sum type | Boundary |
| L-Factor | Cycle A→B→C→A | Shared + DAG | Link structure |
| D-Factor | Mixed loop | Homogeneous products | Dimension |

**Key insight**: Refactoring doesn't reduce complexity — it reveals implicit structure by decomposing composites into explicit primitives.

---

## The Three Factorization Rules

```
┌─────────────────────┐  ┌─────────────────────┐  ┌─────────────────────┐
│      B-FACTOR       │  │      L-FACTOR       │  │      D-FACTOR       │
│                     │  │                     │  │                     │
│  if x==a: ...       │  │  A → B              │  │  for item in mixed: │
│  if x==b: ...   →   │  │  ↓   ↓   →         │  │    if type_a: ...   │
│  if x==c: ...       │  │  C ← ←              │  │    if type_b: ...   │
│         ↓           │  │       ↓             │  │         ↓           │
│  T = a|b|c  (B)     │  │  [State]  (shared)  │  │  D[a] × D[b]        │
│  dispatch(T)  (L)   │  │  A → S              │  │  (homogeneous       │
│                     │  │  B → S   (DAG)      │  │   dimensions)       │
│                     │  │  C → S              │  │                     │
└─────────────────────┘  └─────────────────────┘  └─────────────────────┘
```

---

## 1. The Fundamental Operation

### 1.1 Definition

**FACTOR** is the operation that decomposes structure into smaller structures:

```
FACTOR : Structure → Structure × Structure × ... × Structure
         S        → S₁ × S₂ × ... × Sₙ

Properties:
  1. |Sᵢ| < |S|           (each factor is strictly smaller)
  2. Π Sᵢ ≅ S             (factors reconstruct original — isomorphism)
  3. Terminates at B,L,D  (irreducible primitives)
```

**What FACTOR is NOT**:
- NOT transformation (changing structure)
- NOT optimization (reducing cost)
- NOT simplification (removing complexity)

**What FACTOR IS**:
- Decomposition (breaking into parts)
- Revelation (making implicit explicit)
- Factorization (like prime factorization of numbers)

### 1.2 Analogy: Prime Factorization

```
Number factorization:     60 → 2 × 2 × 3 × 5
Tensor factorization:     T → Σ aᵢ ⊗ bᵢ ⊗ cᵢ
Lie algebra decomposition: g → g₁ ⊕ g₂  (direct sum of simple algebras)
Structure factorization:  S → B × L × D  (decomposition to primitives)
```

All follow the same pattern: composite → product of irreducibles.

---

## 2. Structural Terms

### 2.1 Syntax

Building on the BLD Calculus ([bld-calculus.md](../definitions/bld-calculus.md)), structural terms are:

```
s ::= b                   -- Boundary primitive (irreducible)
    | l                   -- Link primitive (irreducible)
    | d                   -- Dimension primitive (irreducible)
    | s × s               -- Product (composite)
    | s + s               -- Sum (choice)
    | s → s               -- Function (dependency)
```

**Correspondence to BLD Calculus types**:

| Structural Term | BLD Calculus Type | Meaning |
|-----------------|-------------------|---------|
| b | τ₁ + τ₂ | Boundary (partition/case) |
| l | τ₁ → τ₂ | Link (reference/function) |
| d | Πₙτ | Dimension (repetition/product) |
| s × s | Composite | Product structure |
| s + s | Composite | Sum structure |
| s → s | Composite | Dependent structure |

### 2.2 Size Measure

The **size** of a structural term is the count of primitives plus composites:

```
|b| = 1
|l| = 1
|d| = 1
|s₁ × s₂| = 1 + |s₁| + |s₂|
|s₁ + s₂| = 1 + |s₁| + |s₂|
|s₁ → s₂| = 1 + |s₁| + |s₂|
```

**Key property**: Factorization strictly reduces composite size while preserving primitive count.

### 2.3 Reducibility

A structure is **reducible** iff at least one factorization rule applies.

A structure is **irreducible** iff it is one of: b, l, d.

A structure is in **normal form** iff it is a product of irreducibles:
```
S* = b₁ × b₂ × ... × l₁ × l₂ × ... × d₁ × d₂ × ...
```

---

## 3. Factorization Rules

### 3.1 B-Factor (Boundary Decomposition)

**Pattern**: Scattered conditionals on the same discriminant

```
B-Factor:
───────────────────────────────────────────────────────────────────
S[if x==c₁:e₁ | if x==c₂:e₂ | ... | if x==cₙ:eₙ]
    ↓ FACTOR
B(x) × Dispatch(e₁, e₂, ..., eₙ)

where:
  B(x) = c₁ + c₂ + ... + cₙ    (explicit sum type — boundary)
  Dispatch = {cᵢ → eᵢ}          (factored-out logic)
```

**In code terms**:

Before (implicit boundary):
```python
def process(event):
    if event.type == "click":
        handle_click(event)
    elif event.type == "hover":
        handle_hover(event)
    elif event.type == "drag":
        handle_drag(event)
```

After (explicit boundary):
```python
EventType = Click | Hover | Drag    # B: explicit sum type

handlers = {
    Click: handle_click,
    Hover: handle_hover,
    Drag: handle_drag,
}

def process(event):
    handlers[event.type](event)     # B × L: boundary + dispatch
```

The scattered conditionals are an implicit boundary. FACTOR extracts it as an explicit sum type.

### 3.2 L-Factor (Link Decomposition)

**Pattern**: Cyclic dependency hiding shared state

```
L-Factor:
───────────────────────────────────────────────────────────────────
S[A → B → C → A]    (cycle)
    ↓ FACTOR
Shared × (A → S) × (B → S) × (C → S)    (DAG)

where:
  Shared = extracted common state
  → S = directed links to shared (acyclic)
```

**In code terms**:

Before (implicit shared state via cycle):
```python
class A:
    def __init__(self, b): self.b = b
    def update(self): self.b.notify(self.state)

class B:
    def __init__(self, c): self.c = c
    def notify(self, s): self.c.process(s)

class C:
    def __init__(self, a): self.a = a
    def process(self, s): self.a.receive(s)
```

After (explicit shared state):
```python
class SharedState:
    state: Any

class A:
    def __init__(self, shared): self.shared = shared
class B:
    def __init__(self, shared): self.shared = shared
class C:
    def __init__(self, shared): self.shared = shared
```

The cycle encodes shared state. FACTOR extracts it, leaving a DAG.

### 3.3 D-Factor (Dimension Decomposition)

**Pattern**: Heterogeneous dimension (mixed types in loop)

```
D-Factor:
───────────────────────────────────────────────────────────────────
S[D(mixed items)]
    ↓ FACTOR
D_A(items_A) × D_B(items_B)

where:
  D_A = homogeneous dimension over type A
  D_B = homogeneous dimension over type B
```

**In code terms**:

Before (heterogeneous loop):
```python
def process_all(items):
    for item in items:
        if isinstance(item, User):
            process_user(item)
        elif isinstance(item, Product):
            process_product(item)
```

After (homogeneous loops):
```python
def process_all(users: list[User], products: list[Product]):
    for user in users:
        process_user(user)
    for product in products:
        process_product(product)
```

The mixed loop contains two implicit dimensions. FACTOR separates them into explicit homogeneous products.

---

## 4. Termination

### 4.1 Theorem (Termination)

**Theorem**: FACTOR terminates for all finite structures.

**Proof**:

1. Define size measure |S| as above
2. Each factorization rule produces structures with |Sᵢ| < |S|
3. Size is bounded below by primitive count (≥ 0)
4. Therefore, any sequence of factorizations must terminate
5. Terminal forms are products of irreducibles (B, L, D)
6. By the irreducibility theorem ([irreducibility-categorical.md](../proofs/irreducibility-categorical.md)), B, L, D cannot be further decomposed

∎

### 4.2 Fixed Point

The **fixed point** S* satisfies:

```
∀ rule R: R(S*) = S*
```

At the fixed point:
- No scattered conditionals remain (B fully factored)
- No cycles remain (L fully factored to DAG)
- No mixed dimensions remain (D fully factored to homogeneous)

### 4.3 Normal Form

Every structure has a unique **normal form** (up to reordering):

```
S* = B₁ × B₂ × ... × Bₘ × L₁ × L₂ × ... × Lₙ × D₁ × D₂ × ... × Dₖ
```

where each Bᵢ, Lⱼ, Dₖ is irreducible.

---

## 5. Isomorphism Preservation

### 5.1 Theorem (Behavior Preservation)

**Theorem**: FACTOR preserves behavior:

```
eval(S) = eval(FACTOR(S))
```

**Proof sketch**:

1. B-Factor: Sum type dispatch computes same values as scattered conditionals
2. L-Factor: DAG with shared state produces same results as cycle
3. D-Factor: Two homogeneous loops compute same as one heterogeneous loop

Each rule is a local transformation preserving input-output behavior.

∎

### 5.2 Corollary

Factorization is a **structural isomorphism**:

```
S ≅ FACTOR(S)
```

as computational objects (same behavior), though not identical as terms.

---

## 6. Connection to Proven Infrastructure

### 6.1 BLD Calculus

The RF-Calculus structural terms correspond to BLD Calculus types ([bld-calculus.md](../definitions/bld-calculus.md)):

```
BLD Calculus types:    τ ::= 1 | τ₁+τ₂ | τ₁→τ₂ | Πₙτ

RF-Calculus terms:     s ::= b | l | d | s×s | s+s | s→s

Correspondence:
  τ₁ + τ₂  ↔  b (boundary)
  τ₁ → τ₂  ↔  l (link)
  Πₙτ      ↔  d (dimension)
```

FACTOR is the **inverse of type composition** in BLD Calculus.

### 6.2 Irreducibility

The termination of FACTOR depends on the irreducibility theorem ([irreducibility-categorical.md](../proofs/irreducibility-categorical.md)):

**Theorem**: B, L, D are mutually irreducible.

- B cannot be expressed using only L and D
- L cannot be expressed using only B and D
- D cannot be expressed using only B and L

**Consequence**: Factorization MUST terminate — no infinite chains of decomposition.

### 6.3 Lie Correspondence

FACTOR on structures corresponds to **Levi decomposition** on Lie algebras ([lie-correspondence.md](../../lie-theory/lie-correspondence.md)):

```
Lie algebra:    g = r ⋊ l    (radical ⋊ Levi subalgebra)
                l = s₁ ⊕ s₂ ⊕ ... ⊕ sₖ    (direct sum of simple algebras)

Structure:      S = FACTOR(S)
                S* = B₁ × ... × L₁ × ... × D₁ × ...
```

The Levi decomposition is unique. Similarly, factorization to BLD normal form is unique.

### 6.4 Observer Correction

From the structural-observer framework: factorization reveals the **hidden cost** of implicit structure.

```
C_visible(S)  = cost of explicit BLD
C_hidden(S)   = cost of implicit structure

C_total = C_visible + C_hidden    (conserved)

FACTOR: C_hidden → C_visible      (reveals hidden cost)
```

Implicit structure has hidden cost that multiplies perceived complexity. Factorization makes this cost auditable by converting it to explicit BLD.

---

## 7. Worked Examples

### 7.1 Example: Event Handler Refactoring

**Initial structure** (implicit B):
```
S = [if click: A | if hover: B | if drag: C]
```

**Apply B-Factor**:
```
FACTOR(S) = EventType × Handler
where EventType = click + hover + drag    (B)
      Handler = {type → action}           (L × D)
```

**Size reduction**:
- Before: |S| = 7 (3 conditions + 3 actions + 1 container)
- After: |EventType| = 1 (boundary), |Handler| = 4 (3 entries + 1 map)
- Structure preserved, implicit boundary now explicit

### 7.2 Example: Circular Dependency

**Initial structure** (cycle):
```
S = A → B → C → A
```

**Apply L-Factor**:
```
FACTOR(S) = State × (A → State) × (B → State) × (C → State)
```

**Result**: DAG with explicit shared state. Cycle eliminated.

### 7.3 Example: Mixed Collection

**Initial structure** (heterogeneous D):
```
S = D[User, Product, User, Product, User]
```

**Apply D-Factor**:
```
FACTOR(S) = D[User, User, User] × D[Product, Product]
          = D₃(User) × D₂(Product)
```

**Result**: Two homogeneous dimensions. Processing logic separated.

---

## 8. Notation Summary

| Symbol | Meaning |
|--------|---------|
| S | Composite structure |
| s | Structural term |
| b, l, d | Irreducible primitives |
| FACTOR | Decomposition operation |
| \|S\| | Size of structure |
| S* | Normal form (fixed point) |
| ≅ | Structural isomorphism |
| × | Product (composition) |
| + | Sum (choice) |
| → | Function (dependency) |

---

## 9. Open Questions

1. **Uniqueness of factorization order**: Does the order of applying rules matter for the final result? (Conjecture: No — confluence)

2. **Optimal factorization**: Is there a canonical sequence that minimizes intermediate size?

3. **Partial factorization**: Can useful invariants be proven without reaching full normal form?

4. **Cost prediction**: Can we predict the cost of factorization before performing it?

---

## See Also

- [Glossary](../../../glossary.md) — Central definitions
- [BLD Calculus](../definitions/bld-calculus.md) — Type system foundation
- [Irreducibility Theorem](../proofs/irreducibility-categorical.md) — Why factorization terminates
- [Lie Correspondence](../../lie-theory/lie-correspondence.md) — FACTOR = Levi decomposition
- [Structural Cost Conservation](./structural-cost-conservation.md) — Cost algebra
