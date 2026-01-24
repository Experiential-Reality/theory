---
status: VALIDATED
layer: application
depends_on:
  - ../../mathematics/foundations/structural/factorization-calculus.md
  - ../../mathematics/foundations/structural/structural-cost-conservation.md
  - ../../meta/discovery-method.md
used_by:
  - ../../paths/practitioner.md
  - ../../README.md
  - README.md
  - bld-driven-development.md
---

# Refactoring Philosophy: Make State Explicit

> **Status**: Foundational

## Quick Summary (D≈7 Human Traversal)

**Refactoring with BLD in 7 steps:**

1. **Refactoring is factorization** — Decompose complex structures into explicit B × L × D primitives; complexity is conserved but becomes visible
2. **Horizontal: Extract dispatch tables** — Scattered if/elif against same value = hidden Boundary; extract to `dict[Key, Handler]`
3. **Vertical: Enumerate state space** — Magic strings in 5 places = hidden Dimension; extract to enum or config dataclass
4. **Structural: Break cycles into DAG** — Circular dependencies = hidden Links; extract shared state to third module
5. **Cost conservation** — `C_total = C_visible + C_hidden`; FACTOR moves hidden cost to visible cost
6. **Same fixes improve performance** — Explicit B enables branch elimination, explicit D enables vectorization, explicit L enables parallelism
7. **Refactoring = finding Lie structure** — Dispatch tables reveal group topology (B), enums reveal generators (D), DAGs reveal structure constants (L)

| Component | BLD Mapping |
|-----------|-------------|
| Dispatch table | B: value partitions handler space |
| Enum/config | D: N states form axis of repetition |
| DAG dependencies | L: directed connections, no cycles |
| Hidden state | Implicit B, cyclic L, or scattered D |
| Performance gain | Explicit structure enables compiler optimization |

---

> **Data and control should flow through explicit, visible paths.**
> **If you can't draw it as a clean DAG, there's hidden state. Find it and name it.**

This document connects practical refactoring patterns to the three structural primitives (Boundary, Link, Dimension) and explains why these patterns work from the perspective of experiential reality theory.

---

## Refactoring = Factorization

**Refactoring is decomposition, not transformation.**

The mathematical formalization of refactoring is the **FACTOR** operation:

```
FACTOR : S → S₁ × S₂ × ... × Sₙ

where |Sᵢ| < |S|           (each piece is smaller)
and   Π Sᵢ ≅ S             (pieces reconstruct original)
```

**Key insight**: The structure already exists. Refactoring **reveals** it by decomposing composites into explicit, smaller structures. Factorization terminates at **irreducible BLD primitives**.

| Misconception | Truth |
|---------------|-------|
| Refactoring reduces complexity | Complexity is conserved — it becomes visible |
| Refactoring transforms code | Code computes the same — structure is revealed |
| Refactoring is optional style | Explicit structure enables optimization |

**Cost Conservation**: Total structural cost is invariant under refactoring:

```
C_total = C_visible + C_hidden    (conserved)

FACTOR: C_hidden → C_visible      (reveals hidden cost)
```

See [Factorization Calculus](../../mathematics/foundations/structural/factorization-calculus.md) and [Cost Conservation](../../mathematics/foundations/structural/structural-cost-conservation.md) for the mathematical details.

---

## The Core Thesis

**Structure is substrate-independent.** The same structural patterns that make code readable to humans also make it optimizable by compilers and understandable by LLMs. This isn't coincidence — all three are responding to the same underlying structural properties.

When we refactor code to "make state explicit," we're not just following style guidelines. We're aligning the code's structure with the structure of the problem it solves. This alignment reduces friction for any system that needs to traverse the code — human, machine, or AI.

---

## Three Dimensions of Explicit State

### 1. Horizontal: Dispatch Tables → Boundary

**The Pattern:**

Comparisons against the same value are an implicit state machine:

```python
# Implicit (scattered)          # Explicit (tabular)
if x == A: ...                   handlers = {A: do_a, B: do_b, C: do_c}
elif x == B: ...                 handlers[x](state)
elif x == C: ...
```

**When to extract:** 4+ states, or complex bodies → extract to `dict[Key, Handler]`

**Structural Primitive:** This is a **Boundary** — the value `x` partitions the handler space into regions of meaning.

**Why It Works:**

A boundary partitions VALUE SPACE, not code space. When you scatter if/elif checks through code, you're hiding the fact that there's a single value partitioning behavior. The boundary exists structurally, but it's not visible.

When you extract to a dispatch table:
- The partition becomes visible (you can see all cases)
- The discriminator is explicit (the key)
- Adding cases is additive (just add an entry)
- Missing cases are obvious (key not in dict)

**Connection to Theory:**

From the structural language: "The discriminator is always OUTSIDE the scope it controls." In a dispatch table, the key (discriminator) is literally separate from the handlers (scopes). In scattered if/elif, the discriminator is repeated and mixed with the logic.

---

### 2. Vertical: State Space Visibility → Dimension

**The Pattern:**

If N discrete values affect behavior, all N should be visible in one place:

| Implicit | Explicit |
|----------|----------|
| Magic strings checked in 5 places | Enum with exhaustive match |
| Feature flags scattered across codebase | Feature table with capabilities |
| Scattered `if config.x` checks | Config dataclass, passed explicitly |

**Why:** Completeness is verifiable. Missing cases are obvious. Extension is additive.

**Structural Primitive:** This is a **Dimension** — N states form an axis of repetition.

**Why It Works:**

A dimension is "an axis of repetition where all instances share the same structure." When you have N feature flags checked in various places, that's an implicit dimension — there are N variations of behavior, but you can't see them together.

When you extract to an enum or config:
- The extent is visible (exactly N values)
- Properties are explicit (what each value means)
- Traversal is possible (you can iterate all states)
- Homogeneity is enforced (all values have the same interface)

**Connection to Theory:**

From the structural language: "Dimensions are irreducible. You cannot represent 'N of these' using only boundary and link." Feature flags represent multiplicity — multiple configurations of the same system. Making the dimension explicit lets you reason about all configurations at once.

---

### 3. Structural: Dependencies Form a DAG → Link

**The Pattern:**

State flows one direction. Cycles = hidden shared state.

| Smell | Explicit Alternative |
|-------|---------------------|
| Class inheritance hierarchy | Composition + Protocol |
| Circular imports | Extract shared state to third module |
| Global mutable state | Explicit context passed down |
| "God object" everything touches | Split by responsibility, clear interfaces |

**Why:** Inheritance IS implicit state. The child's behavior depends on which parent methods it overrides—that's hidden state scattered across a hierarchy. Composition + protocols make it explicit.

**Structural Primitive:** This is **Link** — dependencies are connections that should form a DAG.

**Why It Works:**

A link connects one value to another with explicit direction. When dependencies form cycles, you can't determine which value comes first — there's hidden state in the order of initialization, the timing of mutations, the path of control flow.

When you break cycles:
- Direction is explicit (A depends on B, not vice versa)
- Traversal order is determined (topological sort exists)
- State flows one way (no hidden feedback loops)
- Testing is possible (you can mock dependencies)

**Connection to Theory:**

From the structural language: "Links create the graph structure. Direction matters (A → B ≠ B → A)." Circular dependencies are bidirectional links that should be decomposed. Inheritance is implicit linkage — the child links to the parent, but also the parent's behavior depends on which methods the child overrides, creating a hidden reverse link.

---

## The Mapping: Refactoring → Structure → Performance

| Refactoring Pattern | Hidden State | Primitive | Structural Fix | Performance Impact |
|---------------------|--------------|-----------|----------------|-------------------|
| if/elif chains | Implicit dispatch | Boundary | Extract to dict | Branch prediction improves |
| Scattered checks | Invisible state space | Dimension | Enumerate in one place | Enables optimization |
| Circular deps | Hidden coupling | Link | Make DAG explicit | Enables parallelism |
| Deep inheritance | Scattered overrides | Link + Boundary | Composition + Protocol | Enables inlining |
| God objects | Hidden data flow | All three | Split by responsibility | Enables caching |

The same transformations that make code readable also make it faster. This is because:

1. **Compilers optimize what they can see.** Explicit structure is visible structure.
2. **CPUs predict what's regular.** Explicit dimensions have regular access patterns.
3. **Caches exploit locality.** Explicit links reveal data dependencies.

---

## Practical Methodology

### Step 1: Identify Hidden State

Ask these questions:
- Is there a value that partitions behavior? (Hidden Boundary)
- Are there N things that should be visible together? (Hidden Dimension)
- Can I draw the dependency graph as a DAG? (Hidden Links)

### Step 2: Make It Explicit

Apply the corresponding transformation:

| If you find... | Extract to... |
|---------------|--------------|
| 4+ comparisons against same value | Dispatch table (dict) |
| Same check in 3+ places | Enum or config dataclass |
| Circular imports | Third module with shared state |
| Inheritance hierarchy | Composition + Protocol |
| Global mutable state | Explicit context parameter |

### Step 3: Verify the Structure

After refactoring, you should be able to:
- **Draw the DAG** — If you can't, there's still hidden state
- **Enumerate all states** — If you can't list them, dimensions are hidden
- **Point to the discriminator** — If you can't find it, boundaries are implicit

### Step 4: Test the Alignment

Good structure has these properties:
- **Adding a case is additive** — You add, not modify
- **Missing cases are obvious** — Exhaustive match, key errors
- **Dependencies are injectable** — You can substitute for testing
- **Traversal is deterministic** — Same input, same path

---

## Why This Connects to Performance

The experiential reality framework proposes that performance is predictable from structure. Here's why refactoring for explicit state also improves performance:

### Boundaries Enable Branch Elimination

```python
# Implicit: unpredictable branches
if x == A: do_a()
elif x == B: do_b()
elif x == C: do_c()

# Explicit: jump table
handlers[x]()  # Single indirect call, no branches
```

The CPU can't predict scattered if/elif, but it can execute a jump table in constant time.

### Dimensions Enable Vectorization

```python
# Implicit: irregular access
for item in items:
    if item.type == "special":
        process_special(item)
    else:
        process_normal(item)

# Explicit: separate dimensions
for item in special_items:
    process_special(item)
for item in normal_items:
    process_normal(item)
```

When you separate dimensions, each loop has homogeneous elements — SIMD can vectorize.

### Links Enable Parallelism

```python
# Implicit: hidden dependencies
def process():
    a = step1()
    b = step2()  # Does this depend on a?
    c = step3()  # Does this depend on a or b?

# Explicit: visible DAG
def process():
    a = step1()
    b = step2()  # Explicitly takes no args
    c = step3(a, b)  # Explicitly depends on both
```

When dependencies are explicit, a scheduler can run `step1()` and `step2()` in parallel.

---

## The Deep Connection

These refactoring patterns aren't arbitrary style rules. They're the same structural principles that govern:

- **Data formats** (ZIP files have boundaries, links, and dimensions)
- **Algorithms** (JPEG decoding is a dimension of process stages)
- **Hardware** (GPUs have workgroup boundaries, memory links, thread dimensions)

When you refactor code to make state explicit, you're aligning with universal structural patterns. That's why the same transformation:
- Makes code readable to humans
- Makes code optimizable by compilers
- Makes code understandable by LLMs
- Makes code efficient on hardware

**Structure is substrate-independent. Alignment with structure is universally beneficial.**

---

## Summary

| Principle | Pattern | Primitive | Question to Ask |
|-----------|---------|-----------|-----------------|
| **Horizontal** | Dispatch table | Boundary | "What value partitions behavior?" |
| **Vertical** | Enum/config | Dimension | "What N things should be visible together?" |
| **Structural** | DAG dependencies | Link | "Can I draw the flow as a directed graph?" |

The goal is always: **If you can't draw it as a clean DAG, there's hidden state. Find it and name it.**

---

## Connection to Lie Theory

Refactoring code to make state explicit IS finding Lie structure.

When you extract a dispatch table, you're identifying a boundary (group topology). When you enumerate states in a config, you're identifying a dimension (generator). When you break circular dependencies into a DAG, you're identifying link structure (structure constants).

| Refactoring | Lie Discovery |
|-------------|---------------|
| Extract dispatch table | Find group topology (boundary) |
| Enumerate config states | Find generators (dimension) |
| Break cycles into DAG | Find structure constants (links) |

This is why the same refactoring makes code readable to humans, optimizable by compilers, and understandable by LLMs — all three are responding to the same Lie structure becoming explicit.

See [Discovery Method](../../meta/discovery-method.md) for the general methodology.

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Discovery Method](../../meta/discovery-method.md) — The three questions
- [Structural Language](../../theory/structural-language.md) — B/L/D specification
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Why this works
