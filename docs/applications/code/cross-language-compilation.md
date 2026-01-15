---
status: VALIDATED
layer: application
depends_on:
  - ../../theory/bld-as-language.md
  - ../../mathematics/lie-theory/lie-correspondence.md
used_by:
  - cross-language-targets.md
---

# Cross-Language Compilation

> **Status**: Validated

## Quick Summary (D≈7 Human Traversal)

**Cross-language compilation via BLD in 7 steps:**

1. **Traditional transpilers fail** — Syntax-to-syntax translation loses semantic meaning; `foldl` vs `foldr` distinctions get blurred
2. **BLD captures structure** — Translate meaning (what computation does) not spelling (how it looks)
3. **Link properties encode dependencies** — `deps=0` means parallel, `deps=1` means sequential, `hierarchy_depth` means tree structure
4. **Boundaries partition behavior** — Empty vs non-empty, predicate passes vs fails
5. **Dimensions specify repetition** — The axis over which computation repeats (list elements, etc.)
6. **Generate any target** — Same BLD structure produces Python, C, WGSL with preserved semantics
7. **Validation through tests** — `foldl(-, 0, [1,2,3]) = -6` vs `foldr(-, 0, [1,2,3]) = 2` proves semantic preservation

| Component | BLD Mapping |
|-----------|-------------|
| Source semantics | BLD Structure (D, L, B properties) |
| Dependency pattern | L: deps, hierarchy_depth, communication_distances |
| Case handling | B: partitions (empty, non_empty, etc.) |
| Iteration axis | D: extent, parallel property |
| Target code | BLD → language-specific constructs |

---

BLD serves as a universal intermediate language for cross-language compilation. We validated this by defining Haskell's Prelude as BLD structures and generating working implementations across multiple target languages.

---

## Summary

| Finding | Status | Evidence |
|---------|--------|----------|
| BLD captures language-independent semantics | Validated | 11 functions translated |
| Generated Python matches source semantics | Validated | 48/48 tests pass |
| Semantic distinctions preserved | Validated | `foldr` vs `foldl` produce different results |
| Parallelism automatically detected | Validated | `deps=0` identifies independent operations |

For C, WGSL, and test generation targets, see [Cross-Language Targets](./cross-language-targets.md).

---

## The Insight: Structure IS the Translation

Traditional transpilers translate **syntax to syntax**:

```
Haskell source → Parser → AST → Transformer → Python AST → Printer → Python
```

BLD compilation translates **structure to structure**:

```
Haskell semantics → BLD Structure → Python BLD → Python code
     (meaning)        (universal)     (target)     (syntax)
```

The BLD structure captures *what the computation does*, not how it's spelled. This enables semantic preservation that syntax-based approaches cannot guarantee.

---

## The Haskell Prelude Experiment

We selected Haskell's Prelude as test case because:

1. **Well-understood semantics** - Functions have precise mathematical definitions
2. **Semantic distinctions matter** - `foldl` and `foldr` behave differently
3. **Parallelism properties vary** - Some functions are parallel, others sequential
4. **Small but complete** - 11 functions cover the fundamental patterns

### Functions Translated

| Function | Haskell Type | BLD Key Properties |
|----------|--------------|-------------------|
| `map` | `(a -> b) -> [a] -> [b]` | D: parallel, L: deps=0 |
| `filter` | `(a -> Bool) -> [a] -> [a]` | B: predicate boundary |
| `foldl` | `(b -> a -> b) -> b -> [a] -> b` | L: deps=1 (sequential) |
| `foldr` | `(a -> b -> b) -> b -> [a] -> b` | L: hierarchy_depth (tree) |
| `zip` | `[a] -> [b] -> [(a, b)]` | D: two parallel lists |
| `zipWith` | `(a -> b -> c) -> [a] -> [b] -> [c]` | L: deps=0, B: either_empty |
| `take` | `Int -> [a] -> [a]` | B: count_check |
| `takeWhile` | `(a -> Bool) -> [a] -> [a]` | B: predicate (stops entirely) |
| `scanl` | `(b -> a -> b) -> b -> [a] -> [b]` | L: communication_distances |
| `concat` | `[[a]] -> [a]` | L: flatten pattern |
| `concatMap` | `(a -> [b]) -> [a] -> [b]` | L: apply + flatten |

---

## BLD Structure Examples

### map: Parallel, Independent Operations

**Haskell:**
```haskell
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs
```

**BLD:**
```python
MAP_BLD = Structure(
    name="map",
    dimensions=[
        Dimension(name="xs", extent="N", properties=["parallel", "contiguous"]),
    ],
    boundaries=[
        Boundary(name="empty_check", partitions=["empty", "non_empty"]),
    ],
    links=[
        Link(name="apply_f", from_="element", to="result", deps=0),
    ],
)
```

**Key insight:** `deps=0` means each application is independent. This is why `map` is parallelizable.

**Generated Python:**
```python
def map_(f: Callable[[A], B], xs: Iterable[A]) -> Iterator[B]:
    """Generated from Haskell Prelude."""
    # Dimension: xs is parallel -> can use generator (lazy map)
    # Link: apply_f has deps=0 -> each application is independent
    for x in xs:
        yield f(x)
```

---

### foldl vs foldr: Sequential vs Tree Structure

This is the critical test. `foldl` and `foldr` have different **structure**, not just different syntax:

**BLD for foldl:**
```python
FOLDL_BLD = Structure(
    name="foldl",
    dimensions=[
        Dimension(name="xs", extent="N", properties=["contiguous"]),  # NOT parallel
    ],
    links=[
        Link(name="combine", from_="accumulator", to="accumulator",
             deps=1, pattern="reduce"),  # deps=1: each step depends on previous
    ],
)
```

**BLD for foldr:**
```python
FOLDR_BLD = Structure(
    name="foldr",
    dimensions=[
        Dimension(name="xs", extent="N", properties=["contiguous"]),
    ],
    links=[
        Link(name="combine", from_="element", to="accumulator",
             hierarchy_depth=10, pattern="reduce"),  # Tree structure
    ],
)
```

**The difference:** `deps=1` forces left-to-right evaluation. `hierarchy_depth` indicates right-associative tree structure.

**Semantic validation:**
```python
# Haskell:
# foldl (-) 0 [1,2,3] = ((0-1)-2)-3 = -6
# foldr (-) 0 [1,2,3] = 1-(2-(3-0)) = 2

# Our generated Python produces:
foldl(lambda acc, x: acc - x, 0, [1, 2, 3])  # Returns -6
foldr(lambda x, acc: x - acc, 0, [1, 2, 3])  # Returns 2
```

The different results prove BLD captured the **structural** difference, not just syntactic difference.

---

### scanl: Communication Distances

**BLD:**
```python
SCANL_BLD = Structure(
    name="scanl",
    links=[
        Link(name="accumulate", from_="element", to="running_total",
             communication_distances=(1,)),  # Each depends on previous
    ],
)
```

The `communication_distances=(1,)` captures the prefix-sum pattern: element N depends on element N-1.

**Generated Python:**
```python
def scanl(f: Callable[[B, A], B], z: B, xs: Iterable[A]) -> Iterator[B]:
    yield z  # Always yield initial value
    acc = z
    for x in xs:
        acc = f(acc, x)
        yield acc
```

---

## Why This Works

### BLD Captures Computation, Not Syntax

Haskell's syntax (pattern matching, recursion) differs from Python's (iteration, generators). But both express the same **computational structure**:

| Concept | Haskell Syntax | Python Syntax | BLD Structure |
|---------|----------------|---------------|---------------|
| Independence | Implicit in recursion | `for` loop | `deps=0` |
| Sequence | Left fold | `acc = f(acc, x)` | `deps=1` |
| Tree | Right fold | `reversed()` | `hierarchy_depth` |
| Boundary | Pattern match | `if/else` | `Boundary(partitions=[...])` |

The BLD is the **invariant** across syntactic representations.

### Lie Theory Connection

This works because BLD captures the Lie-algebraic structure of computation:

| BLD | Lie Component | What It Means |
|-----|---------------|---------------|
| D (Dimension) | Generators | Axes of transformation |
| L (Link) | Structure constants | How transformations interact |
| B (Boundary) | Topology | What's connected/separated |

Any computation has these three aspects. BLD makes them explicit, enabling translation between any pair of languages that can express them.

---

## Implications

### 1. Library Portability

Define a library's semantics as BLD once, generate implementations for any language:

```
Standard Library BLD -> Python + JavaScript + Rust + ...
```

### 2. Automatic Parallelism Detection

`deps=0` in BLD identifies parallelizable operations automatically:

```python
# BLD analysis reveals:
map:    deps=0 -> parallel-safe
filter: deps=0 -> parallel-safe (but order matters for output)
foldl:  deps=1 -> sequential only
foldr:  deps>0 -> sequential (or tree-parallel)
```

### 3. Verified Transpilation

Because BLD captures semantics, transpilation correctness can be tested:

```python
# If Haskell BLD -> Python passes all semantic tests,
# the transpilation preserves meaning
assert foldl_python(f, z, xs) == foldl_haskell(f, z, xs)
```

### 4. Language Design Analysis

Languages are BLD traversers. Comparing BLDs reveals what a language is good at:

| Language | D Strength | L Strength | B Strength |
|----------|------------|------------|------------|
| Haskell | Lazy lists | Pattern matching | Types |
| Python | Generators | Duck typing | Dynamic |
| Rust | Iterators | Ownership | Types |

---

## See Also

- [Cross-Language Targets](./cross-language-targets.md) — C, WGSL generation and validation
- [BLD as Universal Language](../../theory/bld-as-language.md) — The theoretical foundation
- [Code Generation](./code-generation.md) — Python generation framework
- [Human Language Structure](../../theory/human-language-structure.md) — BLD -> Explanation
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Why BLD works
- [Glossary](../../glossary.md) — Central definitions
