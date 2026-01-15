---
status: VALIDATED
layer: application
depends_on:
  - ../../theory/bld-as-language.md
  - ../../mathematics/lie-theory/lie-correspondence.md
used_by:
  - code-generation-cli.md
  - cross-language-compilation.md
---

# BLD Code Generation

> **Status**: Foundational

## Quick Summary (D≈7 Human Traversal)

**BLD code generation in 7 steps:**

1. **Python is a traverser** — Just as GPU traverses algorithm structure to produce cost, Python traverses to produce code
2. **Boundaries map to control flow** — 2 partitions → `if/else`, 3-4 → `match/case`, 5+ → dispatch dict
3. **Links map to dependencies** — `deps=0` → parallel map, `deps=1` → sequential fold, `hierarchy_depth` → tree reduction
4. **Dimensions map to iteration** — Parallel → `asyncio.gather` or `Pool.map`, sequential → `for` loop
5. **Alignment determines quality** — Good structure match produces clean code, mismatch produces awkward code
6. **Alignment scoring** — Score < 2.0 means clean code; higher scores indicate structural mismatch
7. **Cross-language extension** — Same BLD → Python, C, WGSL, Rust with appropriate construct selection

| Component | BLD Mapping |
|-----------|-------------|
| Control flow | B: partition count → if/match/dispatch |
| Data flow | L: deps, pattern → reduce/accumulate/map |
| Iteration style | D: parallel property → Pool.map vs for |
| Code complexity | Alignment score (sum of construct costs) |
| Generated docstring | BLD structure annotation |

---

Generate Python code from BLD algorithm structures by treating Python as a traverser.

---

## The Core Insight

Just as:
```
Algorithm Structure + GPU Traverser → Cost Prediction
```

We can do:
```
Algorithm Structure + Python Structure → Code Generation
```

The "cost" becomes code complexity. Good alignment produces clean code, misalignment produces awkward code.

---

## Python as a BLD Structure

Python has its own BLD primitives:

### Boundaries (B) - Control Flow

| Construct | Partitions | Properties |
|-----------|------------|------------|
| `if/else` | 2 | Binary, not exhaustive |
| `if/elif` | N | Chain, not exhaustive |
| `match/case` | N | Pattern matching, exhaustive with `_` |
| `try/except` | N | Exception types |
| `dispatch_dict` | N | O(1) lookup, cleanest for many cases |

### Links (L) - Dependencies

| Construct | Direction | Properties |
|-----------|-----------|------------|
| Function call | Caller → Callee | Can be async |
| Parameter | Caller → Callee input | Explicit in signature |
| Return | Callee → Caller output | Single value |
| Yield | Generator → Consumer | Lazy evaluation |
| Import | Module → Symbol | One-time cost |

### Dimensions (D) - Iteration

| Construct | Parallelism | Properties |
|-----------|-------------|------------|
| `for` loop | None | Sequential, early exit possible |
| List comprehension | Implicit | Communicates map-like intent |
| `asyncio.gather` | Async | Concurrent I/O |
| `Pool.map` | Process | True parallelism |
| Generator expression | None | Lazy, memory efficient |

---

## Alignment Rules

The generator selects Python constructs by matching algorithm structure:

| Algorithm BLD | Python Construct |
|---------------|------------------|
| `Dimension(parallel=True)` | `asyncio.gather` or `Pool.map` |
| `Dimension(parallel=False)` | `for` loop or comprehension |
| `Boundary(partitions=2)` | `if/else` |
| `Boundary(partitions=3-4)` | `match/case` |
| `Boundary(partitions>4)` | Dispatch dict |
| `Link(hierarchy_depth=N)` | `functools.reduce` or recursion |
| `Link(communication_distances)` | `itertools.accumulate` or manual |

---

## Usage

```python
from experiential_reality.codegen import (
    generate_reduction,
    generate_scan,
    generate_map,
    PYTHON_STANDARD,
    PYTHON_ASYNC,
)

# Generate a reduction function
result = generate_reduction()
print(result.full_code())

# Generate parallel map (uses multiprocessing)
result = generate_map(parallel=True)
print(result.full_code())

# Generate async map (uses asyncio.gather)
result = generate_map(parallel=True, python=PYTHON_ASYNC)
print(result.full_code())
```

---

## Example: Generated Reduction

### Input: BLD Structure

```python
Structure(
    name="reduction",
    dimensions=[
        Dimension("elements", extent="N", properties=["parallel", "contiguous"]),
    ],
    boundaries=[
        Boundary("cardinality", partitions=["empty", "single", "multiple"]),
    ],
    links=[
        Link("combine", from_="element", to="accumulator",
             hierarchy_depth=10, pattern="reduce"),
    ],
)
```

### Output: Generated Python

```python
from functools import reduce
from typing import TypeVar, Callable, Sequence

T = TypeVar("T")

def reduction(
    elements: Sequence[T],
    combine: Callable[[T, T], T],
    identity: T,
) -> T:
    """Generated from BLD Structure: reduction

    Boundaries:
    - cardinality: empty | single | multiple

    Dimensions:
    - elements: parallel, contiguous

    Links:
    - combine: element → accumulator (tree reduction)
    """
    # Boundary: cardinality
    match len(elements):
        case 0:
            return identity
        case 1:
            return elements[0]
        case _:
            # Dimension: elements (parallel, contiguous)
            # Link: combine with hierarchy_depth → tree reduction
            return reduce(combine, elements)
```

### Structure Reflected in Code

- **Boundary** (`cardinality`) → `match` statement with three cases
- **Dimension** (`elements`) → Implicit in `reduce`
- **Link** (`combine`) → `functools.reduce` function call

---

## Example: Generated Scan

### Input: BLD Structure

```python
Structure(
    name="prefix_sum",
    dimensions=[
        Dimension("elements", extent="N", properties=["parallel"]),
    ],
    links=[
        Link("up_sweep", communication_distances=(1, 2, 4, 8, ...)),
        Link("down_sweep", communication_distances=(8, 4, 2, 1)),
    ],
)
```

### Output: Generated Python

```python
from itertools import accumulate
from typing import TypeVar, Callable, Sequence

T = TypeVar("T")

def prefix_sum(
    elements: Sequence[T],
    combine: Callable[[T, T], T],
) -> list[T]:
    """Generated from BLD Structure: prefix_sum"""
    # Link: up_sweep + down_sweep → itertools.accumulate
    return list(accumulate(elements, combine))
```

### Why This Works

The phased `communication_distances` pattern (Blelloch scan) aligns with Python's `itertools.accumulate`, which implements inclusive scan. The generator recognizes this pattern and selects the cleanest implementation.

---

## Alignment Scoring

Each alignment decision has a score (lower is better):

| Decision | Score | Rationale |
|----------|-------|-----------|
| `if/else` for 2 partitions | 0.0 | Perfect match |
| `match/case` for 3-4 partitions | 0.2 | Clean pattern matching |
| Dispatch dict for 5+ partitions | 0.3 | O(1) lookup |
| `if/elif` for 5+ partitions | 1.5 | Gets unwieldy |
| `Pool.map` for parallel | 0.2 | True parallelism |
| `for` loop for sequential | 0.0 | Simple iteration |

The total score indicates code complexity. Score < 2.0 means clean code.

---

## Misalignment Cases

Some algorithm patterns don't align well with Python:

| Pattern | Python Limitation | Generated Code |
|---------|-------------------|----------------|
| Tree reduction | No native tree | `functools.reduce` (sequential) |
| SIMD operations | No native SIMD | Explicit loop or numpy |
| Scatter writes | Lists are sequential | Dict or pre-allocated list |
| GPU parallelism | No GPU support | Falls back to multiprocessing |

The alignment score reflects these misalignments.

---

## BLAS Library: Full Validation

The BLD compiler generates a complete BLAS library from 8 structural specifications.

| Routine | Level | Pattern | Status |
|---------|-------|---------|--------|
| dasum, ddot, dnrm2, idamax | 1 | D reduction | PASS |
| daxpy, dscal | 1 | D parallel | PASS |
| dgemv | 2 | D×D (matrix-vector) | PASS |
| dgemm | 3 | D×D×D (matrix-matrix) | PASS |

**The thesis proven**:
- Structure is traverser-independent
- Same `.bld` file → CPU code (C) AND GPU code (WGSL)
- Both produce identical results (verified against NumPy, <1e-10 error)

*(BLAS library experiments demonstrate this capability.)*

---

## Cross-Language Compilation

This framework extends to cross-language compilation. We validated this by defining Haskell's Prelude as BLD structures and generating working Python:

- 11 Haskell functions → BLD → Python
- 48 tests verify semantic equivalence
- `foldl` vs `foldr` produce different results (correctly!)

See [Cross-Language Compilation](./cross-language-compilation.md) for full details.

---

## See Also

- [CLI and Multi-Target Generation](./code-generation-cli.md) — Unified CLI, WGSL, tests, and meta-validation
- [Cross-Language Compilation](./cross-language-compilation.md) — Haskell → Python via BLD
- [BLD as Universal Language](../../theory/bld-as-language.md) — The theoretical foundation
- [BLD-Driven Development](./bld-driven-development.md) — Design with structure
- [Discovery Method](../../meta/discovery-method.md) — The three questions
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Why BLD works
- [Glossary](../../glossary.md) — Central definitions
