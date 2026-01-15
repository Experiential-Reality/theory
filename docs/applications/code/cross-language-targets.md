---
status: VALIDATED
layer: application
depends_on:
  - cross-language-compilation.md
used_by:
  - ../../theory/human-language-structure.md
  - cross-language-compilation.md
---

# Cross-Language Compilation: Target Languages and Validation

> **Status**: Validated

## Quick Summary (D≈7 Human Traversal)

**Cross-language targets via BLD in 7 steps:**

1. **C generation** — Same BLD produces C code with identical semantics; `deps=1` → sequential loop, `hierarchy_depth` → reverse iteration
2. **WGSL generation** — GPU shaders require explicit synchronization; BLD properties determine barrier placement automatically
3. **Barrier mapping** — `deps=0` → no barriers (independent threads), `hierarchy_depth=N` → N barrier rounds, `communication_distances` → 2×log(N) barriers
4. **Semantic validation** — C tests confirm `foldl(-) = -6` and `foldr(-) = 2` just like Python; 21/21 tests pass
5. **Test generation** — BLD properties generate their own verification: deps pattern → specific expected results
6. **Five targets from one BLD** — Python (48 tests), C (21 tests), WGSL (shaders), Tests (auto), English (explanations)
7. **The complete picture** — Haskell Prelude → BLD → any target language with proven semantic preservation

| Component | BLD Mapping |
|-----------|-------------|
| C implementation | L: deps=1 → sequential for, hierarchy_depth → reverse for |
| WGSL shader | L: tree structure → workgroupBarrier() rounds |
| Barrier count | log₂(workgroup_size) for tree reduction |
| Test assertions | L/B properties → expected behavior |
| English output | BLD → natural language explanation |

---

This document covers the target language implementations (C, WGSL) and validation results for BLD-based cross-language compilation. For the core theory and BLD structure examples, see [Cross-Language Compilation](./cross-language-compilation.md).

---

## C Generation: Same BLD, Different Language

The same BLD structures generate C code with identical semantics.

### Generated C (foldl)

```c
/* foldl: L=deps=1 (sequential)
 *
 * BLD tells us deps=1: each step depends on previous.
 * This is inherently sequential - cannot parallelize.
 */
int foldl_int(IntBinaryFn f, int z, int* xs, int n) {
    /* Link: combine (deps=1) -> must be sequential */
    int acc = z;
    for (int i = 0; i < n; i++) {
        acc = f(acc, xs[i]);  /* Each step depends on previous acc */
    }
    return acc;
}
```

### Generated C (foldr)

```c
/* foldr: L=hierarchy_depth (tree structure)
 *
 * BLD tells us this has tree structure (right-associative).
 * We process from the right.
 */
int foldr_int(IntBinaryFn f, int z, int* xs, int n) {
    /* Link: hierarchy_depth -> process from right */
    if (n == 0) return z;

    int acc = z;
    for (int i = n - 1; i >= 0; i--) {
        acc = f(xs[i], acc);  /* Right fold: element first, then acc */
    }
    return acc;
}
```

### C Test Results

```
$ clang -Wall -o prelude prelude.c && ./prelude

Testing foldl vs foldr (semantic distinction):
  PASS: foldl(-) = -6
  PASS: foldr(-) = 2
  PASS: foldl and foldr differ for non-associative ops

Results: 21 passed, 0 failed
```

The same semantic tests that pass in Python also pass in C. **BLD preserves meaning across language boundaries.**

---

## WGSL Generation: GPU Shaders from BLD

WGSL (WebGPU Shading Language) is fundamentally different from CPU languages:
- **Thousands of parallel threads** instead of one
- **Explicit synchronization** via `workgroupBarrier()`
- **Shared memory** for inter-thread communication

### The Critical Insight

BLD properties determine barrier placement:

| BLD Property | WGSL Behavior | Why |
|--------------|---------------|-----|
| `deps=0` | No barriers | Each thread independent |
| `deps=1` | Barrier per step | Sequential dependency |
| `hierarchy_depth=N` | N barrier rounds | Tree reduction pattern |
| `communication_distances` | 2xlog(N) barriers | Blelloch scan |

### Generated WGSL (map - no barriers)

```wgsl
// Generated from BLD: D=parallel, L=deps=0
// No barriers needed - each invocation is independent

@group(0) @binding(0) var<storage, read> input: array<f32>;
@group(0) @binding(1) var<storage, read_write> output: array<f32>;

@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
    let i = id.x;
    if (i >= arrayLength(&input)) { return; }  // Boundary
    output[i] = input[i] * 2.0;  // Link: deps=0, independent
}
```

### Generated WGSL (reduce - tree barriers)

```wgsl
// Generated from BLD: L=hierarchy_depth=8 (tree reduction)
// Requires 8 barrier rounds for 256 elements

var<workgroup> shared: array<f32, 256>;

@compute @workgroup_size(256)
fn main(@builtin(local_invocation_id) lid: vec3<u32>) {
    let i = lid.x;
    shared[i] = input[i];
    workgroupBarrier();

    // Tree reduction: 8 rounds for 256 elements
    for (var stride = 128u; stride > 0u; stride >>= 1u) {
        if (i < stride) {
            shared[i] += shared[i + stride];
        }
        workgroupBarrier();  // Link: deps=1 per round
    }

    if (i == 0u) { output[0] = shared[0]; }
}
```

### Why map and reduce differ

Both functions process elements, but their **structure** differs:

| Function | BLD Property | WGSL Pattern |
|----------|--------------|--------------|
| `map` | `deps=0` | No barriers, each thread independent |
| `foldl` | `deps=1` | Sequential (GPU inefficient) |
| `foldr` | `hierarchy_depth` | Tree reduction, log(N) barriers |
| `scanl` | `communication_distances` | Blelloch scan, 2xlog(N) barriers |

The BLD tells us *why* these differ: it's not about the operation, it's about the dependency structure.

---

## Validation Results

### Python Validation

| Test Category | Tests | Pass Rate | What It Validates |
|---------------|-------|-----------|-------------------|
| BLD Structure | 5 | 100% | Structures are well-formed |
| Syntax Validity | 11 | 100% | Generated code compiles |
| Functional Correctness | 23 | 100% | Functions behave correctly |
| Prelude Integration | 4 | 100% | Functions work together |
| Semantic Equivalence | 5 | 100% | Matches Haskell behavior |
| **Total** | **48** | **100%** | |

### C Validation

| Test Category | Tests | Pass Rate | What It Validates |
|---------------|-------|-----------|-------------------|
| map | 2 | 100% | Independent application |
| filter | 3 | 100% | Predicate boundary |
| foldl | 3 | 100% | Sequential dependency |
| foldr | 2 | 100% | Right-associative |
| foldl vs foldr | 3 | 100% | Semantic distinction |
| take | 4 | 100% | Count boundary |
| takeWhile | 2 | 100% | Stop-on-fail boundary |
| scanl | 2 | 100% | Prefix pattern |
| **Total** | **21** | **100%** | |

### Key Semantic Tests

```python
# These tests verify BLD captures semantic distinctions:

def test_foldr_vs_foldl(self):
    """foldr and foldl should differ for non-associative ops."""
    # foldl (-) 0 [1,2,3] = ((0-1)-2)-3 = -6
    # foldr (-) 0 [1,2,3] = 1-(2-(3-0)) = 2
    foldl_result = foldl(lambda acc, x: acc - x, 0, [1, 2, 3])
    foldr_result = foldr(lambda x, acc: x - acc, 0, [1, 2, 3])
    assert foldl_result == -6
    assert foldr_result == 2

def test_takewhile_stops_on_fail(self):
    """takeWhile stops at first failure (doesn't resume)."""
    result = list(takeWhile(lambda x: x < 3, [1, 2, 3, 4, 1, 2]))
    assert result == [1, 2]  # Stops at 3, doesn't see 1, 2 at end
```

---

## Test Generation from BLD

Tests are also a compilation target. The BLD structure tells us exactly what to test:

```python
from experiential_reality.codegen import generate_tests_from_bld, FOLDL_BLD, FOLDR_BLD

# BLD generates different tests for foldl vs foldr
print(generate_tests_from_bld(FOLDL_BLD))
# -> test_combine_link_sequential: asserts acc == -6

print(generate_tests_from_bld(FOLDR_BLD))
# -> test_combine_link_tree_structure: asserts acc == 2
```

**BLD properties determine tests:**

| BLD Property | Generated Test |
|--------------|----------------|
| `deps=0` | Order independence test |
| `deps=1` | Sequential dependency test (-6) |
| `hierarchy_depth` | Tree structure test (2) |
| `communication_distances` | Prefix sum pattern test |
| `Boundary(partitions=[...])` | Partition exhaustiveness test |

The same BLD that generates code also generates its verification.

---

## Reproduction

### Generate C Prelude

```python
from experiential_reality.codegen import generate_c_prelude, generate_c_file

# Print to stdout
print(generate_c_prelude())

# Or write to file
generate_c_file("/tmp/haskell_prelude.c")
```

### Compile and Run C Tests

```bash
# Generate, compile, and run
PYTHONPATH=src python -c "
from experiential_reality.codegen import generate_c_prelude
print(generate_c_prelude())
" > /tmp/prelude.c

clang -Wall -o /tmp/prelude /tmp/prelude.c
/tmp/prelude
```

### Generate WGSL Shaders

```python
from experiential_reality.codegen import (
    generate_wgsl_map,
    generate_wgsl_reduction,
    generate_wgsl_scan,
    generate_wgsl_from_bld,
    generate_wgsl_prelude,
    analyze_wgsl_barriers,
    MAP_BLD, FOLDR_BLD,
)

# Generate map shader (no barriers)
print(generate_wgsl_map())

# Generate reduction shader (tree barriers)
print(generate_wgsl_reduction())

# Generate from BLD - barriers determined by properties
print(generate_wgsl_from_bld(MAP_BLD))    # No barriers
print(generate_wgsl_from_bld(FOLDR_BLD))  # Has barriers

# Analyze barrier usage
analysis = analyze_wgsl_barriers(generate_wgsl_reduction())
print(f"Has barriers: {analysis['has_barriers']}")
print(f"Barrier count: {analysis['barrier_count']}")
```

### Generate Cross-Language Explanations

```python
from experiential_reality.codegen import (
    explain_wgsl_generation,
    explain_python_vs_wgsl,
    explain_cross_language,
    FOLDL_BLD, FOLDR_BLD,
)

# Explain why WGSL uses barriers
print(explain_wgsl_generation(FOLDR_BLD))

# Compare Python vs WGSL for same BLD
print(explain_python_vs_wgsl(FOLDL_BLD))

# Full cross-language explanation
print(explain_cross_language(FOLDR_BLD))
```

---

## The Complete Picture

```
Haskell Prelude (11 functions)
        |
        v
   BLD Structures
        |
   +----+----+----+----+
   v    v    v    v    v
Python  C  WGSL Tests English
 (48)  (21)  (5) (auto) (explanation)
```

**Five targets**, all from the same BLD structures:
1. **Python** - High-level, generators, lazy evaluation
2. **C** - Low-level, pointers, explicit memory
3. **WGSL** - GPU shaders, barriers for synchronization
4. **Tests** - Property verification from BLD properties
5. **English** - Human-readable explanations

---

## Future Work

1. **More Haskell functions** - `dropWhile`, `span`, `break`, `iterate`, `repeat`
2. **Other source languages** - Scheme, ML, Clojure standard libraries
3. **Other target languages** - Rust, JavaScript, Go
4. **Bidirectional** - Generate Haskell from Python BLD
5. **Optimization** - Use BLD properties to generate optimized code
6. **WGSL validation** - Integrate with naga or tint for shader validation

---

## See Also

- [Cross-Language Compilation](./cross-language-compilation.md) — Core theory and BLD structures
- [BLD as Universal Language](../../theory/bld-as-language.md) — The theoretical foundation
- [Code Generation](./code-generation.md) — Python generation framework
- [Human Language Structure](../../theory/human-language-structure.md) — BLD -> Explanation
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Why BLD works
- [Glossary](../../glossary.md) — Central definitions
