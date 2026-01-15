---
status: VALIDATED
layer: application
depends_on:
  - ../../theory/bld-as-language.md
  - ../../meta/discovery-method.md
used_by: []
---

# BLD for Code

> **Status**: Validated (117 tests across Python, C, WGSL)

BLD applied to software: from refactoring legacy code to generating new code to compiling across languages.

---

## The Insight

Code has structure. BLD makes it explicit.

```
Hidden structure → bugs, complexity, friction
Explicit structure → readable, testable, fast
```

The same three primitives that predict GPU performance also explain why some code is easy to work with and other code fights you at every turn.

---

## Documents

| Document | What It Covers | Key Insight |
|----------|----------------|-------------|
| [Refactoring](./refactoring.md) | Making implicit state explicit | Scattered if/elif = hidden B, cycles = hidden L |
| [BLD-Driven Development](./bld-driven-development.md) | Design with structure from the start | Find B/L/D *before* writing code |
| [Code Generation](./code-generation.md) | Generate code from BLD structures | Python as a traverser, CLI tools |
| [Cross-Language Compilation](./cross-language-compilation.md) | Haskell → Python/C/WGSL via BLD | Same semantics, different syntax |

---

## Validation Summary

| Target | Tests | Status |
|--------|-------|--------|
| Python (Haskell Prelude) | 48 | 100% pass |
| C (Haskell Prelude) | 21 | 100% pass |
| WGSL (GPU shaders) | 38 | Barrier placement validated |
| Meta-validation (BLD validator) | 6/6 | 5.6% avg error |

**Total: 117 tests validating cross-language semantic preservation.**

---

## Quick Reference

### Refactoring Patterns → BLD

| Code Smell | Hidden Primitive | Fix |
|------------|------------------|-----|
| Scattered if/elif on same value | Boundary | Extract to dispatch dict |
| Same check in N places | Dimension | Enumerate in enum/config |
| Circular dependencies | Link | Break into DAG |
| Type checking inside loops | Boundary inside Dimension | Separate collections or use polymorphism |

### BLD Properties → Code Constructs

| BLD Property | Python | C | WGSL |
|--------------|--------|---|------|
| `deps=0` | `map()`, comprehension | independent loop | No barriers |
| `deps=1` | `reduce()`, accumulator | sequential loop | Barrier per step |
| `hierarchy_depth=N` | `functools.reduce` | reversed loop | N barrier rounds |
| `Boundary(N)` | `match/case`, dispatch dict | `switch` | Guard clause |

### CLI Commands

```bash
bld compile map.bld --target rust    # Generate Rust
bld run foldl.bld --data 1,2,3,4,5   # Execute directly
bld info foldr.bld                    # Show structure
bld list                              # Available targets
```

---

## The Core Claim

**Code structure should mirror domain structure.**

When they align:
- Code is readable (humans see structure)
- Code is testable (boundaries partition test cases)
- Code is fast (compilers optimize explicit structure)
- Code is parallelizable (explicit DAGs reveal independence)

When they misalign:
- You fight the code
- Bugs hide in implicit state
- Performance surprises you
- Refactoring feels endless

BLD gives you the vocabulary to see the alignment—or lack of it.

---

## See Also

- [BLD as Universal Language](../../theory/bld-as-language.md) — Code is just one target
- [Discovery Method](../../meta/discovery-method.md) — The three questions
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Why this works
