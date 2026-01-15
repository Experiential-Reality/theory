---
status: VALIDATED
layer: application
depends_on:
  - code-generation.md
  - cross-language-compilation.md
used_by:
  - code-generation.md
---

# BLD Code Generation: CLI and Multi-Target

> **Status**: Validated

## Quick Summary (D≈7 Human Traversal)

**BLD CLI and multi-target generation in 7 steps:**

1. **Unified CLI** — `bld compile <file.bld> --target <lang>` generates code; `bld run <file.bld>` executes directly
2. **Pattern detection from Link properties** — `deps=0` → parallel, `deps=1` → sequential, `hierarchy_depth` → tree, `communication_distances` → scan
3. **Multiple targets from same BLD** — Python, Rust, C, WGSL all generated from identical structure specification
4. **WGSL barrier placement** — BLD properties determine where `workgroupBarrier()` calls are needed (deps=0: none, hierarchy_depth=N: N rounds)
5. **Test generation from structure** — BLD properties generate appropriate tests (deps=1 → test for -6, hierarchy_depth → test for 2)
6. **Meta-validation** — BLD describes its own validator, proving general-purpose expressiveness
7. **English as target** — Generate human-readable explanations alongside code

| Component | BLD Mapping |
|-----------|-------------|
| Execution pattern | L: deps, hierarchy_depth, communication_distances |
| Target language | Traverser structure (Python, C, WGSL, Rust) |
| Barrier placement | L: deps=0 → none, deps>0 → sync required |
| Generated tests | L/B properties → semantic assertions |
| Documentation | BLD → English explanation |

---

This document covers the unified CLI, multi-target compilation, and advanced code generation features. For core concepts and Python generation, see [BLD Code Generation](./code-generation.md).

---

## Unified CLI: Write Once, Run Anywhere

BLD structures can be compiled to any target or executed directly via the `bld` command.

### Installation

```bash
pip install -e .
```

### Available Commands

| Command | Description |
|---------|-------------|
| `bld compile <file.bld> --target <lang>` | Generate code for target language |
| `bld run <file.bld> --data <data>` | Execute directly with interpreter |
| `bld list` | List available targets |
| `bld info <file.bld>` | Show structure information |

### Pattern Detection

The backend detects execution patterns from BLD Link properties:

| BLD Property | Pattern | Execution Strategy |
|--------------|---------|-------------------|
| `deps=0` | parallel | Independent operations (map) |
| `deps=1` | sequential | Linear fold |
| `hierarchy_depth=N` | tree | Log(N) reduction |
| `communication_distances=[...]` | scan | Prefix sum |

This is BLD theory in action: **Link properties determine execution strategy**. The `deps` field captures the dependency structure between iterations, which directly maps to parallelism potential.

### Examples

**Compile to Different Targets:**

```bash
# Generate Rust
bld compile map.bld --target rust

# Generate C
bld compile foldl.bld --target c

# Generate WGSL shader
bld compile scanl.bld --target wgsl

# Generate Python
bld compile map.bld --target python
```

**Execute Directly:**

```bash
# Sum: foldl uses deps=1 → sequential fold
$ bld run foldl.bld --data 1,2,3,4,5
Pattern: sequential
Result: [15]

# Prefix sums: scanl uses communication_distances → scan
$ bld run scanl.bld --data 1,2,3,4,5
Pattern: scan
Result: [1, 3, 6, 10, 15]

# Tree reduction: foldr uses hierarchy_depth → tree
$ bld run foldr.bld --data 1,2,3,4,5,6,7,8
Pattern: tree
Result: [36]
```

**Show Structure Info:**

```bash
$ bld info foldr.bld
Structure: foldr
  Pattern: tree
  Dimensions:
    D xs: N [contiguous]
  Boundaries:
    B empty_check: empty | non_empty
  Links:
    L combine: element -> acc (hierarchy_depth=8)
```

### Programmatic API

```python
from experiential_reality.codegen import compile_bld, run_bld

# Compile to target
rust_code = compile_bld("structure map\nL apply: e -> r (deps=0)", "rust")

# Execute directly
result = run_bld("structure foldl\nL combine: a -> a (deps=1)", [1,2,3,4,5])
# result == [15]
```

### Available Backends

| Backend | Description |
|---------|-------------|
| `python` | Python with alignment-selected constructs |
| `rust` | Rust with iterator patterns |
| `c` | C with appropriate loops |
| `wgsl` | WebGPU shaders with barrier placement |
| `interpret` | Direct execution in Python |

---

## Test Generation

BLD structures also generate their own tests. The structure properties determine what to test:

| BLD Property | Generated Test |
|--------------|----------------|
| `deps=0` | Order independence |
| `deps=1` | Sequential dependency (`-6` for foldl) |
| `hierarchy_depth` | Tree structure (`2` for foldr) |
| `communication_distances` | Prefix sum pattern |

See [Test Generation from BLD](./cross-language-targets.md#test-generation-from-bld) for details.

---

## WGSL Generation

WGSL (WebGPU Shading Language) is now a supported target. The key insight: **BLD properties determine barrier placement**.

### WGSL as a BLD Structure

| Primitive | WGSL Construct | Properties |
|-----------|----------------|------------|
| **D** (Dimension) | `global_invocation_id` | Massive parallelism (thousands) |
| **D** (Dimension) | `local_invocation_id` | Within-workgroup parallelism |
| **B** (Boundary) | `if (id >= N) { return; }` | Guard clauses |
| **L** (Link, deps=0) | Independent loads/stores | No barriers needed |
| **L** (Link, deps=1) | `workgroupBarrier()` | Synchronization required |
| **L** (Link, tree) | Log(N) barrier rounds | Tree reduction pattern |

### BLD to Barrier Mapping

| BLD Property | WGSL Behavior | Why |
|--------------|---------------|-----|
| `deps=0` | No barriers | Each thread independent |
| `hierarchy_depth=N` | N barrier rounds | Tree reduction |
| `communication_distances` | 2xlog(N) barriers | Blelloch scan |

### Usage

```python
from experiential_reality.codegen import (
    generate_wgsl_map,        # No barriers
    generate_wgsl_reduction,  # Tree barriers
    generate_wgsl_scan,       # Phased barriers
    generate_wgsl_from_bld,   # From any BLD
    analyze_wgsl_barriers,    # Barrier analysis
)

# Generate from BLD - barriers determined by properties
wgsl = generate_wgsl_from_bld(MAP_BLD)    # No barriers
wgsl = generate_wgsl_from_bld(FOLDR_BLD)  # Has barriers
```

See [WGSL Generation](./cross-language-targets.md#wgsl-generation-gpu-shaders-from-bld) for full details.

---

## English Generation

Human language is also a BLD target. The `explain.py` module "compiles" BLD to natural language:

```python
from experiential_reality.codegen import (
    explain_wgsl_generation,   # Why WGSL needs barriers
    explain_python_vs_wgsl,    # Cross-language comparison
    explain_cross_language,    # Unified explanation
    explain_from_haskell_bld,  # Haskell function explanation
)

# Explain why foldr uses barriers on GPU
print(explain_wgsl_generation(FOLDR_BLD))

# Compare implementations across languages
print(explain_cross_language(FOLDL_BLD))
```

---

## Meta-Validation: BLD Describes Its Own Validator

The GPU validation framework is now generated from BLD, proving that BLD is expressive enough for general-purpose programming — not just GPU cost prediction.

### Validation Pipeline as BLD

| Stage | Dimensions | Boundaries | Links |
|-------|------------|------------|-------|
| Load Calibration | — | calibration_match | read_json, parse_traverser |
| Enumerate GPUs | adapters (N) | gpu_filter (5 partitions) | enumerate, filter |
| Run Validation | kernels (3, seq), sizes (N, par) | kernel_type, pass_fail | benchmark, predict, compute_error |
| Aggregate Results | results (N) | — | count_ok, sum_error (reduce) |

### BLD Structure Definition

```python
RUN_VALIDATION = Structure(
    name="run_validation",
    dimensions=[
        Dimension("kernels", extent=3, properties=[]),  # Sequential
        Dimension("sizes", extent="N", properties=["parallel"]),
    ],
    boundaries=[
        Boundary("kernel_type", ["reduction", "scan", "conv2d"]),
        Boundary("pass_fail", ["pass", "fail"], "abs(error) < 20"),
    ],
    links=[
        Link("benchmark", from_="(device, size)", to="actual_ms"),
        Link("predict", from_="(structure, traverser)", to="predicted_ms"),
        Link("compute_error", from_="(predicted, actual)", to="error_pct", ops=3),
    ],
)
```

### Generated Code

- **BLD Source**: `model/validation_structure.py` (BLD structures)
- **Generator**: `codegen/generate_validation.py`
- **Output**: `scripts/validate_bld_generated.py` (423 lines)
- **Generation**: `uv run python scripts/generate_validate_bld.py`

### Verification

Both validators produce equivalent results:

| Version | Pass Rate | Avg Error | Lines |
|---------|-----------|-----------|-------|
| Hand-written | 6/6 | 5.0% | 347 |
| Generated | 6/6 | 5.6% | 423 |

The generated version is 76 lines longer due to BLD documentation in comments — the structure is explicitly annotated.

### Why This Matters

If BLD can describe its own validator:
1. **General purpose**: BLD is not limited to algorithms — it describes tools too
2. **Self-documenting**: Generated code shows its BLD origins
3. **Maintainable**: Change BLD, regenerate code
4. **Verifiable**: BLD structure can be validated before generation

This is meta-validation: using BLD to validate BLD.

---

## Future Extensions

1. **Generate Rust code** - Different L structure (ownership)
2. **Generate SQL queries** - Treat SQL as a traverser
3. **Multi-target generation** - Same algorithm → multiple implementations
4. **WGSL validation** - Integrate with naga or tint for shader validation

The framework is extensible: define a new language's BLD structure, implement alignment rules, generate code.

---

## See Also

- [BLD Code Generation](./code-generation.md) — Core concepts and Python generation
- [Cross-Language Compilation](./cross-language-compilation.md) — Haskell → Python via BLD
- [BLD as Universal Language](../../theory/bld-as-language.md) — The theoretical foundation
- [BLD-Driven Development](./bld-driven-development.md) — Design with structure
- [Discovery Method](../../meta/discovery-method.md) — The three questions
- [Glossary](../../glossary.md) — Central definitions
