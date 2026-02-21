---
status: VALIDATED
layer: application
depends_on:
  - ../../theory/structural-language.md
  - ../ml/performance-theorem.md
used_by:
  - gpu-calibration.md
---

# Engine Temporal Scope

> **Status**: Validated

> **When hardware engines overlap, costs combine as max() not sum().**

## Summary

**When hardware engines overlap, costs combine as max() not sum():**

1. GPU has multiple engines (memory, compute, copy) operating in parallel — naive sum overpredicts 2x — [Engine Temporal Scope](#1-engine-temporal-scope)
2. When engines overlap: use max() not sum() for cost aggregation — [Engine Temporal Scope](#1-engine-temporal-scope)
3. Overlap efficiency (0.22 on Intel Xe): resource contention when engines compete — [Sustained Compute Rate](#2-sustained-compute-rate-via-overlap-efficiency)
4. Sqrt cache efficiency models tiled access: √(L2_size/working_set) — [Sqrt Cache Efficiency](#3-sqrt-cache-efficiency)
5. Together achieves <20% prediction error on GEMM (256×256 to 4096×4096) — [Validation Results](#validation-results)

| Component | BLD | Description |
|-----------|-----|-------------|
| Cache boundary | B | Topological threshold at L2 size |
| Memory/compute rates | L | Geometric coupling — ns_per_access |
| Engine overlap efficiency | L | Scaling factor for parallel execution |
| Block count / workgroups | D | Repetition — multiplies link costs |

This document describes three interrelated concepts that emerged from achieving accurate GEMM predictions:

1. **Engine Temporal Scope** - Links belong to hardware engines that can execute in parallel
2. **Sustained Compute Rate** - Realistic throughput when engines compete for resources
3. **Sqrt Cache Efficiency** - Non-linear model for cache hit rates in tiled access patterns

---

## 1. Engine Temporal Scope

### The Problem: Overlapping Engines

GPU hardware has multiple execution engines:
- **Memory Engine** - handles global/shared memory loads and stores
- **Compute Engine** - executes arithmetic operations
- **Copy Engine** - handles async memory transfers

Naive cost models sum all costs:
```
total = memory_cost + compute_cost  # WRONG for overlapping engines
```

This overpredicts by 2x when both engines are busy simultaneously (double buffering, compute hiding latency).

### The Solution

Add an `engine` field to TraverserLink to classify each link by hardware engine:

```python
@dataclass(frozen=True)
class TraverserLink:
    name: str
    from_: str
    to: str
    pattern: str = "coalesced"
    engine: str = "memory"  # Which hardware engine: "memory", "compute", "copy"
    ns_per_access: float = 0.0
```

Add `engine_overlap` to Traverser to declare which engines can execute in parallel and at what efficiency:

```python
@dataclass
class Traverser:
    name: str
    # ...
    engine_overlap: list[tuple[str, str, float]] = field(default_factory=list)
    # e.g., [("memory", "compute", 0.22)] means:
    # - memory and compute can overlap
    # - compute runs at 22% efficiency when overlapping (4.5x slowdown)
```

The efficiency factor captures resource contention—when engines compete for register ports, instruction bandwidth, or cache, throughput drops.

### Cost Aggregation

When engines overlap, use `max()` instead of `sum()`:

```python
# Group costs by engine
engine_costs = {"memory": 15.0, "compute": 8.0}

# Check for overlapping engines
if traverser.engines_can_overlap("memory", "compute"):
    # Overlapping: max(15, 8) = 15ms
    total = max(engine_costs["memory"], engine_costs["compute"])
else:
    # Non-overlapping: 15 + 8 = 23ms
    total = engine_costs["memory"] + engine_costs["compute"]
```

---

## 2. Sustained Compute Rate (via Overlap Efficiency)

### The Problem: Resource Contention

When memory and compute engines overlap, they compete for shared resources:
- Register file ports
- Instruction issue bandwidth
- Power budget

The "independent" compute rate (theoretical peak) is unrealistic during overlap.

### Measured Rates on Intel Xe (TGL GT2)

| Rate Type | ns/op | GFLOPS | Context |
|-----------|-------|--------|---------|
| compute_independent | 0.00207 | ~484 | Compute-only benchmark |
| compute_serial | 0.0207 | ~48 | Serial dependency chain |

The sustained rate (~0.0095 ns/op, ~105 GFLOPS) is **derived** from overlap efficiency, not stored separately.

### Implementation

The efficiency factor in `engine_overlap` captures this directly:

```python
engine_overlap = [("memory", "compute", 0.22)]  # 22% efficiency when overlapping

if has_memory_compute_overlap:
    efficiency = traverser.get_overlap_efficiency("memory", "compute")
    if efficiency < 1.0:
        # slowdown = 1/efficiency (e.g., 0.22 → 4.5x slowdown)
        engine_costs["compute"] /= efficiency
```

### Why This Works

The efficiency factor directly expresses resource contention:
- `1.0`: Full parallelism (no contention, dedicated resources)
- `0.22`: 22% efficiency (integrated GPU sharing bandwidth/cache)
- Near `0.0`: Engines can't effectively overlap

Different hardware has different efficiencies:
- High-end discrete GPU: efficiency closer to 1.0
- Integrated GPU: efficiency of 0.2-0.3

This unifies the old "sustained rate" link with the engine overlap model—one concept instead of two.

---

## 3. Sqrt Cache Efficiency

### The Problem: Cache Miss Prediction

For algorithms with working sets larger than L2 cache, we need to model cache efficiency. Linear models are too pessimistic:

```python
# Linear model (too pessimistic)
cache_efficiency = min(1.0, l2_cache_bytes / working_set_bytes)
# At 2x cache: 50% hit rate - but reality is higher
```

### The Insight

Tiled access patterns (like GEMM) have spatial locality. Even when the total working set exceeds cache, tiles are accessed sequentially with high temporal locality. Cache hit rates follow diminishing returns, not linear decay.

### Sqrt Model

```python
import math

cache_ratio = l2_cache_bytes / working_set_bytes
cache_efficiency = min(1.0, math.sqrt(cache_ratio))

# Effective traffic: blend unique data with raw traffic
effective_reads = unique_data + (raw_traffic - unique_data) * (1 - cache_efficiency)
```

| Working Set / L2 | Linear Efficiency | Sqrt Efficiency |
|------------------|-------------------|-----------------|
| 0.5x (fits) | 100% | 100% |
| 2x | 50% | 71% |
| 4x | 25% | 50% |
| 10x | 10% | 32% |

The sqrt model better matches observed behavior in GEMM benchmarks.

### When to Use

- **Sqrt model**: Tiled algorithms with sequential access to tiles (GEMM, convolution)
- **Linear model**: Random access patterns (hash tables, graph traversal)
- **No model needed**: Working set fits in cache

---

## Validation Results

These three concepts together achieve <20% prediction error on GEMM:

| Size | Predicted | Actual | Error |
|------|-----------|--------|-------|
| 256×256 | 1.51ms | 1.33ms | -13.6% |
| 1024×1024 | 22.85ms | 20.33ms | -12.4% |
| 4096×4096 | 2030ms | 1759ms | -15.4% |

---

## Relationship to B/L/D

These concepts extend the traverser model within the BLD framework:

**TraverserLink.engine** is a new property on Links that classifies them by hardware execution unit.

**engine_overlap** is a relationship between engines (themselves a kind of Boundary - they partition hardware resources).

**Cache efficiency** affects the effective count on memory Links based on Dimension sizes and hardware properties.

The framework remains: algorithm Structure meets hardware Traverser, alignment cost predicts performance.

---

## Implementation Reference

- `src/experiential_reality/model/traverser.py` - TraverserLink.engine, Traverser.engine_overlap
- `src/experiential_reality/model/predict.py` - Engine overlap cost aggregation
- `src/experiential_reality/model/structure.py` - Sqrt cache efficiency in create_gemm_structure()
- `calibration.json` - Hardware-specific rates and engine overlap configuration

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [GPU Calibration](./gpu-calibration.md) — Hardware traverser measurement
- [Structural Language](../../theory/structural-language.md) — TraverserLink definition
- [Performance Theorem](../ml/performance-theorem.md) — Theoretical foundation
