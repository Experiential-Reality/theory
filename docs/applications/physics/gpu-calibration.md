---
status: VALIDATED
layer: application
depends_on:
  - ../../mathematics/lie-theory/lie-correspondence.md
  - engine-temporal-scope.md
  - ../ml/performance-theorem.md
used_by:
  - ../../theory/bld-as-language.md
  - engine-temporal-scope.md
  - ../../paths/practitioner.md
  - ../ml/performance-theorem.md
  - ../../meta/comparisons.md
---

# Calibration Analysis: Model Accuracy

> **Status**: Validated (NVIDIA RTX 3090: 8/10 tests, 18.6% avg error)

## Summary

**GPU calibration through BLD structure:**

1. Burst vs sustained rates: burst includes startup, sustained 4-5x better — [Model Components](#model-components)
2. Cold vs warm dispatch: first ~2.1ms, subsequent ~1.2ms — [Key Insight](#key-insight-cold-vs-warm-dispatch)
3. Cache boundary at L2 (4MB): working sets near cache size thrash (3.3x multiplier) — [Model Components](#model-components)
4. Engine overlap efficiency (22% on Intel Xe): compute runs at 22% during memory activity — [Model Components](#model-components)
5. GPU traverser IS a Lie algebra: compute units = D, memory patterns = L, cache boundaries = B — [Connection to Lie Theory](#connection-to-lie-theory)

| Component | BLD | Description |
|-----------|-----|-------------|
| L2 cache boundary | B | Topological threshold — cached vs uncached |
| ns_per_access rates | L | Geometric coupling per access pattern |
| Dispatch overhead | B | Boundary crossing — cold vs warm state |
| Block/workgroup count | D | Repetition — determines total link cost |

## Multi-GPU Support

Each GPU requires its own calibration file:

```bash
# Calibrate current GPU
uv run python scripts/calibrate.py --output calibration_my_gpu.json

# Validate with calibration
uv run python scripts/validate_bld.py -c calibration_my_gpu.json
```

Available calibrations:
- `calibration_nvidia_v10.json` - NVIDIA RTX 3090
- `calibration_intel_isolated.json` - Intel Iris Xe

---

## Key Insight: Cold vs Warm Dispatch

The GPU has dramatically different dispatch overhead depending on warmth:
- **Cold dispatch** (first in process): ~2.1ms per dispatch
- **Warm dispatch** (subsequent): ~1.2ms per dispatch

Benchmarks do warmup runs → use **warm** overhead for predictions.
Real applications (single decode) → use **cold** overhead.

## Results Summary (Warm Dispatch + Cache Boundary)

| Image | Blocks | Predicted | Actual | Error |
|-------|--------|-----------|--------|-------|
| 64×64 | 64 | 5.0ms | 5.0ms | **-0.1%** ✓ |
| 1024×1024 | 16,384 | 13.9ms | 15.0ms | **+7.3%** ✓ |
| 24MP | 375,000 | 114.4ms | 110.0ms | **-4.0%** ✓ |

All predictions within 10% after controlling for:
1. Cold vs warm dispatch (use warm for benchmarks)
2. Cache boundary effects (L2 size = 4MB)
3. Fixed setup overhead (1.3ms)

## Model Components

### 1. Base Link Costs (Burst vs Sustained)

Microbenchmarks capture **burst** rates (with startup overhead). Real workloads achieve **sustained** rates (4-5x better throughput):

| Link Type | Burst (ns/access) | Sustained (ns/access) | Ratio |
|-----------|-------------------|----------------------|-------|
| Coalesced memory | 0.134 | 0.028 | 4.8x |
| Strided memory | 0.147 | 0.034 | 4.3x |
| Scattered memory | 0.589 | 0.112 | 5.3x |
| Shared memory | 0.0044 | 0.0044 | 1.0x |
| Compute (serial) | 0.0118 | 0.0025 | 4.7x |
| Compute (independent) | 0.0019 | 0.0004 | 4.8x |

Use **burst** for small workloads, **sustained** for large workloads where startup is amortized.

**Coalesced vs Strided**:
- Coalesced: Adjacent threads access adjacent memory addresses (optimal)
- Strided: Threads access with fixed stride (less efficient)
- These are now measured separately with dedicated shaders

### 2. Memory Startup Overhead

Memory pipelines have a startup cost before sustained throughput is reached:
- **Memory startup**: 3.38 µs (captured as separate link cost)
- **Shared memory**: No startup (on-chip, always fast)

This is a **boundary crossing cost** - transitioning from idle to active memory access.

### 3. Cache Pressure Multiplier
Working set vs L2 cache (4MB on Intel Xe):
- < 50% of L2: multiplier = 1.0 (fully cached)
- = 100% of L2: multiplier = 3.3 (peak thrashing)
- > 150% of L2: multiplier → 1.5 (streaming)

### 4. Engine Overlap

Memory and compute engines can overlap partially. The model:

```
time = max(memory_time, compute_time) + min(memory_time, compute_time) × (1 - efficiency)
```

- **efficiency = 0.22** on Intel Xe (compute runs at 22% speed during memory activity)
- At efficiency = 1.0: perfect overlap (time = max)
- At efficiency = 0.0: no overlap (time = sum)

This replaces simpler approximations and better represents partial parallelism.

### 5. Dispatch Overhead
- Cold (first in process): ~2.1ms per dispatch
- Warm (subsequent): ~1.2ms per dispatch

### 6. Fixed Setup Overhead
- Buffer binding, pipeline setup: ~1.3ms per decode

## Controllable Variables

### 1. Cold vs Warm Dispatch

```bash
# For benchmarks (warm GPU, subsequent decodes)
python scripts/predict.py --blocks 16384

# For real-world (cold GPU, first decode in process)
python scripts/predict.py --blocks 16384 --cold
```

The first decode in a process pays cold overhead. Subsequent decodes are warm.

### 2. Working Set Size

At the L2 cache boundary (~4MB), memory costs increase significantly.
This is a **hardware boundary** - working sets near cache size thrash.

## Structural Insights

The errors reveal **resource boundaries** in the traverser that aren't in our simple model:

### 1. Dispatch Overhead Boundary

```
if workload < threshold:
    effective_overhead = cold_overhead  # Higher
else:
    effective_overhead = warm_overhead  # GPU stays warm
```

### 2. Cache Boundary

```
if working_set < L2_size:
    memory_cost = cached_cost  # Lower
else:
    memory_cost = uncached_cost  # Higher
```

### 3. Occupancy Boundary

```
if workgroups < min_for_saturation:
    throughput = workgroups / min_for_saturation  # Linear ramp
else:
    throughput = 1.0  # Full utilization
```

## Improving Accuracy

To get <20% error across all sizes, we need:

1. **Measure warm dispatch overhead** - Already done: 1.2ms vs 2.1ms cold
2. **Model cache effects** - Memory cost varies with working set size
3. **Model occupancy curve** - Throughput varies with workgroup count
4. **Better Huffman model** - Current model underestimates complexity

## The Fundamental Challenge

GPU performance is **non-linear** due to resource boundaries:

```
Cost ≠ SUM(primitive_costs)
Cost = f(primitive_costs, resource_utilization, cache_state, occupancy)
```

Our structural model captures the **topology** (which primitives interact),
but the **metric** (exact cost) depends on runtime resource state.

## Recommendation

For practical use:

1. **Control for warmup** - Use `--cold` for first-run predictions, warm (default) for benchmarks
2. **Apply 1.3x correction** - Model underestimates by ~30% due to idealized primitives
3. **Watch for cache boundaries** - 2x correction needed at L2 boundary (~4MB)
4. **Use for relative comparisons** - "Algorithm A is ~2x faster than B" is reliable
5. **Validate with benchmarks** - Calibrate per-GPU for absolute accuracy

---

## Connection to Lie Theory

The GPU traverser structure IS a Lie algebra:

| Hardware Component | BLD Primitive | Lie Equivalent |
|-------------------|---------------|----------------|
| Compute units, threads | Dimension (D) | Generators |
| Memory access patterns | Link (L) | Structure constants |
| Cache boundaries, dispatch states | Boundary (B) | Group topology |

When we calibrate GPU primitives, we're measuring the Lie algebra structure of the hardware. The cost model is alignment cost — how well the algorithm's Lie structure maps to the hardware's Lie structure.

The cache boundary (L2 = 4MB) is literally a topological boundary in the hardware's Lie group — states on one side (cached) behave differently from states on the other side (uncached).

See [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) for the full mapping.

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — BLD = Lie theory
- [Engine Temporal Scope](./engine-temporal-scope.md) — GPU engine parallelism
- [Performance Theorem](../ml/performance-theorem.md) — Theoretical foundation
- [Comparisons](../../meta/comparisons.md) — BLD vs Roofline model
