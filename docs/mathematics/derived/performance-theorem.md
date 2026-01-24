---
status: VALIDATED
depends_on:
  - ../foundations/proofs/irreducibility-proof.md
  - manifold-applications.md
---

# Performance Comparison Theorem

## Quick Summary (D≈7 Human Traversal)

**Performance prediction in 7 steps:**

1. **Structure S meets traverser T** — Algorithm (S) runs on hardware (T)
2. **Cost = alignment penalty** — Misalignment between S and T creates performance loss
3. **Cost decomposes** — cost(S,T) = Σ boundary + Σ link + Σ dimension + overhead
4. **Compare traversers** — T₁ outperforms T₂ ⟺ cost(S,T₁) < cost(S,T₂)
5. **Geometric view** — On manifold, better hardware is "closer" to your algorithm
6. **Predictive** — Rank hardware options by alignment cost without running code
7. **Universal** — Same math applies to GPU optimization, protein engineering, ML architecture search

| Misalignment Type | What Causes It | Penalty |
|-------------------|---------------|---------|
| Link pattern | Scatter vs coalesced memory | conflict_factor (e.g., 4×) |
| Dimension extent | extent % subgroup_width ≠ 0 | Wasted lanes |
| Latency hiding | Insufficient parallelism | 1/hiding_ratio |
| Boundary | Missing sync support | barrier_cost × count |

> **Status**: Validated

Given the structural manifold and alignment cost function, we can mathematically prove when one traverser will outperform another for a given structure.

---

## Theorem Statement

**Theorem (Traverser Performance Ordering)**:

Let S be a structure and T₁, T₂ be traversers. Then:

```
T₁ outperforms T₂ on S  ⟺  cost(S, T₁) < cost(S, T₂)
```

Where cost is the alignment cost function on the structural manifold.

---

## Proof

**Definition**: Performance is inversely related to cost. Lower cost = higher performance.

**The alignment cost decomposes**:

```
cost(S, T) = Σ_b penalty(S.boundary_b, T)
           + Σ_l penalty(S.link_l, T)
           + Σ_d penalty(S.dimension_d, T)
           + overhead(T)
```

Each term is determined by structural (mis)alignment:

### Boundary Alignment Cost

```
penalty(boundary_b, T) =
  | 0                           if T has matching boundary with compatible temporal_scope
  | barrier_cost × num_barriers if boundary requires synchronization T doesn't support
  | ∞                           if boundary is incompatible with T
```

### Link Alignment Cost

```
penalty(link_l, T) = base_cost(l, T) × misalignment_factor(l, T)

where:
  base_cost = l.count × l.ops × T.ns_per_op  (or T.ns_per_access for memory)

  misalignment_factor =
    | 1.0                    if l.pattern aligns with T (e.g., coalesced → coalesced)
    | T.conflict_factor      if l.pattern misaligns (e.g., scatter → bank boundary)
    | 1/hiding_ratio         if dependency chain exceeds T's hiding capacity
```

### Dimension Alignment Cost

```
penalty(dimension_d, T) = efficiency_loss(d, T)

where:
  efficiency_loss =
    | 0                                        if d.extent % T.subgroup_width == 0
    | (sw - (extent % sw)) / extent           otherwise (wasted lanes)
```

---

## Comparison Formula

For traversers T₁ and T₂:

```
Δcost = cost(S, T₁) - cost(S, T₂)

      = Σ_l [base(l,T₁)×misalign(l,T₁) - base(l,T₂)×misalign(l,T₂)]
      + Σ_d [efficiency_loss(d,T₁) - efficiency_loss(d,T₂)]
      + Σ_b [barrier_cost(b,T₁) - barrier_cost(b,T₂)]
      + [overhead(T₁) - overhead(T₂)]
```

**T₁ outperforms T₂ ⟺ Δcost < 0**

---

## Decomposed Performance Prediction

We can predict exactly WHY one traverser wins:

### Case 1: Link Pattern Alignment

If S has scatter links and:
- T₁.conflict_factor = 2.0
- T₂.conflict_factor = 4.0

Then T₁ wins on scatter-heavy workloads by factor of 2×.

```
Δcost_link = Σ_scatter_links count × ops × (T₁.factor - T₂.factor)
           = Σ_scatter_links count × ops × (2.0 - 4.0)
           = negative → T₁ wins
```

### Case 2: Dimension Alignment

If S has dimension extent = 64 and:
- T₁.subgroup_width = 32 (64 % 32 = 0, perfect)
- T₂.subgroup_width = 48 (64 % 48 = 16, wastage)

Then T₁ wins by:
```
efficiency_T₁ = 1.0
efficiency_T₂ = 48/64 = 0.75

Δcost_dim = (1 - 1.0) - (1 - 0.75) = -0.25 → T₁ wins by 25%
```

### Case 3: Latency Hiding

If S has dependency chain depth = 8 and:
- T₁ has 256 parallel threads, latency_cycles = 4
- T₂ has 64 parallel threads, latency_cycles = 4

Then:
```
hiding_ratio_T₁ = 256 × 4 / (8 × cycle_cost) = high (full hiding)
hiding_ratio_T₂ = 64 × 4 / (8 × cycle_cost) = lower (partial hiding)

T₁ wins on dependency-heavy workloads
```

---

## The Geometric View

On the structural manifold:

- S is a point (the structure)
- T₁ and T₂ are points (the traversers)
- cost(S, T) is the "distance" from S to T in alignment space

**T₁ outperforms T₂ ⟺ S is closer to T₁ than to T₂**

```
         T₁
        /
       / d₁ (shorter)
      /
     S
      \
       \ d₂ (longer)
        \
         T₂

d₁ < d₂ → T₁ wins
```

This is why "hardware-software co-design" works: you're either moving S toward T (optimizing code) or moving T toward S (designing hardware).

---

## Optimal Traverser Selection

**Corollary**: For a given structure S, the optimal traverser is:

```
T* = argmin_T cost(S, T)
```

This is the point on the traverser submanifold closest to S.

**Corollary**: For a given traverser T, the optimal structure is:

```
S* = argmin_S cost(S, T)
```

This is why some algorithms are "natural" for certain hardware—they're near the minimum.

---

## Example: GPU vs CPU for Matrix Multiply

**Structure S (GEMM)**:
```
dimensions: [M, N, K] all large, parallel
links: [memory_read: coalesced, compute: high ops, deps=K]
boundaries: [tiles]
```

**Traverser T_GPU**:
```
dimensions: [compute_units: 96, threads: 1024]
boundaries: [subgroup: width=32, memory_bank: count=32]
links: [global_coalesced: 0.14 ns, compute: 0.019 ns]
temporal_scope: parallel
```

**Traverser T_CPU**:
```
dimensions: [cores: 8, simd: 8]
boundaries: [cache_line: 64B]
links: [memory: 10 ns, compute: 0.3 ns]
temporal_scope: mostly sequential
```

**Alignment Analysis**:

| Component | GPU Alignment | CPU Alignment |
|-----------|---------------|---------------|
| Dimension (parallel M,N) | ALIGNED (1024 threads) | PARTIAL (8 cores) |
| Link (coalesced reads) | ALIGNED | PARTIAL (no coalescing) |
| Link (high compute) | ALIGNED (0.019 ns/op) | MISALIGNED (0.3 ns/op) |
| Boundary (tiles) | ALIGNED (workgroups) | PARTIAL (manual blocking) |

**Result**:
```
cost(GEMM, GPU) << cost(GEMM, CPU)
```

The GPU wins not by magic, but by structural alignment:
- Parallel dimensions match GPU's parallel temporal_scope
- Coalesced pattern matches GPU's memory system
- High compute density matches GPU's throughput

---

## Predictive Power

This framework lets us predict performance WITHOUT running code:

1. Describe algorithm as structure S
2. Describe hardware options as traversers T₁, T₂, ...
3. Compute alignment costs
4. Rank by cost

**The prediction is mathematical, not empirical.**

---

## Implications

1. **Hardware selection**: Choose traverser with minimum alignment cost for your workload.

2. **Code optimization**: Transform S to reduce alignment cost with fixed T.

3. **Hardware design**: Design T to minimize cost for target workload class.

4. **Complexity bounds**: Some structures have high cost on ALL physical traversers (NP-hard = globally-constrained boundaries that no local traverser can efficiently align with).

5. **Universal optimization**: The same math applies to:
   - GPU kernel optimization
   - Protein engineering (design sequence to fold correctly)
   - ML architecture search (design network to align with data)
   - Compiler optimization (transform code to align with target)

---

## Connection to Lie Theory

The alignment cost has a deeper mathematical meaning: it measures the **obstruction to a Lie homomorphism**.

Structure S and traverser T each have Lie algebra structure (D = generators, L = structure constants, B = topology). A perfect alignment would be a structure-preserving map (homomorphism) between them.

The alignment cost decomposes as:
```
cost(S, T) = obstruction_D(S, T)  # Dimension mismatch
           + obstruction_L(S, T)  # Link pattern mismatch
           + obstruction_B(S, T)  # Boundary incompatibility
```

When cost = 0, a perfect homomorphism exists. When cost > 0, there is no structure-preserving map, and the cost measures how much structure must be lost in translation.

See [Constructive Lie](../lie-theory/constructive-lie.md) for the formal treatment.

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Constructive Lie](../lie-theory/constructive-lie.md) — Alignment as Lie homomorphism
- [Manifold Foundations](./manifold-foundations.md) — The structural manifold
- [GPU Calibration](../../applications/physics/gpu-calibration.md) — Performance validation
