# The Structural Manifold: Geometry

> **Status**: Validated

The metric and differential geometry of the structural manifold.

---

## Information-Geometric Foundation

**Theorem (Probability Distribution Submanifold)**: When structures are probability distributions, the structural manifold reduces to the statistical manifold with Fisher-Rao metric.

**Proof**:

Let P(x; θ) be a family of probability distributions parameterized by θ.

1. **Points**: Each distribution P_θ is a structure with:
   - Boundaries: Support regions, level sets
   - Links: Conditional dependencies (correlation structure)
   - Dimensions: Random variables, sample space

2. **Alignment cost**: For distributions, alignment cost is the KL divergence:
   ```
   cost(P, Q) = D_KL(P || Q) = ∫ p(x) log(p(x)/q(x)) dx
   ```

3. **Metric tensor**: The Hessian of KL divergence at P = Q gives:
   ```
   gᵢⱼ = ∂²D_KL(P_θ || P_θ')/∂θⁱ∂θ'ʲ |_{θ'=θ}
       = E_P[∂log p/∂θⁱ × ∂log p/∂θʲ]
   ```
   This is exactly the **Fisher information matrix**.

4. **Conclusion**: Our definition (metric = Hessian of alignment cost) recovers the Fisher-Rao metric on probability distributions. ∎

**Corollary**: The BLD framework generalizes classical information geometry. Statistical inference is structural alignment on the probability distribution submanifold.

**References**:
- Amari, S. "Information Geometry and Its Applications." Springer, 2016.
- Efron, B. "Defining the Curvature of a Statistical Problem." Ann. Stat. 3(6), 1975.

---

## Connection to Symmetric Spaces and Lie Theory

The probability distribution manifold is a **symmetric space**, which connects BLD to Lie theory.

### SPD(d) as a Symmetric Space

The space of symmetric positive-definite matrices SPD(d) is:

```
SPD(d) = GL⁺(d) / O(d)
```

This is a symmetric space of non-compact type. The key properties:

1. **Fisher metric comes from Killing form**: The Fisher-Rao metric on SPD(d) is induced by the Killing form on the Lie algebra gl(d), pulled back through the quotient structure.

2. **Curvature from Lie bracket**: For symmetric spaces, the Riemann curvature tensor is:
   ```
   R(X,Y)Z = -[[X,Y], Z]
   ```

   For SPD(2) at correlation ρ:
   ```
   K(ρ) = -1/(2(1-ρ²)²)
   ```

3. **Geodesics = matrix exponentials**: Geodesics on SPD(d) are matrix exponential curves, which are one-parameter subgroups of GL⁺(d).

### BLD = Lie Theory

This connection explains why BLD primitives map to Lie theory primitives:

| BLD Primitive | Lie Theory | On SPD(d) |
|---------------|------------|-----------|
| **D** (Dimension) | Generator | Symmetric matrix direction |
| **L** (Link) | Structure constant | [Dᵢ, Dⱼ] = Lᵢⱼᵏ Dₖ |
| **B** (Boundary) | Topology | Non-compact (open) |

The Killing form (bi-invariant inner product on the Lie algebra) is constant, while the Fisher metric varies with position Σ. But they are structurally related—both arise from the same Lie algebra structure.

**Key insight**: The curvature K(ρ) that constrains optimization IS the Lie bracket structure. Higher correlation → more curved → less shortcutting possible → higher α.

See [Lie Correspondence](../lie-theory/lie-correspondence.md) for the full mapping.

---

## Points on the Manifold

Each point is a **structure**: a configuration of boundaries, links, and dimensions.

```
S = (B, L, D)

where:
  B = {b₁, b₂, ...}  set of boundaries
  L = {l₁, l₂, ...}  set of links
  D = {d₁, d₂, ...}  set of dimensions
```

Both algorithms and traversers are points on the same manifold. They differ only in interpretation, not in kind.

---

## Stratification

The manifold is **stratified** by topology. Each stratum contains structures with the same number and connectivity of primitives.

```
M = ∐_τ M_τ

where τ indexes topologies (how many B/L/D, how they connect)
```

Within a stratum, coordinates are continuous:
- Boundary parameters: partition sizes, discriminator values
- Link parameters: count, ops, deps, pattern weights
- Dimension parameters: extent, property weights

Between strata, there are discrete jumps (adding/removing primitives).

---

## Coordinates Within a Stratum

For a structure with fixed topology τ:

```
θ = (θ_B, θ_L, θ_D)

θ_B = (partition_sizes, discriminator_values, ...)
θ_L = (counts, ops, deps, pattern_weights, ...)
θ_D = (extents, property_weights, ...)
```

The dimension of M_τ equals the total number of continuous parameters.

---

## The Metric

For two structures S₁ (algorithm) and S₂ (traverser), the **alignment cost** defines distance:

```
cost(S₁, S₂) = Σᵢ alignment_penalty(S₁.component_i, S₂)
```

From `alignment.py`, the components are:

### Link Alignment

```
penalty(link, traverser) =
  | conflict_factor     if link.pattern misaligns with traverser boundary
  | 1.0                 if aligned
  | 1/efficiency        if partial
```

Specifically for scatter vs memory_bank:
```
cost_multiplier = traverser.bank_conflict_factor  (typically 4.0)
```

### Dimension Alignment

```
penalty(dim, traverser) =
  | 1.0                           if dim.extent % subgroup_width == 0
  | extent / (floor(extent/sw)*sw) otherwise  (sawtooth function)
```

This creates **periodic ridges** in the metric at multiples of subgroup_width.

### Dependency Alignment (Latency Hiding)

```
hiding_ratio = parallel_instances × latency_cycles / (serial_deps × cycle_cost)

penalty =
  | 1.0                  if hiding_ratio ≥ 1.0  (full hiding)
  | 1/hiding_ratio       if hiding_ratio < 0.5  (insufficient parallelism)
  | interpolated         otherwise
```

### Barrier Alignment

```
penalty = 1.0 + barriers × 0.1
```

### The Metric Tensor (Local Form)

For infinitesimal changes in structure parameters θ:

```
ds² = gᵢⱼ dθⁱ dθʲ
```

The metric tensor g is the **Hessian of alignment cost**:

```
gᵢⱼ = ∂²cost/∂θⁱ∂θʲ
```

This is analogous to the Fisher information metric in classical information geometry, where:
```
Fisher: gᵢⱼ = E[∂log p/∂θⁱ × ∂log p/∂θʲ]  (Hessian of KL divergence)
Ours:   gᵢⱼ = ∂²cost/∂θⁱ∂θʲ              (Hessian of alignment cost)
```

### Metric Properties

#### Piecewise Smooth

The metric is smooth within regions but has discontinuities at:
- Pattern transitions (scatter ↔ coalesced): step function
- Subgroup width multiples: sawtooth ridges
- Latency hiding threshold: kink

#### Singularities

Curvature concentrates at:
- `extent = k × subgroup_width` (efficiency peaks)
- `hiding_ratio = 1.0` (latency hiding threshold)
- Pattern boundaries

These singularities are **physically meaningful**:
- Ridges at subgroup multiples = SIMD efficiency boundaries
- Pattern transitions = memory access mode changes
- Hiding threshold = parallelism sufficiency

---

## Geodesics

A geodesic is the **shortest path** between two structures (minimum cost transformation).

For optimization:
- Gradient descent on cost follows the negative gradient
- Optimal transformations follow geodesics
- Local minima are structures where gradient = 0

For protein folding:
- The native state is a geodesic minimum
- Misfolded states are alternative minima
- Folding pathway follows geodesic descent

---

## Curvature

Local curvature encodes **sensitivity to perturbation**:

```
High curvature: small structural changes → large cost changes (fragile)
Low curvature:  small structural changes → small cost changes (robust)
```

**Flat regions**: Many structures have similar cost (degenerate solutions)

**High curvature regions**: Precise structure matters (optimization-sensitive)

---

## Related Documents

- [Manifold Foundations](./manifold-foundations.md) — What the manifold IS
- [Manifold Applications](./manifold-applications.md) — Domain interpretations

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — BLD = Lie theory mapping
- [Boundary Derivation](../lie-theory/boundary-derivation.md) — Exact B formula derivation
- [Variational Inference](../../applications/ml/variational-inference.md) — Experimental validation
- [Thermodynamics](./thermodynamics.md) — Statistical mechanics on the manifold
