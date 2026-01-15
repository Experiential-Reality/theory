---
status: DERIVED
depends_on:
  - lie-theory/lie-correspondence.md
  - foundations/irreducibility-proof.md
---

# Comparisons to Existing Frameworks

## Quick Summary (D≈7 Human Traversal)

**BLD vs established frameworks in 7 steps:**

1. **GPU: BLD extends Roofline** — Captures bank conflicts, cache pressure, coalescing that Roofline ignores
2. **Proteins: BLD complements Force Fields** — Explains WHY (alignment cost) not just WHAT (energy terms)
3. **Statistics: BLD generalizes Fisher-Rao** — Distributions are one type of structure; BLD handles non-probabilistic
4. **Complexity: BLD characterizes P vs NP** — Local vs global temporal scope (structural, not computational)
5. **Mathematics: BLD = constructive Lie theory** — Finds structure in any system (operational FFT : Fourier)
6. **Pattern** — BLD doesn't replace frameworks; provides unifying perspective
7. **Connection** — Shows why existing frameworks work and where they connect

| Domain | Established | BLD Relationship |
|--------|-------------|------------------|
| GPU | Roofline Model | Subsumes + extends (bank conflicts, cache) |
| Proteins | Force Fields | Complementary (explains why) |
| Statistics | Fisher-Rao | Generalizes (distributions = structures) |
| Complexity | Circuit Complexity | Orthogonal (structural vs computational) |
| Math | Lie Theory | BLD is constructive Lie theory |

> **Status**: Foundational

How the BLD framework relates to established models in different domains.

---

## GPU Performance: B/L/D vs Roofline Model

### The Roofline Model

The roofline model (Williams, Waterman, Patterson 2009) predicts GPU performance as:

```
Performance = min(Peak_Compute, Peak_Bandwidth × Arithmetic_Intensity)
```

Or equivalently for time:
```
Time = max(Compute_Bound, Memory_Bound)
```

This creates a "roofline" where performance is limited by either compute or memory bandwidth.

### BLD Approach

The BLD model predicts performance as:
```
Time = Σ(link_costs) × alignment_multipliers
```

Where link costs depend on:
- Memory links: `count × pattern_cost × cache_efficiency`
- Compute links: `ops × cycles_per_op`

### Equivalence

The roofline model emerges from the BLD model when:

1. **Memory bound** = Sum of memory link costs dominates
   - High memory link count, low compute ops
   - Memory links scale with data size

2. **Compute bound** = Sum of compute link costs dominates
   - High compute ops per memory access
   - Compute links scale with arithmetic intensity

3. **Arithmetic intensity** = ratio of compute links to memory links

### Where B/L/D Goes Further

The BLD model captures effects roofline ignores:

| Effect | Roofline | B/L/D |
|--------|----------|-------|
| Bank conflicts | ✗ | ✓ (scatter pattern multiplier) |
| Cache pressure | ✗ | ✓ (working set vs L2 size) |
| Memory coalescing | ✗ | ✓ (coalesced vs scatter pattern) |
| Latency hiding | ✗ | ✓ (parallel instances vs dependency depth) |
| Engine overlap | ✗ | ✓ (memory + compute in parallel) |

**Result**: BLD predictions are within 15% for GEMM and JPEG, while roofline gives only order-of-magnitude guidance.

---

## Protein Folding: B/L/D vs Force Fields

### Molecular Mechanics Force Fields

AMBER, CHARMM, and similar force fields compute energy as:

```
E = E_bond + E_angle + E_torsion + E_vdW + E_electrostatic
```

Each term is a sum over structural features:
- `E_bond = Σ k_b(r - r_0)²` (bond stretching)
- `E_angle = Σ k_θ(θ - θ_0)²` (angle bending)
- `E_torsion = Σ V_n[1 + cos(nφ - γ)]` (dihedral rotation)
- `E_vdW = Σ 4ε[(σ/r)¹² - (σ/r)⁶]` (van der Waals)
- `E_electrostatic = Σ q_i q_j / r_ij` (Coulomb)

### B/L/D Approach

In the BLD framework, the protein sequence is a structure, and physics is the traverser:

```
Sequence Structure:
- Boundaries: Ramachandran regions, hydrophobic/hydrophilic
- Links: Backbone bonds, potential hydrogen bonds, disulfide bridges
- Dimensions: Residue chain, secondary structure elements

Physics Traverser:
- Boundaries: Steric exclusion, favorable angle regions
- Links: Force interactions with distance/angle dependence
- Dimensions: 3D space, rotational degrees of freedom

Alignment Cost = Free Energy
```

### Correspondence

| Force Field Term | B/L/D Concept |
|------------------|---------------|
| Bond stretching | Link alignment (bond exists vs doesn't) |
| Angle bending | Boundary alignment (Ramachandran regions) |
| Torsion | Link alignment (rotational constraints) |
| van der Waals | Boundary alignment (steric exclusion) |
| Electrostatic | Link alignment (charge interactions) |
| Hydrophobic effect | Boundary alignment (hydrophobic core formation) |

### Where B/L/D Adds Perspective

Force fields compute energy. The BLD framework explains WHY:

1. **Levinthal's Paradox**: Alignment is local, so gradient descent works. Each residue evaluates its own alignment independently.

2. **Folding Funnel**: The funnel IS the alignment cost surface. Native state is the global minimum.

3. **Misfolding**: Alternative alignment minima (like PrPˢᶜ) exist and can be stable.

4. **Template Conversion**: A second structure (existing PrPˢᶜ) acts as an additional traverser, changing the effective energy landscape.

---

## Information Theory: B/L/D vs Fisher-Rao

### Classical Information Geometry

The Fisher-Rao metric on probability distributions:

```
ds² = g_ij dθ^i dθ^j

where g_ij = E[∂log p/∂θ^i × ∂log p/∂θ^j]
```

KL divergence:
```
D(P||Q) = ∫ p(x) log(p(x)/q(x)) dx
```

The Fisher information matrix is the Hessian of KL divergence at P = Q.

### B/L/D Approach

Structures live on a manifold with metric derived from alignment cost:

```
ds² = g_ij dθ^i dθ^j

where g_ij = ∂²cost/∂θ^i∂θ^j
```

### The Relationship

**Probability distributions are a special case of structure:**

| Distribution Concept | B/L/D Concept |
|---------------------|---------------|
| Support | Boundaries (which outcomes are possible) |
| Conditional independence | Links (which variables depend on which) |
| Sample size, dimensions | Dimensions (how many random variables) |
| KL divergence | Alignment cost (traversing P's structure with Q's expectations) |
| Fisher information | Hessian of alignment cost (alignment sensitivity) |

### BLD as Generalization

Classical information geometry is the **submanifold** of the BLD manifold where:
- Structures happen to be probability distributions
- Alignment cost happens to be KL divergence
- The traverser is "expectation under Q"

The BLD framework extends to structures that aren't distributions:
- GPU algorithms (no probabilistic interpretation)
- Molecular structures (discrete configurations)
- Code structure (no measure-theoretic foundation needed)

---

## Complexity Theory: B/L/D vs Circuit Complexity

### Circuit Complexity

Traditional complexity theory characterizes problems by:
- Circuit depth (parallel time)
- Circuit width (space)
- Gate types (operations allowed)

P vs NP concerns whether polynomial-time algorithms exist.

### B/L/D Structural Characterization

The BLD framework characterizes problem difficulty by:
- **Boundary temporal scope**: Can constraints be evaluated locally?
- **Link dependency depth**: How deep is the dependency chain?
- **Dimension parallelism**: Can elements be processed independently?

### The P vs NP Perspective

**P problems**: Constraints have local temporal scope
- Each element can evaluate its own constraints
- Gradient descent (local improvement) leads to global optimum
- Example: Shortest path—local distances determine global distance

**NP problems**: Constraints have global temporal scope
- Visit-once (TSP), satisfiability (SAT) require knowing entire solution
- No local gradient toward global optimum
- Example: TSP—can't evaluate "visit-once" without full tour

### Caveat

This is a **structural characterization**, not a proof. It explains WHY P and NP appear different if they are, but doesn't prove they are different.

The framework suggests: If physics only provides local traversers (which it does), then problems requiring global constraint evaluation cannot be solved efficiently by physical systems.

---

---

## Mathematics: B/L/D vs Lie Theory

### Classical Lie Theory

Lie theory (Sophus Lie, 1870s) is the mathematics of continuous symmetry:
- **Lie group**: A group that is also a smooth manifold
- **Lie algebra**: The tangent space at the identity, capturing infinitesimal structure
- **Structure constants**: How generators combine: [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ

Lie theory is analytical: given a symmetry group, it tells you its properties.

### BLD Approach

BLD is constructive: given any system, it finds the structure—which turns out to be Lie structure.

### The Correspondence

| Lie Component | BLD Primitive | What It Captures |
|--------------|---------------|------------------|
| Generators | Dimension (D) | Directions of transformation |
| Structure constants | Link (L) | How generators interact |
| Group topology | Boundary (B) | Bounded vs unbounded regions |

### BLD as Constructive Lie Theory

The relationship is like:
- **FFT** : Fourier analysis (constructive method : analytical theory)
- **Autodiff** : Calculus
- **BLD** : Lie theory

Lie theory tells you properties of symmetry groups. BLD tells you how to **find** the symmetry group in any system.

See [Lie Correspondence](./lie-theory/lie-correspondence.md) for the full mapping and [Why Lie Theory](./lie-theory/why-lie-theory.md) for an accessible explanation.

---

## Summary

| Domain | Established Framework | B/L/D Relationship |
|--------|----------------------|-------------------|
| GPU | Roofline Model | BLD subsumes and extends (captures bank conflicts, cache, coalescing) |
| Proteins | Force Fields (AMBER, etc.) | Complementary view (explains why, not just what) |
| Statistics | Fisher-Rao / Info Geometry | BLD generalizes (distributions are one type of structure) |
| Complexity | Circuit Complexity | Orthogonal characterization (structural vs computational) |
| Mathematics | Lie Theory | BLD is constructive Lie theory (finds structure, doesn't just analyze it) |

The pattern: the BLD framework doesn't replace existing frameworks—it provides a unifying perspective that shows why they work and where they connect.

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Lie Correspondence](./lie-theory/lie-correspondence.md) — BLD = Lie theory mapping
- [Why Lie Theory](./lie-theory/why-lie-theory.md) — Accessible explanation
- [GPU Calibration](../applications/physics/gpu-calibration.md) — BLD vs Roofline in practice
