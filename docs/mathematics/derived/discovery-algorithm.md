---
status: FOUNDATIONAL
depends_on:
  - ../foundations/proofs/irreducibility-proof.md
---

# The BLD Discovery Algorithm

## Summary

**Algorithm for discovering BLD structure in any system:**

1. Input any system (code, data, neural nets, physics) — [Abstract Algorithm](#abstract-algorithm)
2. Find partitions → B (if/switch/match) — [Schema](#the-schema)
3. Find connections → L (pointers, calls, forces) — [Domain Instantiations](#domain-instantiations)
4. Find repetitions → D (loops, arrays, dimensions) — [Domain Instantiations](#domain-instantiations)
5. Output = Lie algebra configuration — [Connection to Lie](#connection-to-lie-theory)
6. Complete (every system has BLD), non-unique, polynomial time — [Properties](#properties)

| Domain | Find B | Find L | Find D | Complexity |
|--------|--------|--------|--------|------------|
| Code (AST) | if/switch | pointers/calls | for/while | O(n+e) |
| Data | Clusters | Correlations | Shape | O(n·d²) |
| Neural nets | Activations | Weights | Tensors | O(params) |
| Physics | Phase transitions | Forces | DOF | O(n²) |

> **Status**: Foundational

A formal specification of the algorithm for discovering BLD structure in any system.

---

## Abstract Algorithm

```
DISCOVER_STRUCTURE(system: System) → (B, L, D)

Input:  Any system with observable behavior
Output: BLD structure

1. B ← FIND_PARTITIONS(system)
   "Where does behavior change based on value?"

2. L ← FIND_CONNECTIONS(system)
   "What affects what?"

3. D ← FIND_REPETITIONS(system)
   "What repeats?"

4. Return (B, L, D)
```

The algorithm is a **schema** — the abstract structure is domain-independent, but the `FIND_*` operations are domain-specific.

---

## The Schema

```
┌─────────────────────────────────────────────────────────┐
│                    DISCOVERY SCHEMA                     │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  1. Enumerate behavior changes  →  Boundaries (B)       │
│  2. Enumerate dependencies      →  Links (L)            │
│  3. Enumerate repetitions       →  Dimensions (D)       │
│                                                         │
│  The "enumerate" operation is domain-specific.          │
│  The output structure is domain-independent.            │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

---

## Domain Instantiations

### Code (AST / Control Flow / Data Flow)

```python
def discover_structure_code(ast: AST) -> BLD:

    # Find Boundaries: value-dependent control flow
    B = set()
    for node in ast.traverse():
        if node.type in {IF, SWITCH, MATCH, TERNARY}:
            B.add(Boundary(
                discriminator=node.condition,
                partitions=node.branches
            ))

    # Find Links: references and dependencies
    L = set()
    for node in ast.traverse():
        if node.type in {POINTER, CALL, ASSIGNMENT, FIELD_ACCESS}:
            L.add(Link(
                source=node.source,
                target=node.target,
                properties=node.properties
            ))

    # Find Dimensions: repetition structures
    D = set()
    for node in ast.traverse():
        if node.type in {FOR, WHILE, MAP, ARRAY_DECL}:
            D.add(Dimension(
                extent=node.count,
                structure=node.body_structure
            ))

    return BLD(B, L, D)
```

**Signatures to match**:
- Boundaries: `if`, `switch`, `match`, `?:`, pattern guards
- Links: pointers, function calls, assignments, field access
- Dimensions: `for`, `while`, `map`, array declarations, recursion

### Data (Probability Distributions)

```python
def discover_structure_data(samples: np.ndarray) -> BLD:

    # Find Boundaries: cluster structure (modes)
    B = set()
    clusters = cluster_analysis(samples)  # GMM, k-means, DBSCAN
    for cluster in clusters:
        B.add(Boundary(
            discriminator=cluster.assignment_rule,
            partitions=cluster.members
        ))

    # Find Links: statistical dependencies
    L = set()
    correlations = compute_correlations(samples)
    for i, j in significant_correlations(correlations):
        L.add(Link(
            source=f"var_{i}",
            target=f"var_{j}",
            properties={"strength": correlations[i, j]}
        ))

    # Find Dimensions: data shape
    D = set()
    n_samples, n_features = samples.shape
    D.add(Dimension(extent=n_samples, structure="sample"))
    D.add(Dimension(extent=n_features, structure="feature"))

    return BLD(B, L, D)
```

**Signatures to match**:
- Boundaries: clusters, modes, class boundaries, support regions
- Links: correlations, mutual information, causal dependencies
- Dimensions: sample size, feature dimensions, repeated patterns

### Neural Networks

```python
def discover_structure_nn(architecture: NNSpec) -> BLD:

    # Find Boundaries: partitioning operations
    B = set()
    for layer in architecture.layers:
        if layer.type == ACTIVATION:
            B.add(Boundary(
                discriminator=layer.function,  # ReLU, sigmoid, etc.
                partitions=["active", "inactive"]
            ))
        if layer.type == ATTENTION:
            B.add(Boundary(
                discriminator="attention_mask",
                partitions=layer.mask_pattern
            ))

    # Find Links: connectivity
    L = set()
    for layer in architecture.layers:
        if layer.type == LINEAR:
            L.add(Link(
                source=layer.input,
                target=layer.output,
                properties={"type": "dense", "static": True}
            ))
        if layer.type == CONV:
            L.add(Link(
                source=layer.input,
                target=layer.output,
                properties={"type": "sparse", "local": True}
            ))
        if layer.type == ATTENTION:
            L.add(Link(
                source=layer.input,
                target=layer.output,
                properties={"type": "dynamic", "content_dependent": True}
            ))
    for skip in architecture.skip_connections:
        L.add(Link(source=skip.from_, target=skip.to, properties={"type": "skip"}))

    # Find Dimensions: tensor shapes
    D = set()
    D.add(Dimension(extent=architecture.batch_size, structure="batch"))
    for dim_name, dim_size in architecture.dimensions.items():
        D.add(Dimension(extent=dim_size, structure=dim_name))

    return BLD(B, L, D)
```

**Signatures to match**:
- Boundaries: activations (ReLU, sigmoid), attention masks, dropout
- Links: weight matrices (dense/sparse/dynamic), skip connections
- Dimensions: batch, spatial, channel, sequence, layer dimensions

### Physical Systems

```python
def discover_structure_physics(system: PhysicalSystem) -> BLD:

    # Find Boundaries: phase boundaries, domains
    B = set()
    for phase_transition in system.phase_transitions:
        B.add(Boundary(
            discriminator=phase_transition.order_parameter,
            partitions=phase_transition.phases
        ))

    # Find Links: interactions
    L = set()
    for interaction in system.interactions:
        L.add(Link(
            source=interaction.particle_i,
            target=interaction.particle_j,
            properties={"force": interaction.force_law}
        ))

    # Find Dimensions: degrees of freedom
    D = set()
    D.add(Dimension(extent=3, structure="spatial"))
    D.add(Dimension(extent=system.n_particles, structure="particles"))
    for dof in system.internal_dof:
        D.add(Dimension(extent=dof.size, structure=dof.name))

    return BLD(B, L, D)
```

**Signatures to match**:
- Boundaries: phase transitions, domain walls, energy barriers
- Links: forces, bonds, interactions, field couplings
- Dimensions: spatial coordinates, particle count, internal degrees of freedom

---

## Properties

### Completeness

**Theorem**: Every system has a BLD representation.

**Proof**:
1. If system has no behavior changes: B = ∅
2. If system has no dependencies: L = ∅
3. If system has no repetition: D = {point} (single instance)
4. The trivial structure (∅, ∅, {point}) always exists
5. Therefore, a BLD representation always exists. ∎

**Note**: Completeness guarantees existence, not usefulness. A trivial representation captures no structure.

### Non-Uniqueness

**Theorem**: BLD representations are not unique.

**Proof by counterexample**:

Consider: `Array[N] of Struct{a: int, b: int}`

**Representation 1** (struct-centric):
```
D = {elements: N}
L = {a→b for each element}  (N links)
B = ∅
```

**Representation 2** (field-centric):
```
D = {fields: N×2}
B = {field_type: {a, b}}
L = ∅
```

Both are valid. They describe the same system at different granularities. ∎

### Canonical Form

**Definition**: A BLD representation is **canonical** if it minimizes:

```
cost(B, L, D) = |B| + |L| + |D|
```

subject to: the representation is complete (captures all behavior).

**Theorem (self-referential)**: Finding the canonical form requires global temporal scope.

**Proof sketch**:
1. To find the minimal representation, must compare ALL valid representations
2. This is a global optimization over the space of BLD configurations
3. Cannot be evaluated locally — no gradient points toward minimal
4. Therefore requires `temporal_scope = "global"`

**Corollary**: Finding canonical BLD is computationally hard (likely NP-hard).

This is the BLD framework predicting its own complexity: the question "what is the minimal description of this system?" has the same structure as NP-hard problems (global constraint that cannot be evaluated locally).

**Computable**: Yes — the space of representations is finite for finite systems.
**Efficient**: No — requires exhaustive search (no local traverser suffices).

**Conjecture**: Finding the canonical form is equivalent to finding the minimal Lie algebra presentation, which is known to be computationally difficult.

---

## Complexity Analysis

### Code

For AST with n nodes and e edges:

| Operation | Complexity | Method |
|-----------|------------|--------|
| Find B | O(n) | Single pass, match node types |
| Find L | O(e) | Extract edges from AST |
| Find D | O(n) | Single pass, match loop constructs |
| **Total** | **O(n + e)** | Linear in AST size |

### Data

For n samples with d dimensions:

| Operation | Complexity | Method |
|-----------|------------|--------|
| Find B | O(n·k·d·i) | k-means: k clusters, i iterations |
| Find L | O(d²·n) | Correlation matrix |
| Find D | O(1) | Read from data shape |
| **Total** | **O(n·d²)** | Dominated by correlation |

For more sophisticated clustering (GMM with EM):
- Find B: O(n·k·d²·i) per iteration

### Neural Networks

For architecture with p parameters and l layers:

| Operation | Complexity | Method |
|-----------|------------|--------|
| Find B | O(l) | Count activation layers |
| Find L | O(p) | Enumerate weight matrices |
| Find D | O(1) | Read from specification |
| **Total** | **O(p)** | Linear in parameters |

### Physical Systems

For n particles with m interactions:

| Operation | Complexity | Method |
|-----------|------------|--------|
| Find B | O(phase transitions) | Enumerate known transitions |
| Find L | O(m) or O(n²) | Explicit or all-pairs |
| Find D | O(dof) | Count degrees of freedom |
| **Total** | **O(n²)** worst case | Dominated by interactions |

---

## Implementation Notes

### Handling Ambiguity

When the algorithm encounters ambiguous cases:

1. **Is this a boundary or a link?**
   - Boundary: value → one-of-many interpretations
   - Link: value → specific target
   - Test: Does the target depend on the value (B) or is it fixed (L)?

2. **Is this a dimension or multiple boundaries?**
   - Dimension: homogeneous repetition (same structure)
   - Multiple boundaries: heterogeneous alternatives (different structures)
   - Test: Do all instances have the same structure?

3. **What granularity?**
   - Coarse: fewer primitives, more abstraction
   - Fine: more primitives, more detail
   - Heuristic: Match the granularity of your analysis goal

### Iterative Refinement

The algorithm can be applied iteratively:

```
1. Initial pass: coarse BLD structure
2. For each boundary partition: recurse to find sub-structure
3. For each dimension element: recurse if heterogeneous
4. Stop when structure is atomic or analysis is sufficient
```

This produces a **hierarchical BLD structure** (tree of BLD configurations).

---

## Connection to Lie Theory

The discovery algorithm produces Lie structures because:

1. **Find B** → finds group topology (compact vs non-compact)
2. **Find L** → finds structure constants [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ
3. **Find D** → finds generators (basis of the Lie algebra)

The enumeration procedures are constructive methods for identifying these Lie algebra components without requiring prior knowledge of the symmetry group.

See [Constructive Lie](../lie-theory/constructive-lie.md) for the mathematical connection.

---

## Open Questions

1. **Is canonical form computable?** Can we find the minimal BLD representation in polynomial time?

2. **Is canonical form unique?** Or are there multiple minimal representations?

3. **What about implicit structure?** The algorithm finds explicit structure. How do we discover structure that isn't syntactically apparent?

4. **Automatic granularity selection?** Can we automatically choose the right level of detail?

5. **Cross-domain transfer?** Can BLD structure learned in one domain transfer to another?

---

## Conclusion

```
┌─────────────────────────────────────────────────────────────┐
│                  DISCOVERY ALGORITHM                        │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  INPUT:  Any system                                         │
│                                                             │
│  STEPS:  1. Find partitions      → B (boundaries)           │
│          2. Find connections     → L (links)                │
│          3. Find repetitions     → D (dimensions)           │
│                                                             │
│  OUTPUT: BLD structure (= Lie algebra configuration)        │
│                                                             │
│  PROPERTIES:                                                │
│    - Complete: Every system has a representation            │
│    - Non-unique: Multiple valid representations exist       │
│    - Polynomial: O(n + e) for code, O(n·d²) for data        │
│                                                             │
│  The algorithm is a schema instantiated per domain.         │
│  The output structure is domain-independent.                │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Discovery Method](../../meta/discovery-method.md) — The three questions (informal)
- [Structural Language](../../theory/structural-language.md) — B/L/D definitions
- [Constructive Lie](../lie-theory/constructive-lie.md) — Why this produces Lie structures
- [Canonical Hardness](../foundations/structural/canonical-hardness.md) — Complexity of minimal BLD
