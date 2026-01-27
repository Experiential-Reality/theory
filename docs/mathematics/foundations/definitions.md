---
status: FOUNDATIONAL
layer: 0
depends_on: []
used_by:
  - ../../../README.md
---

# BLD Formal Definitions

## Boundary

A **boundary** B partitions a value space V into disjoint regions based on a discriminator function:

```
B = (V, d, {R₁, R₂, ..., Rₙ})

where:
  V = value space
  d: V → {1, 2, ..., n}     discriminator function
  Rᵢ = interpretation/structure for partition i

  ∀v ∈ V: v belongs to exactly one Rᵢ where i = d(v)
```

**Capability**: Choice. Selection of one interpretation from many based on value.

**Examples**:
- Type discriminator: `d(tag) → {Ok, Err}`
- Memory region: `d(address) → {global, shared, register}`
- Physical state: `d(energy) → {folded, unfolded}`

---

## Link

A **link** L is a directed connection from source to target:

```
L = (s, t, properties)

where:
  s = source (value, location, or structure)
  t = target (value, location, or structure)
  properties = {pattern, count, ops, deps, ...}
```

**Capability**: Reference. One value points to, affects, or determines another.

**Examples**:
- Pointer: `offset → memory_location`
- Dependency: `input → computation → output`
- Force: `particle_i → particle_j` (with strength, direction)

---

## Dimension

A **dimension** D is an axis of homogeneous repetition:

```
D = (n, S, properties)

where:
  n = extent (number of instances)
  S = structure (shared by all instances)
  properties = {parallel, sequential, contiguous, ...}

  Homogeneity: ∀i ∈ [0,n): instance_i has structure S
```

**Capability**: Multiplicity. N instances of the same structure as a single unit.

**Examples**:
- Array: `elements[1024]` — 1024 instances of element structure
- Threads: `workers[256]` — 256 parallel execution contexts
- Residues: `amino_acids[208]` — 208 instances along protein chain

---

## Structure

A **structure** is a triple:

```
S = (B, L, D)

where:
  B = {b₁, b₂, ...}  finite set of boundaries
  L = {l₁, l₂, ...}  finite set of links
  D = {d₁, d₂, ...}  finite set of dimensions
```

---

## Irreducibility

Each primitive provides a unique capability not expressible by the other two:

| Primitive | Capability | Cannot express |
|-----------|------------|----------------|
| Boundary | Choice (value-based selection) | Reference, Multiplicity |
| Link | Reference (directed connection) | Choice, Multiplicity |
| Dimension | Multiplicity (homogeneous N) | Choice, Reference |

See [Irreducibility Proof](proofs/irreducibility-proof.md) for formal proof.

---

## Alignment Cost

For structures S₁ and S₂, the alignment cost is:

```
cost(S₁, S₂) = Σ_b penalty(S₁.b, S₂) + Σ_l penalty(S₁.l, S₂) + Σ_d penalty(S₁.d, S₂)

where penalty measures structural mismatch:
  - Aligned: penalty = 0
  - Partial: penalty = efficiency_loss
  - Misaligned: penalty = cost_multiplier × base_cost
```

See [Performance Theorem](../derived/performance-theorem.md) for derivation.
