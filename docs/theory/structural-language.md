---
status: Foundational
depends_on: []
---

# Structural Description Language

> **Status**: Foundational

> Three primitives for describing the shape of information.

## Summary

**Three primitives for describing structure:**

1. Three concept characters: `|` (B), `/` (L), `\n` (D) — [Concept Characters](#the-three-concept-characters)
2. Three questions: Where partitions? What connects? What repeats? — [Three Questions](#the-three-questions)
3. Cost = B + D×L: boundaries topological, links scale with dimension — [Cost Formula](#the-cost-formula)
4. Lie correspondence: B=topology, L=structure constants, D=generators — [Why Exactly Three](#why-exactly-three)
5. Irreducibility: each provides unique capability (choice, reference, multiplicity) — [Three Primitives](#the-three-primitives)
6. Traverser provides causal direction; structure alone is static — [Traverser](#traverser-as-causal-agent)

| Component | BLD |
|-----------|-----|
| Value partitions | B (Boundary) |
| Dependencies, references | L (Link) |
| Repetition, arrays | D (Dimension) |
| Processing direction | Traverser |

---

> **Implementation**: The self-hosted BLD compiler is being developed at [Experiential-Reality/bld](https://github.com/Experiential-Reality/bld).

---

## The Three Concept Characters

BLD has exactly THREE concept characters:

| Character | Primitive | Meaning | Lie Theory |
|-----------|-----------|---------|------------|
| `\|` | **B** (Boundary) | Partitions left from right | Group topology |
| `/` | **L** (Link) | Connects, traversible both directions | Structure constants fᵢⱼᵏ |
| `\n` | **D** (Dimension) | Each line is a position | Lie algebra generator |

That's the entire language.

---

## The Three Questions

To describe ANY structure, ask:

| Question | Primitive | What to find |
|----------|-----------|--------------|
| **Where does behavior partition?** | B | Choices, thresholds, type tags |
| **What connects to what?** | L | References, dependencies |
| **What repeats?** | D | Arrays, sequences |

The output is structure. This IS the description.

---

## The Cost Formula

```
Cost = B + D × L
```

- **B** = boundary cost (topological, invariant under scaling)
- **D** = dimension (repetition count)
- **L** = link cost (geometric, scales with D)

D multiplies L, not B:
- More lines → more link costs
- Boundaries stay local

---

## Quick Reference (Type Theory)

| Primitive | Type Constructor | What It Does | Elimination |
|-----------|-----------------|--------------|-------------|
| **Boundary** | Sum (+) | Partitions value space | `case` analysis |
| **Link** | Function (→) | Connects values | `apply` |
| **Dimension** | Product (Πₙ) | Repeats structure | `project` |

**Formal Foundation**: See [BLD Calculus](../mathematics/foundations/definitions/bld-calculus.md) for the type-theoretic formalization and [Irreducibility Theorem](../mathematics/foundations/proofs/irreducibility-categorical.md) for the proof that B/L/D are independent primitives.

**Mathematical Foundation**: These three primitives map exactly to Lie theory: D = generators, L = structure constants, B = group topology. See [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md) for the verified mapping.

---

## The Three Primitives

### 1. Boundary

**What it is:** Partitions value space into regions of meaning.

**Lie correspondence:** B = **Group topology**. A compact Lie group (closed boundary) has periodic generators—rotate 360° and you're back. A non-compact group (open boundary) has unbounded generators—translations go forever. See [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md).

**Key insight:** Boundaries operate on VALUES, not bytes. The medium (bytes, fields, bits) is just how values are encoded. The boundary itself is a value comparison that selects interpretation.

**Terminology note:** "Boundary" refers to both the discriminating criterion (the test) and the regions it creates (the partitions). Context makes clear which is meant: "the boundary partitions..." refers to the discriminator; "falls within the boundary" refers to a partition.

**Examples:**
```
signature == 0x504B0304 → local_file_entry
signature == 0x504B0102 → central_dir_entry
signature == 0x504B0506 → end_of_central_dir

flags.bit3 == 0 → sizes inline
flags.bit3 == 1 → sizes deferred

compressed_size != 0xFFFFFFFF → use this value
compressed_size == 0xFFFFFFFF → use zip64 extension
```

**Properties:**
- A single boundary can partition into N regions (not just 2)
- Boundaries are recognized by VALUE comparison
- The discriminator is always OUTSIDE the scope it controls
- What shares a boundary partition shares fate (scope)

---

### 2. Link

**What it is:** Connects one value to another.

**Lie correspondence:** L = **Structure constants fᵢⱼᵏ**. Links capture how dimensions couple: [Dᵢ, Dⱼ] = Lᵢⱼᵏ Dₖ. For angular momentum, the Levi-Civita tensor εᵢⱼₖ IS the link structure. This is why non-commuting operations create curved geometry.

**Examples:**
```
cd_offset → central_dir_entry[0]        # Offset points to position
local_offset → local_file_entry[?]      # Index reference
filename_len → extent of filename       # Length determines size
entries_total → extent of dimension     # Count determines repetition
discriminator → selected interpretation # Value selects partition
```

**Properties:**
- Links create the graph structure (DAG or otherwise)
- Links imply dependency (to understand A, may need B)
- Direction matters (A → B ≠ B → A)
- Offsets, lengths, counts, discriminators are ALL links

**Link types by what they connect:**
| Link Type | From | To |
|-----------|------|-----|
| Offset | Position value | Target location |
| Length | Count value | Extent of region |
| Count | Number value | Dimension extent |
| Discriminator | Partition key | Selected interpretation |

**Algorithm Link properties:**

When describing algorithm structure, links have these properties:

| Property | Type | Default | Meaning |
|----------|------|---------|---------|
| `name` | str | required | Identifier for the link |
| `from_` | str | required | Source location (global, shared, register) |
| `to` | str | required | Destination location |
| `count` | int | 1 | Number of accesses/operations |
| `ops` | int | 0 | Compute operations per access |
| `deps` | int | 0 | Dependency chain length for latency hiding |
| `pattern` | Literal | "coalesced" | Access pattern (coalesced, scatter, broadcast, reduce) |
| `engine` | Literal | "memory" | Hardware engine: "memory", "compute", "copy" |
| `scaling` | Literal | "per_block" | Invocation scaling: "per_block", "per_chunk" |

The `engine` field explicitly declares which hardware engine executes this link, enabling correct cost aggregation with engine overlap.

The `scaling` field declares how link invocations scale with data size: most links scale with the number of blocks, but Huffman decode links scale with chunks (groups of 64 blocks).

**Structure properties:**

| Property | Type | Default | Meaning |
|----------|------|---------|---------|
| `cache_model` | Literal | "dynamic" | How cache efficiency is handled |

Cache model values:
- `"prebaked"`: Efficiency already in Link.count (e.g., GEMM with sqrt model)
- `"dynamic"`: Apply runtime cache pressure multiplier (JPEG default)
- `"none"`: No cache modeling (small working sets)

**TraverserLink properties (hardware links):**

When describing hardware traversers, links gain additional properties:

| Property | Type | Meaning |
|----------|------|---------|
| `engine` | string | Which hardware engine: "memory", "compute", "copy" |
| `ns_per_access` | float | Time cost per access (calibrated) |
| `pattern` | string | Access pattern: "coalesced", "scatter", "broadcast", "reduce" |
| `bandwidth_gbps` | float | Peak bandwidth for this link type |

The `engine` property enables cost aggregation: when engines can execute in parallel (overlap), costs combine as `max()` not `sum()`. See [Engine Temporal Scope](../applications/physics/engine-temporal-scope.md).

**Traverser properties (hardware structure):**

The Traverser dataclass captures hardware structure:

| Property | Type | Meaning |
|----------|------|---------|
| `engine_overlap` | list[tuple[str, str]] | Pairs of engines that can execute in parallel |
| `barrier_cost_ns` | float | Cost of workgroup synchronization |
| `l2_cache_bytes` | int | L2 cache size for efficiency modeling |
| `dispatch_overhead_ms` | float | Fixed cost per GPU dispatch |

Example:
```python
Traverser(
    name="Intel Xe",
    engine_overlap=[("memory", "compute")],  # These engines overlap
    barrier_cost_ns=200.0,
    l2_cache_bytes=4 * 1024 * 1024,
)
```

**TraverserBoundary and temporal_scope:**

Traverser boundaries define how constraints are evaluated across parallel elements. The key property is `temporal_scope`:

| temporal_scope | Meaning | Example |
|----------------|---------|---------|
| `"parallel"` | Constraint evaluated independently for each element | Element-wise operations |
| `"sequential"` | Elements must be processed in order | Dependency chains |
| `"simd"` | Constraint at SIMD lane level (width = subgroup_width) | Vectorized operations |
| `"workgroup"` | Constraint at workgroup level | Shared memory access |
| `"global"` | Constraint on entire system (requires global sync) | Visit-once in TSP |

**Why temporal_scope matters:**

The scope determines whether alignment can be evaluated locally:
- **Local scopes** (parallel, simd, workgroup): Gradient descent works. Each element can evaluate its own alignment.
- **Global scope**: No local gradient. Must consider entire system state to evaluate constraint.

This distinction is central to the P ≠ NP characterization: NP-hard problems have constraints with global temporal scope, and no physically-realizable traverser can evaluate them locally.

Example:
```python
TraverserBoundary(
    name="subgroup",
    temporal_scope="simd",
    width=32,  # 32 lanes execute in lockstep
)

TraverserBoundary(
    name="visit_once",
    temporal_scope="global",  # Must know entire tour to verify
)
```

---

### Barrier Terminology

**Note**: The term "barrier" has multiple meanings across domains:

| Term | Domain | Meaning |
|------|--------|---------|
| **Synchronization barrier** | GPU computing | A point where threads must wait for each other (cost in nanoseconds) |
| **Energy barrier** | Thermodynamics | Saddle point between two minima on the energy landscape |
| **Kinetic barrier** | Protein folding | Activation energy required for a structural transition |

These are related conceptually (all involve "getting past something") but have different units and mechanisms. In GPU contexts, `barrier_cost_ns` refers to synchronization barriers. In protein folding, "barrier" typically means energy or kinetic barriers.

---

### 3. Dimension

**What it is:** An axis of repetition.

**Lie correspondence:** D = **Lie algebra generator**. A generator is an infinitesimal symmetry direction—"rotate slightly around the x-axis." Dimensions ARE generators: both represent directions along which structure extends. Multiple D's form a basis for the structural space, just as generators form a basis for the Lie algebra.

**Key insight:** Dimensions are irreducible. You cannot represent "N of these" using only boundary and link. Multiplicity implies dimensionality.

**Examples:**
```
local_file_entry[N]     # N files (extent from structure)
central_dir_entry[M]    # M entries (extent from link: entries_total)
pixels[width * height]  # Exactly width*height elements
handlers[N]             # N handlers, linked to state count
```

**Properties:**
- All instances share the same structure (homogeneous)
- Extent may be fixed, bounded, or determined by link
- Dimensions can nest (arrays of structs containing arrays)

---

## Dimension Descriptors

Dimensions have properties that enable optimization and correct interpretation:

### Bounds
| Descriptor | Meaning | Example |
|------------|---------|---------|
| `fixed(N)` | Exactly N elements | `pixels[1920*1080]` |
| `range(min, max)` | Between min and max | `children[0..255]` |
| `unbounded` | No upper limit | `log_entries[*]` |

### Memory Properties
| Descriptor | Meaning | Optimization |
|------------|---------|--------------|
| `contiguous` | Elements adjacent in memory | Sequential read, prefetch |
| `aligned(N)` | Elements aligned to N bytes | SIMD, GPU coalescing |
| `stride(N)` | N bytes between element starts | Interleaved access |

### Element Properties
| Descriptor | Meaning | Optimization |
|------------|---------|--------------|
| `homogeneous` | All elements same size | Random access O(1) |
| `heterogeneous` | Elements vary in size | Must scan from start |

### Order Properties
| Descriptor | Meaning | Optimization |
|------------|---------|--------------|
| `ordered` | Sequence matters | Preserve order |
| `unordered` | Set semantics | Parallel processing |
| `sorted(key)` | Sorted by key | Binary search |

---

## Why Exactly Three?

### Type-Theoretic Answer

Each primitive provides a unique capability:
- **Boundary**: Choice (cannot be expressed by Link or Dimension)
- **Link**: Reference (cannot be expressed by Boundary or Dimension)
- **Dimension**: Multiplicity (cannot be expressed by Boundary or Link)

See [Irreducibility Proof](../mathematics/foundations/proofs/irreducibility-proof.md).

### Lie-Theoretic Answer

These are exactly the components that define any Lie algebra:
- **Generators** (D): The infinitesimal symmetry directions
- **Structure constants** (L): How generators combine [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ
- **Topology** (B): Whether the group is compact (closed) or non-compact (open)

Every Lie algebra has exactly these three components. No more, no fewer.

This explains why BLD works across physics, computation, biology, and mathematics: they all involve symmetry, and Lie theory is the mathematical framework underlying all continuous symmetry (Noether's theorem).

See [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md) and [Why Lie Theory](../mathematics/lie-theory/why-lie-theory.md).

---

## The Euler Unification

> **Status**: Exploratory

The three primitives unify through Euler's formula:

```
e^(iπ) + 1 = 0
```

| Symbol | BLD Meaning |
|--------|-------------|
| **e** | Exponential compensation base (L^D cascades) |
| **i** | Rotation operator (angular direction) |
| **π** | Closure constant (half-turn inverts) |
| **1** | Identity (perfect alignment) |
| **0** | Equilibrium (zero cost) |

**Two compensation mechanisms, one equation**:

| Mechanism | Formula | Constant | Domain |
|-----------|---------|----------|--------|
| **Exponential** | L^D = e^(D·ln(L)) | e | Cascades, depth, gain |
| **Angular** | D×L = 2π × B | π | Rotations, phases, closure |

**Physical validation**: The α-helix in proteins demonstrates angular compensation (π mechanism):

```
Cylindrical helix (parametric form):
  x(n) = r × cos(θn)
  y(n) = r × sin(θn)
  z(n) = a × n          ← LINEAR rise, not exponential

In complex notation (xy-plane projection):
  xy(n) = r × e^(iθn)   ← Angular: rotation via e^(iθ)
  z(n) = a × n          ← Linear: NOT e^(an)

where:
  a = 1.5 Å (linear rise per residue)
  θ = 100° = 2π/3.6 radians (angular rotation per residue)

Result: 3.6 residues complete one full turn (360° = 2π)
```

The α-helix demonstrates angular closure (π mechanism) with linear extension. It is a cylindrical helix, not a logarithmic spiral.

**Empirical completeness**: Every structural domain examined decomposes into B/L/D without residue:
- Non-periodic cascades (circuits, neural depth) use exponential compensation (e)
- Periodic structures (rotations, phases) use angular compensation (π)
- No structural phenomenon has required a fourth primitive

This is an **empirical observation**, not a proven theorem.

See [Euler's Formula in BLD](../glossary.md#eulers-formula-in-bld), [π from BLD](../examples/pi-from-bld.md), and [Compensation Principle](../mathematics/foundations/structural/compensation-principle.md).

---

## Composition: What Emerges

Complex patterns emerge from combining primitives:

| Pattern | Composition |
|---------|-------------|
| **Containment** | Boundary (defines region) + Links (to contents) |
| **Scope** | Shared boundary partition |
| **Extent** | Link to dimension size, or fixed |
| **Conditional** | Boundary + link to selected interpretation |
| **Variant/Union** | Boundary (discriminator) + links to alternatives |
| **Length-prefix** | Link (length) → extent of dimension |
| **Null-terminated** | Boundary (sentinel) terminates dimension |

### Example: Containment Emerges

"Containment" isn't primitive—it's boundary + links:

```
local_file_entry                    # Boundary: signature == 0x504B0304
├── link: filename_len → filename   # Link to extent
├── link: extra_len → extra         # Link to extent
├── link: compressed_size → data    # Link to extent
└── (all links point to regions within this boundary)
```

The boundary defines "what's inside." The links define "how to find what's inside." Together they create containment.

### Example: Scope Emerges

"Scope" is what shares a boundary partition:

```
flags.bit3 == 0:
    crc32, compressed_size, uncompressed_size live in header

flags.bit3 == 1:
    crc32, compressed_size, uncompressed_size live in descriptor
```

These three fields share fate—they move together based on which partition of `flags.bit3` value space we're in. The boundary defines the scope.

---

## Notation

### Tree View (Boundaries + Links)
```
ZIP
│
├── boundary: signature partitions entry type
│
├── dimension[N]: local_file_entry
│   ├── link: filename_len → extent of filename
│   ├── link: extra_len → extent of extra
│   └── link: compressed_size → extent of data
│
├── dimension[M]: central_dir_entry
│   └── link: local_offset → local_file_entry[?]
│
└── end_of_central_dir
    ├── link: entries_total → extent of central_dir dimension
    └── link: cd_offset → central_dir_entry[0]
```

### Value Space View (Boundaries)
```
            SIGNATURE VALUE SPACE
┌─────────────────┬─────────────────┬─────────────────┐
│   0x504B0304    │   0x504B0102    │   0x504B0506    │
│  local_file     │  central_dir    │  end_of_central │
└─────────────────┴─────────────────┴─────────────────┘
```

### Graph View (Links)
```
end_of_central_dir
    │
    ├── entries_total ────► dimension extent
    │
    └── cd_offset ────────► central_dir_entry[0]
                                │
                                └── local_offset ──► local_file_entry[?]
```

---

## Drawing Conventions

1. **Show boundaries as value partitions**, not byte positions
2. **Show links with arrows** indicating direction
3. **Show dimensions with [N] notation** and note how N is determined
4. **Annotate dimensions** with relevant descriptors (bounds, contiguous, etc.)

---

## Notation Conventions

### Arrow Types

| Arrow | Unicode | Usage |
|-------|---------|-------|
| → | U+2192 | Type constructors (τ₁ → τ₂), references in prose |
| ⇒ | U+21D2 | Pattern matching in formal syntax (inl(x) ⇒ e₁) |
| ⟶ | U+27F6 | Reduction/evaluation steps (e ⟶ e') |
| ────► | Extended | Diagram arrows (visual emphasis) |

### Abbreviations

- **B/L/D**: When referring to the three primitives as a set ("B/L/D primitives", "B/L/D irreducibility")
- **BLD**: In compound nouns ("BLD Calculus", "BLD framework", "BLD model")

---

## Open Questions

These are discovered by drawing, not by theorizing:

### 1. Transformation ✓ Resolved
Is `input → [process] → output` a structural concept, or behavioral?

**Resolution:** A process IS structure—it's a dimension whose elements are intermediate structures, with links defining traversal order.

```
process: dimension[N]
├── element[0]: input structure
├── element[1]: intermediate structure
├── ...
└── element[N]: output structure

links: element[i] → element[i+1]  (traversal order)
```

The "cost" of a process is the path length through this dimension. Short paths = low cost. Paths with cycles or backtracking = high cost.

This is why well-structured code "glides" and poorly-structured code has "friction"—the traversal dimension is clean vs tangled.

### 2. Invariants
Where do constraints live? (e.g., "crc32 must match data")

Current thinking: Invariants are cross-cutting assertions that reference structure. They might need separate treatment, or they might be metadata on links.

### 3. Bidirectional Links
Should `A ↔ B` be explicit, or always decomposed to `A → B` and `B → A`?

Current thinking: Two links. Annotate as `bidirectional: true` if commonly paired.

### 4. Order
Is sequence implicit in medium, or explicit in dimension descriptor?

Current thinking: Dimension descriptor (`ordered`, `unordered`, `sorted`).

---

## Validation

The three primitives are validated by drawing real structures:

| Test Case | Status | Notes |
|-----------|--------|-------|
| ZIP file | ✓ Complete | See [ZIP Format](../examples/zip.md) |
| GPU traverser | ✓ Complete | Hardware as B/L/D |
| GPU algorithm (IDCT, GEMM) | ✓ Complete | Kernels as B/L/D |
| Protein folding (Prion) | ✓ Complete | See [Protein Folding](../applications/physics/protein-folding.md) - physics as traverser |
| Probability distributions | ✓ Complete | Fisher info = alignment sensitivity, KL = traversal cost |
| NP-hard problems (TSP) | ✓ Complete | Global boundary = structural hardness |
| JPEG pipeline | ✓ Complete | See [JPEG Pipeline](../examples/wgpu-jpeg-process.md) |
| Engine overlap | ✓ Complete | See [Engine Temporal Scope](../applications/physics/engine-temporal-scope.md) |

Success = same primitives describe all domains with no friction.

**Domains validated:**
- File formats (ZIP)
- GPU computing (algorithms + hardware)
- Molecular biology (protein folding)
- Statistical inference (information geometry)
- Computational complexity (P vs NP)
- **Lie theory** — BLD = Lie algebras (D=generators, L=structure constants, B=topology)

The Lie correspondence explains WHY BLD works universally: it's the same mathematics that describes all continuous symmetry.

---

## Traverser as Causal Agent

> **Status**: Exploratory

The traverser is more than a processing mechanism — it is the **source of causal agency** in the BLD framework.

### Observation vs Intervention

BLD captures structure, but structure alone has no inherent direction. The traverser provides the arrow:

| Operation | Direction | Meaning |
|-----------|-----------|---------|
| `see(X)` | structure → traverser | Passive reading (correlation) |
| `do(X)` | traverser → structure | Active intervention (causation) |

**Pearl's do-calculus in BLD**: The `do(X)` operator that cuts incoming edges IS the traverser acting on structure:

```
Correlation: see(X), see(Y)  →  structure ↔ structure (bidirectional L)
Causation:   do(X), see(Y)   →  traverser → structure (unidirectional L)
```

Intervention = traverser writing to structure, overwriting existing L.

### The Arrow of Time

The traverser carries the temporal direction:

| Traverser | Arrow of Time |
|-----------|---------------|
| Physics | Thermodynamic arrow (entropy increases) |
| CPU | Execution arrow (instructions in order) |
| GPU | Dispatch sequence |
| Gradient descent | Loss decreases |

The structure itself has no inherent direction. Time emerges from the traverser's processing.

### Why No Fourth Primitive for Causation

Causation = structure + traverser interaction:
- B, L, D capture static structure
- The traverser provides direction and agency
- No fourth primitive is needed because the traverser-structure asymmetry (see vs do) generates causal structure

**Key insight**: Confounders and interventions are distinguished by whether L flows through the traverser. This resolves the "hidden structure" question for causation — it's not missing from BLD; it's in the traverser.

**The traverser constant**: The mathematical signature of the traverser is **e** — the constant characterizing sequential accumulation. Just as π characterizes structure (closure), e characterizes the traverser (accumulation). See [e from BLD](../examples/e-from-bld.md) for the derivation.

See [Glossary: Traverser as Causal Agent](../glossary.md#traverser-as-causal-agent) and [e (Traverser Constant)](../glossary.md#e-traverser-constant).

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Irreducibility Proof](../mathematics/foundations/proofs/irreducibility-proof.md) — Why exactly three primitives
- [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md) — BLD = Lie theory mapping
- [Discovery Method](../meta/discovery-method.md) — How to find BLD structure in any system
- [ZIP Example](../examples/zip.md) — Complete worked example
