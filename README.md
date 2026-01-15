> **For newcomers**: Consider using an AI assistant to explore BLD. Ask questions as you read — LLMs are BLD traversers too, and can help you navigate the structural landscape.

# BLD Theory

A structural theory of alignment.

> **BLD is an operational interface to Lie theory** — it makes symmetry structure accessible without requiring the standard mathematical machinery.

---

## The Contribution

BLD is not new mathematics — Lie theory is 150 years old.

The contribution is a **constructive method** for finding structure:

```
Lie Theory:  GIVEN structure → analyze properties
BLD Method:  GIVEN any system → FIND structure
```

This is like:
- **FFT** : Fourier analysis (algorithm : theory)
- **Autodiff** : Calculus
- **BLD** : Lie theory

The method is three questions anyone can ask:
1. **Where does behavior partition?** → Find Boundaries
2. **What connects to what?** → Find Links
3. **What repeats?** → Find Dimensions

The output is a Lie algebra configuration. You don't need to know Lie theory to use it — just ask the questions.

See [Discovery Method](docs/theory/discovery-method.md) for the full methodology.

---

## The Claim

All structure—in computation, physics, biology, mathematics—can be described with three irreducible primitives:

| BLD Primitive | Meaning | Lie Theory Equivalent |
|---------------|---------|----------------------|
| **Boundary** | Partition. Distinction. "This, not that." | Group topology (compact ↔ closed) |
| **Link** | Connection. Relation. "This affects that." | Structure constants [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ |
| **Dimension** | Repetition. Extension. "More of the same." | Lie algebra generators |

Cost, behavior, and dynamics emerge from **alignment** between structures.

This started as hypothesis. The Lie correspondence is now **verified** — BLD primitives map exactly to the components that define any Lie algebra. This explains why BLD works everywhere: Lie theory works everywhere (Noether's theorem).

---

## Formal Definitions

### Boundary

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

### Link

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

### Dimension

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

### Structure

A **structure** is a triple:

```
S = (B, L, D)

where:
  B = {b₁, b₂, ...}  finite set of boundaries
  L = {l₁, l₂, ...}  finite set of links
  D = {d₁, d₂, ...}  finite set of dimensions
```

### Irreducibility (Proven)

Each primitive provides a unique capability not expressible by the other two:

| Primitive | Capability | Cannot express |
|-----------|------------|----------------|
| Boundary | Choice (value-based selection) | Reference, Multiplicity |
| Link | Reference (directed connection) | Choice, Multiplicity |
| Dimension | Multiplicity (homogeneous N) | Choice, Reference |

See [Irreducibility Proof](docs/mathematics/foundations/irreducibility-proof.md) for formal proof.

### Alignment Cost

For structures S₁ and S₂, the alignment cost is:

```
cost(S₁, S₂) = Σ_b penalty(S₁.b, S₂) + Σ_l penalty(S₁.l, S₂) + Σ_d penalty(S₁.d, S₂)

where penalty measures structural mismatch:
  - Aligned: penalty = 0
  - Partial: penalty = efficiency_loss
  - Misaligned: penalty = cost_multiplier × base_cost
```

See [Performance Theorem](docs/mathematics/derived/performance-theorem.md) for derivation.

---

## Key Principles

### D×L Scaling

D multiplies L, not B.
- Geometric properties (L) scale with dimension
- Topological properties (B) are invariant
- Validated: R² = 1.0 across VI, neural nets, circuits

### Compensation Principle

L can compensate for B deficiency, not vice versa.
- B is topological (local scope, invariant under D)
- L is geometric (can span distance, scales with D)
- D×L accumulates → can approximate complex B
- D×B stays local → cannot replace missing L
- Validated: 87.8% improvement via cascading (circuits), 6.2% diagonal advantage (neural)

### Link Formula

```
L = -½ ln(1 - ρ²)
```

where ρ is correlation. This is an exact theorem derived from KL divergence.

---

## The Primitives

### Why Three? (Proven)

Structure requires:
1. **Distinction** (Boundary)—or everything is undifferentiated
2. **Relation** (Link)—or nothing interacts
3. **Extension** (Dimension)—or there is only one of each thing

These are not chosen for convenience. They are **provably irreducible**—each provides a capability the others cannot express. See [Irreducibility Proof](docs/mathematics/foundations/irreducibility-proof.md).

### Why These Three?

**First answer (type theory)**: Every attempt to reduce further fails:
- Boundaries without links: disconnected partitions (no structure)
- Links without boundaries: undifferentiated flow (no structure)
- Either without dimensions: no repetition, no pattern, no generality

**Second answer (Lie theory)**: These are exactly the components that define a Lie algebra:
- **Generators** (D): Infinitesimal symmetry directions
- **Structure constants** (L): How generators combine [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ
- **Topology** (B): Whether the group is compact (closed) or non-compact (open)

Every Lie algebra has exactly these three components. No more, no fewer. BLD works because it *is* Lie theory—the mathematical framework underlying all continuous symmetry.

---

## Cross-Domain Validation

The D×L scaling principle and compensation principle have been validated across multiple domains:

| Domain | L (geometric) | B (topological) | D×L Validated | Compensation |
|--------|---------------|-----------------|---------------|--------------|
| Variational Inference | Correlation ρ | Mode count | R² = 1.0 | N/A |
| Neural Networks | Receptive field | Decision boundaries | r = 0.91 | 6.2% diagonal |
| GPU Performance | Memory patterns | Cache/dispatch | ±15% error | Engine overlap |
| Thermodynamics | Fisher metric | Energy barriers | 10/10 tests | N/A |
| **Circuits** | **Capacitance** | **Threshold V_th** | **R² = 1.0 (6/6)** | **87.8%** |

---

## Implications

If this framework is correct:

1. **Structure is substrate-independent**: The same structural laws govern silicon, proteins, markets, and minds.

2. **Cost is alignment**: Performance, energy, fitness, likelihood—all manifestations of structural alignment.

3. **Complexity is structural**: P vs NP is a statement about what traversers physics permits, not about cleverness of algorithms.

4. **Physics is a traverser**: The laws of physics are the traverser structure that reality uses to process configurations.

5. **Experience is alignment**: What it feels like to be a structure aligning with itself and its environment.

6. **Thermodynamics is geometric**: The second law is not a postulate—it's a theorem about manifold exploration. Entropy is the log of accessible structural volume. See [Thermodynamics](docs/mathematics/derived/thermodynamics.md).

---

## Documentation

### Theory
- [Core Thesis](docs/theory/README.md) — Foundational thesis
- [Discovery Method](docs/theory/discovery-method.md) — The three questions
- [Structural Language](docs/theory/structural-language.md) — B/L/D specification
- [Structure as State](docs/theory/structure-as-state.md) — Philosophical foundation
- [BLD as Language](docs/theory/bld-as-language.md) — Universal structural description

### Mathematics

**Foundations**:
- [Irreducibility Proof](docs/mathematics/foundations/irreducibility-proof.md) — Why exactly three primitives
- [BLD Calculus](docs/mathematics/foundations/bld-calculus.md) — Formal operations
- [Compensation Principle](docs/mathematics/foundations/compensation-principle.md) — L compensates B, not vice versa

**Lie Theory**:
- [Lie Correspondence](docs/mathematics/lie-theory/lie-correspondence.md) — **BLD = Lie theory** (verified)
- [Constructive Lie](docs/mathematics/lie-theory/constructive-lie.md) — Alignment as Lie homomorphism
- [Boundary Derivation](docs/mathematics/lie-theory/boundary-derivation.md) — B from two traversers and SPD curvature
- [Why Lie Theory](docs/mathematics/lie-theory/why-lie-theory.md) — The connection explained

**Derived Results**:
- [Performance Theorem](docs/mathematics/derived/performance-theorem.md) — Traverser comparison from structure alone
- [Thermodynamics](docs/mathematics/derived/thermodynamics.md) — Second law derived from manifold geometry
- [Manifold Foundations](docs/mathematics/derived/manifold-foundations.md) — Structures as points, alignment as metric

### BLD Structures

Core theory expressed in BLD itself:
- [theory.bld](theory.bld) — Top-level structure
- [questions.bld](questions.bld) — The three questions
- [formula.bld](formula.bld) — Cost and link formulas
- [principles.bld](principles.bld) — D×L scaling and compensation

Domain-specific:
- [domains/](domains/) — VI, neural, circuits, thermo, gpu, proteins, physics
- [math/](math/) — Foundations, Lie theory, derived results
- [examples/](examples/) — ZIP, JPEG, compiler, music

---

## Related Repositories

- [bld](https://github.com/Experiential-Reality/bld) — BLD compiler and runtime
- [bld-py](https://github.com/Experiential-Reality/bld-py) — Python interpreter for BLD
- [bld-claude](https://github.com/Experiential-Reality/bld-claude) — Claude skill for BLD analysis

---

## License

**Documentation** (docs/, *.md): [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

**BLD Files** (*.bld): [MIT License](LICENSE)

---

*"We started by trying to predict GPU memory bank conflicts. We ended up rediscovering Lie theory—the mathematical framework underlying all continuous symmetry. The same three primitives that predict GPU performance are the same three primitives that define Lie algebras. That's either a coincidence or a hint about what structure really is."*
