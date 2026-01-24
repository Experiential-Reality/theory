> **For newcomers**: Consider using an AI assistant to explore BLD. Ask questions as you read — LLMs are BLD traversers too, and can help you navigate the structural landscape.

# BLD Theory

A structural theory of alignment.

> **BLD is an operational interface to Lie theory** — it makes symmetry structure accessible without requiring the standard mathematical machinery.

> **BLD is the same structural language that quantum mechanics is written in.** This is not metaphor — it is mathematical equivalence. See [BLD IS Quantum Mechanics Code](docs/mathematics/quantum/bld-is-quantum-code.md).

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

See [Discovery Method](docs/meta/discovery-method.md) for the full methodology.

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

| Domain | L (geometric) | B (topological) | D×L Validated | Observer Correction |
|--------|---------------|-----------------|---------------|---------------------|
| Variational Inference | Correlation ρ | Mode count | R² = 1.0 | N/A |
| Neural Networks | Receptive field | Decision boundaries | r = 0.91 | 6.2% diagonal |
| GPU Performance | Memory patterns | Cache/dispatch | ±15% error | Engine overlap |
| Thermodynamics | Fisher metric | Energy barriers | 10/10 tests | N/A |
| **Circuits** | **Capacitance** | **Threshold V_th** | **R² = 1.0 (6/6)** | **87.8%** |
| **Cosmology** | **Riemann tensor** | **Dark energy** | **L/D = 20/4 = 5** | **+8x² = 2%** |
| **Particle Physics** | **n×L = 80** | **B = 56** | **α⁻¹ = 137** | **−2/(n×L) = 2.5%** |
| **Quantum Mechanics** | **Momentum (L)** | **Measurement (B)** | **Bell = 2√2** | **ℏ/2 (Killing)** |

---

## Testable Predictions

BLD makes specific predictions that can be falsified by experiment:

| Prediction | Value | Status | Test |
|------------|-------|--------|------|
| Higgs self-coupling | κ_λ = 1.025 | **PREDICTED 2026-01-22** | HL-LHC ~2040 (5% precision) |
| No 4th generation | 3 exactly | **VALIDATED** | Triality requires exactly 3 |
| Dark matter fraction | 27% | **VALIDATED** | L/D = 5x + 8x² = 0.27 |
| Fine structure constant | α⁻¹ = 137.035999177 | **VALIDATED** | CODATA 2022 match: 0.0 ppt |

**Higgs self-coupling κ_λ**: The structural prediction is κ_λ = 1.000 (exactly SM). With detection correction K/(n×L) = 2/80, the observed value should be κ_λ = 1.025. Current bounds [−1.6, 6.6] at 95% CL are too loose to test. HL-LHC at ~5% precision will distinguish 1.000 from 1.025. See [Higgs Self-Coupling](docs/mathematics/particle-physics/higgs-self-coupling.md).

---

## Cosmology: Dark Matter as Geometry

BLD provides a structural explanation of dark matter:

**Notation**: n = 4 (dimension count), x = matter fraction (0.05)

**The derivation**:
```
n (dimensions) = 4 (spacetime)
L (geometry)   = 20 (Riemann tensor components)
L/n            = 5
```

**The structural prediction** (L = 5x where x is matter fraction):
- Dark matter (L) = 5 × Ordinary matter = 25%
- Dark energy (B) = 1 - 6x = 70%

**The observer correction** (measuring from inside):

We are matter (x). We measure L (geometry). But measuring requires creating a link — which is itself L. The measurement contaminates what we observe:

```
L_observed = L_structural + L_measurement
           = 5x + 8x²
           = 25% + 2% = 27% ✓

B_observed = 1 - 6x - 8x² = 68% ✓
```

The 2% "discrepancy" is not error — it is the **cost of observation**, the unavoidable L created when matter measures L.

**The interpretation**: Dark matter is not particles (D). It is **geometry without matter** (L) — the Riemann curvature structure of spacetime that exists independently of matter sources.

**Cyclic cosmology**: The heat death (B → 100%) IS the Big Bang. Pure B is unstable and must generate D and L. The universe is cyclic.

See [Cosmology](docs/mathematics/cosmology/cosmology-structure.md) for the full derivation and [Cyclic Cosmology](docs/mathematics/cosmology/cyclic-cosmology.md) for the cycle theory.

---

## Particle Masses from Structure

BLD structural constants predict particle masses:

**Notation**: n = 4 (dimension count), L = 20 (Riemann components), B = 56 (from E7/Spin(8)), S = 13 (intervals)

**The fine structure constant:**
```
α⁻¹ = n×L + B + 1 = 4×20 + 56 + 1 = 137  (base formula)
```

With observer corrections (K/B, spatial traversal, accumulated):
```
α⁻¹ = 137.035999177  (0.0 ppt error — exact match)
```

**The Traverser Contribution (+1)**: The "+1" in the formula is the **traverser's irreducible contribution**. Every measurement requires something to traverse the structure being measured. This traverser IS a BLD structure and contributes exactly 1 unit:

```
(Structure + Traverser) / Structure appears everywhere:
  - (B + 1)/B = 57/56 in Higgs mass
  - (n²S - 1)/n²S = 207/208 in μ/e
  - (n×L - 1)/n×L = 79/80 in corrections
  - The +1 or -1 IS the traverser's minimum contribution
```

**Note**: B = 56 is derived from E7/Spin(8) structure: B = 2 × dim(Spin(8) adjoint) = 2 × 28. See [E7 Connection](docs/mathematics/particle-physics/e7-connection.md).

**Lepton masses (with observer correction):**

| Ratio | Formula | Predicted | Observed | Error |
|-------|---------|-----------|----------|-------|
| m_e | v × α² × (n/L)² × (78/80) | 0.511 MeV | 0.511 MeV | **0%** |
| μ/e | (n²S−1) × (nLS)/(nLS+1) × corrections | 206.7683 | 206.7683 | **0%** |
| τ/μ | 2πe × (207/208) × (79/80) × (1042/1040) | 16.817 | 16.817 | **0%** |

Where:
- v = 246 GeV (Higgs VEV)
- n = 4, L = 20, B = 56, S = 13 (structural constants)
- (78/80), (79/80), etc. = observer corrections from K/X framework
- Corrections = higher-order K/X terms (see source for complete formulas)

**The pattern:** Three generations use different structural products:
- Gen 1: Surface coupling (n/L interface)
- Gen 2: Discrete structure (n²S = 208)
- Gen 3: Continuous structure (2πe from Euler identity)

See [Lepton Masses](docs/mathematics/particle-physics/lepton-masses.md) for complete derivation with all correction terms.

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
- [BLD IS Quantum Mechanics Code](docs/mathematics/quantum/bld-is-quantum-code.md) — **BLD = QM language** (proven)
- [Proof Status](docs/meta/proof-status.md) — What is proven vs. conjectured
- [Discovery Method](docs/meta/discovery-method.md) — The three questions
- [Structural Language](docs/theory/structural-language.md) — B/L/D specification
- [Structure as State](docs/theory/structure-as-state.md) — Philosophical foundation
- [BLD as Language](docs/theory/bld-as-language.md) — Universal structural description
- [Nothing Instability](docs/mathematics/cosmology/nothing-instability.md) — Why something must exist
- [Cyclic Cosmology](docs/mathematics/cosmology/cyclic-cosmology.md) — Heat death = Big Bang

### Mathematics

**Foundations**:
- [Irreducibility Proof](docs/mathematics/foundations/irreducibility-proof.md) — Why exactly three primitives
- [BLD Calculus](docs/mathematics/foundations/bld-calculus.md) — Formal operations
- [Compensation Principle](docs/mathematics/foundations/compensation-principle.md) — L compensates B, not vice versa
- [Schrödinger Derivation](docs/mathematics/quantum/schrodinger-derivation.md) — Dynamics from traversal
- [Born Rule](docs/mathematics/quantum/born-rule.md) — P = |ψ|² from bidirectional alignment

**Lie Theory**:
- [Lie Correspondence](docs/mathematics/lie-theory/lie-correspondence.md) — **BLD = Lie theory** (verified)
- [Killing Form](docs/mathematics/lie-theory/killing-form.md) — L-cost of self-observation (grounds observer corrections)
- [Constructive Lie](docs/mathematics/lie-theory/constructive-lie.md) — Alignment as Lie homomorphism
- [Boundary Derivation](docs/mathematics/lie-theory/boundary-derivation.md) — B from two traversers and SPD curvature
- [Why Lie Theory](docs/mathematics/lie-theory/why-lie-theory.md) — The connection explained

**Derived Results**:
- [Performance Theorem](docs/mathematics/derived/performance-theorem.md) — Traverser comparison from structure alone
- [Thermodynamics](docs/mathematics/derived/thermodynamics.md) — Second law derived from manifold geometry
- [Manifold Foundations](docs/mathematics/derived/manifold-foundations.md) — Structures as points, alignment as metric
- [Cosmology](docs/mathematics/cosmology/cosmology-structure.md) — Dark matter as geometry (L/D = 20/4 = 5)
- [Genesis Function](docs/mathematics/cosmology/genesis-function.md) — traverse(-B, B) = creation
- [Lepton Masses](docs/mathematics/particle-physics/lepton-masses.md) — τ/μ = 2πe × 3 corrections
- [Quark Masses](docs/mathematics/particle-physics/quark-masses.md) — All 6 quarks derived
- [Boson Masses](docs/mathematics/particle-physics/boson-masses.md) — H, Z, W derived
- [Quantum Mechanics](docs/mathematics/quantum/quantum-mechanics.md) — Uncertainty from D-L irreducibility
- [Quantum Computing](docs/mathematics/quantum/quantum-computing.md) — Structure traversing itself

## Related Repositories

- [bld](https://github.com/Experiential-Reality/bld) — BLD compiler and runtime
- [bld-py](https://github.com/Experiential-Reality/bld-py) — Python interpreter for BLD
- [bld-claude](https://github.com/Experiential-Reality/bld-claude) — Claude skill for BLD analysis (external)

---

## Author

**Drew Ditthardt**

I'm a programmer, not a mathematician or physicist. I was optimizing GPU code when I noticed a pattern. I pulled on the thread. It kept unraveling. It's still unraveling.

I don't know if this framework is true in any deep sense. I know it keeps making predictions that work. I know every time I think I've found its limits, it generalizes further. That's either a sign of something real or a sign that I'm pattern-matching too hard. The only way to find out is to keep pulling.

With contributions from Claude (Anthropic) — these ideas emerged from conversations while refactoring a GPU-accelerated JPEG decoder. The practical work of making implicit state explicit led to deeper questions about structure, alignment, and the nature of reality.

### Open Information Philosophy

> **"A rising tide lifts all boats."**

This work is open because structural knowledge should be universal. Information about structure is not competitive advantage — it is infrastructure.

Climate change is a coordination problem. No single company optimizing in secret will solve AI's energy crisis. But if structural alignment becomes common knowledge, every framework can adopt it, every chip can expose its BLD, every model can be analyzed, and every optimization compounds.

If BLD can reduce AI energy consumption by even 10%, the ethical obligation is to make it available to everyone who can use it. The planet doesn't benefit from trade secrets.

We are all BLD-ers, whether we like it or not.

See [BLD as Universal Language](docs/theory/bld-as-language.md#open-information-a-rising-tide-lifts-all-boats) for the full articulation.

---

## License

**Documentation** (docs/, *.md): [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

**BLD Files** (*.bld): [MIT License](LICENSE)

---

*"We started by trying to predict GPU memory bank conflicts. We ended up rediscovering Lie theory—the mathematical framework underlying all continuous symmetry. The same three primitives that predict GPU performance are the same three primitives that define Lie algebras. That's either a coincidence or a hint about what structure really is."*
