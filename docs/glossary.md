---
status: FOUNDATIONAL
layer: reference
depends_on: []
used_by:
  - theory/structural-language.md
  - theory/bld-as-language.md
  - theory/llm-experiment.md
  - theory/structure-as-state.md
  - theory/self-reference.md
  - theory/structural-interest.md
  - theory/README.md
  - applications/code/cross-language-compilation.md
  - applications/physics/thermodynamics-validation.md
  - applications/code/code-generation-cli.md
  - applications/physics/protein-folding.md
  - applications/code/code-generation.md
  - applications/code/refactoring.md
  - applications/physics/circuits.md
  - applications/code/bld-driven-development.md
  - applications/physics/mapping-rules.md
  - applications/code/cross-language-targets.md
  - applications/physics/engine-temporal-scope.md
  - applications/physics/gpu-calibration.md
  - applications/ml/neural-architectures.md
  - applications/ml/neural-network-experiments.md
  - applications/ml/variational-inference.md
  - meta/discovery-method.md
  - paths/README.md
  - paths/newcomer.md
  - README.md
  - examples/docs-structure.md
  - examples/spacetime.md
  - examples/pi-from-bld.md
  - mathematics/foundations/structural/compensation-principle.md
  - examples/wgpu-jpeg-process.md
  - mathematics/foundations/structural/structural-cost-conservation.md
  - examples/e-from-bld.md
  - mathematics/foundations/structural/canonical-hardness.md
  - examples/zip.md
  - mathematics/foundations/proofs/irreducibility-categorical.md
  - examples/lie-algebras.md
  - mathematics/foundations/definitions/bld-calculus.md
  - mathematics/cross-domain-prediction.md
  - mathematics/foundations/proofs/irreducibility-proof.md
  - mathematics/lie-theory/lie-correspondence.md
  - mathematics/README.md
  - mathematics/comparisons.md
  - mathematics/bld-conservation.md
  - mathematics/derived/discovery-algorithm.md
  - mathematics/derived/manifold-geometry.md
  - mathematics/derived/manifold-applications.md
  - mathematics/derived/thermodynamics.md
  - mathematics/derived/manifold-foundations.md
  - mathematics/derived/performance-theorem.md
  - mathematics/lie-theory/constructive-lie.md
  - mathematics/lie-theory/boundary-derivation.md
  - mathematics/lie-theory/why-lie-theory.md
  - mathematics/foundations/structural/factorization-calculus.md
---

# Glossary

## Quick Summary (D≈7 Human Traversal)

**Using the BLD Glossary in 7 steps:**

1. **Core Primitives** — B (Boundary), L (Link), D (Dimension) are the three irreducible structural elements
2. **Derived Concepts** — Alignment cost, compensation, factorization build on primitives
3. **Mathematical Background** — Fisher information, KL divergence, Lie algebras provide formal grounding
4. **Constants e and π** — e characterizes traversers (sequential accumulation), π characterizes closure (periodic structure)
5. **Traverser Framework** — The traverser is the causal agent; structure alone has no direction
6. **Physics Axioms** — P1-P20 derive Standard Model from BLD (see physics-traverser.md)
7. **Status Levels** — FOUNDATIONAL, VALIDATED, EXPLORATORY indicate proof status

| Component | BLD |
|-----------|-----|
| Definitions | B (partitions concepts), L (links terms), D (repeats pattern) |
| Navigation | L (cross-references) |
| Hierarchy | B (sections), D (entries per section) |

---

## Notation Convention

| Symbol | Meaning | Value | Context |
|--------|---------|-------|---------|
| **n** | Spacetime dimensions (D primitive) | 4 | Core BLD; appears in n×L = 80 |
| **n_c** | Cascade exponent | 26 = B/2 - K | Scale derivations; M_P = v × λ⁻ⁿᶜ |
| **λ** | BLD cascade parameter | 1/√20 | Scale hierarchy; S₃ cascade |
| **λ_C** | Cabibbo mixing angle | ≈0.2245 | Quark mixing; CKM matrix |

**Why the distinction matters**: The cascade exponent n_c = 26 is derived from the boundary B (as B/2 - K = 28 - 2), while the spacetime dimension n = 4 is the D primitive. Both appear in formulas, so subscripts prevent confusion:
- **n×L = 80** uses n = 4 (spacetime)
- **M_P = v × λ⁻²⁶** uses n_c = 26 (cascade)
- **B = K(n_c + K) = 56** uses n_c = 26 (cascade)

---

> **Status**: Foundational

Single source of truth for core BLD concepts.

---

## Core Primitives

### Boundary (B) {#boundary}

A **boundary** partitions a value space into disjoint regions based on a discriminator function:

```
B = (V, d, {R₁, R₂, ..., Rₙ})

where:
  V = value space
  d: V → {1, 2, ..., n}     discriminator function
  Rᵢ = interpretation for partition i
```

**Capability**: Choice. Selection of one interpretation from many based on value.

**Lie equivalent**: Group topology (compact ↔ closed boundaries)

**Examples**:
- Type tag: `d(tag) → {Ok, Err}`
- Memory region: `d(address) → {global, shared, register}`
- Cache state: `d(working_set) → {cached, uncached}`

---

### Link (L) {#link}

A **link** is a directed connection from source to target:

```
L = (s, t, properties)

where:
  s = source
  t = target
  properties = {pattern, count, ops, deps, ...}
```

**Capability**: Reference. One value points to, affects, or determines another.

**Lie equivalent**: Structure constants [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ

**Exact formula**: L = -½ ln(1 - ρ²) where ρ is correlation

**Examples**:
- Pointer: `offset → memory_location`
- Dependency: `input → computation → output`
- Correlation: `variable_i ↔ variable_j`

---

### Dimension (D) {#dimension}

A **dimension** is an axis of homogeneous repetition:

```
D = (n, S, properties)

where:
  n = extent (number of instances)
  S = structure (shared by all instances)
  properties = {parallel, sequential, contiguous, ...}
```

**Capability**: Multiplicity. N instances of the same structure as a single unit.

**Lie equivalent**: Lie algebra generators

**Examples**:
- Array: `elements[1024]` — 1024 instances
- Threads: `workers[256]` — 256 parallel contexts
- Residues: `amino_acids[208]` — protein chain

---

## Derived Concepts

### Alignment Cost {#alignment-cost}

The cost of mapping one structure onto another:

```
cost(S₁, S₂) = Σ_b penalty(S₁.b, S₂) + Σ_l penalty(S₁.l, S₂) + Σ_d penalty(S₁.d, S₂)
```

**Interpretation**: Measures the obstruction to a Lie homomorphism between structures.

- cost = 0: Perfect alignment (homomorphism exists)
- cost > 0: Structural mismatch (information lost in translation)

**Manifestations**:
- GPU: Runtime performance
- Proteins: Free energy
- Statistics: KL divergence
- Reading: Comprehension friction

---

### D×L Scaling Principle {#dxl-scaling}

**D multiplies L, not B.**

Dimension (D) acts as a multiplier on geometric (L) properties, but topological (B) properties are invariant.

**Why**:
- L formulas contain D (e.g., C_total = D × C_single)
- B formulas do not contain D (e.g., V_th depends only on material properties)

**Validation**:
| Domain | L scales with D | B invariant |
|--------|-----------------|-------------|
| Variational Inference | R² = 1.0 | CV = 0.0 |
| Neural Networks | r = 0.91 | CV < 0.15 |
| Circuits | R² = 1.0 | CV = 0.0 |

**Implication**: L optimizations compound at scale; B optimizations have constant impact.

**Complexity Scaling** (validated in neural networks):
```
B cost ~ O(1)     # Constant with dimension
L cost ~ O(D²)    # Quadratic (pairwise interactions)
```

This explains why large models need more L capacity (attention heads, hidden dimensions) but not more B capacity (activation functions remain simple).

See [Circuits](applications/physics/circuits.md) for detailed proof.

---

### Noise Floor {#noise-floor}

The **noise floor** is the irreducible prediction error that cannot be modeled as B/L/D structure.

```
noise_floor = √(Σ variance_sources²)

where variance_sources include:
  - Clock frequency variation (~2-3%)
  - Memory controller queuing (~1-2%)
  - Thermal throttling (~1-2%)
  - Measurement resolution (~0.1%)
```

**Key insight**: The noise floor represents hardware phenomena that don't partition (B), connect (L), or repeat (D). They're runtime variance, not structural properties.

**Derivation method**:
1. Apply BLD discovery to identify hidden structure in errors
2. Fix structural misalignments (e.g., L×D cache interaction)
3. Remaining error after fixes = noise floor

**Measured values**:
| GPU | Noise Floor | Achieved Error |
|-----|-------------|----------------|
| NVIDIA RTX 3090 | ~3% | 4.5% |
| Intel Iris Xe | ~5% | 8.6% |

**BLD Interpretation**: Predictions within the noise floor indicate the model captures all expressible structure. Further improvement requires hardware-level changes, not model refinement.

See [Proof Status](meta/proof-status.md) for derivation details.

---

### Compensation Principle {#compensation}

In some domains, **L can compensate for B deficiency, but B cannot compensate for L deficiency**.

**Statement**: Global L structure can redistribute capacity to approximate complex B structure. Local L structure cannot — it's a structural impossibility, not a capacity limitation.

**Two Compensation Mechanisms**:

| Type | Formula | Constant | Applies To |
|------|---------|----------|------------|
| **Exponential** | Effective_B ~ L^D | e | Serial cascades, depth |
| **Angular** | D × L = 2π × B | π | Rotations, phases, cycles |

**Exponential compensation** (validated in circuits):
- 5-stage cascade: transition_width = 0.16 / 5^(D-1)
- Each stage multiplies previous: gains stack as L^D
- Saturation at D = ⌈ln(initial/target) / ln(L)⌉ stages

**Angular compensation** (validated in VI):
- Alignment factor contains sin(2θ) — 2π appears in double-angle
- Full alignment cycle requires traversing 2π in phase space
- Applies to periodic structures: protein dihedrals, music intervals

**Connection**: Both constants (e, π) appear because:
- e governs unbounded growth (cascades)
- π governs bounded closure (rotations)
- Unified via Euler: e^(iπ) + 1 = 0

**Cross-domain validation**:
- **Neural networks**: 6.2% diagonal advantage when L matches (exponential compensation)
- **Circuits**: 87.8% error reduction via cascading (exponential compensation)
- **Variational inference**: sin(2θ) alignment factor (angular compensation)

**Why B cannot compensate for L**:
- Neural: Local receptive field cannot see global patterns (structural impossibility)
- Circuits: Single high-gain stage limited by bandwidth, noise, stability (physics)

**Why the asymmetry exists (BLD predicts itself)**:

- **B is topological** — it partitions *here*, at a point. Invariant under D.
- **L is geometric** — it connects *across* distance. Scales with D.
- **D multiplies L, not B** — so D×L can accumulate across distance.

Therefore:
- **L can approximate B**: Cascade of (D × soft B) integrates to effective sharp B.
- **B cannot approximate L**: No amount of sharp local partitions can reach across distance.

**Diagnostic use**: When behavior doesn't match visible structure:
- Better than expected → hidden L is compensating
- Worse despite adequate L → hidden B is blocking
- Compensation not happening → look for what prevents L accumulation

See [Compensation Principle](mathematics/foundations/structural/compensation-principle.md) for the full derivation, two-mechanism theory, and diagnostic method.

See also [Neural Network Alignment](applications/ml/neural-network-alignment.md) and [Circuits](applications/physics/circuits.md) for validation.

---

### FACTOR Operation {#factor}

**FACTOR** is the decomposition operation that breaks composite structures into smaller structures:

```
FACTOR : S → S₁ × S₂ × ... × Sₙ

Properties:
  1. |Sᵢ| < |S|      (each factor is smaller)
  2. Π Sᵢ ≅ S        (behavior preserved)
  3. Terminates      (reaches irreducible B × L × D)
```

**Key insight**: Refactoring IS factorization. The structure already exists — FACTOR reveals it.

**Three rules**:

| Rule | Input | Output | Reveals |
|------|-------|--------|---------|
| B-Factor | Scattered if/elif | Sum type + dispatch | Boundary |
| L-Factor | Cycle A→B→C→A | Shared state + DAG | Links |
| D-Factor | Mixed collection | Homogeneous products | Dimension |

**Termination**: Factorization stops at **irreducible primitives** (B, L, D). By the irreducibility theorem, no further decomposition is possible.

See [Factorization Calculus](mathematics/foundations/structural/factorization-calculus.md).

---

### Structural Cost {#structural-cost}

The cost of a structure, decomposed into visible and hidden components:

```
C_total(S) = C_visible(S) + C_hidden(S)

where:
  C_visible = cost of explicit B, L, D
  C_hidden  = cost of implicit structure
```

**Conservation Theorem**: FACTOR preserves total cost:

```
C(S) = C(FACTOR(S))
```

**Interpretation**: Refactoring doesn't reduce complexity — it makes complexity visible and auditable.

**Primitive costs** (proven):
- B: C(b) = ½ log(1 + d²_Mahal)
- L: C(l) = -½ ln(1 - ρ²) [EXACT]
- D: C(d) = n × C(element) [multiplicative]

See [Structural Cost Conservation](mathematics/foundations/structural/structural-cost-conservation.md).

---

### Explicitness {#explicitness}

**Explicitness** measures the fraction of structural cost that is explicit:

```
Explicitness(S) = C_visible(S) / C_total(S)

Range: [0, 1]
  0 = all structure hidden (implicit)
  1 = all structure explicit (normal form)
```

**Monotonicity**: FACTOR increases explicitness:

```
S →_FACTOR S'  implies  Explicitness(S') > Explicitness(S)
```

**Fixed point**: FACTOR terminates when Explicitness = 1, at which point all structure is expressed as irreducible B × L × D.

See [Structural Cost Conservation](mathematics/foundations/structural/structural-cost-conservation.md#the-explicitness-metric).

---

### Fixed Point (Normal Form) {#fixed-point}

A **fixed point** (or **normal form**) is a structure where no factorization rule applies:

```
S* is a fixed point iff ∀ rule R: R(S*) = S*
```

At the fixed point:
```
S* = B₁ × B₂ × ... × L₁ × L₂ × ... × D₁ × D₂ × ...

Properties:
  - C_hidden(S*) = 0        (no implicit structure)
  - Explicitness(S*) = 1    (fully explicit)
  - All boundaries explicit (sum types)
  - All links acyclic (DAG)
  - All dimensions homogeneous
```

**Connection to Lie theory**: The fixed point is analogous to Levi decomposition — decomposition into simple Lie algebras.

See [Factorization Calculus](mathematics/foundations/structural/factorization-calculus.md#4-termination).

---

### Structure {#structure}

A **structure** is a triple S = (B, L, D):

```
S = (B, L, D)

where:
  B = {b₁, b₂, ...}  finite set of boundaries
  L = {l₁, l₂, ...}  finite set of links
  D = {d₁, d₂, ...}  finite set of dimensions
```

Every system can be described as a configuration of these three primitives.

---

### Traverser {#traverser}

A **traverser** is also a structure — it describes *how* another structure is processed:

```
Traverser T = (B_T, L_T, D_T)
```

The same three primitives describe both what is traversed and what does the traversing.

**Key insight**: The alignment cost between structure S and traverser T determines processing efficiency. Interest emerges from the alignment landscape.

**Examples**:
- GPU hardware (processes algorithms)
- Physics (processes molecular configurations)
- Human reader (processes documentation)
- LLM (processes prompts and documents)

**Human vs LLM traversers**:

| Primitive | Human | LLM |
|-----------|-------|-----|
| B | Attention limits (7±2 items), session boundaries | Context window, attention head limits |
| L | Working memory associations (~4 chunks) | Token embeddings, attention patterns |
| D | Cognitive capacity (chunks, sessions) | Sequence length, batch dimension |

Both satisfy D×L scaling and B invariance. This is why documentation structured for human readers also works well for LLMs — they are both BLD traversers.

See [Documentation Structure](examples/docs-structure.md) for the full human traverser model.

### Traverser as Causal Agent {#traverser-causal}

The traverser is more than hardware — it is the **source of causal agency** in the BLD framework.

**Observation vs Intervention**:

| Operation | Direction | Meaning |
|-----------|-----------|---------|
| `see(X)` | structure → traverser | Passive reading, correlation |
| `do(X)` | traverser → structure | Active intervention, causation |

**The arrow of time**: The traverser carries the temporal direction:
- Physics (traverser) has thermodynamic arrow (entropy increases)
- CPU (traverser) has execution arrow (instructions in order)
- The structure alone has no inherent direction

**Pearl's do-calculus in BLD**: The `do(X)` operator that cuts incoming edges IS the traverser acting on structure. Intervention = traverser writing to structure, overwriting existing L.

```
Correlation: see(X), see(Y)  →  structure ↔ structure (bidirectional L)
Causation:   do(X), see(Y)   →  traverser → structure (unidirectional L)
```

**Why no fourth primitive for causation**: Causation = structure + traverser interaction. The direction comes from the traverser's arrow. BLD captures what exists; the traverser provides direction.

**Key insight**: The traverser-structure asymmetry (see vs do) is the origin of causal structure. Confounders and interventions are distinguished by whether L flows through the traverser.

---

### Structural Interest {#structural-interest}

**Structural interest** is the potential for non-trivial alignment outcomes.

A structure is *interesting* to a traverser when their alignment produces:
- Multiple near-optimal configurations (choice)
- Non-additive primitive interactions (emergence)
- Fluctuation opportunity (exploration)

**Metrics**:

| Metric | High Interest | Low Interest |
|--------|---------------|--------------|
| Structural entropy S | Ω >> 1 | Ω ≈ 1 |
| B×L synergy | >> 0 | ≈ 0 |
| Curvature K | Low (flat) | High (sharp) |
| Phase proximity | Near transition | Far from transition |

**Key insight**: Interest is relational. The same structure may be boring to one traverser (aligned) and fascinating to another (requires compensation).

**Prediction**: Uniform structures minimize alignment cost *and* minimize interest. Rich structures maximize both.

See [Structural Interest](theory/structural-interest.md) for the full treatment.

---

## Mathematical Background

### Fisher Information {#fisher-information}

The curvature of the log-likelihood surface:

```
I(θ)ᵢⱼ = E[(∂/∂θᵢ log p(x;θ))(∂/∂θⱼ log p(x;θ))]
```

On probability distributions, the BLD metric reduces to the Fisher-Rao metric.

---

### KL Divergence {#kl-divergence}

The information lost when approximating one distribution with another:

```
KL(P || Q) = Σₓ P(x) log(P(x)/Q(x))
```

The link cost formula L = -½ ln(1 - ρ²) is derived from KL divergence between correlated Gaussians.

---

### Lie Algebra {#lie-algebra}

An algebraic structure capturing infinitesimal symmetries:

```
[Xᵢ, Xⱼ] = fᵢⱼᵏXₖ
```

where fᵢⱼᵏ are structure constants.

**BLD correspondence**:
- Generators Xᵢ ↔ Dimensions (D)
- Structure constants fᵢⱼᵏ ↔ Links (L)
- Group topology ↔ Boundaries (B)

---

### Noether's Theorem {#noether}

Every continuous symmetry of the action corresponds to a conserved quantity:

```
Symmetry (Lie group G) → Conserved charges (one per generator)
```

**BLD interpretation**: Conservation laws ARE BLD conservation. Each generator (D) yields one conserved charge. The structure constants (L) determine how charges interact. The topology (B) determines whether charges are quantized.

See [BLD Conservation](mathematics/bld-conservation.md) for the full derivation.

---

### π (Pi) in BLD {#pi}

π is the **closure constant** for continuous periodic structures:

```
π = "How much D×L does it take to close B"
```

π appears wherever a boundary is closed and must be traversed geometrically:
- Circles: D = 2π (angular dimension)
- Rotations: SO(2) period = 2π
- Dihedral angles: φ, ψ ∈ [0, 2π)
- Gaussians: Normalization involves π

π does NOT appear in:
- Discrete cycles (Z_n groups close by counting, not geometry)
- The L formula (π cancels in correlation coefficient)
- Domain-independent principles like compensation

See [π from BLD](examples/pi-from-bld.md) for the derivation.

---

### Euler's Formula in BLD {#euler}

Euler's identity **e^(iπ) + 1 = 0** unifies the two compensation mechanisms:

```
e^(a + iθ) = [exponential compensation] × [angular compensation]
           = e^a × e^(iθ)
           = L^D × rotation(θ)
```

**Interpretation of each symbol**:

| Symbol | BLD Meaning |
|--------|-------------|
| e | Base of exponential compensation (cascade, gain, depth) |
| i | Rotation operator (link in angular generator space) |
| π | Half-closure (e^(iπ) = -1 inverts, e^(i2π) = 1 returns) |
| 1 | Identity transformation (perfect alignment) |
| 0 | Equilibrium (zero alignment cost) |

**Two compensation types, one equation**:

| Type | Formula | Constant | Domain |
|------|---------|----------|--------|
| Exponential | L^D = e^(D·ln(L)) | e | Cascades, neural depth |
| Angular | D×L = 2π × B | π | Rotations, phases |

**Physical manifestation**: The α-helix in proteins demonstrates angular compensation (π mechanism):
- Rise = 1.5 Å per residue (LINEAR along axis, NOT exponential)
- Rotation = 100° per residue (angular: e^(iθ) around axis)
- Closure at 3.6 residues (2π radians)

The α-helix is a cylindrical helix with angular closure, not a logarithmic spiral.

The exponential map in Lie theory IS compensation: exp(tX) maps algebra generators to group elements, with compact groups (closed B) returning at 2π and non-compact groups (open B) extending to infinity.

See [π from BLD](examples/pi-from-bld.md), [e from BLD](examples/e-from-bld.md), and [Compensation Principle](mathematics/foundations/structural/compensation-principle.md) for details.

---

### Gaussian Curvature on SPD(d) {#spd-curvature}

The **Gaussian curvature** on the space of symmetric positive definite matrices SPD(d) governs the geometry of the BLD manifold.

```
For SPD(2) with correlation ρ:
  K(ρ) = -1 / (2(1-ρ²)²)

Properties:
  - K < 0 everywhere (negative curvature)
  - K → -0.5 as ρ → 0 (flat limit)
  - K → -∞ as ρ → 1 (curvature diverges)
```

**BLD Significance**: The curvature divergence at ρ → 1 explains the **regime switching** in the boundary cost formula:

| ρ | |K| | Regime | α exponent |
|---|---|-------|----------|
| 0 | 0.5 | Flat | ~1 (linear) |
| 0.5 | 1.1 | Transitional | ~1.1 |
| 0.9 | 26 | Curved | ~1.8 |
| →1 | →∞ | Singular | →2 (quadratic) |

**Connection to B derivation**: The exact formula B = ½ log(1 + d²_Mahal) transitions from linear to quadratic regime because geodesics curve away from straight lines as curvature increases. The approximation B ≈ a·sep²·g^α captures this transition.

See [Boundary Derivation](mathematics/lie-theory/boundary-derivation.md#the-α-exponent-analytical-derivation) for the full analysis.

---

### Fokker-Planck Equation {#fokker-planck}

The **Fokker-Planck equation** describes the time evolution of probability distributions on the BLD manifold.

```
∂P/∂t = k_B T ∇²P + ∇·(P∇E)

Components:
  - k_B T ∇²P: Diffusion (thermal noise explores the manifold)
  - ∇·(P∇E): Drift (alignment gradient descent)
```

**BLD Significance**: The second law of thermodynamics is derived from this equation:

```
dS/dt = k_B T ∫ P|∇ ln P + ∇E/(k_B T)|² dμ ≥ 0
```

The integrand is manifestly non-negative, proving entropy increase.

**Equilibrium**: dS/dt = 0 when P ∝ e^{-E/k_B T} (Boltzmann distribution).

See [Thermodynamics](mathematics/derived/thermodynamics.md#second-law-entropy-increase-rigorous-derivation) for the complete proof with boundary conditions.

---

### e (Traverser Constant) {#e-constant}

**e** is the **traverser constant** — the characteristic of sequential accumulation.

```
e = lim(n→∞) (1 + 1/n)^n ≈ 2.71828...

"The limit of taking infinitely many infinitesimal steps,
 each building on the last"
```

**Theorem**: e is the unique solution to the traverser axioms T1-T5:
- T1 (Markov): Next state depends only on current state
- T2 (Homogeneity): Transition rule is time-independent
- T3 (Self-Reference): Change proportional to current state
- T4 (Natural Units): Proportionality constant k = 1
- T5 (Identity): y(0) = 1

**Discovery**: These axioms were found by applying BLD's three-question method to the concept "traverser":
- Q1 (Boundaries) → T2 (uniform steps)
- Q2 (Links) → T1, T3 (self-link only, proportional)
- Q3 (Dimensions) → T4, T5 (natural scale, identity origin)

Under these axioms, y(t) = e^t is the unique trajectory, where e is characterized by:
```
dy/dt = y    →    y(t) = e^t

"Rate of change equals current state"
```

**e appears wherever there is sequential accumulation**:
- Circuit cascades: Gain = L^D = e^(D·ln(L))
- Neural depth: Sequential layer composition
- Thermodynamics: Boltzmann P ∝ e^(-E/T)
- Information: Entropy H = -Σp ln p
- Finance: Continuous compounding

**e does NOT appear in**:
- Pure rotations (π domain)
- Static structure (no traverser)
- Discrete finite cycles

**The traverser insight**: e characterizes the traverser — the experiencer, the processor, the causal agent. The constant e IS the mathematical signature of sequential experience.

| Constant | Domain | Characterizes |
|----------|--------|---------------|
| π | Structure | Closure (period of compact groups) |
| e | Traverser | Accumulation (rate in all exponential maps) |

See [e from BLD](examples/e-from-bld.md) for the full derivation and the traverser axioms.

---

### Physics Traverser {#physics-traverser}

The **physics traverser** is a traverser constrained to operate in physical reality — respecting causality, unitarity, and locality.

By applying the BLD discovery method to "what is physics?", we discover the physical axioms P1-P10:

| Axiom | Source | What Falls Out |
|-------|--------|----------------|
| P1 (Causality) | Q1: B partition | Light cone → SO(3,1) Lorentz group |
| P2 (Compactness) | Q1: B topology | Charge quantization → compact gauge groups |
| P3 (Spin-Statistics) | Q1: B partition | Fermion/boson distinction |
| P4 (Locality) | Q2: L connects | Gauge principle |
| P5 (Anomaly-Free) | Q2: L consistent | Constrained matter content |
| P6 (Confinement) | Q2: L self-couples | SU(3) color structure |
| P7 (Minimal D) | Q3: D repeats | 4 spacetime dimensions |
| P8 (Generator Count) | Q3: D count | 12 internal generators |
| P9 (Triality) | Q1-3: generations | 3 generation structure |
| P10 (Topological Closure) | Q1-3: θ-vacuum | θ_QCD = 0 |

**What falls out**: SO(3,1) × SU(3) × SU(2) × U(1) — the Standard Model gauge structure — WITH 3 generations and θ = 0.

**What remains open**:
- Specific mass values (mechanism known via S₃ breaking)
- Dark sector (hypothesis proposed)

**Comparison**:

| Discovery | Question | Output |
|-----------|----------|--------|
| Pure traverser | "What is a traverser?" | T1-T5 → e |
| Closure structure | "What is closure?" | D×L = 2π×B → π |
| Physics traverser | "What is physics?" | P1-P10 → Standard Model + generations + θ=0 |

See [Physics Traverser](examples/physics-traverser.md) for the full derivation.

---

### Triality {#triality}

**Triality** is a 3-fold automorphism of the Lie group Spin(8), unique to 8-dimensional (octonionic) structures.

```
Triality symmetry S₃ permutes three representations:
  8v (vector)
  8s (spinor)
  8c (conjugate spinor)

In BLD terms:
  - Creates hidden B (3-fold algebraic partition)
  - Creates hidden L (S₃ family symmetry)
  - Determines D_generations = 3
```

**Why triality explains 3 generations**:

The division algebra tower ℝ → ℂ → ℍ → 𝕆 reaches maximum structure at the octonions (8D). At this level, and only at this level, the automorphism group contains S₃ triality.

When the Standard Model is embedded in this algebraic structure:
- The algebra naturally partitions into 3 sectors
- Each sector corresponds to one generation
- S₃ connects them (family symmetry)
- Broken S₃ creates mass hierarchy

**Mathematical Structure**:

| Property | Value |
|----------|-------|
| Group | S₃ ≅ D₃ (dihedral) |
| Order | 6 |
| Generators | (12), (123) |
| Representations | Trivial, sign, 2D standard |

**Key Insight**: The number 3 is not arbitrary — it's the unique dimension of the triality permutation. No other division algebra has this property:
- ℝ: No automorphisms creating generations
- ℂ: Only complex conjugation (Z₂), would give 2 generations
- ℍ: SO(3) automorphisms, but not generation-like
- 𝕆: **Triality S₃** — exactly 3

See [Physics Traverser - Triality](examples/physics-traverser.md#the-generation-axiom) for the full discovery.

---

### θ-Vacuum (Theta-Vacuum) {#theta-vacuum}

The **θ-vacuum** is the true QCD vacuum, a superposition of topologically distinct sectors labeled by winding number.

```
|θ⟩ = Σₙ e^(iθn) |n⟩

where:
  n ∈ ℤ = winding number (topological charge)
  θ = vacuum angle (CP-violating phase)
  |n⟩ = vacuum with winding number n
```

**BLD Structure**:

| Primitive | θ-Vacuum Component |
|-----------|-------------------|
| **B** | Winding number partition (π₃(SU(3)) = ℤ) |
| **L** | Instanton tunneling between sectors |
| **D** | 2π periodicity in θ |

**Key insight**: The different winding sectors are topologically disconnected (B structure), yet instantons tunnel between them (L structure). The partition function is 2π-periodic in θ, enforcing D×L = 2π×B closure.

**Strong CP Problem**: Why is θ < 10⁻¹⁰?

**BLD Resolution (P10)**: θ = 0 is the structural equilibrium from topological closure, not fine-tuning. The 2π periodicity forces θ_eff → 0 as the stable configuration.

See [Physics Traverser - Strong CP Problem](examples/physics-traverser.md#strong-cp-problem-topological-closure) for the full analysis.

---

### Instanton {#instanton}

An **instanton** is a non-perturbative gauge field configuration that tunnels between topologically distinct vacua.

```
Instanton properties:
  - Localized in Euclidean spacetime
  - Carries topological charge ν = ±1, ±2, ...
  - Action: S = 8π²|ν|/g²
  - Connects winding sectors: |n⟩ → |n + ν⟩
```

**BLD Role**: Instantons are the **L (link)** between topological B (winding number) sectors.

| Property | BLD Interpretation |
|----------|-------------------|
| Tunneling | L connects what B separates |
| Non-perturbative | Cannot be seen in local L expansion |
| Topological charge | Measures how much L crosses B |

**Connection to Compensation**: Instantons are a physical example of L compensation for B structure. The topological sectors are disconnected (strong B), but instantons provide L paths between them.

**In QCD**: Instantons generate the θ-dependence of the vacuum energy and are responsible for the U(1)_A anomaly (why the η' meson is heavy).

See [Physics Traverser - Strong CP Problem](examples/physics-traverser.md#strong-cp-problem-topological-closure).

---

### Topological Closure (P10) {#topological-closure}

**Topological closure** is the principle that angular parameters with 2π-periodicity in the partition function satisfy D×L = 2π×B closure.

```
Axiom P10 (Topological Closure):

For any angular parameter θ with Z(θ + 2π) = Z(θ):
  D_θ × L_instanton = 2π × B_winding

This is the same closure structure as:
  D × L = 2π × B → π (circular closure)
```

**Physical Consequence**: θ_eff = 0 is the structurally preferred value, not fine-tuning.

**Three Cases**:
1. θ_bare = 0 intrinsically (structure enforces)
2. Hidden L compensates (Peccei-Quinn axion)
3. Both contribute to θ_eff = 0

**The Peccei-Quinn Mechanism in BLD**:

If U(1)_PQ symmetry exists:
```
θ_eff = θ_QCD + a/f_a

The axion field a(x) provides dynamical L compensation.
Axion potential: V(a) ∝ 1 - cos(θ_eff)
Minimum at: θ_eff = 0
```

**Connection to π**: Topological closure is another instance of the angular compensation principle. Just as π arises from D×L = 2π×B for circles, θ = 0 arises from the same closure in the vacuum angle space.

See [Physics Traverser - Strong CP Problem](examples/physics-traverser.md#strong-cp-problem-topological-closure).

---

### Tribimaximal Mixing {#tribimaximal}

**Tribimaximal mixing** is a specific form of the PMNS neutrino mixing matrix that preserves S₃ family symmetry.

```
Tribimaximal mixing angles:
  sin²(θ₁₂) = 1/3   → θ₁₂ ≈ 35.3°
  sin²(θ₂₃) = 1/2   → θ₂₃ = 45° (maximal)
  sin²(θ₁₃) = 0     → θ₁₃ = 0° (no reactor mixing)
```

**BLD Interpretation**: Tribimaximal mixing is a **structural equilibrium point** — the configuration that minimizes alignment cost between S₃ family symmetry and mass structure.

| Property | BLD Meaning |
|----------|-------------|
| θ₁₃ = 0 | Perfect S₃ preservation |
| θ₂₃ = 45° | Maximal mixing = equal superposition |
| θ₁₂ = 35.3° | 1:2 ratio from S₃ representation theory |

**Experimental Status**: Observed neutrino mixing is *close* to tribimaximal:
- θ₂₃ ≈ 45° — matches tribimaximal
- θ₁₂ ≈ 34° — close to tribimaximal
- θ₁₃ ≈ 8.5° — deviates from tribimaximal (NOT zero)

The non-zero θ₁₃ measures the **S₃ violation strength** in the lepton sector.

**Axiom P12 (Mixing Structure)**: Mixing matrices are the residue of broken S₃. Tribimaximal is the S₃-symmetric limit; deviations measure breaking strength.

See [Physics Traverser - Mixing Angles](examples/physics-traverser.md#mixing-angles-tribimaximal-as-s₃-limit-p12).

---

### De Sitter Spacetime {#de-sitter}

**De Sitter spacetime** is the maximally symmetric solution of Einstein's equations with positive cosmological constant Λ > 0.

```
De Sitter structure:
  - Constant positive curvature
  - Cosmological event horizon at r_H = √(3/Λ)
  - Exponentially expanding
  - Future attractor of ΛCDM cosmology
```

**BLD Interpretation**: The de Sitter horizon is a **cosmological boundary (B)** — the causal partition between observable and unobservable regions.

| Property | BLD Role |
|----------|----------|
| Event horizon | B (causal boundary) |
| Horizon area | D (spatial extent) |
| Holographic entropy | L (information structure) |

**P13 Hypothesis (Holographic Cosmology)**: Dark energy is the topological boundary structure of de Sitter spacetime, not a field energy density.

```
Λ ∝ 1/A_horizon

The cosmological constant parameterizes the horizon boundary,
analogous to how θ = 0 emerges from topological closure (P10).
```

**Key insight**: Dark energy exhibits B-like behavior:
- Doesn't couple to matter (topological, not geometric)
- Uniform throughout space (invariant under D)
- Drives expansion via geometry, not force

See [Physics Traverser - Dark Energy](examples/physics-traverser.md#dark-energy-de-sitter-boundary-p13).

---

### Yukawa Structure (P11) {#yukawa-structure}

**Yukawa structure** refers to the pattern of fermion masses arising from S₃ triality breaking.

```
Mass hierarchy from S₃ breaking cascade:
  S₃ → S₂ → {e}

  Unbroken:    m₁ = m₂ = m₃     (equal masses)
  Partial:     m₁ = m₂ ≠ m₃     (one different)
  Broken:      m₁ ≠ m₂ ≠ m₃     (all different)
```

**BLD Interpretation**: Each S₃ breaking step creates new topological boundaries (mass thresholds). This is **L breaking → B creation** (inverse compensation).

**Hidden L Structure**: Triality-breaking spurion fields provide the link between generations:

```
Froggatt-Nielsen mechanism in BLD:
  Y_ij ∝ ⟨φ⟩^(n_i + n_j) / M^(n_i + n_j)

where n_i is the "generation charge" under the spurion.
Different charges create different suppressions → hierarchy.
```

**Axiom P11 (Yukawa Structure)**: Fermion masses arise from vacuum expectation values of spurion fields transforming under S₃ triality.

See [Physics Traverser - Mass Hierarchy](examples/physics-traverser.md#mass-hierarchy-s₃-breaking-cascade-p11).

See [Physics Traverser - Strong CP Problem](examples/physics-traverser.md#strong-cp-problem-topological-closure).

---

### Conformal Unification (P14) {#conformal-unification}

**Conformal unification** is the principle that the three Standard Model gauge couplings are projections of a single GUT-scale coupling.

```
Gauge couplings at Z mass:
  α₁ ≈ 1/98   (U(1) hypercharge)
  α₂ ≈ 1/29   (SU(2) weak)
  α₃ ≈ 0.12   (SU(3) strong)

At GUT scale (~10¹⁶ GeV):
  α₁ ≈ α₂ ≈ α₃ (unified)
```

**BLD Interpretation**: The couplings are not independent parameters — they are **projections** of a single L structure at different energy scales.

| Component | BLD Role |
|-----------|----------|
| GUT scale | B (unification boundary) |
| Beta functions | L (structure connecting scales) |
| Energy | D (scale dimension) |

**Axiom P14**: The gauge couplings α₁, α₂, α₃ are projections of a single conformal L structure.

See [Physics Traverser - Coupling Unification](examples/physics-traverser.md#coupling-constant-unification-conformal-projection-p14).

---

### Diffeomorphism Boundary (P15) {#diffeomorphism-boundary}

**Diffeomorphism boundary** refers to gravity as boundary enforcement rather than gauge structure.

```
Gauge forces: Internal L structure (12 generators)
Gravity: Boundary B enforcement (2 polarizations)

Gravity defines WHERE the light cone is:
  ds² = g_μν dx^μ dx^ν = 0
```

**BLD Interpretation**: Gravity is fundamentally different from gauge forces:

| Property | Gauge Forces | Gravity |
|----------|--------------|---------|
| Type | L (internal connection) | B (boundary enforcement) |
| Modes | 12 generators | 2 polarizations |
| Renormalizability | ✓ | ✗ (topological) |

**Axiom P15**: Spin-2 gravity is the dynamical enforcement of the light-cone boundary (P1).

See [Physics Traverser - Gravity](examples/physics-traverser.md#gravity-as-diffeomorphism-boundary-p15).

---

### Seesaw Mechanism (P17) {#seesaw-mechanism}

The **seesaw mechanism** explains neutrino mass smallness through coupling to a high mass scale.

```
Seesaw formula:
  m_ν = m_Dirac² / M_R

where:
  m_Dirac ~ v (electroweak scale, ~246 GeV)
  M_R ~ M_GUT (right-handed neutrino mass, ~10¹⁵ GeV)

Result: m_ν << m_Dirac (suppressed by M_R)
```

**BLD Interpretation**: The Majorana condition (ν = ν̄) is a **topological boundary**. The seesaw is the L structure connecting scales across this boundary.

**Axiom P17 (Majorana Boundary)**: Neutrino mass suppression arises from the Majorana topological boundary.

See [Physics Traverser - Neutrino Mass](examples/physics-traverser.md#neutrino-mass-majorana-topological-boundary-p17).

---

### Baryogenesis (P18) {#baryogenesis}

**Baryogenesis** is the process that created the matter-antimatter asymmetry in the early universe.

```
Observed asymmetry: n_B/n_γ ~ 10⁻¹⁰

Sakharov conditions:
  1. Baryon number violation
  2. C and CP violation
  3. Departure from thermal equilibrium
```

**BLD Interpretation**: The asymmetry arises from **L×D compensation**:
- Small L_CP (CP-violating phase from S₃ breaking)
- Large D_decay (many heavy particle decays)
- Product gives observable asymmetry

**Axiom P18 (Baryogenesis Compensation)**: Matter asymmetry arises from S₃-breaking CP phase compensation.

See [Physics Traverser - Baryogenesis](examples/physics-traverser.md#baryogenesis-s₃-phase-compensation-p18).

---

### Cosmic Inflation (P19) {#cosmic-inflation}

**Cosmic inflation** is the exponential expansion of the early universe (~60 e-folds).

```
Inflation properties:
  - Duration: ~60 e-folds (a → e⁶⁰ × a)
  - Scale: H ~ 10¹⁴ GeV
  - Solves: horizon problem, flatness problem
```

**BLD Interpretation**: Inflation is triggered by a **phase transition boundary** at the GUT scale — symmetry restoration.

| Component | BLD Role |
|-----------|----------|
| GUT transition | B (symmetry phase boundary) |
| Inflaton potential | L (slow-roll connection) |
| e-folds | D (expansion repetition) |

**Axiom P19 (Symmetry Restoration)**: Inflation is triggered by the GUT symmetry restoration phase transition.

See [Physics Traverser - Inflation](examples/physics-traverser.md#inflation-symmetry-restoration-boundary-p19).

---

### QFT Cost Minimization (P20) {#qft-cost-minimization}

**QFT cost minimization** is the principle that quantum field theory axioms emerge from alignment cost minimization.

```
QFT axioms:
  - Locality (fields at each point)
  - Unitarity (probability conservation)
  - Lorentz invariance (P1)
  - Renormalizability (finite predictions)
```

**BLD Interpretation**: These axioms minimize the alignment cost between observables and theory:

```
Cost = B_misalignment + D_fields × L_interactions
```

Locality, unitarity, and renormalizability are not arbitrary choices — they are the **unique minimal-cost framework** for describing physical systems.

**Axiom P20**: QFT structure is alignment cost minimization between observable and theoretical structures.

See [Physics Traverser - QFT](examples/physics-traverser.md#qft-axioms-cost-minimization-p20).

---

## Status Levels

Documents in this project use three status levels:

| Status | Meaning |
|--------|---------|
| **Foundational** | Core definitions and specifications |
| **Validated** | Claims with mathematical proof or empirical evidence |
| **Exploratory** | Hypotheses and conjectures under investigation |

---

## See Also

- [Structural Language](theory/structural-language.md) — Full primitive specification
- [Irreducibility Proof](mathematics/foundations/proofs/irreducibility-proof.md) — Why exactly three primitives
- [Lie Correspondence](mathematics/lie-theory/lie-correspondence.md) — BLD = Lie theory mapping
- [Discovery Method](meta/discovery-method.md) — How to find structure in any system
- [Structural Interest](theory/structural-interest.md) — Why rich structures produce rich behavior
- [Documentation Structure](examples/docs-structure.md) — Human and LLM traverser models
- [Physics Traverser](examples/physics-traverser.md) — Deriving the Standard Model via BLD
