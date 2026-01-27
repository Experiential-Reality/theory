---
status: FOUNDATIONAL
depends_on:
  - ../mathematics/foundations/proofs/irreducibility-proof.md
---

# The BLD Discovery Method

> **Status**: Foundational

A constructive procedure for finding structure in any system.

## Summary

**Constructive procedure for finding structure:**

1. Lie theory inverted: given system → find structure — [Contribution](#the-contribution)
2. Q1: Where does behavior partition? → find B — [Three Questions](#the-three-questions)
3. Q2: What connects to what? → find L — [Three Questions](#the-three-questions)
4. Q3: What repeats? → find D — [Three Questions](#the-three-questions)
5. Output S=(B,L,D) is a Lie algebra configuration — [Output](#the-output)
6. How to recognize each primitive — [Recognize Primitives](#how-to-recognize-each-primitive)
7. Worked example: neural network architectures — [Worked Example](#worked-example-neural-network-architectures)

---

## The Contribution

**Lie theory** (1870s) is the mathematics of continuous symmetry. It's analytical: given a symmetry group, it tells you its properties.

**BLD** is constructive: given any system, it finds the structure—which turns out to be Lie structure.

```
Lie Theory:  GIVEN structure → analyze properties
BLD Method:  GIVEN any system → FIND structure
```

The mathematics is known. The **method of finding it** is the contribution.

---

## The Three Questions

To find structure in any system, ask three questions:

### Question 1: Where does behavior partition?

**Ask**: "What values cause different interpretations or behaviors?"

**Look for**:
- Conditionals (`if x > 0`, `switch`, `match`)
- Type tags (discriminated unions, enum variants)
- State boundaries (mode changes, phase transitions)
- Thresholds (activation functions, decision boundaries)

**Output**: Boundaries B = {b₁, b₂, ...}

**Example (code)**:
```python
match header.signature:
    case 0x504B0304: parse_local_file()
    case 0x504B0102: parse_central_dir()
    case 0x504B0506: parse_end_record()
```
→ Boundary on `signature` with 3 partitions.

**Example (neural net)**:
```
ReLU(x) = max(0, x)
```
→ Boundary at x=0 partitioning into {negative, non-negative}.

### Question 2: What connects to what?

**Ask**: "What references, affects, or depends on what?"

**Look for**:
- Pointers, offsets, indices (direct reference)
- Dependencies (A must complete before B)
- Correlations (changes in A correlate with changes in B)
- Forces, interactions (A affects B's state)

**Output**: Links L = {l₁, l₂, ...}

**Example (code)**:
```python
data = buffer[header.offset : header.offset + header.length]
```
→ Links from `offset` and `length` to data region.

**Example (neural net)**:
```
y = W @ x + b
```
→ Links from each input dimension to each output dimension (weight matrix).

### Question 3: What repeats?

**Ask**: "What has multiple homogeneous instances?"

**Look for**:
- Arrays, lists, sequences (explicit repetition)
- Loops, iterations (temporal repetition)
- Parallel instances (concurrent repetition)
- Layers, levels (hierarchical repetition)

**Output**: Dimensions D = {d₁, d₂, ...}

**Example (code)**:
```python
for block in blocks:  # dimension: blocks
    for pixel in block.pixels:  # dimension: pixels
        process(pixel)
```
→ Two nested dimensions.

**Example (neural net)**:
```
batch of 32 samples, each 784 pixels → 128 hidden → 10 classes
```
→ Dimensions: batch (32), input (784), hidden (128), output (10).

---

## The Output

After asking the three questions, you have:

```
Structure S = (B, L, D)

Where:
  B = {boundaries}   → partitions behavior space
  L = {links}        → connects components
  D = {dimensions}   → provides multiplicity
```

**This IS a Lie algebra configuration**:
- D = generators (directions of transformation)
- L = structure constants (how generators interact: [Dᵢ, Dⱼ] = Lᵢⱼᵏ Dₖ)
- B = topology (compact/closed vs non-compact/open)

See [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md).

---

## How to Recognize Each Primitive

### Boundary vs Link

**Boundary**: Value → interpretation mapping (one-to-many)
```
signature → {local_file | central_dir | end_record}
```

**Link**: Value → value mapping (one-to-one)
```
offset → memory_location
```

**Key difference**: Boundaries select among alternatives. Links reference specific targets.

### Link vs Dimension

**Link**: Connects two specific things
```
pointer → target
```

**Dimension**: Groups many homogeneous things
```
array[N] of identical structure
```

**Key difference**: Links are singular. Dimensions are plural.

### Boundary vs Dimension

**Boundary**: Heterogeneous partitions (different behavior in each)
```
{Ok(value), Err(error)} — structurally different
```

**Dimension**: Homogeneous repetition (same structure in each)
```
pixels[N] — all pixels have same structure
```

**Key difference**: Boundaries partition by kind. Dimensions repeat by count.

---

## Common Patterns

### Containment = Boundary + Links

"This contains that" emerges from:
- Boundary defining the container region
- Links pointing to contents within

```
struct {
    header: Header,      ← link to header region
    data: [u8; N],       ← link to data region (with dimension N)
}
```

### Scope = Shared Boundary

"These share a context" emerges from:
- Multiple values within same boundary partition
- They change together when boundary changes

```
if debug_mode:
    log_level = DEBUG     ← same boundary
    verbose = True        ← same boundary
```

### Pipeline = Dimension + Sequential Links

"Process in stages" emerges from:
- Dimension of stages
- Links connecting stage[i] → stage[i+1]

```
input → encode → transform → decode → output
  D = [stages]
  L = {stage[i] → stage[i+1]}
```

---

## Worked Example: Neural Network Architectures

Apply the three questions to common architectures:

### Multi-Layer Perceptron (MLP)

**Boundaries**:
- Activation functions (ReLU, sigmoid): partition input space
- Dropout (training vs inference): partition execution mode

**Links**:
- Weight matrices: connect layer[i] → layer[i+1]
- Biases: connect to each layer
- Gradient flow: backward links for training

**Dimensions**:
- Batch: N independent samples
- Layers: L sequential stages
- Hidden: H neurons per layer

```
MLP Structure:
  B = {activation_boundaries, dropout_mode}
  L = {weights, biases, gradients}
  D = {batch, layers, hidden}
```

### Convolutional Neural Network (CNN)

**Boundaries**:
- Activation functions (per position)
- Pooling regions (partition spatial domain)

**Links**:
- Convolution kernels: local connectivity (sparse L)
- Skip connections: non-local links
- Gradients

**Dimensions**:
- Batch, height, width, channels
- Kernel dimensions (shared across positions)

```
CNN Structure:
  B = {activations, pooling_regions}
  L = {kernels (local), skips (non-local)}
  D = {batch, spatial, channels}
```

**Key insight**: CNN has **sparse L** (local connectivity). MLP has **dense L** (full connectivity). This is a structural difference, not just a parameter difference.

### Transformer

**Boundaries**:
- Attention masks: which tokens can attend to which
- Layer boundaries

**Links**:
- Attention weights: **dynamic links** (content-dependent!)
- Feed-forward weights: static links
- Residual connections: skip links

**Dimensions**:
- Batch, sequence length, heads, hidden

```
Transformer Structure:
  B = {attention_masks, layers}
  L = {attention (dynamic), FFN (static), residuals}
  D = {batch, sequence, heads, hidden}
```

**Key insight**: Transformer has **dynamic L** — the links themselves depend on input. This is structurally different from MLP/CNN where L is fixed.

---

## What the Method Reveals

Applying BLD to neural networks reveals structural differences:

| Architecture | B (partitions) | L (connectivity) | D (repetition) |
|-------------|----------------|------------------|----------------|
| MLP | Simple (activations) | Dense, static | batch × layers × hidden |
| CNN | Pooling regions | Sparse, static, local | batch × spatial × channels |
| Transformer | Attention masks | Dynamic, content-dependent | batch × seq × heads |

**Prediction**: Architectures succeed when their B/L/D structure aligns with the data's B/L/D structure.

- **CNN** works for images because local L matches spatial locality of visual features
- **Transformer** works for language because dynamic L matches context-dependent semantics
- **MLP** is general but inefficient — dense L doesn't match any specific structure

See [Neural Network Architectures](../applications/ml/neural-architectures.md) for the full analysis with testable predictions.

---

## The Method Summarized

```
┌─────────────────────────────────────────────────────────┐
│                  BLD DISCOVERY METHOD                   │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  INPUT: Any system                                      │
│                                                         │
│  1. Find BOUNDARIES                                     │
│     "Where does behavior partition based on value?"     │
│                                                         │
│  2. Find LINKS                                          │
│     "What references, affects, or connects to what?"    │
│                                                         │
│  3. Find DIMENSIONS                                     │
│     "What repeats homogeneously?"                       │
│                                                         │
│  OUTPUT: Structure S = (B, L, D)                        │
│          which IS a Lie algebra configuration           │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

The structure you find is the structure that exists. BLD doesn't impose—it reveals.

---

## Why This Works

The three questions are complete because they correspond to the three components of any Lie algebra:

1. **Boundaries** → Group topology (what's bounded vs unbounded)
2. **Links** → Structure constants (how generators interact)
3. **Dimensions** → Generators (directions of transformation)

Every continuous symmetry has exactly these three components. By asking these three questions, you find the Lie structure of any system.

See [Why Lie Theory](../mathematics/lie-theory/why-lie-theory.md) for the mathematical foundation.

---

## The Euler Connection: Two Compensation Mechanisms

> **Status**: Exploratory

Applying the three questions to Euler's identity demonstrates BLD completeness:

**e^(iπ) + 1 = 0**

### Q1: Where does behavior partition? (B)

- At e^(iπ): sign inverts (B = inversion boundary)
- At e^(i2π): returns to start (B = closure boundary)
- The boundary determines compact vs non-compact topology

### Q2: What connects to what? (L)

- Exponential connects iterations: e^a × e^b = e^(a+b)
- Angular connects rotations: e^(iθ) × e^(iφ) = e^(i(θ+φ))
- Structure constants determine how connections compose

### Q3: What repeats? (D)

- Exponent increments: e^(n×step) for n iterations
- Helix turns: 3.6 residues per full rotation
- Generators determine directions of repetition

**Physical validation — the α-helix**:

```
Cylindrical helix (parametric form):
  x(n) = r × cos(θn)
  y(n) = r × sin(θn)
  z(n) = a × n          ← LINEAR rise

Measured parameters:
  Rise: 1.5 Å per residue (linear, NOT exponential)
  Rotation: 100° per residue (angular: θ = 2π/3.6)
  Closure: 3.6 residues = 360° = 2π
```

The α-helix demonstrates angular compensation (π mechanism) with linear extension — a cylindrical helix, not a logarithmic spiral.

**Implication**: The three questions find structure because they identify both compensation mechanisms:

1. **e** arises from exponential compensation (L^D cascades in circuits, neural depth)
2. **π** arises from angular compensation (B-closure traversal, rotations)
3. **i** arises from angular L-direction in generator space

**Empirical observation**: Every domain examined decomposes into B/L/D without residue, and no structural phenomenon has required a fourth primitive. This is supported by evidence, not mathematical proof.

See [Euler's Formula in BLD](../glossary.md#euler) and [Compensation Principle](../mathematics/foundations/structural/compensation-principle.md).

---

## How BLD Discovered Itself

The discovery of BLD was itself an application of BLD. The framework existed before we named it — we were just finding structure that was already there.

### Every Step Was BLD

**Finding Boundaries**:
- "Where does behavior partition?" → We separated primitives (B vs L vs D)
- "What's proven vs conjectural?" → We partitioned claims by epistemic status
- "Which domain?" → We partitioned applications (GPU, VI, proteins)

**Finding Links**:
- "What affects what?" → We traced how formulas depend on each other
- "What corresponds to what?" → We found BLD ↔ Lie theory mapping
- "What aligns?" → We checked structure against reality

**Finding Dimensions**:
- "What repeats?" → The same patterns across GPU, VI, proteins, thermodynamics
- "What generalizes?" → Three primitives appearing in every domain
- "What scales?" → D as structural multiplier from KL additivity

### The Process Was Alignment

We didn't invent BLD. We **aligned** our representations with structure that already existed:

```
Our models (representations)     Reality (structure)
         │                              │
         └────── alignment ─────────────┘
                     │
                     ▼
              Friction when wrong
              Glide when right
```

When our representation was wrong (e.g., thinking α came from curvature), there was friction — things didn't fit. When we found the right structure (e.g., exact B formula from Killing form), there was glide — everything clicked.

### BLD Is Self-Describing

The framework describes its own discovery:

| Discovery Step | BLD Primitive |
|----------------|---------------|
| "Is this B, L, or D?" | Finding boundaries (partitioning primitives) |
| "How do these connect?" | Finding links (tracing dependencies) |
| "Does this pattern repeat?" | Finding dimensions (generalizing across domains) |
| "Does our model align?" | Computing alignment cost (testing predictions) |

This is not circular — it's **self-consistent**. A framework for describing structure should be able to describe the structure of its own discovery.

### Example: Discovering e via BLD

The derivation of e as the "traverser constant" demonstrates self-application in action:

**We applied the three questions to the concept "traverser":**

| Question | Applied to "Traverser" | Discovery |
|----------|------------------------|-----------|
| Q1 (Boundaries) | Where does traverser behavior partition? | Steps are uniform → T2 (Homogeneity) |
| Q2 (Links) | What connects to what? | Self-link only, proportional → T1, T3 |
| Q3 (Dimensions) | What repeats? | Time dimension, natural scale → T4, T5 |

**The result**: Five axioms emerged from structural analysis. From these axioms, dy/dt = y follows as a theorem, with solution y = e^t.

**The derivation was itself traversal**: We processed the concept sequentially (Q1, Q2, Q3), each question accumulated insight from the previous, and the process was self-referential — BLD analyzing BLD.

See [e from BLD](../examples/e-from-bld.md) for the complete derivation.

### It Was Always There

Lie theory existed in 1870. Information geometry existed in 1945. The patterns we found in GPU code existed the moment GPUs were built.

We didn't create BLD. We found a path to structure that was already there. The contribution is the **method of finding** — the three questions that make Lie theory accessible without requiring the mathematical machinery.

The framework was waiting. We just learned to see it.

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Structural Language](../theory/structural-language.md) — Formal definitions of B/L/D
- [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md) — Why B/L/D = Lie theory
- [Discovery Algorithm](../mathematics/derived/discovery-algorithm.md) — Formal algorithm specification
- [Neural Architectures](../applications/ml/neural-architectures.md) — Worked example on ML
- [Lie Algebra Examples](../examples/lie-algebras.md) — Worked examples from physics
