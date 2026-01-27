---
status: VALIDATED
depends_on:
  - ../../mathematics/lie-theory/lie-correspondence.md
  - ../../mathematics/foundations/proofs/irreducibility-proof.md
---

# Neural Network Architectures: BLD Analysis

> **Status**: Validated (see [Neural Network Alignment](./neural-network-alignment.md))

## Summary

**Neural Architecture BLD Analysis:**

1. Every architecture has distinct BLD structure — [The Analysis](#the-analysis)
2. L determines connectivity: MLP dense, CNN sparse local, Transformer dynamic — [Key Differences](#key-structural-differences)
3. B determines partitioning: activations, masks, gates — [The Analysis](#the-analysis)
4. D determines repetition axes: batch, spatial, sequence, heads — [The Analysis](#the-analysis)
5. Architecture-data alignment predicts success — [Prediction 1](#prediction-1-architecture-data-alignment--validated)
6. L subtypes are distinct and complementary — [L Subtype Taxonomy](#l-subtype-taxonomy-validated)
7. Inductive bias = BLD constraint — [Prediction 4](#prediction-4-inductive-bias-is-structural-constraint)

| Architecture | L Structure | B Structure | D Structure |
|--------------|-------------|-------------|-------------|
| MLP | Dense, static | Activation boundaries | batch × hidden × layers |
| CNN | Sparse, local | Activations + pooling | batch × H × W × channels |
| Transformer | Dynamic (attention) | Masks + layer bounds | batch × seq × heads × hidden |
| GNN | Graph-structured | Aggregation boundaries | batch × nodes × features |
| LSTM | Sequential (recurrent) | Gate activations | batch × sequence × hidden |

---

Applying the BLD discovery method to neural network architectures reveals structural differences that may explain why certain architectures work for certain tasks.

---

## The Analysis

### MLP (Multi-Layer Perceptron)

```
Structure:
  B = {activation_boundaries}
      - ReLU: partition at x=0
      - Sigmoid: smooth partition

  L = {weight_matrices}
      - Dense: every input connects to every output
      - Static: connections don't change with input
      - Bidirectional (backprop): gradients flow backward

  D = {batch, layers, hidden}
      - batch: independent samples (parallel)
      - layers: sequential stages
      - hidden: neurons per layer
```

**Lie interpretation**:
- D = dim(input) + dim(hidden) × layers + dim(output) generators
- L = dense structure constants (all generators interact)
- B = piecewise topology (ReLU creates boundaries)

### CNN (Convolutional Neural Network)

```
Structure:
  B = {activation_boundaries, pooling_boundaries}
      - Activations: per-position partitions
      - Pooling: coarse-grains spatial structure

  L = {convolution_kernels, skip_connections}
      - Sparse: each output only connects to local inputs
      - Translation-equivariant: same L applied at each position
      - Skip connections: non-local links (ResNet)

  D = {batch, height, width, channels, kernel_dims}
      - batch: independent samples
      - height × width: spatial repetition
      - channels: feature dimensions
      - kernel: shared across positions (parameter sharing)
```

**Lie interpretation**:
- D includes spatial generators (translation symmetry)
- L is sparse and translation-invariant (equivariant structure constants)
- B (pooling) reduces topology at each level

### Transformer

```
Structure:
  B = {attention_masks, layer_boundaries}
      - Causal mask: which tokens can see which
      - Padding mask: valid vs padding tokens

  L = {attention_weights, FFN_weights, residual_connections}
      - Attention: DYNAMIC links (content-dependent!)
      - FFN: static dense links (like MLP)
      - Residuals: skip links across layers

  D = {batch, sequence, heads, hidden}
      - batch: independent samples
      - sequence: token positions
      - heads: parallel attention mechanisms
      - hidden: feature dimension
```

**Lie interpretation**:
- D = position generators + feature generators
- L = **dynamic structure constants** (attention)
- B defines which generators can interact (masking)

### GNN (Graph Neural Network) ✓ VALIDATED

```
Structure:
  B = {aggregation_boundaries}
      - Neighborhood boundaries: which nodes to aggregate
      - Message passing rounds: depth of information propagation

  L = {edge_connections, message_functions}
      - Graph-structured: L follows data relationships
      - Sparse: only connected nodes interact
      - Permutation-equivariant: node order doesn't matter

  D = {batch, nodes, features, layers}
      - batch: independent graphs
      - nodes: variable per graph
      - features: node embedding dimension
      - layers: message passing rounds
```

**Lie interpretation**:
- D = node generators (one per node)
- L = adjacency structure (only connected nodes have non-zero structure constants)
- B = aggregation topology (how neighborhoods are defined)

**Validated results** (see [Neural Network Alignment](./neural-network-alignment.md)):
- Multi-hop reasoning: GNN 93.25% vs MLP 63.5% (+29.75%)
- Average margin: +11.9% across graph tasks
- GNN wins when relational reasoning is required

### LSTM (Recurrent Network)

```
Structure:
  B = {gate_activations}
      - Input gate: partition of information to remember
      - Forget gate: partition of state to discard
      - Output gate: partition of state to expose

  L = {recurrent_weights, input_weights}
      - Recurrent: hidden[t] → hidden[t+1]
      - Input: input[t] → hidden[t]
      - Sequential: information flows through time

  D = {batch, sequence, hidden}
      - batch: independent sequences
      - sequence: temporal positions
      - hidden: state dimension
```

**Validated results**:
- LSTM advantage is **task-specific**, not universal
- Average margin: -10.9% (feedforward often wins)
- Wins only on cumulative computation tasks

---

## Key Structural Differences

| Property | MLP | CNN | Transformer | GNN | LSTM |
|----------|-----|-----|-------------|-----|------|
| **L density** | Dense | Sparse (local) | Dynamic | Graph-sparse | Sequential |
| **L variability** | Static | Static | Content-dependent | Static | Static |
| **Structure** | None | Translation-equiv | Permutation-equiv* | Permutation-equiv | Temporal |
| **Parameter sharing** | None | Across positions | Across positions | Across nodes | Across time |

*With positional encoding, transformers have position-awareness but not strict equivariance.

### L Subtype Taxonomy (Validated)

The different L types serve **distinct computational purposes**:

| L Subtype | Architecture | Computational Role | Validated Task |
|-----------|--------------|-------------------|----------------|
| **Dense** | MLP | Global pattern memorization | Small enumerable sets |
| **Sparse** | CNN | Local feature detection | Spatial patterns (CIFAR) |
| **Dynamic** | Transformer | Context-dependent selection | Associative recall (+5.7%) |
| **Sequential** | LSTM | Cumulative state propagation | Cumulative sum (+2%) |
| **Graph** | GNN | Relational reasoning | Multi-hop (+29.75%) |

**Critical insight**: Dynamic L ≠ Sequential L. Transformers fail on XOR parity (52% at length 8) while LSTMs succeed (99.6% at length 16). Attention enables **feature selection**, not **state accumulation**.

**Hybrid L validation**: Combining L subtypes in parallel (Transformer + LSTM) achieves 99% on XOR parity at lengths where each alone is at chance. L subtypes are **complementary**.

---

## BLD Predictions

### Prediction 1: Architecture-Data Alignment ✓ VALIDATED

**Claim**: Architectures succeed when their B/L/D structure aligns with the data's B/L/D structure.

See [Neural Network Alignment](./neural-network-alignment.md) for experimental results showing 6.2% diagonal advantage and the compensation principle.

**CNN ↔ Images**:
- Image data has spatial locality (nearby pixels are correlated)
- CNN has local L (sparse connectivity)
- **Alignment**: Data L matches architecture L

**Transformer ↔ Language**:
- Language has context-dependent relations (meaning depends on context)
- Transformer has dynamic L (attention)
- **Alignment**: Dynamic data structure matches dynamic architecture L

**MLP ↔ Tabular**:
- Tabular data has no obvious spatial/sequential structure
- MLP has no structural bias
- **Alignment**: Lack of structure matches lack of bias (but inefficient)

### Prediction 2: ResNets and Gradient Flow

**Claim**: ResNets succeed because skip connections align the layer dimension D with gradient flow L.

```
Without skip connections:
  gradient L: layer[N] → layer[N-1] → ... → layer[1]
  decay: gradients vanish/explode over long paths

With skip connections:
  gradient L: layer[N] → layer[1] (direct path)
  no decay: gradients flow directly
```

**BLD interpretation**: Skip connections add non-local L that shortcuts the D (depth) dimension, aligning gradient structure with forward structure.

### Prediction 3: Attention as Dynamic Structure Constants

**Claim**: Attention's power comes from making L content-dependent.

In Lie terms:
- Fixed L (MLP, CNN): [Dᵢ, Dⱼ] = fᵢⱼᵏ Dₖ where f is constant
- Dynamic L (Transformer): [Dᵢ, Dⱼ] = fᵢⱼᵏ(x) Dₖ where f depends on input

**Implication**: Transformers can represent context-dependent symmetries that fixed-L architectures cannot.

### Prediction 4: Inductive Bias is Structural Constraint

**Claim**: Inductive bias = constraints on B/L/D structure.

| Inductive Bias | BLD Constraint |
|----------------|----------------|
| Translation equivariance | L is translation-invariant |
| Local receptive field | L is sparse |
| Permutation equivariance | L is symmetric under permutation |
| Depth | Large D (layer dimension) |

Architectures with "appropriate" inductive bias = architectures whose B/L/D aligns with data's B/L/D.

### Prediction 5: Training Dynamics

**Claim**: Training difficulty correlates with alignment cost between architecture and data.

- **Easy training**: Architecture B/L/D matches data B/L/D (low alignment cost)
- **Hard training**: Architecture B/L/D differs from data B/L/D (high alignment cost)

**Testable**: Compare training curves of MLP vs CNN on image data. BLD predicts CNN trains faster because its structure is pre-aligned.

---

## Open Questions

1. **Can we compute alignment cost?** Given network structure and data structure, can we predict training efficiency?

2. **What's the BLD of data?** How do we extract B/L/D from a dataset?

3. **Architecture search**: Can BLD guide neural architecture search by matching data structure?

4. **Attention patterns**: What Lie algebra do learned attention patterns correspond to?

5. **Training = alignment?** Is SGD finding the minimum-cost homomorphism from data structure to network structure?

---

## Potential Experiments

### Experiment 1: Architecture Comparison

Train MLP, CNN, Transformer on same task (e.g., MNIST).
- Compute BLD structure of each architecture
- Compute BLD structure of data (somehow)
- Measure alignment cost
- Predict: lower alignment cost → faster training

### Experiment 2: Ablation Studies

Remove structural components and measure impact:
- Remove skip connections (reduce L connectivity)
- Remove pooling (change B)
- Reduce depth (change D)

Predict: removing components that align with data structure should hurt more.

### Experiment 3: Synthetic Data ✓ COMPLETED

Create synthetic data with known B/L/D structure:
- Data with local correlations (matches CNN)
- Data with global correlations (matches Transformer)
- Data with no structure (matches MLP)

Test: does matching architecture → better performance?

> **Result**: YES. See [Neural Network Alignment](./neural-network-alignment.md). Local architectures on global data: 69-77%. Global architectures on global data: 99%. Also discovered the **compensation principle**: L can compensate for B, but not vice versa.

---

## Conclusion

BLD analysis of neural networks reveals:

1. **MLP**: Dense static L, minimal structural bias
2. **CNN**: Sparse local L, translation-equivariant structure
3. **Transformer**: Dynamic L, content-dependent structure constants

The core prediction: **architectures work when their structure aligns with data structure**.

This is not a new claim (inductive bias), but BLD provides a formal language for it: alignment = Lie homomorphism, cost = homomorphism obstruction.

---

## See Also

- [Neural Network Alignment](./neural-network-alignment.md) — **Validated experimental results**
- [Glossary](../../glossary.md) — Central definitions
- [Discovery Method](../../meta/discovery-method.md) — How we extracted B/L/D
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Why B/L/D = Lie theory
- [Constructive Lie](../../mathematics/lie-theory/constructive-lie.md) — Alignment as Lie homomorphism
- [Variational Inference](./variational-inference.md) — Related ML application
