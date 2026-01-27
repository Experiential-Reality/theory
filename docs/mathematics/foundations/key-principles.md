---
status: DERIVED
layer: 1
depends_on:
  - definitions.md
  - proofs/irreducibility-proof.md
  - ../lie-theory/killing-form.md
used_by:
  - ../../../README.md
  - ../quantum/entanglement-entropy.md
  - ../quantum/black-hole-entropy.md
---

## Summary

**Core principles governing BLD structure:**

1. D multiplies L, not B: geometric properties scale with dimension — [D×L Scaling](#dl-scaling)
2. L can compensate for B deficiency, but not vice versa — [Compensation Principle](#compensation-principle)
3. Link formula: L = -1/2 ln(1 - rho^2) derives from KL divergence — [Link Formula](#link-formula)
4. Three primitives are necessary: distinction, relation, extension — [Why Three Primitives?](#why-three-primitives)
5. Entropy formula: S = K × L unifies entropy across domains — [Entropy Formula](#entropy-formula)

# Key Principles

## D×L Scaling {#dl-scaling}

D multiplies L, not B.
- Geometric properties (L) scale with dimension
- Topological properties (B) are invariant
- Validated: R² = 1.0 across VI, neural nets, circuits

---

## Compensation Principle

L can compensate for B deficiency, not vice versa.
- B is topological (local scope, invariant under D)
- L is geometric (can span distance, scales with D)
- D×L accumulates → can approximate complex B
- D×B stays local → cannot replace missing L
- Validated: 87.8% improvement via cascading (circuits), 6.2% diagonal advantage (neural)

See [Compensation Principle](structural/compensation-principle.md) for full derivation.

---

## Link Formula

```
L = -½ ln(1 - ρ²)
```

where ρ is correlation. This is an exact theorem derived from KL divergence.

---

## Entropy Formula

```
S = K × L
```

where K = 2 is the Killing form (bidirectional observation cost) and L is link cost.

**Unifies entropy across three domains:**

| Domain | Formula | Interpretation |
|--------|---------|----------------|
| **Entanglement** | S = 2L | At max entanglement, S = 2L exactly. See [Entanglement Entropy](../quantum/entanglement-entropy.md) |
| **Black holes** | S = A/(4ℓ_P²) = K × L | L = A/(8ℓ_P²). The 1/4 comes from n=4 dimensions. See [Black Hole Entropy](../quantum/black-hole-entropy.md) |
| **Phase transitions** | L → ∞ as ρ → 1 | At criticality, correlations become long-range. See [Phase Transitions](../../applications/physics/phase-transitions.md) |

**Why K = 2?** Observation requires bidirectional traversal: forward query + backward response. K = 2 is the Killing form diagonal for SO(3,1). See [Killing Form](../lie-theory/killing-form.md).

**Why this matters**: The same formula governs quantum entanglement, gravitational entropy, and classical phase transitions. Entropy IS link cost times observation cost.

---

## Why Three Primitives?

Structure requires:
1. **Distinction** (Boundary)—or everything is undifferentiated
2. **Relation** (Link)—or nothing interacts
3. **Extension** (Dimension)—or there is only one of each thing

These are not chosen for convenience. They are **provably irreducible**—each provides a capability the others cannot express.

**Type theory answer**: Every attempt to reduce further fails:
- Boundaries without links: disconnected partitions (no structure)
- Links without boundaries: undifferentiated flow (no structure)
- Either without dimensions: no repetition, no pattern, no generality

**Lie theory answer**: These are exactly the components that define a Lie algebra:
- **Generators** (D): Infinitesimal symmetry directions
- **Structure constants** (L): How generators combine [Xᵢ, Xⱼ] = fᵢⱼᵏXₖ
- **Topology** (B): Whether the group is compact (closed) or non-compact (open)

Every Lie algebra has exactly these three components. No more, no fewer. BLD works because it *is* Lie theory.

See [Irreducibility Proof](proofs/irreducibility-proof.md) for formal proof.
