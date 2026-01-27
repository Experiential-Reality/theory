---
status: DERIVED
layer: 1
depends_on:
  - definitions.md
  - proofs/irreducibility-proof.md
used_by:
  - ../../../README.md
---

# Key Principles

## D×L Scaling

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

See [Compensation Principle](compensation-principle.md) for full derivation.

---

## Link Formula

```
L = -½ ln(1 - ρ²)
```

where ρ is correlation. This is an exact theorem derived from KL divergence.

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
