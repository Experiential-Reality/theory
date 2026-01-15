---
status: FOUNDATIONAL
layer: reference
depends_on: []
used_by:
  - mathematician.md
  - README.md
  - newcomer.md
---

# Reading Path: Practitioner

> **Status**: Foundational

> For those who want to apply BLD to real problems.

This path focuses on methodology and applications.

## Quick Summary (D≈7 Human Traversal)

**Practitioner reading path in 7 steps:**

1. **Discovery Method** — Learn the three diagnostic questions that reveal B, L, D in any system
2. **BLD-Driven Development** — Design with structure from the start, finding primitives before code
3. **Domain Applications** — Explore software, ML, or physics examples relevant to your work
4. **Worked Examples** — Study ZIP format analysis, then try the three questions on your own system
5. **Why It Works** — Understand the Lie theory foundation that makes BLD universally applicable
6. **Application Checklist** — Use the 6-step checklist for analyzing new systems systematically
7. **e vs π Diagnostic** — Identify which compensation mechanism applies: exponential, angular, or both

---

## Step 1: The Discovery Method

**Read**: [Discovery Method](../meta/discovery-method.md)

**Key takeaway**: The three questions:
1. Where does behavior partition? → B
2. What connects to what? → L
3. What repeats? → D

---

## Step 2: BLD-Driven Development

**Read**: [BLD-Driven Development](../applications/code/bld-driven-development.md)

**Key takeaway**: Design with structure from the start. Find B/L/D before writing code.

---

## Step 3: See It Applied

Pick your domain:

### Software
- [Code Refactoring](../applications/code/refactoring.md) — Make state explicit
- [Code Generation](../applications/code/code-generation.md) — Generate code from BLD

### Machine Learning
- [Neural Architectures](../applications/ml/neural-architectures.md) — BLD analysis of MLP/CNN/Transformer
- [Neural Network Alignment](../applications/ml/neural-network-alignment.md) — The compensation principle

### Physics/Engineering
- [GPU Calibration](../applications/physics/gpu-calibration.md) — Measuring structure on hardware
- [Circuits](../applications/physics/circuits.md) — D×L scaling in electronics

---

## Step 4: Worked Examples

**Read**: [ZIP Format](../examples/zip.md) — File format structure in BLD

Then try analyzing your own system using the three questions.

---

## Step 5: Understanding Why It Works

**Read**: [Why Lie Theory](../mathematics/lie-theory/why-lie-theory.md)

**Key takeaway**: BLD works because it's Lie theory in disguise.

---

## Quick Application Checklist

When analyzing a new system:

1. **Find all boundaries (B)**
   - Conditionals, mode switches, thresholds
   - Type tags, state machines, phase transitions

2. **Find all links (L)**
   - Pointers, references, dependencies
   - Correlations, coupling, interactions

3. **Find all dimensions (D)**
   - Arrays, loops, parallel instances
   - Layers, stages, batches

4. **Check D×L scaling**
   - L should scale with D
   - B should be invariant

5. **Look for compensation opportunities**
   - Can global L approximate complex B?
   - Cascading stages can approximate boundaries

6. **Identify which compensation mechanism applies**
   - **Exponential (e)**: Serial stages, multiplicative gain, non-periodic
   - **Angular (π)**: Rotations, phase alignment, periodic at 2π
   - **Both**: Spirals, helices, mixed compact/non-compact structure

---

## The Cost Formula

```
Cost = B_cost + D × L_cost
```

Misalignment creates friction. Alignment creates flow.

---

## Diagnostic: Identifying e vs π in New Domains

When analyzing a new system, determine which compensation mechanism applies:

| Question | If Yes → | If No → |
|----------|---------|---------|
| Does structure return to start? | **π** (angular, compact) | **e** (exponential, non-compact) |
| Are stages multiplicative? | **e** (cascade) | **π** (additive rotation) |
| Is there periodic closure? | **π** (2π boundary) | **e** (unbounded growth) |
| Does behavior spiral? | **Both** (e^(a+iθ)) | Single mechanism |

**Examples**:
- Circuit cascades: No return → **e**
- Pitch space (music): Octave equivalence → **π**
- α-helix: Rise + rotation → **Both**
- Neural depth: Non-periodic stacking → **e**
- VI alignment: Phase-dependent → **π**

See [Compensation Principle](../mathematics/foundations/compensation-principle.md) for full theory.

---

## See Also

- [Newcomer Path](./newcomer.md) — Conceptual background
- [Mathematician Path](./mathematician.md) — Theoretical depth
- [BLD-Driven Development](../applications/code/bld-driven-development.md) — Design methodology
