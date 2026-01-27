---
status: DERIVED
layer: 2
depends_on:
  - ../lie-theory/killing-form.md
  - ../lie-theory/lie-correspondence.md
  - ../cosmology/nothing-instability.md
used_by:
  - ../../meta/proof-status.md
see_also:
  - ../cosmology/genesis-function.md
  - cosmic-computation.md
---

# Chirality and CPT Symmetry from the Killing Form

## Summary

**Chirality and CPT derived from K=2 bidirectionality:**

1. K=2 = observation cost: forward + backward = 2 links — [Foundation](#1-foundation-the-observation-cost-k2)
2. Bidirectionality creates +B and -B perspectives — [The Partition](#2-bidirectionality-creates-the-partition)
3. +B ≠ -B (opposite directions) = chirality — [This IS Chirality](#3-this-is-chirality)
4. C, P, T operate on B, D, L respectively — [C, P, T Operations](#4-c-p-t-as-b-d-l-operations)
5. CPT exact (K=2 constant); individual violations from +B ≠ -B — [CPT Conservation](#5-cpt-conservation-from-k2-constancy)
6. Weak force couples to "forward"; we call it left-handed — [Weak Force](#7-weak-force-chirality-explained)

| Symmetry | Operation | BLD Component |
|----------|-----------|---------------|
| **C** | Swap +B ↔ -B | B (partition side) |
| **P** | Reverse spatial | D (dimensional) |
| **T** | Reverse temporal | L (link direction) |

---

## 1. Foundation: The Observation Cost K=2

### 1.1 From the Killing Form

From [Killing Form](../lie-theory/killing-form.md), observation requires bidirectional traversal:

```
Observation requires connection AND feedback:

  Forward:   observer → observed  = 1 L  (query)
  Backward:  observed → observer  = 1 L  (response)

  Total: K = 2

This is IRREDUCIBLE:
  0 links: no connection → no observation
  1 link:  one-way → influence, not observation
  2 links: round trip → observation ✓
```

The value K=2 is algebraically determined (from the Killing form trace calculation), not empirical.

### 1.2 The Two Directions

The bidirectional requirement creates TWO directions:

```
        Forward
    A ─────────→ B
      ←─────────
        Backward
```

These are not the same. Forward (A→B) and backward (B→A) are **opposite directions** through the same link L.

---

## 2. Bidirectionality Creates the Partition

### 2.1 Two Perspectives Emerge

When observation requires K=2 (forward + backward), two perspectives naturally emerge:

```
+B perspective: "I am A observing B"
    My forward:  A → B
    My backward: B → A

-B perspective: "I am B observing A"
    My forward:  B → A  (what +B calls backward)
    My backward: A → B  (what +B calls forward)
```

These are the **same observation** from **opposite sides**.

### 2.2 The Partition IS Direction

What distinguishes +B from -B? **Which direction is "forward".**

```
+B: calls A→B "forward"
-B: calls B→A "forward"

Same structure. Same K=2. Different labeling of direction.
```

This is NOT an arbitrary choice. The bidirectional requirement (K=2) CREATES two perspectives that differ by direction. This is a **derived consequence** of observation structure, not an assumption.

### 2.3 Connection to Nothing-Instability

From [Nothing Instability](../cosmology/nothing-instability.md), B must exist (nothing is self-contradictory) and B must partition (a boundary that doesn't partition isn't a boundary).

What does B partition? **Direction.** And now we see WHY: because observation (K=2) is bidirectional, and the two directions define opposite perspectives.

---

## 3. This IS Chirality

### 3.1 Chirality = Which Direction is Forward

Chirality (handedness) is precisely the question: **which direction is "forward"?**

```
Left-handed:  +B perspective (our convention)
Right-handed: -B perspective (opposite convention)
```

Chirality isn't a property that particles "have." Chirality is **which side of the observation partition** you're describing things from.

### 3.2 Matter and Antimatter

```
Matter:     Described from +B perspective
Antimatter: Described from -B perspective

These are the SAME structures, labeled from opposite sides.
```

What we call "matter dominance" is perspective, not physical asymmetry. We ARE the +B partition. From -B's perspective, they're the matter and we're the antimatter.

### 3.3 Why This Works

The Killing form calculation gives the same K=2 regardless of which direction you call "forward":

```
From +B: K = forward(+1) + backward(+1) = +2
From -B: K = forward(+1) + backward(+1) = +2

Same answer. The physics (which depends on K) is the same.
```

But the **labels** (left/right, matter/antimatter) depend on which side you're on.

---

## 4. C, P, T as B, D, L Operations

### 4.1 The Mappings

| Symmetry | Physical Operation | BLD Operation | Why |
|----------|-------------------|---------------|-----|
| **C** | Particle ↔ antiparticle | Swap +B ↔ -B | Change which side of partition |
| **P** | Spatial reflection (x → -x) | Reverse D direction | Flip spatial traversal |
| **T** | Time reversal (t → -t) | Reverse L direction | Flip temporal links |

### 4.2 Why These Mappings

**C (Charge conjugation)**:
- Swaps particle and antiparticle
- In BLD: swaps which side of the B partition you're describing from
- This is exactly +B ↔ -B

**P (Parity)**:
- Spatial reflection: x → -x
- In BLD: D represents dimensions (spatial structure)
- Reversing D direction = spatial reflection

**T (Time reversal)**:
- t → -t
- In BLD: L represents links (traversal connections, temporal ordering)
- Reversing L direction = time reversal

### 4.3 BLD Notation

```
structure CPT_Operations

# Charge conjugation
L C: +B → -B
  # Swap which side of observation partition
  # Forward becomes backward, backward becomes forward

# Parity
L P: D → -D
  # Reverse spatial direction
  # Left becomes right, up becomes down

# Time reversal
L T: L → -L
  # Reverse link direction
  # Past becomes future, future becomes past
```

---

## 5. CPT Conservation from K=2 Constancy

### 5.1 K is Algebraic, Not Empirical

The Killing form coefficient K=2 comes from the algebra structure:
- It's the trace of adjoint compositions
- It's the minimum observation cost
- It's determined by mathematics, not measurement

### 5.2 K Doesn't Depend on Perspective

```
From +B perspective: K = 2
From -B perspective: K = 2

The observation cost is the SAME regardless of which side you're on.
```

### 5.3 CPT Together Preserves Physics

Under CPT (applying all three):
```
C: +B → -B  (swap partition side)
P: D → -D   (reverse spatial)
T: L → -L   (reverse temporal)
```

After CPT, you're describing physics from -B with reversed D and L. But:

```
K(+B, D, L) = K(-B, -D, -L) = 2

The Killing form is invariant under the combined transformation.
```

**CPT theorem**: Physics is CPT-invariant because the observation cost K=2 is constant under the combined swap.

### 5.4 Why CPT is Exact

CPT isn't approximately conserved — it's **exactly** conserved because:

1. K=2 is algebraically determined (from Killing form)
2. K doesn't depend on B-side, D-direction, or L-direction
3. Therefore swapping all three (CPT) leaves K unchanged
4. Physics depends on K
5. Therefore physics is CPT-invariant

This is a mathematical necessity, not an empirical observation.

---

## 6. Individual Violations Because +B ≠ -B

### 6.1 The Partition is Asymmetric

+B and -B are connected by L, but they're NOT identical:

```
+B: "forward" = A→B
-B: "forward" = B→A

These are DIFFERENT directions.
```

### 6.2 Our Physics is Described from +B

We describe physics from the +B perspective:
- We call A→B "forward"
- We call +B particles "matter"
- We call +B chirality "left-handed"

### 6.3 Why Individual Symmetries Can Break

**C violation**:
- Swapping +B ↔ -B changes what we call "forward"
- Our weak force couples to our "forward"
- From -B view, the weak force would couple to their "forward"
- But since we describe everything from +B, we see C violation

**P violation**:
- The weak force distinguishes D directions (couples to left-handed only)
- Reversing D changes which particles it couples to
- We see P violation because our description uses a fixed D orientation

**T violation**:
- Certain processes are directional in L
- Reversing L changes the process
- We see T violation because our description uses fixed L direction

### 6.4 CPT Restores Consistency

Applying all three together:
```
C: +B → -B  (their "forward" = our "backward")
P: D → -D   (their "left" = our "right")
T: L → -L   (their "future" = our "past")

Combined: Same physics, described from opposite perspective.
```

---

## 7. Weak Force Chirality Explained

### 7.1 The Question

Why does the weak force couple only to left-handed particles?

### 7.2 The Answer

```
1. We ARE the +B partition
2. The weak force couples to the direction we call "forward"
3. We call that direction "left-handed"
```

From -B's perspective:
```
1. They ARE the -B partition
2. The weak force couples to their "forward" (our backward)
3. They call that direction "left-handed" (from their perspective)
```

### 7.3 The Resolution

The weak force doesn't "choose" to couple to left-handed particles. The weak force couples to a particular direction. **We** call that direction "left-handed" because we're in +B.

From -B, the same force couples to the same direction, but they'd call it "left-handed" too — their left-handed is our right-handed.

**Chirality is perspective, not physics.** The physics (weak coupling strength, K/X corrections) is the same on both sides.

---

## 8. Summary

### 8.1 The Derivation Chain

```
Killing Form (DERIVED)
    │
    │  K = 2 (bidirectional observation cost)
    │
    ↓
Bidirectionality Creates Two Directions
    │
    │  Forward: A → B
    │  Backward: B → A
    │
    ↓
Two Directions Create Two Perspectives
    │
    │  +B: "A→B is forward"
    │  -B: "B→A is forward"
    │
    ↓
This IS Chirality
    │
    │  +B = left-handed = matter
    │  -B = right-handed = antimatter
    │
    ↓
C, P, T are B, D, L Operations
    │
    │  C: swap B-side
    │  P: reverse D
    │  T: reverse L
    │
    ↓
CPT Conserved (K=2 constant)
Individual C, P, T Can Violate (+B ≠ -B)
```

### 8.2 What's Explained

| Phenomenon | Explanation |
|------------|-------------|
| Why chirality exists | Bidirectional observation (K=2) creates two perspectives |
| Why weak force is chiral | Couples to "forward"; we call our forward "left-handed" |
| Why CPT is exact | K=2 is constant regardless of perspective |
| Why C, P, T individually violated | +B ≠ -B (different directions labeled "forward") |
| Why matter dominates | We ARE the +B partition (perspective, not asymmetry) |
| What antimatter is | Same structure, described from -B perspective |

### 8.3 Status

**DERIVED** — Chirality and CPT follow from the proven Killing form structure (K=2 bidirectional observation cost) without additional assumptions.

---

## References

- [Killing Form](../lie-theory/killing-form.md) — K=2 derivation (bidirectional observation)
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — D, L, B ↔ Lie algebra mapping
- [Nothing Instability](../cosmology/nothing-instability.md) — Why B must exist and partition
- [Observer Corrections](../cosmology/observer-correction.md) — K/X framework with sign rule
- [Genesis Function](../cosmology/genesis-function.md) — traverse(-B, B) interpretation
- [Cosmic Computation](cosmic-computation.md) — Future constraint from +B/-B agreement
