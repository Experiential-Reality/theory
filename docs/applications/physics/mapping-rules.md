---
status: VALIDATED
layer: application
depends_on:
  - validation-roadmap.md
  - circuits.md
  - ../../meta/discovery-method.md
used_by:
  - ../../meta/epistemic-honesty.md
  - validation-roadmap.md
---

# BLD Mapping Rules for Physics

> **Status**: Foundational (establishes criteria for B/L/D assignment)

## Summary

**Falsifiable criteria for B/L/D assignment:**

1. B is topological: X unchanged when D changes (e.g., V_th same for 1 or 100 transistors) — [Rule 1](#rule-1-b--topological-invariant-under-d)
2. L is geometric: X scales proportionally with D (e.g., C_total = N × C_single) — [Rule 2](#rule-2-l--geometric-scales-with-d)
3. D is repetition: X counts instances of identical structure — [Rule 3](#rule-3-d--repetition-count)
4. Falsification tests: B must be D-invariant, L must scale with D, total cost = B + D×L — [Rule 4](#rule-4-falsification-criteria)
5. Common errors: confusing intensive (B) with extensive (L/D), ratios with absolutes — [Common Mapping Errors](#common-mapping-errors)
6. Cross-domain consistency: same observable type maps consistently across domains — [Cross-Domain Consistency](#cross-domain-consistency-check)

| Rule | Test | Classification |
|------|------|----------------|
| D-invariant? | X(D) = X(D') for all D | B (boundary) |
| Scales with D? | X(αD) = αᵏ × X(D) | L (link) |
| Counts identical things? | X = integer count | D (dimension) |

This document defines **explicit rules** for determining which physical observable maps to B, L, or D. The goal is to eliminate post-hoc fitting by providing falsifiable criteria.

---

## The Problem

Current physics documentation sometimes has **underdetermined mappings**:
- The same quantity could plausibly be B or L
- Mappings are chosen after knowing the answer
- No rule distinguishes correct from incorrect assignments

This document provides rules to resolve ambiguity and detect errors.

---

## The Three Rules

### Rule 1: B = Topological (Invariant Under D)

**Definition**: Observable X is a **boundary (B)** if and only if X is unchanged when system size D changes.

**Test**:
```
X(D) = X(D') for all D, D' → X is B
X(D) ≠ X(D') for some D → X is NOT B
```

**Physics Examples**:

| Observable | Scales with D? | Classification | Reasoning |
|------------|---------------|----------------|-----------|
| Threshold voltage V_th | No | **B** | Same V_th for 1 or 100 transistors |
| Light cone angle | No | **B** | 45° in any dimension |
| Critical Reynolds Re_c | No | **B** | Same Re_c regardless of pipe length |
| Curie temperature T_c | No | **B** | Same T_c for small or large sample |
| Speed of light c | No | **B** | Independent of observer scale |
| Conductivity σ | No | **B** | Material property, not size-dependent |

**Counter-examples (NOT B)**:

| Observable | Why NOT B |
|------------|-----------|
| Total resistance R | R = ρL/A, scales with length L |
| Total capacitance | C_total = n × C, scales with count |
| Correlation length ξ | Can grow without bound |

### Rule 2: L = Geometric (Scales with D)

**Definition**: Observable X is a **link (L)** if and only if X scales proportionally with system size D.

**Test**:
```
X(αD) = α^k × X(D) for some k > 0 → X is L
X(αD) = X(D) → X is NOT L (probably B)
```

**The L Formula**:

For correlations, the exact formula is:
```
L = -½ ln(1 - ρ²)
```

For other domains, L typically appears in cost formulas as the quantity that multiplies D.

**Physics Examples**:

| Observable | Scaling | Classification | Formula |
|------------|---------|----------------|---------|
| Capacitance | C ~ n | **L** | C_total = n × C_single |
| Correlation strength | ~ log(samples) | **L** | L = -½ ln(1-ρ²) |
| Field energy | U ~ V | **L** | U = (ε₀E²/2) × Volume |
| Momentum flux | ~ ρv | **L** | Reynolds L term |
| Entanglement entropy | S ~ n (for area law) | **L** | S ∝ boundary area |

**Counter-examples (NOT L)**:

| Observable | Why NOT L |
|------------|-----------|
| Threshold voltage | Invariant under scaling |
| Phase boundary | Topological, doesn't scale |
| Spin-statistics | Fermion/boson doesn't depend on count |

### Rule 3: D = Repetition Count

**Definition**: Observable X is a **dimension (D)** if and only if X counts instances of identical structure.

**Test**:
```
X = integer count of homogeneous elements → X is D
X = continuous quantity or ratio → X is NOT D
```

**Physics Examples**:

| Observable | Classification | Reasoning |
|------------|----------------|-----------|
| Particle number N | **D** | Count of identical particles |
| Spatial dimension d | **D** | Count of orthogonal directions |
| Qubit count | **D** | Count of identical 2-level systems |
| Stage count | **D** | Count of cascaded amplifiers |
| Mode number | **D** | Count of field modes |
| Lattice size L | **D** | Count of lattice sites |

**Counter-examples (NOT D)**:

| Observable | Why NOT D |
|------------|-----------|
| Temperature | Continuous, not a count |
| Coupling constant | Ratio, not a count |
| Phase angle | Continuous variable |

---

## Rule 4: Falsification Criteria

These rules provide falsification tests for mappings:

### Test 4.1: B Must Be D-Invariant

If you claim X is B, then:
```
Prediction: X(D) = X(D') for all valid D
Test: Vary D, measure X
Falsification: X changes with D → X is NOT B
```

**Example**: Claimed B = threshold voltage V_th
- Test: Measure V_th for N = 1, 2, 4, 8, 16 parallel transistors
- Result: V_th constant (validated as B)
- If V_th changed: Falsified, not actually B

### Test 4.2: L Must Scale with D

If you claim X is L, then:
```
Prediction: X(αD) = α^k × X(D) for some k > 0
Test: Vary D, plot X vs D
Falsification: X doesn't scale → X is NOT L
```

**Example**: Claimed L = capacitance
- Test: Measure C for N = 1, 2, 4, 8, 16 parallel capacitors
- Result: C_total = N × C_single (R² = 1.0, validated as L)
- If C saturated: Falsified, not pure L

### Test 4.3: Cost Must Be B + D×L

The total cost formula:
```
Cost = B_cost + D × L_cost
```

If your B and L mappings are correct, cost should decompose this way.

**Test**:
1. Measure total cost for varying D
2. Fit: Cost = a + b×D
3. Intercept a should equal B_cost (from independent B measurement)
4. Slope b should equal L_cost (from independent L measurement)

**Falsification**: If Cost ≠ B + D×L with independently measured B and L, mapping is wrong.

---

## Decision Procedure

When faced with ambiguous observable X:

```
Step 1: Vary D (system size)
  - X unchanged → candidate B
  - X scales with D → candidate L
  - X is count of identical things → candidate D

Step 2: Check formula role
  - X appears as threshold/boundary → confirms B
  - X appears multiplied by count → confirms L
  - X appears as multiplier → confirms D

Step 3: Verify predictions
  - B claim: Check D-invariance
  - L claim: Check D-scaling
  - D claim: Check it's actually counting repetition

Step 4: Test cost decomposition
  - Cost = B + D×L should hold
  - If not, revisit mapping
```

---

## Common Mapping Errors

### Error 1: Confusing Intensive and Extensive

**Intensive** (independent of system size) → B
**Extensive** (proportional to system size) → L or D

| Property | Type | BLD |
|----------|------|-----|
| Temperature | Intensive | B (thermal boundary) |
| Energy | Extensive | D×L |
| Pressure | Intensive | B (force/area ratio) |
| Volume | Extensive | D |
| Density | Intensive | B or L depending on context |

### Error 2: Ratio vs Absolute

Ratios are often B (threshold), absolutes are often L or D.

| Quantity | BLD | Why |
|----------|-----|-----|
| Reynolds number Re = ρvL/μ | Ratio | Re_c (critical value) is B |
| Velocity v | Absolute | Part of L (momentum) |
| Length L | Absolute | D (extent) |

### Error 3: Parameter vs Variable

**Parameters** (fixed for a system) are usually B
**Variables** (change during operation) are usually L or D

| Quantity | Type | BLD |
|----------|------|-----|
| V_th (threshold) | Parameter | B |
| V_gs (gate voltage) | Variable | Input that crosses B |
| Conductivity σ | Parameter | B (material property) |
| Current I | Variable | L (flow that scales) |

---

## Cross-Domain Consistency Check

The same observable type should map consistently across domains:

| Observable Type | Circuits | Thermo | Fluids | QM |
|----------------|----------|--------|--------|-----|
| **Threshold** | V_th | T_c | Re_c | Measurement |
| **Coupling** | C, R | κ (thermal) | μ (viscosity) | Entanglement |
| **Count** | N (devices) | N (particles) | - | N (qubits) |

If "threshold" is B in circuits, it should be B in all domains.

---

## Application to Existing Documentation

### Circuits (Validated)

| Mapping | Rule | Status |
|---------|------|--------|
| B = V_th | Rule 1 (D-invariant) | VALIDATED (CV = 0%) |
| L = C | Rule 2 (scales with D) | VALIDATED (R² = 1.0) |
| D = transistor count | Rule 3 (repetition) | VALIDATED |

### Thermodynamics (Validated)

| Mapping | Rule | Status |
|---------|------|--------|
| B = energy barriers | Rule 1 (topology of landscape) | VALIDATED |
| L = Fisher metric | Rule 2 (scales with correlations) | VALIDATED |
| D = configuration dimension | Rule 3 (degrees of freedom) | VALIDATED |

### Quantum Mechanics (Exploratory)

| Mapping | Rule | Status |
|---------|------|--------|
| B = measurement | Rule 1 (collapse same for any N) | TESTABLE |
| L = entanglement | Rule 2 (should scale with pairs) | TESTABLE |
| D = Hilbert dimension | Rule 3 (count of states) | REASONABLE |

### Phase Transitions (Exploratory)

| Mapping | Rule | Status |
|---------|------|--------|
| B = phase boundary | Rule 1 (T_c invariant) | TESTABLE |
| L = correlation length | Rule 2 (diverges, scales) | TESTABLE |
| D = system size | Rule 3 (lattice sites) | REASONABLE |

---

## When Rules Conflict

If tests give conflicting results:

1. **Reconsider decomposition**: Maybe X is a compound quantity
2. **Check for hidden structure**: X might have both B and L components
3. **Look for boundary cases**: Rules may break down at extremes

**Example**: Entropy S
- Extensive (scales with N) → suggests L or D
- But S = k_B ln Ω is about counting states
- Resolution: S = D × L_per_particle (entropy per particle × particle count)

---

## See Also

- [Validation Roadmap](validation-roadmap.md) — Test status for all claims
- [Circuits](circuits.md) — Validated B/L/D mappings
- [Discovery Method](../../meta/discovery-method.md) — The three questions
- [Glossary](../../glossary.md) — Central definitions
