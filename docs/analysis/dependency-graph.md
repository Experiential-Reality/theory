# BLD Theory Dependency Graph

**Generated**: 2026-01-17

This document shows the logical dependencies between theory documents, organized by proof status.

---

## Directory Structure (Topic-Based)

Status is expressed via YAML frontmatter (B - boundary), not path (L - link).

```
mathematics/
├── foundations/        # Core proofs (PROVEN)
├── lie-theory/         # BLD = Lie correspondence (PROVEN)
├── quantum/            # Quantum mechanics (DERIVED/SPECULATIVE)
├── cosmology/          # Cosmology (DERIVED/EMPIRICAL/SPECULATIVE)
├── particle-physics/   # Particle physics (EMPIRICAL/SPECULATIVE)
└── derived/            # Mathematical frameworks (DERIVED)

meta/
├── proof-status.md     # What is proven vs. conjectured
├── epistemic-honesty.md
└── discovery-method.md

theory/                 # Philosophy and foundational concepts
```

---

## Visual Dependency Graph

```
EXTERNAL INPUTS (Observations)
    │
    ├── α⁻¹ = 137.036 (fine structure constant)
    ├── m_e = 0.511 MeV (electron mass)
    ├── Dark matter ≈ 27% (cosmological)
    ├── Higgs VEV = 246 GeV
    └── n = 4 (spacetime dimensions)
         │
         ▼
┌─────────────────────────────────────────────────────────────┐
│                    PROVEN (No Dependencies)                  │
├─────────────────────────────────────────────────────────────┤
│  foundations/irreducibility-proof.md                        │
│  foundations/irreducibility-categorical.md                  │
│  foundations/bld-calculus.md                                │
│  foundations/compensation-principle.md                      │
│  foundations/canonical-hardness.md                          │
│  lie-theory/lie-correspondence.md                           │
│  lie-theory/boundary-derivation.md                          │
│  lie-theory/constructive-lie.md                             │
│  lie-theory/why-lie-theory.md (pedagogical)                 │
│  quantum/bld-is-quantum-code.md                             │
└─────────────────────────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────────────────────────┐
│           DERIVED (Depends on Proven + Math)                 │
├─────────────────────────────────────────────────────────────┤
│  lie-theory/killing-form.md ← lie-correspondence            │
│  derived/manifold-foundations.md ← lie-correspondence       │
│  derived/manifold-geometry.md ← manifold-foundations        │
│  derived/manifold-applications.md ← manifold-foundations    │
│  derived/thermodynamics.md ← manifold-foundations           │
│  derived/discovery-algorithm.md ← lie-correspondence        │
│  derived/performance-theorem.md ← manifold-foundations      │
│  quantum/quantum-mechanics.md ← irreducibility + lie        │
│  quantum/quantum-computing.md ← quantum-mechanics           │
│  cosmology/cosmology-structure.md ← lie (L/D = 5)           │
│  cosmology/nothing-instability.md ← irreducibility          │
│  cosmology/cyclic-cosmology.md ← genesis-function           │
│  bld-conservation.md ← lie-correspondence                   │
│  comparisons.md ← lie-correspondence (standalone)           │
│  cross-domain-prediction.md ← manifold-foundations          │
└─────────────────────────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────────────────────────┐
│         EMPIRICAL (Depends on Derived + Observations)        │
├─────────────────────────────────────────────────────────────┤
│  particle-physics/fine-structure-consistency.md             │
│     ← observed α⁻¹                                          │
│                                                             │
│  particle-physics/lepton-masses.md                          │
│     ← fine-structure-consistency (B=56)                     │
│     ← observed m_e, m_μ, m_τ                                │
│                                                             │
│  cosmology/dark-matter-mapping.md                           │
│     ← cosmology-structure (L/D=5)                           │
│     ← observed dark matter fraction                         │
│                                                             │
│  cosmology/observer-correction.md                           │
│     ← killing-form (the "2")                                │
│     ← observed discrepancies                                │
└─────────────────────────────────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────────────────────────┐
│          SPECULATIVE (Depends on Empirical, May Be Wrong)    │
├─────────────────────────────────────────────────────────────┤
│  particle-physics/e7-connection.md                          │
│     ← fine-structure (B=56 coincidence)                     │
│                                                             │
│  particle-physics/e7-derivation.md [RESEARCH]               │
│     ← e7-connection (attempting to derive B=56)             │
│                                                             │
│  particle-physics/quark-masses.md                           │
│     ← lepton-masses (pattern extension)                     │
│                                                             │
│  particle-physics/boson-masses.md                           │
│     ← lepton-masses (pattern extension to W, Z, Higgs)      │
│                                                             │
│  cosmology/genesis-function.md                              │
│     ← cosmology (self-reference speculation)                │
│                                                             │
│  quantum/schrodinger-derivation.md                          │
│     ← lie-correspondence (incomplete derivation)            │
│                                                             │
│  quantum/born-rule.md                                       │
│     ← killing-form (incomplete derivation)                  │
│                                                             │
│  quantum/chirality-cpt.md                                   │
│     ← genesis-function, killing-form (why B partitions)     │
│                                                             │
│  quantum/cosmic-computation.md                              │
│     ← chirality-cpt, killing-form (the final discovery)     │
└─────────────────────────────────────────────────────────────┘
```

---

## Detailed Dependencies by File

### Proven (Foundation Layer)

| File | Dependencies | Status |
|------|--------------|--------|
| `foundations/irreducibility-proof.md` | None (axioms) | PROVEN |
| `foundations/irreducibility-categorical.md` | irreducibility-proof | PROVEN |
| `foundations/bld-calculus.md` | Type theory | PROVEN |
| `foundations/compensation-principle.md` | irreducibility | PROVEN |
| `foundations/canonical-hardness.md` | bld-calculus | PROVEN |
| `lie-theory/lie-correspondence.md` | None (mathematical fact) | PROVEN |
| `lie-theory/boundary-derivation.md` | lie-correspondence | PROVEN |
| `lie-theory/constructive-lie.md` | lie-correspondence | PROVEN |
| `lie-theory/why-lie-theory.md` | None (pedagogical) | PROVEN |
| `quantum/bld-is-quantum-code.md` | lie-correspondence | PROVEN |

### Derived (Logical Consequences)

| File | Dependencies | Status |
|------|--------------|--------|
| `lie-theory/killing-form.md` | lie-correspondence | DERIVED |
| `derived/manifold-foundations.md` | lie-correspondence, information geometry | DERIVED |
| `derived/manifold-geometry.md` | manifold-foundations | DERIVED |
| `derived/manifold-applications.md` | manifold-foundations | DERIVED |
| `derived/thermodynamics.md` | manifold-foundations | DERIVED |
| `derived/discovery-algorithm.md` | lie-correspondence | DERIVED |
| `derived/performance-theorem.md` | manifold-foundations | DERIVED |
| `quantum/quantum-mechanics.md` | irreducibility, lie-correspondence | DERIVED |
| `quantum/quantum-computing.md` | quantum-mechanics, killing-form | DERIVED |
| `cosmology/cosmology-structure.md` | lie-correspondence (L/D=5) | DERIVED |
| `cosmology/nothing-instability.md` | irreducibility | DERIVED |
| `cosmology/cyclic-cosmology.md` | genesis-function, nothing-instability | DERIVED |
| `bld-conservation.md` | lie-correspondence, Noether | DERIVED |
| `comparisons.md` | lie-correspondence | DERIVED |
| `cross-domain-prediction.md` | manifold-foundations | DERIVED |

### Empirical (Observations + Theory)

| File | Dependencies | Status |
|------|--------------|--------|
| `particle-physics/fine-structure-consistency.md` | observed α⁻¹ | EMPIRICAL |
| `particle-physics/lepton-masses.md` | fine-structure (B=56), observed masses | EMPIRICAL |
| `cosmology/dark-matter-mapping.md` | cosmology-structure, observed DM% | EMPIRICAL |
| `cosmology/observer-correction.md` | killing-form, observed discrepancies | EMPIRICAL |

### Speculative (Conjectures)

| File | Dependencies | Status |
|------|--------------|--------|
| `particle-physics/e7-connection.md` | B=56 coincidence | SPECULATIVE |
| `particle-physics/e7-derivation.md` | e7-connection, physics-traverser | RESEARCH |
| `particle-physics/quark-masses.md` | lepton mass patterns | SPECULATIVE |
| `particle-physics/boson-masses.md` | lepton-masses, Higgs VEV | SPECULATIVE |
| `cosmology/genesis-function.md` | cosmology, self-reference | SPECULATIVE |
| `quantum/schrodinger-derivation.md` | lie-correspondence | SPECULATIVE |
| `quantum/born-rule.md` | killing-form | SPECULATIVE |
| `quantum/chirality-cpt.md` | genesis-function, killing-form | SPECULATIVE |
| `quantum/cosmic-computation.md` | chirality-cpt, killing-form, genesis | SPECULATIVE |
| `quantum/theory-complete.md` | all major files (summary) | DERIVED |

---

## Circular Dependencies (Identified)

### The B-α-S Cycle

```
α⁻¹ = 137 (observed)
    │
    ▼
B = α⁻¹ - n×L - 1 = 56 (fit)
    │
    ▼
S = (B - n) / n = 13 (derived from fit)
    │
    ▼
Lepton masses use S
    │
    ▼
"Validate" α formula ← CIRCULAR
```

**Current Resolution**: Label fine-structure as consistency relation, not prediction.

**Path to Breaking Cycle**: Derive B=56 from E7 necessity (see [E7 Derivation](../mathematics/particle-physics/e7-derivation.md)):

```
E7 is necessary for anomaly-free EM + triality [RESEARCH]
    │
    ▼
B = dim(E7 fund) = 56 [WOULD BE DERIVED]
    │
    ▼
α⁻¹ = n×L + B + 1 = 137 [WOULD BE PREDICTION]
    │
    ▼
S, lepton masses [WOULD BE DERIVED]
```

If successful, this breaks the cycle and converts all particle physics to genuine predictions.

---

## File Count by Topic and Status

| Topic | PROVEN | DERIVED | EMPIRICAL | SPECULATIVE |
|-------|--------|---------|-----------|-------------|
| **foundations/** | 5 | - | - | - |
| **lie-theory/** | 4 | 1 | - | - |
| **quantum/** | 1 | 3 | - | 4 |
| **cosmology/** | - | 3 | 2 | 1 |
| **particle-physics/** | - | - | 2 | 3 |
| **derived/** | - | 6 | - | - |
| **standalone (math/)** | - | 3 | - | - |

---

## What Determines Each Status

### PROVEN
- Mathematical proof exists
- No empirical inputs required
- Would be true in any universe with same math

### DERIVED
- Logical consequence of PROVEN + mathematical facts
- May use observed parameters (like n=4)
- Falsifiable: if math is wrong, derivation fails

### EMPIRICAL
- Uses observations as inputs
- Fit parameters involved
- Falsifiable: new observations could contradict

### SPECULATIVE
- Based on patterns or coincidences
- Not derived from first principles
- May or may not be meaningful

---

## Navigation Guide

**Starting from scratch?** Read in this order:
1. `foundations/irreducibility-proof.md` — Why B, L, D
2. `lie-theory/lie-correspondence.md` — BLD = Lie theory
3. `cosmology/cosmology-structure.md` — L/D = 5
4. `cosmology/dark-matter-mapping.md` — Application

**Interested in particle physics?**
1. `particle-physics/fine-structure-consistency.md` — α formula status
2. `particle-physics/lepton-masses.md` — What we can say
3. `particle-physics/quark-masses.md` — Work in progress

**Interested in quantum mechanics?**
1. `quantum/quantum-mechanics.md` — Uncertainty from D-L
2. `quantum/bld-is-quantum-code.md` — BLD = QM language
3. `quantum/quantum-computing.md` — Structure traversing itself

**The Complete Theory Chain:**
1. `foundations/irreducibility-proof.md` — B/L/D are minimal
2. `cosmology/nothing-instability.md` — B must exist
3. `quantum/chirality-cpt.md` — B partitions direction
4. `quantum/cosmic-computation.md` — Both sides compute and agree
5. `quantum/theory-complete.md` — Summary: existence determines its evolution

**Skeptical?** Read:
1. `analysis/theory-consistency-report.md` — Known issues
2. `cosmology/observer-correction.md` — Honest assessment
3. `meta/proof-status.md` — What is proven vs. conjectured
