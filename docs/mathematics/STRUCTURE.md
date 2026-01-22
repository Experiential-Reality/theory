# BLD Theory Derivation Structure

This document maps how derivations connect — the DAG of dependencies that forms the theory's structure.

---

## Layer Model

```
Layer 0: Axioms (BLD primitives, Lie correspondence)
Layer 1: Core Derivations (octonions, Killing form, genesis)
Layer 2: Physics Derivations (masses, forces, cosmology)
Layer 3: Validations (cross-domain, error analysis)
```

---

## Dependency DAG

```
                           ┌──────────────────────┐
                           │     ENTRY POINTS     │
                           └──────────┬───────────┘
                                      │
              ┌───────────────────────┼───────────────────────┐
              │                       │                       │
              ▼                       ▼                       ▼
┌─────────────────────┐  ┌─────────────────────┐  ┌─────────────────────┐
│    CLAUDE.md        │  │     README.md       │  │   glossary.md       │
│  (context seed)     │  │  (entry point)      │  │ (definitions)       │
└─────────────────────┘  └──────────┬──────────┘  └─────────────────────┘
                                    │
                    ┌───────────────┴───────────────┐
                    │                               │
                    ▼                               ▼
        ┌───────────────────┐           ┌───────────────────┐
        │  meta/            │           │  foundations/     │
        │                   │           │                   │
        │ • discovery-method│           │ • bld-calculus    │
        │ • proof-status    │           │ • irreducibility  │
        └─────────┬─────────┘           │ • completeness    │
                  │                     │ • octonion-*      │
                  │                     └─────────┬─────────┘
                  │                               │
                  └───────────────┬───────────────┘
                                  │
                                  ▼
                      ┌───────────────────┐
                      │   lie-theory/     │
                      │                   │
                      │ • lie-corresp     │◀─── BLD = Lie (key result)
                      │ • killing-form    │◀─── K=2 (grounds corrections)
                      │ • boundary-deriv  │
                      │ • constructive    │
                      └─────────┬─────────┘
                                │
        ┌───────────────────────┼───────────────────────┐
        │                       │                       │
        ▼                       ▼                       ▼
┌───────────────┐      ┌───────────────┐      ┌───────────────┐
│   quantum/    │      │  cosmology/   │      │particle-phys/ │
│               │      │               │      │               │
│ • planck-deriv│      │ • genesis     │      │ • lepton-mass │
│ • born-rule   │      │ • ref-scale   │      │ • quark-mass  │
│ • chirality   │      │ • observer    │      │ • boson-mass  │
│ • schrodinger │      │ • dark-map    │      │ • fine-struct │
│ • bld-is-qm   │      │ • cyclic      │      │ • e7-connect  │
└───────────────┘      └───────────────┘      └───────────────┘
        │                       │                       │
        └───────────────────────┼───────────────────────┘
                                │
                                ▼
                      ┌───────────────────┐
                      │    derived/       │
                      │                   │
                      │ • manifold-*      │
                      │ • thermodynamics  │
                      │ • special-rel     │
                      │ • general-rel     │
                      │ • performance     │
                      └───────────────────┘
```

---

## Hub Files (High In-Degree)

These files are referenced by many others — understand them first:

| File | What It Provides | Referenced By |
|------|------------------|---------------|
| `lie-theory/lie-correspondence.md` | BLD = Lie equivalence | All physics derivations |
| `lie-theory/killing-form.md` | K=2 (observer cost) | All K/X corrections |
| `foundations/irreducibility-proof.md` | B, L, D are minimal | Completeness, quantum |
| `cosmology/observer-correction.md` | K/X framework | All precision derivations |
| `foundations/octonion-necessity.md` | n=4, B=56 | Genesis, E7, particle masses |

---

## Leaf Files (Derive Final Results)

These files produce the numerical predictions:

| File | What It Derives | Key Result |
|------|-----------------|------------|
| `particle-physics/fine-structure-consistency.md` | α⁻¹ | 137.035999177 (0.0 ppt) |
| `particle-physics/lepton-masses.md` | m_e, μ/e, τ/μ | All exact (0%) |
| `particle-physics/quark-masses.md` | u, d, s, c, b, t | <0.5% error |
| `particle-physics/boson-masses.md` | H, Z, W | Within measurement |
| `quantum/planck-derivation.md` | M_P, ℏ | 0.00003% error |
| `cosmology/cosmology-structure.md` | Dark matter % | 27% (exact) |

---

## Critical Dependency Chains

### 1. Fine Structure Constant
```
irreducibility → lie-correspondence → octonion-necessity → e7-connection
                                                              ↓
                                                    fine-structure-consistency
                                                              ↓
                                                         α⁻¹ = 137.036
```

### 2. Particle Masses
```
killing-form → observer-correction → lepton-masses
                                  → quark-masses
                                  → boson-masses
```

### 3. Cosmology
```
nothing-instability → genesis-function → cosmology-structure → dark-matter-mapping
        ↓
   chirality-cpt
```

### 4. Quantum Mechanics
```
bld-calculus → quantum-mechanics → schrodinger-derivation
                                → born-rule
                                → planck-derivation
```

---

## Reading Orders

### For Physicists
1. `lie-theory/lie-correspondence.md` — See the Lie equivalence
2. `particle-physics/fine-structure-consistency.md` — α⁻¹ derivation
3. `particle-physics/lepton-masses.md` — Mass predictions
4. `quantum/planck-derivation.md` — ℏ from structure

### For Mathematicians
1. `foundations/irreducibility-proof.md` — Minimal primitives
2. `foundations/completeness-proof.md` — Sufficiency
3. `lie-theory/lie-correspondence.md` — BLD = Lie
4. `derived/manifold-foundations.md` — Geometric structure

### For Understanding K/X Framework
1. `lie-theory/killing-form.md` — What K=2 means
2. `cosmology/observer-correction.md` — How K/X works
3. `particle-physics/fine-structure-consistency.md` — K/X applied to α
4. `particle-physics/lepton-masses.md` — K/X applied to masses

### Quick Start (D≈7)
1. `CLAUDE.md` — Context seed
2. `meta/discovery-method.md` — The three questions
3. `lie-theory/killing-form.md` — K=2 grounds everything
4. Any leaf file — See a complete derivation

---

## File Relationships (Adjacency)

```
bld-calculus ───────────► irreducibility ───────────► completeness
     │                          │                          │
     │                          ▼                          │
     │                   octonion-necessity                │
     │                          │                          │
     ▼                          ▼                          ▼
lie-correspondence ◄──── killing-form ────────────► boundary-derivation
     │                          │
     │              ┌───────────┼───────────┐
     │              │           │           │
     │              ▼           ▼           ▼
     │     observer-corr   genesis    energy-deriv
     │              │           │           │
     │              ▼           ▼           ▼
     └─────► particle-phys   cosmology   force-struct
                    │           │           │
                    ▼           ▼           ▼
              (masses)    (dark matter)  (4 forces)
```

---

## Status Key

| Tag | Meaning |
|-----|---------|
| DERIVED | Follows from BLD axioms with no empirical input |
| VALIDATED | Checked against observation |
| FOUNDATIONAL | Axiom or definition |
| SPECULATIVE | Plausibility argument only |
