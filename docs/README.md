# BLD Theory Documentation

> **Boundary, Link, Dimension**: A structural language that compiles to physics, code, and mathematics.

---

## Why BLD Matters

BLD is not just a theory—it's a **language**. Like how a programming language compiles to machine code, BLD compiles to:
- **Physics**: Quantum mechanics, particle masses, coupling constants
- **Code**: Any programming language (C, Rust, WGSL, Python)
- **Mathematics**: Lie algebras, group theory, differential geometry

### The Self-Hosting Proof

The strongest evidence for BLD is that it is **self-hosted**: BLD can describe its own compiler.

| Claim | Evidence |
|-------|----------|
| BLD describes structure | [Structural Language](theory/structural-language.md) |
| BLD compiles to code | [Code Generation](applications/code/code-generation.md) |
| BLD compiles to physics | [Physics Traverser](examples/physics-traverser.md) |
| BLD describes itself | [Self-Reference](theory/self-reference.md) |

A language that can compile itself proves it captures something fundamental about computation and structure.

---

## The Three Primitives

| Primitive | What it captures | Lie theory | Code | Physics |
|-----------|------------------|------------|------|---------|
| **B** (Boundary) | Partition/choice | Topology | `if/match` | Quantum measurement |
| **L** (Link) | Connection/reference | Structure constants | `&/ptr` | Interaction |
| **D** (Dimension) | Repetition/extent | Generators | `[]/loop` | Spacetime |

These three are **irreducible**: none can be expressed in terms of the others. See [Irreducibility Proof](mathematics/foundations/proofs/irreducibility-proof.md).

---

## Key Experimental Results

| Quantity | BLD Prediction | Observed | Error | Status |
|----------|---------------|----------|-------|--------|
| α⁻¹ | 137.035999177 | 137.035999177 | **matches CODATA** | [DERIVED](mathematics/particle-physics/e7-derivation.md) |
| m_H | **125.20 GeV** | 125.20 GeV | **0.0%** | [DERIVED](mathematics/particle-physics/boson-masses.md) |
| M_P | 1.220890×10¹⁹ GeV | 1.220890×10¹⁹ GeV | <0.01% | [DERIVED](mathematics/quantum/planck-derivation.md) |
| μ/e ratio | 206.768282600 | 206.768282600 | **0.3 ppt** | [DERIVED](mathematics/particle-physics/lepton-masses.md) |
| sin²θ₁₂ | 4/13 = 0.30769 | 0.307 ± 0.012 | **0.06σ** | [DERIVED](mathematics/particle-physics/neutrino-mixing.md) |
| sin²θ₁₃ | 16/729 = 0.02195 | 0.02195 ± 0.00058 | **0.00σ** | [DERIVED](mathematics/particle-physics/neutrino-mixing.md) |
| sin²θ₂₃ | 14/25 = 0.560 | 0.561 ± 0.015 | **0.07σ** | [DERIVED](mathematics/particle-physics/neutrino-mixing.md) |

These are not curve fits—they emerge from structural constants B=56, L=20, n=4, K=2, and the accumulated correction e²×120/119.

---

## Proof Architecture

### Layer 0: Axioms (Definitions)
- [BLD Calculus](mathematics/foundations/definitions/bld-calculus.md) — Type-theoretic foundation

### Layer 1: Theorems (Proven)
- [Irreducibility](mathematics/foundations/proofs/irreducibility-proof.md) — B, L, D are independent
- [Lie Correspondence](mathematics/lie-theory/lie-correspondence.md) — BLD = Lie theory exactly
- [Octonion Derivation](mathematics/foundations/derivations/octonion-derivation.md) — Why octonions are required

### Layer 2: Derivations (Logical consequences)
- [E7 Derivation](mathematics/particle-physics/e7-derivation.md) — α⁻¹ = 137.036
- [Planck Derivation](mathematics/quantum/planck-derivation.md) — ℏ from structure
- [Lepton Masses](mathematics/particle-physics/lepton-masses.md) — Mass ratios

### Validation
- [Proof Status](meta/proof-status.md) — Complete status of all claims
- [Verification Report](analysis/math-verification-report.md) — External source verification
- [Error Analysis](analysis/error-analysis.md) — Why errors match observer corrections

---

## Empirical Inputs

Only these are NOT derived from BLD:
- **v** (Higgs VEV = 246 GeV) — reference scale
- **c** (speed of light) — magnitude
- **G** (gravitational constant) — magnitude
- **"SU(3) matter exists"** — selects octonions over quaternions

Everything else—including α⁻¹, ℏ, particle masses, spacetime dimension—follows from BLD structure.

---

## Quick Start

| Goal | Start Here |
|------|------------|
| **Understand BLD basics** | [Glossary](glossary.md) |
| **See the language spec** | [Structural Language](theory/structural-language.md) |
| **Follow a physics derivation** | [E7 Derivation](mathematics/particle-physics/e7-derivation.md) |
| **See code generation** | [Code Generation](applications/code/code-generation.md) |
| **Verify the math** | [Verification Report](analysis/math-verification-report.md) |
| **Understand the errors** | [Error Analysis](analysis/error-analysis.md) |

---

## Directory Structure

```
docs/
├── mathematics/          # Core derivations
│   ├── foundations/      # BLD calculus, irreducibility, octonions
│   ├── lie-theory/       # Killing form, Lie correspondence
│   ├── quantum/          # Schrödinger, Born rule, Planck
│   ├── particle-physics/ # E7, masses, fine structure
│   └── cosmology/        # Observer corrections
├── applications/
│   ├── code/             # BLD → programming languages
│   └── physics/          # BLD → physical systems
├── theory/               # Foundational documents
├── examples/             # Worked examples (ZIP, JPEG, spacetime)
├── meta/                 # Proof status, methodology
├── analysis/             # Verification, consistency reports
└── paths/                # Reading paths by audience
```

---

## The Compiler Analogy

```
BLD Source          Compilation Target
─────────────────────────────────────────
(B, L, D) ────────→ Lie algebra
(B, L, D) ────────→ Python code
(B, L, D) ────────→ C code
(B, L, D) ────────→ WGSL shader
(B, L, D) ────────→ Physics equations
(B, L, D) ────────→ BLD (self-hosted!)
```

The same structural specification compiles to different targets. This is why BLD works across domains.

---

## Reading Paths

### For Physicists
1. [E7 Derivation](mathematics/particle-physics/e7-derivation.md) — How α⁻¹ emerges
2. [Physics Traverser](examples/physics-traverser.md) — Full physics derivation
3. [Planck Derivation](mathematics/quantum/planck-derivation.md) — ℏ from structure

### For Mathematicians
1. [BLD Calculus](mathematics/foundations/definitions/bld-calculus.md) — Formal type system
2. [Irreducibility Proof](mathematics/foundations/proofs/irreducibility-proof.md) — B, L, D independence
3. [Lie Correspondence](mathematics/lie-theory/lie-correspondence.md) — Connection to Lie theory

### For Software Engineers
1. [BLD-Driven Development](applications/code/bld-driven-development.md) — Methodology
2. [Code Generation](applications/code/code-generation.md) — Multi-target compilation
3. [Discovery Method](meta/discovery-method.md) — The three questions

---

## External Verification

All mathematical claims have been verified against external sources:
- Physics constants: [CODATA 2022](https://physics.nist.gov/cuu/Constants/), [PDG 2024](https://pdg.lbl.gov/)
- Lie theory: Standard textbooks, [nLab](https://ncatlab.org/)
- See [Verification Report](analysis/math-verification-report.md) for details.

---

## Contributing

See [Proof Status](meta/proof-status.md) for open questions and areas needing work.
