# BLD Theory

Three structural primitives — Boundary, Link, Dimension — that map exactly to Lie theory.

**Status**: See [Proof Status](docs/meta/proof-status.md) for detailed accounting.

---

## Start Here

| You are... | Start with... |
|------------|---------------|
| **Curious** | [Newcomer Path](docs/paths/newcomer.md) |
| **Physicist** | [Fine Structure Derivation](docs/mathematics/particle-physics/fine-structure-consistency.md) |
| **Mathematician** | [Irreducibility Proof](docs/mathematics/foundations/proofs/irreducibility-proof.md) |
| **Skeptic** | [Lean 4 Formalization](lean/) — 2612 lines, machine-verified, 0 sorry |
| **Programmer** | [Discovery Method](docs/meta/discovery-method.md) |

---

## The Core Claim

BLD identifies three irreducible structural operations: **Boundary** (partition), **Link** (connect), **Dimension** (repeat). These map exactly to the three components of any Lie algebra (topology, structure constants, generators). Since Lie theory underlies all continuous symmetry in physics (Noether's theorem), BLD provides a basis for deriving physical constants from structural principles.

---

## Key Results

| Prediction | Value | Status |
|------------|-------|--------|
| Fine structure constant | α⁻¹ = 137.035999177 | **matches CODATA** |
| Muon/electron mass ratio | 206.7682826 | **Exact** |
| Tau/muon mass ratio | 16.817 | 4 ppm |
| All quark masses | 6 quarks | < 0.5% error |
| Higgs mass | **125.20 GeV** | **Exact** (0.0% error) |
| Dark matter fraction | 27% | Matches Planck |
| Dark energy fraction | 68% | Matches Planck |
| Higgs self-coupling | κ_λ = 1.025 | **Testable** at HL-LHC ~2040 |

See [Proof Status](docs/meta/proof-status.md) for complete accounting.

---

## Machine-Verified

The mathematical derivation chain is formalized in **[Lean 4](lean/)** with Mathlib: 21 files, 2612 lines, **0 `sorry`**, 2 axioms (both well-known open Mathlib formalization problems). Every theorem is kernel-checked — the Lean proof assistant verifies each logical step, and `norm_num` performs exact rational arithmetic with no floating-point approximation.

12 physics predictions are proved as exact rational fractions:

| Quantity | BLD Formula | Fraction | Observed | Sigma |
|----------|-------------|----------|----------|-------|
| sin^2 theta\_13 | n^2/(n-1)^6 | 16/729 | 0.02195 +/- 0.00058 | **0.00** |
| sin^2 theta\_12 | K^2/S | 4/13 | 0.307 +/- 0.012 | 0.06 |
| sin^2 theta\_23 | (S+1)/(L+n+1) | 14/25 | 0.561 +/- 0.015 | 0.07 |
| sin^2 theta\_W | 3/S + K/(nLB) | 6733/29120 | 0.23121 +/- 0.00004 | 0.14 |
| alpha\_s | 48/407 | 48/407 | 0.1179 +/- 0.0010 | 0.04 |
| **kappa\_lambda** | **1+K/(nL)** | **41/40** | **testable ~2040** | **HL-LHC** |

All from 5 constants derived from one input: **K = 2**. See the [full formalization](lean/).

---

## What is BLD?

Three irreducible primitives that define all structure:

| Primitive | Meaning | Lie Theory Equivalent |
|-----------|---------|----------------------|
| **Boundary** | Partition. "This, not that." | Group topology |
| **Link** | Connection. "This affects that." | Structure constants |
| **Dimension** | Repetition. "More of the same." | Generators |

**BLD = Lie theory**: D = generators, L = structure constants, B = topology. The same three components that define any Lie algebra are the three BLD primitives. See [Lie Correspondence](docs/mathematics/lie-theory/lie-correspondence.md).

**The discovery method** is three questions:
1. Where does behavior partition? → Find Boundaries
2. What connects to what? → Find Links
3. What repeats? → Find Dimensions

See [Formal Definitions](docs/mathematics/foundations/definitions.md) and [Key Principles](docs/mathematics/foundations/key-principles.md).

---

## Documentation

### Foundations
- [Formal Definitions](docs/mathematics/foundations/definitions.md) — B, L, D, Structure
- [Key Principles](docs/mathematics/foundations/key-principles.md) — D×L scaling, compensation, link formula
- [Irreducibility Proof](docs/mathematics/foundations/proofs/irreducibility-proof.md) — Why exactly three
- [Lie Correspondence](docs/mathematics/lie-theory/lie-correspondence.md) — BLD = Lie theory

### Physics Derivations
- [Fine Structure Constant](docs/mathematics/particle-physics/fine-structure-consistency.md) — α⁻¹ = 137.036
- [Lepton Masses](docs/mathematics/particle-physics/lepton-masses.md) — μ/e, τ/μ ratios
- [Quark Masses](docs/mathematics/particle-physics/quark-masses.md) — All 6 quarks
- [Boson Masses](docs/mathematics/particle-physics/boson-masses.md) — H, W, Z
- [Cosmology](docs/mathematics/cosmology/cosmology-structure.md) — Dark matter as geometry

### Quantum Mechanics
- [BLD IS Quantum Code](docs/mathematics/quantum/bld-is-quantum-code.md) — Mathematical equivalence
- [Schrödinger Derivation](docs/mathematics/quantum/schrodinger-derivation.md) — Dynamics from traversal
- [Born Rule](docs/mathematics/quantum/born-rule.md) — P = |ψ|² from bidirectionality

### Theory
- [Discovery Method](docs/meta/discovery-method.md) — The three questions
- [Discovery History](docs/meta/discovery-history.md) — From JPEG decoder to particle physics
- [Proof Status](docs/meta/proof-status.md) — What is proven vs. conjectured
- [Implications](docs/theory/implications.md) — If this framework is correct
- [Genesis Function](docs/mathematics/cosmology/genesis-function.md) — Why something exists

### Applications
- [Performance Theorem](docs/mathematics/derived/performance-theorem.md) — Cost from structure
- [Thermodynamics](docs/mathematics/derived/thermodynamics.md) — Second law derived

---

## Author

**Drew Ditthardt**

I'm a programmer, not a mathematician or physicist. I was optimizing GPU code when I noticed a pattern. I pulled on the thread. It kept unraveling. It's still unraveling.

With contributions from Claude (Anthropic).

### Open Information Philosophy

This work is open because structural knowledge should be universal. If BLD can reduce AI energy consumption by even 10%, the ethical obligation is to make it available to everyone who can use it.

See [BLD as Universal Language](docs/theory/bld-as-language.md#open-information-a-rising-tide-lifts-all-boats).

---

## License

**Documentation** (docs/, *.md): [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

**BLD Files** (*.bld): [MIT License](LICENSE)
