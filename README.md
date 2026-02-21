# BLD Theory

The grammar of structure. Three irreducible primitives — **Boundary**, **Link**, **Dimension** — that generate 50 quantities across nine domains from five derived integers, with zero free parameters.

**Status**: See [Proof Status](docs/meta/proof-status.md) for detailed accounting.

---

## Start Here

| You are... | Start with... |
|------------|---------------|
| **Curious** | [Newcomer Path](docs/paths/newcomer.md) |
| **No math please** | [Layman Path](docs/paths/layman.md) |
| **Physicist** | [Physicist Path](docs/paths/physicist.md) |
| **Mathematician** | [Mathematician Path](docs/paths/mathematician.md) |
| **Engineer** | [Von Kármán Constant](docs/mathematics/classical/von-karman-derivation.md) — κ = 0.384, first derivation |
| **Skeptic** | [Lean 4 Formalization](lean/) — 63 files, 14,321 lines, 0 sorry, 0 axioms |
| **Programmer** | [Practitioner Path](docs/paths/practitioner.md) |
| **LLM** | [LLM Path](docs/paths/llm.md) — file registry, concept index |

---

## The Core Claim

BLD identifies three irreducible constructors of **all** structure: **Boundary** (partition), **Link** (connect), **Dimension** (repeat). Self-observation closure — the requirement that structure can consistently reference itself — uniquely determines five integers:

| Constant | Value | Derived From | Meaning |
|----------|-------|--------------|---------|
| **K** | 2 | Bidirectional observation (Killing form) | Observation cost |
| **n** | 4 | sl(2,ℂ) ⊂ sl(2,𝕆) reference fixing | Spacetime dimensions |
| **L** | 20 | n²(n²−1)/12 (Riemann tensor) | Link components |
| **B** | 56 | 2 × dim(Spin(8)) (triality closure) | Boundary modes |
| **S** | 13 | (B−n)/n | Structural intervals |

From these five integers, with zero free dimensionless parameters, we derive **50 quantities across nine domains** — particle physics, cosmology, quantum foundations, turbulence, chaos, molecular biology, thermodynamics, circuits, and music — all matching experiment to within measurement uncertainty.

This is not a physics theory with applications. It is a theory of structure itself, validated by physics.

**BLD = Lie theory**: D = generators, L = structure constants, B = topology. The same three components that define any Lie algebra are the three BLD primitives. See [Lie Correspondence](docs/mathematics/lie-theory/lie-correspondence.md).

---

## The Discovery Method

Three questions, applied to any domain:

1. **Where does behavior partition?** → Find Boundaries
2. **What connects across that partition?** → Find Links
3. **What repeats?** → Find Dimensions

**Example — deriving the von Kármán constant (turbulence):**
- **B**: The wall partitions solid from fluid
- **L**: Turbulent eddies transfer momentum across the boundary layer
- **D**: Self-similar structure repeats at every height from the wall
- **Result**: κ = K/((n−1)+K) × (1 − μ) = 2/5 × 24/25 = **0.384** — matches high-Re DNS exactly

The same method derives α⁻¹ = 137.036 (particle physics), δ = 4.669 (chaos theory), 20 amino acids (biology), and the Second Law of thermodynamics.

See [Discovery Method](docs/meta/discovery-method.md) and [Formal Definitions](docs/mathematics/foundations/definitions.md).

---

## Key Results

### Particle Physics

| Prediction | BLD Value | Observed | Status |
|------------|-----------|----------|--------|
| Fine structure constant | α⁻¹ = 137.035999177 | 137.035999177 | **matches CODATA** |
| Muon/electron mass ratio | 206.7682826 | 206.7682827 | **0.5 ppb** |
| Tau/muon mass ratio | 16.8172 | 16.8171 | 4 ppm |
| All 6 quark masses | From confined-phase model | — | < 0.5% error |
| Higgs mass | 125.20 GeV | 125.20(11) GeV | **0.0σ** |
| Z boson mass | 91.187 GeV | 91.188(2) GeV | 0.3σ |
| W boson mass | 80.373 GeV | 80.377(12) GeV | 0.3σ |
| Planck mass | 1.221 × 10¹⁹ GeV | 1.221 × 10¹⁹ GeV | 0.002% |
| Weak mixing angle | sin²θ_W = 0.23122 | 0.23121(4) | 0.03σ |
| 3 PMNS neutrino angles | Exact rational fractions | — | χ² = 0.008 |
| Higgs self-coupling | **κ_λ = 41/40 = 1.025** | **not yet** | **HL-LHC ~2030** |

### Cosmology

| Prediction | BLD Value | Observed | Status |
|------------|-----------|----------|--------|
| Dark matter fraction | 27.0% | 27(1)% | 0.0σ |
| Dark energy fraction | 68.0% | 68(1)% | 0.0σ |
| H₀ (CMB) | 67.2 km/s/Mpc | 67.4(5) | 0.4σ |
| H₀ (local) | 72.8 km/s/Mpc | 73.0(10) | 0.2σ |
| Hubble tension | Resolved: H₀(local)/H₀(CMB) = 13/12 | — | **Structural** |

### Turbulence and Chaos

| Prediction | BLD Value | Observed | Status |
|------------|-----------|----------|--------|
| Critical Reynolds (pipe) | Re_c = 2300.5 | 2300 | 0.02% |
| Kolmogorov exponent | −5/3 = −L/(n(n−1)) | −5/3 | **exact** |
| She-Leveque exponents | ζ_p = p/9 + 2(1−(2/3)^(p/3)) | 8 values | < 0.5% |
| Feigenbaum δ | 4.66920 | 4.66920 | **0.00003%** |
| Feigenbaum α_F | 2.50291 | 2.50291 | **5×10⁻⁷%** |
| Von Kármán κ | 48/125 = 0.384 | 0.384(4) | **exact** |

### Biology, Thermodynamics, and Beyond

| Prediction | BLD Value | Observed | Status |
|------------|-----------|----------|--------|
| Amino acids | L = 20 | 20 | **exact** |
| Coding codons | L(n−1)+1 = 61 | 61 | **exact** |
| Degeneracy modulus | n(n−1) = 12 | {1,2,3,4,6} ∣ 12 | **exact** |
| Second Law | dS/dt = ‖·‖²(g_K) ≥ 0 | universal | **derived** |
| Semitones | n(n−1) = 12 | 12 | **exact** |
| Born rule | P = |ψ|² from K = 2 | universal | **derived** |

**First derivations from first principles**: Feigenbaum constants (45+ years numerical only), She-Leveque parameters (30+ years fitted), von Kármán constant (100+ years empirical).

See [Proof Status](docs/meta/proof-status.md) for complete accounting.

---

## Machine-Verified

The mathematical derivation chain is formalized in **[Lean 4](lean/)** with Mathlib: **63 files, 14,321 lines, 0 `sorry`, 0 axioms**. The Cartan classification is fully proved: every indecomposable positive-definite GCM is one of 9 Dynkin types. Every theorem is kernel-checked — the Lean proof assistant verifies each logical step, and `norm_num` performs exact rational arithmetic with no floating-point approximation.

12 physics predictions are proved as exact rational fractions:

| Quantity | BLD Formula | Fraction | Observed | Sigma |
|----------|-------------|----------|----------|-------|
| sin²θ\_13 | n²/(n−1)⁶ | 16/729 | 0.02195 ± 0.00058 | **0.00** |
| sin²θ\_12 | K²/S | 4/13 | 0.307 ± 0.012 | 0.06 |
| sin²θ\_23 | (S+1)/(L+n+1) | 14/25 | 0.561 ± 0.015 | 0.07 |
| sin²θ\_W | 3/S + K/(nLB) | 6733/29120 | 0.23121 ± 0.00004 | 0.14 |
| α\_s | 48/407 | 48/407 | 0.1179 ± 0.0010 | 0.04 |
| **κ\_λ** | **1+K/(nL)** | **41/40** | **testable ~2030** | **HL-LHC** |

All from 5 constants derived from one input: **K = 2**. See the [full formalization](lean/).

---

## Documentation

### Foundations
- [Formal Definitions](docs/mathematics/foundations/definitions.md) — B, L, D, Structure
- [Key Principles](docs/mathematics/foundations/key-principles.md) — D×L scaling, compensation, link formula
- [Irreducibility Proof](docs/mathematics/foundations/proofs/irreducibility-proof.md) — Why exactly three
- [Lie Correspondence](docs/mathematics/lie-theory/lie-correspondence.md) — BLD = Lie theory
- [Genesis Function](docs/mathematics/cosmology/genesis-function.md) — Why something exists
- [Constants](docs/mathematics/foundations/constants.md) — The five integers derived

### Particle Physics
- [Fine Structure Constant](docs/mathematics/particle-physics/fine-structure-consistency.md) — α⁻¹ = 137.036
- [Lepton Masses](docs/mathematics/particle-physics/lepton-masses.md) — μ/e, τ/μ ratios
- [Quark Masses](docs/mathematics/particle-physics/quark-masses.md) — All 6 quarks
- [Boson Masses](docs/mathematics/particle-physics/boson-masses.md) — H, W, Z, Planck mass
- [Force Structure](docs/mathematics/particle-physics/force-structure.md) — Gauge couplings from K/X

### Cosmology
- [Cosmological Structure](docs/mathematics/cosmology/cosmology-structure.md) — Dark matter, dark energy, Λ
- [Observer Corrections](docs/mathematics/cosmology/observer-correction.md) — K/X framework

### Quantum Mechanics
- [Born Rule](docs/mathematics/quantum/born-rule.md) — P = |ψ|² from K = 2
- [Schrödinger Derivation](docs/mathematics/quantum/schrodinger-derivation.md) — Dynamics from traversal
- [BLD IS Quantum Code](docs/mathematics/quantum/bld-is-quantum-code.md) — Mathematical equivalence

### Cross-Domain Universality
- [Feigenbaum Constants](docs/mathematics/classical/feigenbaum-derivation.md) — δ, α_F from first principles
- [She-Leveque Exponents](docs/mathematics/classical/she-leveque-derivation.md) — Turbulence structure functions
- [Von Kármán Constant](docs/mathematics/classical/von-karman-derivation.md) — κ = 0.384 from first principles
- [Reynolds Numbers](docs/mathematics/classical/reynolds-derivation.md) — Re_c = 2300 and variants
- [Thermodynamics](docs/mathematics/classical/thermodynamics.md) — Second Law derived
- [Genetic Code](docs/applications/biology/genetic-code.md) — 20 amino acids, 61 codons, degeneracy
- [Circuits](docs/applications/physics/circuits.md) — D×L scaling, B invariance
- [Music Theory](docs/applications/music-theory.md) — 12 semitones from n(n−1)
- [Black Hole Entropy](docs/mathematics/quantum/black-hole-entropy.md) — S = K×L

### Theory and Meta
- [Discovery Method](docs/meta/discovery-method.md) — The three questions
- [Discovery History](docs/meta/discovery-history.md) — From JPEG decoder to particle physics
- [Proof Status](docs/meta/proof-status.md) — What is proven vs. conjectured
- [Implications](docs/theory/README.md#implications) — If this framework is correct

### The Paper
- [BLD Paper](paper/bld-paper.pdf) — Full paper (50 quantities, 9 domains, 48 pages)

### Applications
- [Performance Theorem](docs/applications/ml/performance-theorem.md) — Cost from structure
- [BLD-Driven Development](docs/applications/code/bld-driven-development.md) — Software from structure

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
