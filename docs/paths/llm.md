---
status: FOUNDATIONAL
layer: reference
depends_on: []
used_by:
  - README.md
---

# Reading Path: LLM

> Machine traverser guide. File registry, concept index, dependency topology.

## Quick Orientation

- **155 markdown files** in docs/
- **Zero broken links** (verified by `tools/check_links.py`)
- **Layer system**: Layer 0 (axioms) -> Layer 1 (proofs/Lie) -> Layer 2 (physics) -> App -> Meta
- **Five constants**: K=2, n=4, L=20, B=56, S=13. Everything derives from these.

---

## File Registry

### docs/paths/ (reading guides)

| File | Purpose |
|------|---------|
| newcomer.md | 30-minute intro to BLD concepts |
| mathematician.md | Formal proofs, category theory, 8-step path |
| practitioner.md | Applying BLD to software, 7-step path |
| physicist.md | Physics derivation chain, 7-step path |
| layman.md | No-math overview, everyday examples |
| llm.md | This file. Machine traverser guide. |

### docs/mathematics/foundations/ (Layer 0-1: axioms, proofs, calculus)

| File | Purpose |
|------|---------|
| axioms.md | **START HERE.** Seven axioms: A1-A3 existence, A4-A6 closure, A7 genesis |
| constants.md | The five derived integers (K, n, L, B, S) |
| definitions.md | Informal definitions of B, L, D, Structure |
| key-principles.md | D*L scaling, compensation, link formula |
| key-formulas.md | Core formulas collected |
| notation.md | Notation conventions |
| discovery-method.md | How to derive using BLD (Q1/Q2/Q3) |
| definitions/bld-calculus.md | Formal type system for B/L/D |
| definitions/ubit.md | Unit of BLD information |
| proofs/irreducibility-proof.md | **B, L, D are minimal.** Can't reduce one to others. |
| proofs/irreducibility-categorical.md | Same proof via category theory |
| proofs/completeness-proof.md | B, L, D are sufficient (Lie + Turing routes) |
| proofs/why-exactly-three.md | No 4th primitive exists |
| proofs/axiom-independence.md | Each axiom independent of others |
| derivations/octonion-derivation.md | **n=4, SU(3), 3 generations from octonions** |
| derivations/octonion-necessity.md | Why octonions specifically (genesis closure) |
| derivations/energy-derivation.md | Energy = accumulated K/X |
| derivations/force-structure.md | All four forces from K/X at different scales |
| derivations/gauge-structure.md | Gauge symmetry from BLD |
| derivations/generation-hierarchy.md | Mass hierarchy between generations |
| derivations/epsilon2-origin.md | Origin of epsilon^2 corrections |
| derivations/equation-of-motion.md | Equations of motion from BLD |
| derivations/weak-origin.md | Weak force origin |
| structural/bld-conservation.md | Noether's theorem connection |
| structural/canonical-hardness.md | Finding minimal BLD is NP-complete |
| structural/categorical-correspondence.md | BLD = Category Theory |
| structural/compensation-principle.md | L compensates B |
| structural/factorization-calculus.md | FACTOR operation on structures |
| structural/structural-cost-conservation.md | Cost algebra |
| machine/universal-machine.md | Universe as self-computing structure |
| machine/integer-machine.md | Integers from BLD (sqrt, i, division algebras) |
| machine/integer-factorization.md | Factoring decomposition (K/X=1 bit, Work=N^{1/D}) |
| machine/detection-structure.md | T intersect S formalism for detection |
| machine/machine-visualization.md | Visual guide to machine concepts |

### docs/mathematics/lie-theory/ (Layer 1: BLD = Lie)

| File | Purpose |
|------|---------|
| lie-correspondence.md | **KEY RESULT.** BLD = Lie theory (D=generators, L=structure constants, B=topology) |
| killing-form.md | K=2 from bidirectional observation; appears in hbar/2, Bell 2sqrt(2) |
| why-lie-theory.md | Accessible explanation of the correspondence |
| constructive-lie.md | Alignment as Lie homomorphism |
| boundary-derivation.md | B from SPD curvature |
| exceptional-algebras.md | G2, E7, exceptional structure |

### docs/mathematics/particle-physics/ (Layer 2: masses, couplings)

| File | Purpose |
|------|---------|
| e7-derivation.md | B=56 from triality + Killing form |
| fine-structure-consistency.md | alpha^-1 = 137.035999177 (full formula) |
| lepton-masses.md | mu/e = 206.768, tau/mu = 16.817 |
| quark-masses.md | All 6 quarks (<0.5% error) |
| boson-masses.md | Higgs, W, Z masses |
| particle-classification.md | Particle taxonomy from BLD |
| strong-coupling.md | alpha_s = 48/407 |
| neutrino-mixing.md | PMNS angles as rational fractions |
| neutrino-masses.md | Neutrino mass derivation |
| nucleon-masses.md | Proton, neutron masses |
| higgs-self-coupling.md | **PREDICTED**: kappa_lambda = 41/40 = 1.025 (HL-LHC ~2030) |
| higgs-couplings.md | **PREDICTED**: All kappa values from detection structure |
| muon-g2.md | **PREDICTED**: Delta a_mu = 250e-11 |
| neutron-lifetime.md | **PREDICTED**: Beam-bottle discrepancy = K/S^2 |

### docs/mathematics/quantum/ (Layer 2: QM foundations)

| File | Purpose |
|------|---------|
| born-rule.md | P = |psi|^2 from K=2 bidirectional alignment |
| selection-rule.md | Single-event selection via Dirichlet-Gamma/Gumbel-max |
| quantum-mechanics.md | Uncertainty from D-L irreducibility |
| schrodinger-derivation.md | ihbar dpsi/dt = H psi from BLD + octonions |
| planck-derivation.md | hbar magnitude derived (0.00003%) |
| structural-observer-framework.md | Observer correction algebra |
| chirality-cpt.md | Chirality and CPT from K=2 |
| bld-is-quantum-code.md | BLD = Lie = QM = e^(i*pi)+1=0 |
| quantum-computing.md | Structure traversing itself |
| black-hole-entropy.md | S = K*L |
| entanglement-entropy.md | Entanglement from BLD |
| path-integral.md | Path integral from BLD |
| wave-function-collapse.md | Collapse mechanism |
| cosmic-computation.md | Future constrained by L-consistency |
| theory-complete.md | Complete BLD theory summary |

### docs/mathematics/cosmology/ (Layer 2: dark matter, Hubble, genesis)

| File | Purpose |
|------|---------|
| observer-correction.md | **Unified K/X framework.** All observer corrections. 843 lines. |
| cosmology-structure.md | L/D = 20/4 = 5 derivation |
| dark-matter-mapping.md | Dark matter as geometry |
| scale-derivation.md | v, c, G from BLD structure |
| reference-scale-derivation.md | Fixed-point proof for reference scale |
| genesis-function.md | traverse(-B, B) = existence |
| nothing-instability.md | Why something exists |
| cyclic-cosmology.md | Heat death = Big Bang |
| hubble-tension.md | H0(local)/H0(CMB) = 13/12 |
| hubble-absolute.md | Absolute Hubble value |
| baryon-asymmetry.md | Matter-antimatter asymmetry |
| sigma8-tension.md | sigma_8 tension resolution |

### docs/mathematics/classical/ (Layer 2: turbulence, chaos)

| File | Purpose |
|------|---------|
| von-karman-derivation.md | kappa = 48/125 = 0.384 (first derivation from first principles) |
| reynolds-derivation.md | Re_c = 2300, Kolmogorov -5/3 |
| feigenbaum-derivation.md | delta = 4.6692 (0.00003%), alpha_F = 2.5029 |
| she-leveque-derivation.md | zeta_p structure function exponents |
| thermodynamics.md | Second Law as geometric theorem |

### docs/mathematics/relativity/

| File | Purpose |
|------|---------|
| special-relativity.md | SR from BLD |
| general-relativity.md | GR from BLD |

### docs/mathematics/geometry/

| File | Purpose |
|------|---------|
| manifold-foundations.md | Structures as points, cost as divergence |
| manifold-geometry.md | Metric structure, Fisher-Rao connection |
| manifold-applications.md | Domain interpretations |

### docs/mathematics/ (top-level)

| File | Purpose |
|------|---------|
| STRUCTURE.md | **Dependency DAG** and reading orders |
| digest.md | Complete formula catalog (all predictions on one page) |

### docs/theory/ (what BLD means)

| File | Purpose |
|------|---------|
| README.md | Core thesis + implications |
| structural-language.md | B/L/D specification |
| bld-as-language.md | BLD as universal language |
| human-language-structure.md | Natural language through BLD |
| structure-as-state.md | Structure IS state |
| structural-interest.md | Why BLD is interesting structurally |
| self-reference.md | Self-referential structure |
| llm-experiment.md | LLM experiments with BLD |
| refusal-analysis.md | Analysis of LLM refusal patterns through BLD |
| traverser-comparison.md | Traverser D capacity comparison |

### docs/examples/ (worked examples)

| File | Purpose |
|------|---------|
| physics-traverser.md | Q1/Q2/Q3 applied to physics — discovering axioms P1-P8 |
| physics-axioms-extended.md | Extended derivations: P9-P20, epistemic stratification |
| spacetime.md | Spacetime as BLD structure |
| zip.md | ZIP compression as BLD |
| lie-algebras.md | Lie algebra examples |
| pi-from-bld.md | Pi from BLD structure |
| e-from-bld.md | Euler's e from BLD |
| wgpu-jpeg-process.md | GPU JPEG processing (discovery origin) |

### docs/applications/ (practical uses)

| File | Purpose |
|------|---------|
| music-theory.md | 12 semitones from n(n-1) |
| biology/genetic-code.md | 20 amino acids, 61 codons |
| biology/neural-architecture.md | Neural architecture through BLD |
| code/*.md | BLD-driven development, code generation, refactoring |
| ml/*.md | Performance theorem, neural network alignment, variational inference |
| physics/*.md | Circuits, electromagnetism, fluids, phase transitions, etc. |
| language/lossless-translation.md | Lossless translation via BLD structure |

### docs/meta/ (governance, methodology)

| File | Purpose |
|------|---------|
| proof-status.md | **What is proven vs. conjectured** |
| epistemic-honesty.md | Standards for claims |
| discovery-method.md | How to find BLD structure (the three questions) |
| discovery-history.md | From JPEG decoder to particle physics |
| discovery-algorithm.md | Formal algorithm for finding structure |
| research-directions.md | Open problems |
| validation-roadmap.md | Experimental validation tracking |
| comparisons.md | BLD vs Roofline, Fisher-Rao, circuit complexity |
| cross-domain-prediction.md | Cross-domain generalization framework |
| docs-structure.md | BLD structure of this documentation |

### docs/analysis/

| File | Purpose |
|------|---------|
| error-analysis.md | Error analysis of predictions |
| math-verification-report.md | Verification of mathematical claims |

---

## Concept Index

| Concept | Canonical File |
|---------|---------------|
| Axioms (A1-A7) | foundations/axioms.md |
| B (Boundary) | foundations/axioms.md, theory/structural-language.md |
| L (Link) | foundations/axioms.md, theory/structural-language.md |
| D (Dimension) | foundations/axioms.md, theory/structural-language.md |
| K = 2 (Killing form) | lie-theory/killing-form.md |
| n = 4 (spacetime) | foundations/derivations/octonion-derivation.md |
| L = 20 (Riemann) | foundations/constants.md |
| B = 56 (E7) | particle-physics/e7-derivation.md |
| S = 13 (structural intervals) | foundations/constants.md |
| Observer correction (K/X) | cosmology/observer-correction.md |
| Fine structure constant | particle-physics/fine-structure-consistency.md |
| Born rule | quantum/born-rule.md |
| Selection rule | quantum/selection-rule.md |
| Octonions | foundations/derivations/octonion-derivation.md |
| Division algebras | foundations/derivations/octonion-derivation.md |
| Triality | particle-physics/e7-derivation.md |
| SU(3) color | foundations/derivations/octonion-derivation.md |
| 3 generations | foundations/derivations/octonion-derivation.md |
| Lie correspondence | lie-theory/lie-correspondence.md |
| BLD calculus | foundations/definitions/bld-calculus.md |
| Irreducibility | foundations/proofs/irreducibility-proof.md |
| Completeness | foundations/proofs/completeness-proof.md |
| Genesis function | cosmology/genesis-function.md |
| Integer machine | foundations/machine/integer-machine.md |
| Detection structure | foundations/machine/detection-structure.md |
| Cost conservation | foundations/structural/structural-cost-conservation.md |
| Compensation principle | foundations/structural/compensation-principle.md |
| Feigenbaum constants | classical/feigenbaum-derivation.md |
| Von Karman constant | classical/von-karman-derivation.md |
| Reynolds number | classical/reynolds-derivation.md |
| Second Law | classical/thermodynamics.md |
| Hubble tension | cosmology/hubble-tension.md |
| Dark matter/energy | cosmology/cosmology-structure.md |
| Higgs self-coupling | particle-physics/higgs-self-coupling.md |
| Neutrino mixing | particle-physics/neutrino-mixing.md |

---

## Dependency Topology

### The Derivation Spine (read in order)

```
axioms.md -> bld-calculus.md -> irreducibility-proof.md -> completeness-proof.md
    |
octonion-derivation.md -> lie-correspondence.md -> killing-form.md
    |
e7-derivation.md -> force-structure.md -> [all particle physics]
```

### By Topic

**To understand alpha^-1 = 137.036**:
1. axioms.md (A1-A7)
2. octonion-derivation.md (n=4, why octonions)
3. killing-form.md (K=2)
4. e7-derivation.md (B=56)
5. fine-structure-consistency.md (the formula)
6. observer-correction.md (the K/X corrections)

**To understand the Born rule**:
1. killing-form.md (K=2)
2. born-rule.md (P = |psi|^2 from bidirectional alignment)
3. selection-rule.md (single-event mechanism)

**To understand turbulence**:
1. constants.md (n, L, K, B, S)
2. von-karman-derivation.md or reynolds-derivation.md
3. she-leveque-derivation.md (structure functions)

**To understand dark matter/energy**:
1. cosmology-structure.md (L/D = 5)
2. observer-correction.md (K/X framework)
3. hubble-tension.md (H0 resolution)

---

## Common Queries

**Find all predictions**: `grep -r "status: PREDICTED" docs/`

**Find all proofs**: `grep -r "status: PROVEN" docs/`

**Find key results**: `grep -r "key_result:" docs/`

**Trace a derivation chain**: `head -20 <file> | grep -A10 "depends_on"`

**Find what uses a file**: `grep -r "<filename>" docs/ --include="*.md"`

**Find all testable predictions**: Look for `[PREDICTED]` tags in particle-physics/ files.

---

## See Also

- [STRUCTURE.md](../mathematics/STRUCTURE.md) — Visual dependency DAG
- [Proof Status](../meta/proof-status.md) — What is proven vs. conjectured
- CLAUDE.md (repo root) — Additional grep recipes and layer structure
