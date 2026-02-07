---
status: DERIVED
layer: 2
key_result: "Feynman path integral = B(partition) × L(phase ×i) × D(iterate) applied to time evolution"
depends_on:
  - schrodinger-derivation.md
  - born-rule.md
  - ../foundations/machine/integer-machine.md
  - ../lie-theory/killing-form.md
  - ../../examples/e-from-bld.md
  - ../../examples/pi-from-bld.md
  - ../foundations/structural/compensation-principle.md
  - ../foundations/proofs/completeness-proof.md
  - ../foundations/definitions/bld-calculus.md
  - ../foundations/derivations/force-structure.md
  - ../particle-physics/particle-classification.md
  - ../particle-physics/boson-masses.md
  - ../particle-physics/higgs-self-coupling.md
  - ../derived/general-relativity.md
  - ../../examples/physics-traverser.md
  - planck-derivation.md
used_by: []
---

# Path Integral from BLD

## Summary

**Feynman path integral derived from BLD primitives:**

1. B partitions state space at each time slice — [Time Slicing](#step-1-time-slicing-b-partitions)
2. L links adjacent slices with phase ×i from observation algebra — [Phase Links](#step-2-phase-links-l-connections)
3. D iterates over all slices, summing all intermediate states — [Path Sum](#step-3-path-sum-d-iteration)
4. Continuous limit via e (discrete→continuous) gives e^(iS/ℏ) — [Continuous Limit](#step-4-continuous-limit-e)
5. Classical limit via L→B compensation gives δS = 0 — [Classical Limit](#classical-limit)

| Standard QM assumes | BLD derives or proves | Status |
|---------------------|----------------------|--------|
| Sum over all paths | D-iteration over B-partitions | Structural identification |
| Phase e^(iS/ℏ) | i (observation unit) + e (discrete→continuous) | DERIVED |
| Action S | Accumulated alignment cost | Structural identification |
| ℏ value | Structure (0.00003% accuracy) | DERIVED |
| Classical limit δS=0 | L→B compensation (exponential + angular mechanisms) | PROVEN |

---

## Derivation Status

Each component of the path integral derivation has a different epistemic status:

| Component | Status | Source |
|-----------|--------|--------|
| Schrödinger equation → path integral | Standard math theorem | Inserting complete sets of states |
| i = observation unit | DERIVED | [Integer Machine](../foundations/machine/integer-machine.md) §10 |
| ℏ from structure | DERIVED | [Planck Derivation](planck-derivation.md) |
| e = discrete→continuous | DERIVED | [e from BLD](../../examples/e-from-bld.md) |
| Classical limit = L→B compensation | Instance of PROVEN theorem | [Compensation Principle](../foundations/structural/compensation-principle.md) |
| D(L(B)) = structural pattern | Structural identification | [BLD Calculus](../foundations/definitions/bld-calculus.md) |
| Phase per link | Observation unit (×i) provides direction; Hamiltonian provides magnitude | See [Step 2](#step-2-phase-links-l-connections) |
| Backward direction (BLD → PI directly) | DERIVED | See [Backward Direction](#backward-bld--path-integral--schrödinger) |
| Path measure Dγ | Constructive; product structure from μ linearity | See [Path Measure Construction](#path-measure-construction) |

---

## Prerequisites (all previously derived)

| Component | Source | Status |
|-----------|--------|--------|
| i = observation unit | [Integer Machine](../foundations/machine/integer-machine.md) §10 | DERIVED |
| Schrödinger equation | [Schrödinger Derivation](schrodinger-derivation.md) | DERIVED |
| e = discrete→continuous | [e from BLD](../../examples/e-from-bld.md) | VALIDATED |
| Born rule: P = \|ψ\|² | [Born Rule](born-rule.md) | DERIVED |
| ℏ from structure | [Planck Derivation](planck-derivation.md) | DERIVED |
| K=2 bidirectional | [Killing Form](../lie-theory/killing-form.md) | DERIVED |

---

## The Derivation

### The Physical Setup

A system evolves from state |x_i⟩ at time 0 to state |x_f⟩ at time t. We want the transition amplitude ⟨x_f|U(t)|x_i⟩.

### Step 1: Time Slicing (B-Partitions)

Divide the time interval [0, t] into N slices of size Δt = t/N:

```
t₀ = 0,  t₁ = Δt,  t₂ = 2Δt,  ...  tₙ = t
```

At each intermediate time t_k, insert a complete set of position states:

```
∑_x |x⟩⟨x| = 1     (resolution of identity)
```

**BLD interpretation**: Each insertion is a **B-operation** — partitioning the state space into all possible positions at that moment. The resolution of identity IS B: every state either is or isn't at position x. The partition is exhaustive and non-overlapping.

### Step 2: Phase Links (L-Connections)

Between adjacent slices, the system propagates by:

```
⟨x_{k+1}| e^{-iĤΔt/ℏ} |x_k⟩
```

This is a single **L-operation**: a directed link from position x_k at time t_k to position x_{k+1} at time t_{k+1}.

The link carries phase from the observation algebra:

```
Phase per link = e^{-iĤΔt/ℏ}

Where:
  i   = observation unit (Im(ℂ), structural necessity)
  Ĥ   = structure being traversed (Hamiltonian)
  Δt  = extent of the link (D-measure)
  ℏ   = structural unit of action (derived)
```

For small Δt (single step), the propagator factorizes:

```
⟨x_{k+1}| e^{-iĤΔt/ℏ} |x_k⟩  ∝  e^{iL(x, ẋ)Δt/ℏ}
```

where L(x, ẋ) is the Lagrangian. The phase per link is proportional to the Lagrangian times the time step — the **action increment** for that link.

**BLD content**: The phase e^{-iĤΔt/ℏ} decomposes into BLD-derived components:
- **Direction** (imaginary axis): i is the observation unit, derived from K=2 → dim(ℂ) → Im(ℂ). Every observation link rotates in the i-direction. This is not postulated — it follows from [Integer Machine](../foundations/machine/integer-machine.md) §10.
- **Magnitude** (how much rotation): ĤΔt/ℏ determines how far along the i-direction each link rotates. The Hamiltonian provides the local structure; ℏ provides the structural unit of action.
- **Accumulation** (exponential): e^{...} is the traverser function, derived from axioms T1-T5 in [e from BLD](../../examples/e-from-bld.md). Discrete phase increments accumulate via the exponential.

A bare observation link = ×i (π/2 rotation). The Hamiltonian modifies the rotation angle per step. The distinction matters: ×i is the structural direction; ĤΔt/ℏ is the structural amount.

### Step 3: Path Sum (D-Iteration)

The full propagator chains all N links together and sums over all intermediate positions:

```
⟨x_f|U(t)|x_i⟩ = ∫...∫ ∏_{k=0}^{N-1} ⟨x_{k+1}|e^{-iĤΔt/ℏ}|x_k⟩  dx₁ dx₂ ... dx_{N-1}
```

**BLD interpretation**: **D-operation** — iterate the L-link across all N time slices. At each slice, sum over all B-partitions (all possible intermediate positions). This is D(L(B)): dimension iterates links across boundaries.

Each specific sequence (x₀, x₁, x₂, ..., xₙ) defines a **path** γ. The integral sums over ALL paths from x_i to x_f.

### Step 4: Continuous Limit (e)

Each path γ accumulates phase from its N link contributions:

```
Phase(γ) = ∏_{k=0}^{N-1} e^{iL_k Δt/ℏ} = e^{i ∑_k L_k Δt/ℏ}
```

As N → ∞, Δt → 0:

```
∑_k L(x_k, ẋ_k) Δt  →  ∫₀ᵗ L(x, ẋ) dt  =  S[γ]     (the action)
```

Therefore:

```
Phase(γ) → e^{iS[γ]/ℏ}
```

**BLD content**: This is the e-derivation operating on phase. BLD derives e from axioms T1-T5 (Markov, Homogeneity, Self-Reference, Natural Units, Identity) discovered via structural analysis — not postulated ([e from BLD](../../examples/e-from-bld.md)). The proof: T1-T5 uniquely imply dy/dt = y, whose solution is y = e^t. The definition e = lim(1+1/n)^n IS the discrete→continuous bridge: discrete compounding of N finite steps becomes continuous exponential accumulation.

Here, the same mechanism operates on phase: N discrete phase increments e^{iL_kΔt/ℏ} compound to the continuous e^{iS/ℏ}. The primordial structure computes in discrete steps (integers); the transcendental e appears because observation takes the continuous limit. This is why the path integral's N→∞ limit works: it's the structural mechanism by which continuous traversal sees discrete structure.

Compare: the primordial structure computes (1 + 1/B)^B = (57/56)^56 ≈ 2.70; we observe e ≈ 2.718 ([Integer Machine](../foundations/machine/integer-machine.md) §5.3). The gap is the observation cost K/X.

### The Result

```
┌──────────────────────────────────────────────────┐
│                                                  │
│  ⟨x_f|U(t)|x_i⟩  =  ∫ e^{iS[γ]/ℏ}  Dγ         │
│                                                  │
│  The Feynman Path Integral                       │
│                                                  │
└──────────────────────────────────────────────────┘
```

Where:
- The integral is over ALL paths γ from x_i to x_f
- S[γ] = ∫ L dt is the classical action along γ
- Dγ = the path measure (product of measures at each time slice)
- ℏ is derived from BLD structure

---

## BLD Structure of the Path Integral

| BLD Primitive | Role | What It Does |
|---------------|------|-------------|
| **B** (Boundary) | Partition | State space partitioned at each time slice |
| **L** (Link) | Phase | Each link carries ×i modified by Hamiltonian |
| **D** (Dimension) | Iteration | Sum over all time slices and intermediate states |
| **K = 2** | Bidirectional | Forward propagator × backward = Born rule |
| **i** | Phase unit | Observation unit: each link rotates by i |
| **e** | Accumulation | Discrete phases → continuous e^(iS/ℏ) |
| **π** | Closure | Full phase cycle = 2π; action measured in π-units |

The path integral is **D(L(B))**: dimension iterates links across boundaries. This is the BLD traversal pattern applied to time evolution.

---

## Classical Limit

When S[γ] >> ℏ (macroscopic systems):

```
Most paths:     Phase oscillates rapidly → contributions cancel
Classical path: δS = 0 → phase is stationary → contributions align
Result:         Only the classical trajectory survives
```

**BLD content**: This is an instance of the **L→B compensation** theorem ([Compensation Principle](../foundations/structural/compensation-principle.md), layer 1, status: PROVEN). The theorem states: L→B works (sufficient links approximate complex boundaries), B→L fails (no amount of boundaries replaces missing links). This is proven from the definitions of the primitives — B is topological (local, D-invariant), L is geometric (global, D-scales).

Two compensation mechanisms operate simultaneously in the classical limit:

1. **Exponential mechanism (e)**: Discrete phase increments accumulate multiplicatively. Each path contributes e^{iS/ℏ}. The cascade sharpness scales as L^D — validated at 87.8% in circuits ([Compensation Principle](../foundations/structural/compensation-principle.md) §9.1).

2. **Angular mechanism (π)**: Phase rotation accumulates until closure. Off-axis paths complete cycles of 2π and cancel; the stationary-phase path has aligned phases. The closure formula D×L = 2πB governs when compensation saturates ([Compensation Principle](../foundations/structural/compensation-principle.md) §9.2).

These two mechanisms ARE Euler's formula operating in the path integral: e^{iS/ℏ} = [exponential accumulation] × [angular phase].

| Path Integral | Compensation Principle (PROVEN) |
|--------------|-------------------------------|
| Sum over many paths | Many L-links cascade |
| Rapidly oscillating phases cancel | Off-axis links cancel (angular mechanism) |
| Stationary phase dominates | Cascade converges to B (exponential mechanism) |
| Classical trajectory = δS = 0 | Sharp boundary from link accumulation |

The classical world emerges from quantum BLD structure exactly as the compensation principle proves: L→B works (many quantum paths → one classical trajectory), but B→L fails (a classical trajectory cannot reconstruct the quantum paths). This is not analogy — the stationary phase approximation is an instance of the same structural theorem that predicts circuit cascades and neural network depth scaling.

---

## The Two Directions

BLD connects to the path integral in both directions:

### Forward: BLD → Schrödinger → Path Integral

```
BLD axioms → i + linearity + ℏ → Schrödinger equation → path integral
```

This is the chain completed above: standard mathematics (inserting complete sets of states) applied to the BLD-derived Schrödinger equation.

### Backward: BLD → Path Integral → Schrödinger

```
BLD axioms → B(partition) + L(×i phase) + D(iteration) → path integral → Schrödinger
```

The path integral and the Schrödinger equation are both consequences of the same BLD-derived generator G = -iĤ/ℏ. Neither is "derived from" the other — both emerge from BLD. The path integral is the global form (all paths); Schrödinger is the infinitesimal form (single step).

**Theorem**: BLD constraints on time evolution uniquely determine the Feynman path integral.

**Proof**:

*Step 1: State space is Hilbert over ℂ*

These results are derived in [Schrödinger Derivation](schrodinger-derivation.md) FROM BLD axioms, before the Schrödinger equation appears (which is Step 7 of that file):
- ℂ from 𝕆 isolation (§0.1): BLD observation → octonions → reference fixing → ℂ = span{1, e₁}
- Linear evolution from Lie algebra (§0.2): G is L-type → Lie algebra action → linear
- Norm conservation → inner product (Step 4): closed system → |S|² constant → G† = -G

Result: the state space is a complex vector space with inner product — a Hilbert space.

*Step 2: B-partitions = resolutions of identity*

At each time t_k, partition the state space into position states. This partition is exhaustive: every state is at some position. Mathematically: ∑_x |x⟩⟨x| = 1 (resolution of identity).

BLD completeness (Theorem 4.1, [Completeness Proof](../foundations/proofs/completeness-proof.md)) guarantees: all observable structure is BLD-describable. A B-partition at each time slice captures all observable positions at that moment.

Note: The path integral uses a FINITE number N of B-partitions. The N→∞ limit is handled in Step 5.

*Step 3: L-links carry phase e^{-iĤΔt/ℏ}*

From [Schrödinger Derivation](schrodinger-derivation.md) Steps 4-6, independent of the Schrödinger equation:
- Norm conservation requires anti-Hermitian generator: G† = -G
- Write G = -iĤ/ℏ where Ĥ is Hermitian (change of variables)
- i is the observation unit ([Integer Machine](../foundations/machine/integer-machine.md) §10)
- ℏ is derived ([Planck Derivation](planck-derivation.md))

Each L-link between adjacent time slices carries phase e^{-iĤΔt/ℏ}.

*Step 4: D-iteration over N time slices*

Divide [0,t] into N slices. Insert B-partition at each slice (Step 2). Chain N L-links (Step 3):

```
⟨x_f|U(t)|x_i⟩ = ∑_{all paths} ∏_k ⟨x_{k+1}|e^{-iĤΔt/ℏ}|x_k⟩
```

This IS D(L(B)): D iterates (N slices), L links (phase between slices), B partitions (all positions at each slice).

*Step 5: Continuous limit*

Each path γ accumulates phase:

```
∏_k e^{iL_kΔt/ℏ} = e^{i∑_k L_kΔt/ℏ}
```

The equality uses the composition property e^a × e^b = e^{a+b} ([e from BLD](../../examples/e-from-bld.md), DERIVED from T1-T5).

As N→∞: ∑_k L_kΔt → ∫ L dt = S[γ] (Riemann sum convergence, standard analysis).

The discrete→continuous bridge IS the e-derivation: the corollary e = lim(1+1/n)^n ([e from BLD](../../examples/e-from-bld.md)) is exactly this mechanism operating on phase.

*Step 6: Result = path integral*

```
⟨x_f|U(t)|x_i⟩ = ∫ e^{iS[γ]/ℏ} Dγ
```

*Step 7: Schrödinger as infinitesimal limit*

Take N=1 (single infinitesimal step):

```
ψ(x, t+dt) = ∫ ⟨x|e^{-iĤdt/ℏ}|x'⟩ ψ(x', t) dx'
```

Expand to first order in dt: iℏ∂ψ/∂t = Ĥψ

This IS the Schrödinger equation — derived in [Schrödinger Derivation](schrodinger-derivation.md) as the final Step 7 of that file. Here it appears as the infinitesimal form of the path integral. Both are consequences of the same BLD-derived generator G = -iĤ/ℏ.

**Uniqueness**: Why this form and no other?
- **Sum over ALL paths**: D iterates ALL B-partitions (Theorem 4.1, [Completeness Proof](../foundations/proofs/completeness-proof.md))
- **×i phase**: i is the unique observation unit in ℂ ([Integer Machine](../foundations/machine/integer-machine.md) §10)
- **Exponential accumulation**: e^t uniquely satisfies T1-T5 ([e from BLD](../../examples/e-from-bld.md))
- **No other form**: Linear + complex + norm-preserving + continuous → U(n) → generators are iĤ → no other form satisfies all four constraints simultaneously

**Status**: DERIVED. Every BLD ingredient is previously DERIVED or PROVEN. The assembly uses standard mathematics (spectral theorem, Riemann sum convergence, Taylor expansion).

---

## Connection to ×i and δ_CP

The path integral's phase structure connects to the CP phase derivation in [Neutrino Mixing](../particle-physics/neutrino-mixing.md):

| Context | Phase Structure | Result |
|---------|----------------|--------|
| Path integral | Accumulated ×i over many links | e^(iS/ℏ) per path |
| Born rule | 2 links: ×i × ×(-i) = 1 → real | Probability |
| δ_CP | 1 link: ×i → phase π/2 survives | Maximal CP violation |

All three are consequences of the same observation algebra: i is the unit of observation, links compose by ×i in ℂ, and the number of links determines whether the result is real (K=2 round trip) or complex (K=1 influence).

---

## What BLD Adds

The standard derivation of the path integral from Schrödinger is a mathematical theorem — valid but structural. BLD reveals WHY each step works, drawing on derived and proven results:

| Step | Standard QM | BLD | Status |
|------|-------------|-----|--------|
| Time slicing | Mathematical convenience | B-partition (structural identification) | Structural |
| Phase direction | "Multiply by e^(-iHΔt/ℏ)" | i = observation unit from K=2 → dim(ℂ) | DERIVED |
| Phase magnitude | Hamiltonian × Δt / ℏ | Structure traversed × D-extent / structural unit | DERIVED (ℏ) |
| Sum over paths | "Insert complete sets" | D-iteration over B-partitions | Structural |
| Continuous limit | "Take N→∞" | e = discrete→continuous (T1-T5 → e^t) | DERIVED |
| Classical limit | "Stationary phase approximation" | L→B compensation (two mechanisms: e and π) | PROVEN |
| ℏ | Empirical constant | Derived from BLD (0.00003%) | DERIVED |
| i | Axiom of QM | Derived from K=2 = dim(ℂ) | DERIVED |

---

## Path Measure Construction

The D(L(B)) construction provides the path measure:

1. At each of N-1 intermediate time slices, a B-partition gives a position-space measure dx_k
2. D-iteration over N slices produces the product ∏_{k=1}^{N-1} dx_k
3. Normalization A(Δt) at each slice is determined by the specific Hamiltonian

```
Dγ = lim_{N→∞} ∏_{k=1}^{N-1} dx_k / A(Δt)
```

**BLD structural insight**: Mode count linearity μ(Πₙτ) = n × μ(τ) ([BLD Calculus](../foundations/definitions/bld-calculus.md) Definition 8.3) predicts this product-measure structure. Mode count counts structural dimensions, not inhabitants (Remark 8.4: "Mode count corresponds to vector space dimension"). N time slices add N independent dimensions — linearly, not exponentially. In standard QFT the product measure is assumed; BLD's μ explains why.

**Remaining limitation**: The normalization factor A(Δt) = √(2πiℏΔt/m) is Hamiltonian-dependent — but the Hamiltonian IS now determined (see below).

---

## Specific Hamiltonians from BLD Structure

BLD-derived inputs + standard uniqueness theorems determine the specific Hamiltonian for each fundamental force. BLD provides the inputs; standard theorems provide the form.

### Gauge Forces (EM, Weak, Strong)

BLD derives the gauge group from the division algebra tower ([Force Structure](../foundations/derivations/force-structure.md) §2):

```
𝕆 (octonions) → Aut(𝕆) = G₂ → fix reference → SU(3)  [strong]
ℍ (quaternions) → unit quaternions = SU(2)                [weak]
ℂ (complex)     → unit circle = U(1)                      [electromagnetic]
```

**Yang-Mills uniqueness**: Given a compact gauge group G, 4D Lorentz invariance ([Octonion Derivation](../foundations/derivations/octonion-derivation.md) Theorem 6.2), and renormalizability ([physics-traverser.md](../../examples/physics-traverser.md) P20), the gauge-field Lagrangian is uniquely:

```
ℒ_gauge = -(1/4) F^a_μν F^{aμν}
```

where F^a_μν = ∂_μ A^a_ν - ∂_ν A^a_μ + g f^{abc} A^b_μ A^c_ν. The structure constants f^{abc} are determined by G (BLD-derived). The coupling g is determined by α⁻¹, sin²θ_W, α_s⁻¹ (BLD-derived in [Force Structure](../foundations/derivations/force-structure.md) §4-6).

**Matter coupling**: Particles in representation R (BLD-derived in [Particle Classification](../particle-physics/particle-classification.md)) couple via:

```
ℒ_matter = ψ̄ iγ^μ D_μ ψ,   D_μ = ∂_μ - igA^a_μ T^a_R
```

The generators T^a_R are determined by R (from BLD).

### Higgs Sector

SU(2)×U(1) breaking requires a scalar doublet. Renormalizability constrains the potential to:

```
V(φ) = λ(|φ|² - v²/2)²
```

BLD goes beyond uniqueness here — it derives the parameters directly:
- v (Higgs VEV) = empirical input (one of only 3: v, c, G)
- m_H = (v/K)(1 + 1/B)(1 − 1/(B×L)) = **125.20 GeV** (0 MeV error) — [Boson Masses](../particle-physics/boson-masses.md)
- λ = m_H²/2v² is therefore fully determined
- κ_λ = 1 + K/(n×L) = **1.025** — a PREDICTION, testable at HL-LHC ~2040 — [Higgs Self-Coupling](../particle-physics/higgs-self-coupling.md)

The Higgs self-coupling prediction is particularly significant: BLD derives not just the potential form (from gauge symmetry + renormalizability) but its specific parameters (from structural constants) and predicts the detection correction (from K/X). The entire Higgs sector is determined.

### Gravity

BLD derives n = 4 and the Einstein equations G_μν = (8πG/c⁴) T_μν ([General Relativity](../derived/general-relativity.md) §4, where 8π = K×n×π = 2×4×π). **Lovelock's theorem**: in 4D, the unique divergence-free symmetric 2-tensor from the metric and ≤2 derivatives is G_μν + Λg_μν. Therefore the gravitational action is uniquely:

```
S_gravity = (c⁴/16πG) ∫ (R - 2Λ) √(-g) d⁴x
```

### Summary

| Force | Gauge group (BLD) | Coupling (BLD) | Lagrangian form |
|-------|-------------------|----------------|-----------------|
| EM | U(1) from ℂ | α⁻¹ = 137.036 | QED: -(1/4)F_μν F^μν + ψ̄ iγ^μ D_μ ψ |
| Weak | SU(2) from ℍ | sin²θ_W = 0.2312 | Electroweak: Yang-Mills + Higgs |
| Strong | SU(3) from 𝕆 | α_s⁻¹ = 8.481 | QCD: -(1/4)G^a_μν G^{aμν} + q̄ iγ^μ D_μ q |
| Higgs | SU(2)×U(1) scalar | m_H = 125.20 GeV, κ_λ = 1.025 | V(φ) = λ(\|φ\|² - v²/2)², λ = m_H²/2v² |
| Gravity | Diffeo from ℝ | M_P = 1.221×10¹⁹ GeV | Einstein-Hilbert: (R-2Λ)√(-g) |

**Consequence for path integral**: With the action S fully determined for each force, the path integral ∫ e^{iS/ℏ} Dγ is fully specified. The normalization A(Δt) is computable from the specific Ĥ.

**Status**: DETERMINED. Every BLD input is DERIVED; the Lagrangian form follows from standard uniqueness theorems (Yang-Mills structure, Lovelock's theorem, renormalizability).

---

## Limitations

| What | Status | Detail |
|------|--------|--------|
| Path measure normalization | Computable | A(Δt) depends on specific Ĥ, which is now determined. See [Specific Hamiltonians](#specific-hamiltonians-from-bld-structure). |
| Renormalization | Unexplored | BLD's discrete structure (Planck scale) implies natural UV cutoff. K/X corrections ([Integer Machine](../foundations/machine/integer-machine.md) §5.4) may relate to RG running. Connection unformalised. |

---

## Research Directions

Areas where the BLD framework for path integrals could generate new predictions:

| Direction | Connection to BLD | Prediction Potential |
|-----------|------------------|---------------------|
| **Berry phases** | Geometric phase from closed D(L(B)) loops in parameter space. Each link carries ×i; a closed loop of N links accumulates N × (π/2) phase. | Could predict specific Berry phases in units of π/2. The angular compensation mechanism (D×L = 2πB) governs when the loop closes. |
| **Aharonov-Bohm effect** | Phase from encircling magnetic flux. The angular compensation formula predicts closure at 2π. | Connects to flux quantization: Φ₀ = h/e as the B-closure quantum. |
| **Topological phases** | BLD's discrete structure naturally gives discrete phase quantization. The integer machine shows structure is fundamentally discrete; phase quantization follows. | Could classify topological phases via BLD mode count μ. |
| **Lattice field theory** | BLD's discrete→continuous framework (finite N → N→∞) mirrors lattice→continuum. The compensation principle governs how the lattice approximation sharpens. | Could provide structural insight into lattice artifacts and continuum limits. |

---

## References

### External
- [Feynman & Hibbs (1965)](https://en.wikipedia.org/wiki/Quantum_Mechanics_and_Path_Integrals) — Original path integral formulation
- [Zinn-Justin (2002)](https://en.wikipedia.org/wiki/Quantum_Field_Theory_and_Critical_Phenomena) — Modern path integral methods

### Internal BLD
- [Schrödinger Derivation](schrodinger-derivation.md) — iℏ∂ψ/∂t = Ĥψ from BLD
- [Born Rule](born-rule.md) — |ψ|² from bidirectional observation (K=2)
- [Integer Machine](../foundations/machine/integer-machine.md) — i = observation unit (§10), discrete structure, primordial integers
- [Killing Form](../lie-theory/killing-form.md) — K=2, 1-link vs 2-link
- [e from BLD](../../examples/e-from-bld.md) — e = discrete→continuous limit (T1-T5 → e^t)
- [π from BLD](../../examples/pi-from-bld.md) — π = closure constant, Euler unification
- [Compensation Principle](../foundations/structural/compensation-principle.md) — L→B compensation = classical limit (PROVEN, layer 1)
- [BLD Calculus](../foundations/definitions/bld-calculus.md) — Mode count μ, structural type system
- [Planck Derivation](planck-derivation.md) — ℏ derived from structure
- [Neutrino Mixing](../particle-physics/neutrino-mixing.md) — δ_CP = 270° from ×i (single link)
