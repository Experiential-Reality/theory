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
| Backward direction (BLD → PI directly) | Structural insight, not yet rigorous | See [Two Directions](#the-two-directions) |
| Path measure Dγ | Constructive from D(L(B)); not a full Lebesgue measure construction | See [Limitations](#limitations) |

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

Taking the infinitesimal limit of the path integral recovers the Schrödinger equation. This direction is more natural for BLD: the path integral emerges from the three primitives — B partitions at each time slice, L connects with ×i-directed phase, D iterates across slices — with the compensation principle's two mechanisms (e for accumulation, π for closure) governing the continuous limit.

**Status: structural insight, not yet rigorous.** The claim is that D(L(B)) applied to time evolution uniquely produces the path integral, with Schrödinger as its infinitesimal form. This is structurally motivated — the compensation principle provides the two transcendental mechanisms (e and π) needed for the continuous limit. A formal proof would need to show that D-iteration with L-phases across B-partitions, combined with the compensation principle, uniquely yields ∫ e^{iS/ℏ} Dγ without assuming the Schrödinger equation.

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

## Limitations

| What | Status | Detail |
|------|--------|--------|
| Path measure Dγ | Constructive, not complete | D(L(B)) iteration constructs the measure from below — sum over all B-partitions at each time slice. But this does not reconstruct the full functional measure in the Lebesgue sense. The mode count μ(Πₙτ) = n × μ(τ) ([BLD Calculus](../foundations/definitions/bld-calculus.md) §8) is a genuine measure-like object (linear, not exponential cardinality), but full measure theory is external to the BLD formal system. |
| Renormalization | Not addressed | BLD does not address ultraviolet divergences, counterterms, or the renormalization group. These remain external to BLD structure. |
| Specific Hamiltonian | Not determined by BLD alone | BLD identifies that each L-link carries Hamiltonian-modified ×i phase, but does not determine the specific form of Ĥ from B, L, D alone. The Hamiltonian comes from the specific physics (force structure, gauge fields). |
| Backward direction | Structural insight, not formal proof | The claim that D(L(B)) directly yields the path integral needs rigorous demonstration. See [Two Directions](#the-two-directions). |

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
