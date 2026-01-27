---
status: VALIDATED
layer: application
depends_on:
  - ../../mathematics/foundations/structural/compensation-principle.md
  - ../../mathematics/lie-theory/lie-correspondence.md
  - ../../meta/discovery-method.md
used_by:
  - ../ml/neural-network-experiments.md
  - electromagnetism.md
---

# BLD for Electrical Circuits

> **Status**: Validated (6/6 tests passing)

## Summary

**BLD validated (6/6 tests):**

1. D×L scaling: C scales with N (R²=1.0), V_th invariant — [Proof](#dl-scaling-proof)
2. Compensation asymmetry: L→B works (cascading), B→L limited — [Principle](#compensation-principle)
3. Circuits use e (gain stacking is multiplicative) — [Why e](#why-circuits-use-e-exponential-compensation)

| BLD | Circuit | Scales? |
|-----|---------|---------|
| B | V_th | No (topological) |
| L | Capacitance | Yes (D×L) |
| D | Transistor count | Multiplier |

**Repo**: [bld-circuits](https://github.com/rax-V/bld-circuits)

---

## BLD Mappings for Circuits

| Primitive | Circuit Domain | Examples |
|-----------|---------------|----------|
| **B** (Boundary) | Operating mode transitions | V_th (cutoff/conducting), V_dsat (linear/saturation) |
| **L** (Link) | Electrical coupling | Capacitance (C_gs, C_gd), resistance (R_on), signal paths |
| **D** (Dimension) | Repetition | Parallel transistors, cascaded stages, array cells |

---

## D×L Scaling Proof

### The Claim

**D multiplies L, not B.**

### Mathematical Proof

**Why L scales with D** (capacitance formula):
```
C_total = N × C_ox × W × L
```
The formula **contains N** as a multiplicative factor. Capacitance is geometric—proportional to total gate area.

**Why B is invariant** (threshold voltage formula):
```
V_th = V_FB + 2φ_F + γ√(2φ_F)
```
The formula **does not contain N**. Threshold depends on material properties and geometry ratios, not device count. All parallel transistors share the same gate voltage—they all turn on at the same V_gs.

### Empirical Validation

| D | C_gg (fF) | V_th (V) | V_dsat (V) |
|---|-----------|----------|------------|
| 1 | 1.60 | 0.2808 | 0.5192 |
| 2 | 3.21 | 0.2808 | 0.5192 |
| 4 | 6.41 | 0.2808 | 0.5192 |
| 8 | 12.83 | 0.2808 | 0.5192 |
| 16 | 25.65 | 0.2808 | 0.5192 |

**Results**:
- L (capacitance): **R² = 1.000** (perfect linear scaling)
- B (thresholds): **CV = 0.000** (perfectly invariant)

---

## Compensation Principle

### The Hypothesis

**L can compensate for B deficiency, but B cannot compensate for L deficiency.**

From neural networks:
- Global L (full connectivity) compensates for weak B (soft decision boundaries)
- Local L cannot be compensated by sharper B

For circuits:
- **B deficiency** = soft mode transitions (linear amplifier instead of comparator)
- **L compensation** = cascading multiple stages

### Experiment: Comparator Approximation

**Task**: Achieve sharp step-function transition at threshold.

| Configuration | Step Error | Improvement |
|---------------|------------|-------------|
| Single soft stage (local L) | 0.129 | baseline |
| 5-stage cascade (global L) | 0.016 | 87.8% |
| 10-stage cascade | 0.016 | 87.8% |
| Ideal comparator | 0.000 | 100% |

**VALIDATED**: Cascading stages (adding L) compensates for soft transitions (weak B).

### Why Op-Amps Use Multiple Stages

This explains a universal circuit design pattern:

| Approach | Why It Fails / Succeeds |
|----------|------------------------|
| Single mega-stage (A=100,000) | Bandwidth destruction, stability nightmare, noise amplification |
| Two cascaded stages (A=100×1000) | Each stage reasonable, Miller compensation ensures stability |

**The asymmetry emerges from physics**: L→B compensation works, B→L compensation is limited by bandwidth, noise, and stability.

### Why the Asymmetry Exists (BLD Predicts Itself)

The compensation asymmetry isn't empirical accident — it follows from the primitive definitions:

- **B (threshold voltage) is topological**: V_th partitions locally (each transistor decides at its own gate). Invariant under D — adding parallel devices doesn't change when they turn on.
- **L (capacitance, stages) is geometric**: Connects across distance, accumulates signal. Scales with D — more stages = more accumulated gain.
- **D×L accumulates**: Each soft stage contributes evidence, links propagate it forward. The cascade integrates to sharp transition.
- **D×B stays local**: Each transistor still makes its own local decision. No integration, no accumulation.

This is why cascading works: you're using D×L to build up an effective sharp boundary from many soft ones. You cannot do the reverse — no amount of threshold sharpening gives you the gain that cascading provides.

### Diagnostic Application

Use compensation asymmetry to find hidden structure in circuits:

| Observation | Inference | Where to Look |
|-------------|-----------|---------------|
| Better than expected | Hidden L compensating | Parasitic coupling, unmodeled signal paths, substrate connections |
| Worse despite good L | Hidden B blocking | Saturation, thermal effects, supply voltage droop |
| Cascade not improving | L not accumulating | Information loss between stages, bandwidth limiting, noise floor |

**Example**: A two-stage amplifier doesn't achieve A₁×A₂ gain.
- If gain is *higher* → parasitic feedback (hidden L)
- If gain is *capped* → one stage saturating (hidden B)
- If gain *degrades* with frequency → bandwidth limiting (L not propagating)

See [Compensation Principle](../../mathematics/foundations/structural/compensation-principle.md) for the full derivation and more diagnostic examples.

---

## Circuit Examples

### CMOS Inverter

```
B: V_th_inv ≈ VDD/2 (switching threshold) — TOPOLOGICAL
L: C_in = C_gs + C_gd (input capacitance) — GEOMETRIC
D: N parallel inverters or N-stage buffer chain

D×L: C_total = N × C_single
B invariant: V_th unchanged with N
```

### Ring Oscillator

The clearest D×L demonstration:

```
Period T = 2 × N × t_pd

Where:
  N = stage count (D)
  t_pd = propagation delay per stage (L)
```

| N stages | Period | Frequency |
|----------|--------|-----------|
| 3 | 60 ps | 16.7 GHz |
| 5 | 100 ps | 10.0 GHz |
| 11 | 220 ps | 4.5 GHz |

**Period scales linearly with D**. Threshold voltage invariant.

### Flash ADC

Flash ADCs demonstrate why D×L matters for architecture decisions:

```
B: Comparator thresholds (2^N - 1 boundaries)
L: Power per comparator, input capacitance
D: Number of comparators = 2^N - 1
```

| Bits | D (comparators) | Power (µW) | Ratio |
|------|-----------------|------------|-------|
| 2 | 3 | 270.57 | 1.00× |
| 3 | 7 | 631.35 | 2.33× |
| 4 | 15 | 1352.91 | 5.00× |

**R² = 1.0** (perfect linear scaling)

This explains why flash ADCs don't scale beyond ~6 bits: D grows as 2^N - 1, making power impractical for high resolution. Each comparator has identical B (threshold structure), but total L (power) scales with D.

### Two-Stage Op-Amp

Canonical compensation example:

```
Single stage gain: A_max ≈ 100 (B limitation)
Required gain: 100,000+

Solution: A_total = A₁ × A₂ = 100 × 1000 = 100,000

L (cascading) compensates for B (limited per-stage gain)
```

---

## Why Circuits Use e (Exponential Compensation)

> **Status**: Validated

Circuit cascades follow **exponential compensation** because gain stacking is multiplicative:

```
A_total = A₁ × A₂ × ... × A_n = A^n = e^(n·ln(A))
```

### The Mathematical Reason

The **natural logarithm** (base e) appears because:
- e is the eigenvalue of differentiation: d/dt(e^t) = e^t
- Cascading is repeated multiplication → repeated application of linear operators
- Only e satisfies this closure property under composition

### The Saturation Formula

```
D_required = ⌈ln(w₀/w_target) / ln(gain)⌉

Example: To sharpen from w=0.16 to w=0.01 with gain=5:
  D = ⌈ln(0.16/0.01) / ln(5)⌉ = ⌈2.77 / 1.61⌉ = ⌈1.72⌉ = 2 stages (≈3 in practice)
```

The **natural logarithm** appears in the saturation formula — this is e at work.

### Why NOT π

Circuits don't use angular (π) compensation because:
- **No periodic return**: Gain extends to infinity (non-compact structure)
- **No rotation**: Signal amplification doesn't cycle back to start
- **Unbounded growth**: A^D → ∞ as D → ∞

This is the signature of **e-dominated** systems:
- Serial stages (no closure)
- Multiplicative accumulation
- Non-compact Lie group structure (boosts, not rotations)

### Euler Connection

In the Euler unification e^(iπ) + 1 = 0:
- Circuits use the **real part**: e^a (exponential growth, non-compact)
- Periodic systems use the **imaginary part**: e^(iθ) (rotation, compact)
- Spirals (α-helix, helical antennas) use **both**: e^(a+iθ)

Circuit cascades are pure exponential because they lack the closed boundary that would make π appear.

See [Compensation Principle](../../mathematics/foundations/structural/compensation-principle.md) and [Euler's Formula in BLD](../../glossary.md#eulers-formula-in-bld).

---

## Connection to Other Domains

| Domain | L (geometric) | B (topological) | D×L Validated | Compensation |
|--------|---------------|-----------------|---------------|--------------|
| Variational Inference | Correlation ρ | Mode count | R² = 1.0 | N/A (independent) |
| Neural Networks | Receptive field | Decision boundaries | r = 0.91 | 6.2% diagonal |
| **Circuits** | **Capacitance** | **Threshold V_th** | **R² = 1.0** | **87.8%** |

The principle is universal because it follows from Lie theory:
- B ↔ Group topology (invariant under representation scaling)
- L ↔ Structure constants (scale with generators)
- D ↔ Generators (representation dimension)

---

## Practical Implications

### Optimization Leverage

Since D multiplies L (not B):

| Optimization Target | Impact at Scale |
|---------------------|-----------------|
| Reduce capacitance (L) | D× power reduction |
| Reduce resistance (L) | D× I²R loss reduction |
| Improve biasing (B) | Constant improvement |

**L optimizations compound with scale. B optimizations don't.**

### Design Guidelines

1. **For large arrays (high D)**: Prioritize L optimization
2. **For small circuits (low D)**: B and L equally important
3. **For high gain**: Use cascaded stages (L compensation)
4. **Mode stability**: Independent of array size (B invariant)

---

## Reproduction

Full implementation and experiments available at: **[github.com/rax-V/bld-circuits](https://github.com/rax-V/bld-circuits)**

```bash
# Clone and run validation suite
git clone https://github.com/rax-V/bld-circuits.git
cd bld-circuits
python -m venv .venv && source .venv/bin/activate
pip install -e .

# Requires ngspice (pacman -S ngspice / apt install ngspice / brew install ngspice)
PYTHONPATH=src python experiments/run_all_validations.py

# Expected: 6/6 validations passing, R² = 1.0 for D×L tests
```

Repository structure:
```
bld-circuits/
├── experiments/
│   ├── run_all_validations.py  # Unified test suite (6/6)
│   ├── flash_adc_validation.py # Flash ADC D×L scaling
│   ├── current_mirror_validation.py
│   └── power_validation.py
├── tests/fixtures/
│   ├── flash_adc_{2,3,4}bit.sp # D=3, 7, 15 comparators
│   ├── current_mirror_d{1,2,4}.sp
│   └── ring_oscillator.sp
└── docs/examples/
    ├── inverter-analysis.md
    ├── current-mirror-analysis.md
    └── ring-oscillator-analysis.md
```

---

## See Also

- [Glossary](../../glossary.md) — Central definitions including D×L principle
- [Neural Network Alignment](../ml/neural-network-alignment.md) — Compensation principle in neural nets
- [Variational Inference](../ml/variational-inference.md) — D×L in statistical inference
- [Discovery Method](../../meta/discovery-method.md) — The three questions
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Why D×L is universal
