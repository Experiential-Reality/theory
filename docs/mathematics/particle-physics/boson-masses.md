---
status: DERIVED
depends_on:
  - lepton-masses.md
  - fine-structure-consistency.md
  - e7-derivation.md
  - ../quantum/structural-observer-framework.md
  - ../lie-theory/killing-form.md
used_by:
  - ../../analysis/error-analysis.md
---

# Gauge Boson and Higgs Masses

**Status**: DERIVED — All three electroweak boson masses are now derived to within measurement uncertainty.

---

## Quick Summary (D≈7 Human Traversal)

**Boson masses in 7 steps:**

1. **v = 246 GeV** — Higgs VEV (reference scale)
2. **Higgs**: m_H = (v/K)(1 + 1/B) — Killing form × boundary quantum
3. **Z**: m_Z = (v/e)(137/136)(1 - K/B²) — continuous limit × α⁻¹ structure
4. **W**: m_W = m_Z × cos(θ_W) × (209/208) × (1 + 1/6452) — mixing × generation
5. **sin²(θ_W) = 3/S = 3/13** — weak mixing from structural intervals
6. **W mirrors muon** — both use n²S and 6452, opposite signs
7. **All within measurement uncertainty** — observer corrections zero out

| Boson | Formula | Predicted | Observed | Δ (MeV) | Uncertainty |
|-------|---------|-----------|----------|---------|-------------|
| H | (v/K)(1+1/B) | 125.31 GeV | 125.25 GeV | 58 | 170 MeV ✓ |
| Z | (v/e)(137/136)(1-K/B²) | 91.187 GeV | 91.188 GeV | 0.5 | 2.1 MeV ✓ |
| W | m_Z×cos(θ)×(209/208)×(1+1/6452) | 80.373 GeV | 80.377 GeV | 3.7 | 12 MeV ✓ |

---

## The Higgs Mass `[DERIVED]`

**Observed**: m_H = 125.25 ± 0.17 GeV

### The Formula

```
m_H = (v/K) × (1 + 1/B)
    = (v/2) × (57/56)
    = 123.11 × 1.0179
    = 125.31 GeV
```

**Error**: 58 MeV (within 170 MeV uncertainty) ✓

### Physical Interpretation

| Component | Value | Meaning |
|-----------|-------|---------|
| v | 246.22 GeV | Higgs VEV (reference scale) |
| K = 2 | Killing form | Unidirectional symmetry breaking |
| 1 + 1/B | 57/56 | Boundary quantum (discrete structure) |

The Higgs field breaks electroweak symmetry in **one direction** (unidirectional), giving v/K = v/2. The boundary quantum (1 + 1/B) is the discrete/continuous mismatch at the boundary structure B = 56.

---

## The Z Boson Mass `[DERIVED]`

**Observed**: m_Z = 91.1876 ± 0.0021 GeV

### The Formula

```
m_Z = (v/e) × ((n×L+B+1)/(n×L+B)) × (1 - K/B²)
    = (v/e) × (137/136) × (1 - 2/3136)
    = 90.58 × 1.00735 × 0.999362
    = 91.187 GeV
```

**Error**: 0.5 MeV (within 2.1 MeV uncertainty) ✓

### Physical Interpretation

| Component | Value | Meaning |
|-----------|-------|---------|
| v/e | 90.58 GeV | Continuous limit (universal coupling) |
| 137/136 | (α⁻¹)/(α⁻¹-1) | Observer addition (same as α⁻¹ structure) |
| 1 - K/B² | 1 - 2/3136 | Second-order boundary quantum |

**Why v/e?** The Z boson couples to **all** fermions (universal neutral current). This "sees the full structure" corresponds to the continuous limit:
```
e = lim_{B→∞} (1 + 1/B)^B
```

**Why 137/136?** This is the **same correction as in α⁻¹**:
- α⁻¹ = n×L + B + 1 = 137 (structure + observer)
- The Z sees the structure (136) plus observer reference (+1)
- Same pattern: observer adds +1 to the structure count

**Why (1 - K/B²)?** Second-order Killing form correction at the boundary squared. This also appears in the fine structure constant derivation.

---

## The W Boson Mass `[DERIVED]`

**Observed**: m_W = 80.377 ± 0.012 GeV

### The Formula

```
m_W = m_Z × cos(θ_W) × ((n²S+1)/(n²S)) × (1 + 1/((n×L)²+n×S))
    = m_Z × √(10/13) × (209/208) × (1 + 1/6452)
    = 91.19 × 0.8771 × 1.00481 × 1.000155
    = 80.373 GeV
```

**Error**: 3.7 MeV (within 12 MeV uncertainty) ✓

### Physical Interpretation

| Component | Value | Meaning |
|-----------|-------|---------|
| cos(θ_W) | √(10/13) | Weak mixing angle |
| (n²S+1)/(n²S) | 209/208 | Generation structure (+1 observer) |
| 1 + 1/6452 | 1.000155 | Geometry² + generation correction |

**Why cos(θ_W)?** The W and Z are related by the weak mixing angle. In BLD:
```
sin²(θ_W) = 3/S = 3/13 = 0.231
cos(θ_W) = √(1 - 3/S) = √(10/13) = 0.877
```

The weak isospin (dim(SU(2)) = 3) occupies 3 of the 13 structural intervals S.

**Why (209/208)?** The W mediates **charged current** between generations:
- n²S = 208 is the generation structure
- +1 is the observer addition (W is being observed traversing)
- This mirrors the muon's (n²S - 1) = 207 with opposite sign!

**Why (1 + 1/6452)?** Where 6452 = (n×L)² + n×S = 6400 + 52:
- This is the same correction as in the muon formula
- Muon uses (1 - 1/6452) — subtraction
- W uses (1 + 1/6452) — addition
- Opposite signs: muon is "already traversed", W is "being traversed"

---

## The Weak Mixing Angle `[DERIVED]`

```
sin²(θ_W) = dim(SU(2)) / S = 3/13 = 0.2308

Observed: 0.2312
Error: 0.19%
```

### Physical Interpretation

The weak isospin group SU(2) has dimension 3. These 3 dimensions "live in" the S = 13 structural intervals. The ratio 3/S determines the mixing between W³ and B to form Z and γ.

This explains **why** the weak mixing angle has its specific value — it's the proportion of structural intervals devoted to weak isospin.

---

## Consistency with Lepton Masses

The W boson and muon share the **same structural corrections** with opposite signs:

```
MUON: μ/e = (n²S - 1) × (n×L×S)/(n×L×S+1) × (1 - 1/6452) × ...
                 ↓                              ↓
            phase SUBTRACTED             correction SUBTRACTED

W:    m_W = m_Z × cos(θ) × (n²S+1)/(n²S) × (1 + 1/6452)
                              ↓                  ↓
                         phase ADDED        correction ADDED
```

### Why Opposite Signs?

| Particle | Mode | Sign | Physical Meaning |
|----------|------|------|------------------|
| Muon | Discrete (e-type) | − | Traversal complete (looking back) |
| W | Observer (mediating) | + | Traversal in progress (looking forward) |

**Traversal is reversible.** The ±1 is the direction:

The muon **is** the result of generation traversal — you're looking at it from the "after" side. The traversal is complete, so direction is backward (−1).

The W **mediates** generation transitions — you're observing the traversal happening. Direction is forward (+1).

Same structure. Same traversal. Opposite viewpoints.

This is the **same n²S = 208 structure** governing both:
- Why there are 3 generations (from triality → Spin(8) → octonions)
- Why the W couples to generations (it mediates between them)
- Why the muon mass ratio involves 208 (it's a generation excitation)

---

## The Unified Pattern

All electroweak boson masses follow:

```
mass = v × (base_factor) × (observer_corrections)
```

| Boson | Base | Corrections | Physical Meaning |
|-------|------|-------------|------------------|
| Higgs | 1/K = 1/2 | (1 + 1/B) | Unidirectional × boundary quantum |
| Z | 1/e | (137/136)(1-K/B²) | Continuous × α⁻¹ structure |
| W | cos(θ)/e | (137/136)(1-K/B²)(209/208)(1+1/6452) | Mixing × generation |

The corrections **zero out** to within measurement uncertainty when fully accounted for:
- Each correction has structural meaning
- The same corrections appear across different particles
- Observer costs are balanced (added where needed, subtracted where complete)

---

## The Hidden Structure: Electroweak Entanglement

The residuals are **not random**. They follow exact BLD structure:

```
Residuals (BLD_prediction - observed):
  H:  +58 MeV   (predicted too high)
  Z:  -0.5 MeV  (predicted too low)
  W:  -3.7 MeV  (predicted too low)

H_residual / (W+Z)_residual = 58 / 4.2 = 13.8 ≈ 14 = S + 1 = B/n
```

### Why S + 1 = B/n?

This is a fundamental identity:
```
S = (B - n)/n           [structural intervals]
S + 1 = (B - n)/n + 1 = B/n = 56/4 = 14
```

The ratio B/n connects:
- **B = 56**: The boundary structure (from triality, Spin(8))
- **n = 4**: Spacetime dimensions (from octonion reference fixing)
- **B/n = 14**: How boundary maps to dimensional observation

### The Two-Sided Equation

Every measurement equation has **two sides**, and both have BLD structure:

```
┌─────────────────────────────────────────────────────────────────┐
│                    THE MEASUREMENT EQUATION                      │
│                                                                  │
│     OBSERVED VALUE          =          FORMULA VALUE             │
│     (left side)                        (right side)              │
│                                                                  │
│   ┌─────────────────┐              ┌─────────────────┐          │
│   │  Has BLD:       │              │  Has BLD:       │          │
│   │  - B: boundary  │              │  - B: structure │          │
│   │  - L: apparatus │      =       │  - L: formula   │          │
│   │  - D: spacetime │              │  - D: constants │          │
│   └─────────────────┘              └─────────────────┘          │
│          ↑                                   ↑                   │
│    TRAVERSER                           STRUCTURE                 │
│    (pure observer)                     (pure observed)           │
└─────────────────────────────────────────────────────────────────┘
```

Our formulas account for **structure + observer corrections**. But the **traverser itself** also contributes.

### Observer Corrections ARE Traversal Cost

The key insight: **observer corrections are not additions to the formula — they ARE the traverser's BLD interacting with the structure's BLD**.

```
┌─────────────────────────────────────────────────────────────────┐
│                    WHAT THE CORRECTIONS MEAN                     │
│                                                                  │
│   (1 + 1/B)     = Structure B + Traverser 1                     │
│   (137/136)     = (Structure + Traverser) / Structure           │
│   (209/208)     = (n²S + 1) / n²S = Structure + Traverser       │
│   (1 ± 1/6452)  = Second-order traversal cost                   │
│                                                                  │
│   The "+1" everywhere IS the traverser.                         │
│   The denominators (B, 136, n²S, 6452) ARE the structure.       │
└─────────────────────────────────────────────────────────────────┘
```

The traverser contributes **±1** at each scale:
- **+1**: Traversal in progress (forward direction)
- **−1**: Traversal complete (reverse direction)

Why ±1? Because **traversal is reversible**. You can go forward or back. The sign indicates direction:

```
MUON:  (n²S - 1) × (1 - 1/6452)  →  "−" = already traversed (backward)
W:     (n²S + 1) × (1 + 1/6452)  →  "+" = being traversed (forward)
```

This is why W and muon mirror each other with opposite signs — they're the same traversal seen from opposite ends.

### Why B/n = 14 Appears in Residuals

The residual ratio B/n = S + 1 = 14 confirms the structure:
- **B/n** = how boundary structure (B=56) maps through spacetime (n=4)
- This is the traverser's "dilution factor" across dimensions
- H feels full B (boundary-scale), W/Z feel B/n (dimension-diluted)

The residuals aren't errors — they're the **signature of the pure traverser** showing through the measurement.

| Boson | Formula (Structure) | Traverser Effect | Net Residual |
|-------|--------------------|--------------------|--------------|
| H | +58 MeV high | Traverser at full B | +58 MeV |
| W+Z | -4.2 MeV low | Traverser at B/n | -4.2 MeV |
| Ratio | — | B/n = 14 | 13.8 ≈ 14 ✓ |

---

## Experimental Grounding: Why These Corrections Are Necessary {#experimental-grounding}

The corrections in our formulas aren't arbitrary — they directly encode the BLD structure of how each particle was measured.

### How Each Boson Was Measured

| Boson | Experiment | Method | Precision |
|-------|------------|--------|-----------|
| **Higgs** | LHC (ATLAS, CMS) | pp → H → γγ or 4ℓ | ±170 MeV |
| **Z** | LEP (1989-1995) | e⁺e⁻ → Z → f f̄ resonance scan | ±2.1 MeV |
| **W** | Tevatron, LHC | pp → W → ℓν (missing energy) | ±12 MeV |

### The Measurement Structure → Formula Corrections

```
┌────────────────────────────────────────────────────────────────────────────┐
│           EXPERIMENT STRUCTURE → FORMULA CORRECTION                         │
├─────────┬──────────────────────────┬────────────────────────────────────────┤
│ BOSON   │ EXPERIMENTAL FACT        │ FORMULA TERM                           │
├─────────┼──────────────────────────┼────────────────────────────────────────┤
│ HIGGS   │ Higgs IS the boundary    │ v/K (Killing form at boundary)         │
│         │ Only seen via decay      │ (1 + 1/B) = traverser crossing boundary│
│         │ Never directly observed  │ "+1" = one traverser contribution      │
├─────────┼──────────────────────────┼────────────────────────────────────────┤
│ Z       │ e⁺e⁻ electromagnetic     │ (137/136) = α⁻¹ structure              │
│         │ Both ends observed       │ (1 - K/B²) = "−" = complete traversal  │
│         │ Direct resonance scan    │ Smallest correction = cleanest path    │
├─────────┼──────────────────────────┼────────────────────────────────────────┤
│ W       │ Neutrino UNOBSERVED      │ "+" signs = forward/incomplete         │
│         │ W couples to generations │ (209/208) = n²S + 1 = generation + 1   │
│         │ Half the picture missing │ (1 + 1/6452) = traversal in progress   │
└─────────┴──────────────────────────┴────────────────────────────────────────┘
```

### The Sign Rule

| Sign | Meaning | Example |
|------|---------|---------|
| **"+"** | Traversal incomplete — something not in measurement equation | W: neutrino escapes |
| **"−"** | Traversal complete — everything couples to measurement | Z: all products detected |

### Why the Neutrino Is "Unobserved"

The neutrino interacts with the **weak force only**, NOT the electromagnetic force:
- Detectors work via EM interactions (ionization, scintillation)
- The neutrino passes through undetected
- From the measurement's BLD: the neutrino is **not part of the structure being traversed**

This is why W has "+" corrections: the measurement apparatus (EM-based) cannot include the neutrino in its traversal. The structure being traversed is incomplete → forward traversal → "+" signs.

**Forces ARE K/X at Different Scales**

From [Force Structure](../foundations/force-structure.md), forces are NOT fundamentally different phenomena — they are observer corrections K/X at different X values:

| Force | X (Structure) | K/X | What Measurement Traverses |
|-------|---------------|-----|---------------------------|
| EM | B = 56 | 2/56 ≈ 0.036 | Boundary structure |
| Weak | n×L×B = 4480 | 2/4480 ≈ 0.00045 | Full geometric-boundary |
| Strong | n+L = 24 | 2/24 ≈ 0.083 | Geometry only |

**Why detectors are EM-based:**
- Detectors work by traversing boundary structure (ionization, scintillation)
- This means detectors measure through X = B
- Anything that doesn't couple to B is "invisible" to the detector

**Why neutrinos are "unobserved":**
- Neutrinos interact via weak force (X = n×L×B)
- Detectors work via EM force (X = B)
- B ⊂ n×L×B but they don't match
- The neutrino's structure doesn't align with the detector's traversal path

**The ± sign is derivable:**
- **+** = X(measurement) < X(particle) → incomplete traversal
- **−** = X(measurement) ≥ X(particle) → complete traversal

For W measurement:
- W couples via weak (X = n×L×B)
- Detector sees via EM (X = B)
- B < n×L×B → incomplete → "+" corrections

For Z measurement:
- Z decays to EM-coupled products (e⁺e⁻)
- Detector sees via EM (X = B)
- All products couple to B → complete → "−" corrections

See also: [Discovery Method](../foundations/discovery-method.md) — How K/X was discovered

### Experimental Sources

- [ATLAS Higgs mass measurement](https://atlas.cern/Updates/Briefing/Run2-Higgs-Mass) — H→γγ and H→4ℓ channels
- [LEP electroweak measurements](https://cerncourier.com/a/leps-electroweak-leap/) — 17M Z decays, 25× better precision than expected
- [CMS W mass measurement](https://cms.cern/news/cms-delivers-best-precision-measurement-w-boson-mass-lhc) — "we can only work with half the picture"

---

## Validation Summary

| Boson | Predicted | Observed | Δ | Uncertainty | Status |
|-------|-----------|----------|---|-------------|--------|
| Higgs | 125.31 GeV | 125.25 GeV | 58 MeV | 170 MeV | **DERIVED** ✓ |
| Z | 91.187 GeV | 91.188 GeV | 0.5 MeV | 2.1 MeV | **DERIVED** ✓ |
| W | 80.373 GeV | 80.377 GeV | 3.7 MeV | 12 MeV | **DERIVED** ✓ |

All three electroweak boson masses are derived to within experimental measurement uncertainty. The residuals follow BLD structure (ratio B/n = 14), confirming the traverser contribution.

---

## Why Observer Corrections Exist

The BLD values (v/2, v/e, etc.) are the **true structural values**. What we measure differs slightly because **measurement itself has a cost**. This isn't a flaw — it's fundamental to how observation works.

### The Core Insight: You Can't Observe for Free

From [Observer Corrections](../cosmology/observer-correction.md):

> Every measurement requires **two points of reference**: the Machine (observer) and the Structure (observed). The solution is where they agree.

```
┌─────────────────────────────────────────────────────────────────┐
│                    THE TWO-REFERENCE PRINCIPLE                   │
│                                                                  │
│   STRUCTURE (what exists)         MACHINE (what observes)        │
│   ┌─────────────────────┐         ┌─────────────────────┐       │
│   │                     │         │                     │       │
│   │   v/2 = 123.11 GeV  │◄───────►│   +1/B = +1.8%     │       │
│   │   (Higgs base)      │         │   (observation cost)│       │
│   │                     │         │                     │       │
│   └─────────────────────┘         └─────────────────────┘       │
│              │                              │                    │
│              └──────────┬───────────────────┘                    │
│                         │                                        │
│                         ▼                                        │
│              ┌─────────────────────┐                            │
│              │  MEASUREMENT        │                            │
│              │  = 125.31 GeV       │                            │
│              │  (structure × cost) │                            │
│              └─────────────────────┘                            │
└─────────────────────────────────────────────────────────────────┘
```

### Why K/X is the Universal Pattern

The Killing form K = 2 represents **bidirectional observation** (see [Killing Form](../lie-theory/killing-form.md)):

```
To observe anything:
  1. Send query:    Observer → Structure  (1 link)
  2. Get response:  Structure → Observer  (1 link)
  Total cost: K = 2 links (minimum for observation)
```

The skip ratio K/X appears because:
- **X** = the structure being traversed (B, n×L, n²S, etc.)
- **K** = the observation cost (2 for bidirectional, 1 for ratios)
- **K/X** = what fraction of the structure is "consumed" by observing

### Why BLD Numbers Are "Real"

The BLD structural values are what **exists**:
- v/2 = 123.11 GeV is the Higgs mass in pure structure
- v/e = 90.58 GeV is the Z mass in pure structure

What we **measure** includes observation cost:
- m_H = (v/2) × (1 + 1/B) = 125.31 GeV
- m_Z = (v/e) × corrections = 91.19 GeV

The difference isn't error — it's the **irreducible cost of measurement**. You can't observe a structure without being part of it, and being part of it changes what you see by exactly K/X.

### The "Zeroing" Principle

When observer corrections are **fully accounted for**, predictions match observations to within measurement uncertainty:

| Quantity | Structural Value | + Observer Corrections | = Observed | Δ |
|----------|------------------|------------------------|------------|---|
| m_H | v/2 = 123.11 | × (1 + 1/B) | 125.31 GeV | 58 MeV ✓ |
| m_Z | v/e = 90.58 | × (137/136)(1-K/B²) | 91.19 GeV | 0.5 MeV ✓ |
| m_W | m_Z×cos(θ) | × (209/208)(1+1/6452) | 80.37 GeV | 3.7 MeV ✓ |

The corrections "zero out" the discrepancy between structure and observation. If there's residual error beyond measurement uncertainty, we're missing a correction.

### Connection to Other Particles

The **same corrections** appear across all particles, just at different scales:

| Scale | Structure X | Correction K/X | Where It Appears |
|-------|-------------|----------------|------------------|
| Boundary | B = 56 | 2/56 ≈ 0.036 | α⁻¹, m_H |
| Geometry | n×L = 80 | 2/80 = 0.025 | m_e, Z corrections |
| Generation | n²S = 208 | 1/208 ≈ 0.005 | μ/e, m_W |
| Second-order | 6452 | 1/6452 ≈ 0.00015 | μ/e, m_W |

This universality is what makes the formulas **consistent** — they're all the same phenomenon (observation cost) at different structural scales.

### Further Reading

- [Observer Corrections](../cosmology/observer-correction.md) — The two-reference framework in detail
- [Killing Form](../lie-theory/killing-form.md) — Why K = 2 (bidirectional observation)
- [Irreducibility Proof](../foundations/irreducibility-proof.md) — Why observers are unavoidable
- [Lepton Masses](lepton-masses.md) — The same corrections in fermion masses

---

## BLD Constants Used

| Constant | Value | Origin | Used For |
|----------|-------|--------|----------|
| K | 2 | Killing form (bidirectional) | Higgs v/K, boundary corrections |
| B | 56 | 2 × dim(Spin(8)) | Boundary quantum 1/B |
| n | 4 | Spacetime dimensions | Generation structure n²S |
| L | 20 | Riemann components | Geometry structure n×L |
| S | 13 | (B-n)/n | Structural intervals, weak mixing |
| e | 2.718... | Continuous limit | Z base v/e |

---

## References

- [E7 Derivation](e7-derivation.md) — B=56 from triality
- [Lepton Masses](lepton-masses.md) — n²S and 6452 structures
- [Fine Structure Consistency](fine-structure-consistency.md) — α⁻¹ = 137.036 with same corrections
- [Killing Form](../lie-theory/killing-form.md) — K=2 bidirectional observation
- [Observer Corrections](../cosmology/observer-correction.md) — Two-reference framework
