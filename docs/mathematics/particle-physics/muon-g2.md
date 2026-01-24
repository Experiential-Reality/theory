---
status: PROVISIONAL
layer: 2
depends_on:
  - ../foundations/integer-machine.md
  - ../cosmology/observer-correction.md
  - ../lie-theory/killing-form.md
  - fine-structure-consistency.md
  - lepton-masses.md
  - detection-structure.md
used_by:
  - ../../meta/proof-status.md
  - ../../analysis/error-analysis.md
---

# Muon g-2 Anomaly: Derivation from BLD

## Quick Summary (D≈7 Human Traversal)

**The g-2 anomaly explained in 7 steps:**

1. **The tension** — Experiment disagrees with Standard Model by ~4σ
2. **What g-2 measures** — Muon's magnetic moment through virtual loops
3. **Loops = K/X** — Virtual contributions are incomplete traversals at intermediate scales
4. **Second-order structure** — α² × K²/((n×L)² × S) = 256×10⁻¹¹ (base)
5. **Detection structure** — Muon decay: e detected (B), neutrinos escape (L)
6. **Detection correction** — X = B + L = 76, correction = 76/78
7. **Result** — Δa_μ = 256 × 76/78 = 250×10⁻¹¹ (**0.4% error**)

| Quantity | BLD Prediction | Observed | Error |
|----------|---------------|----------|-------|
| Δa_μ | 250 × 10⁻¹¹ | 251 × 10⁻¹¹ | **0.4%** |

**Status**: PROVISIONAL — Base formula (α² × K²/((n×L)²×S) = 256) is derived. Detection correction (76/78) gives correct result but form awaits second reference point (J-PARC).

---

## The Experimental Tension

### What's Measured

The [anomalous magnetic moment](https://en.wikipedia.org/wiki/Anomalous_magnetic_moment) of the muon:

```
a_μ = (g-2)/2
```

Where g is the gyromagnetic ratio. For a point particle, g = 2 exactly. Quantum corrections make g slightly larger than 2.

### The Discrepancy

| Source | Value (× 10⁻¹¹) | Reference |
|--------|-----------------|-----------|
| **Experiment** | 116592061 ± 41 | [Fermilab g-2 (2023)](https://muon-g-2.fnal.gov/) |
| **SM Theory** | 116591810 ± 43 | [Muon g-2 Theory Initiative (2020)](https://arxiv.org/abs/2006.04822) |
| **Discrepancy** | **251 ± 59** | ~4.2σ tension |

The experimental value exceeds the SM prediction by Δa_μ ≈ 251 × 10⁻¹¹.

**Note**: Lattice QCD calculations show tension with the data-driven hadronic vacuum polarization estimates. BLD provides an independent derivation of the discrepancy.

---

## BLD Framework: Loops as K/X Corrections

### What g-2 Measures

The anomalous magnetic moment arises from virtual particle loops:

```
g-2 measurement structure:

     μ ──────────────────── μ
         ╲                ╱
          ╲              ╱
           ╲            ╱
            γ          γ
             ╲        ╱
              ╲      ╱
               ◯◯◯◯◯    ← virtual loops (e⁺e⁻, hadrons, etc.)
```

Each virtual loop is an **incomplete K/X traversal** at intermediate scale.

### The Two-Reference Principle

From [Observer Corrections](../cosmology/observer-correction.md):

```
Reference 1 (Structure): The muon's generational structure
Reference 2 (Machine): Virtual particles traversing that structure
```

Virtual particles don't complete full traversals — they "borrow" from the vacuum and return. This incomplete traversal has a cost: K/X at each scale.

### Why α² Appears

The g-2 diagram involves **two photon vertices** (two insertions of the EM coupling):

```
Muon → photon → loop → photon → Muon
         α              α
```

Therefore: base coupling = α × α = α²

### Why (n×L)²×S Is the Structure

The muon is a second-generation lepton. From [Lepton Masses](lepton-masses.md):

| Structure | Value | Meaning |
|-----------|-------|---------|
| **n²** | 16 | Lorentz symmetry (4×4 spacetime) |
| **S** | 13 | Structural intervals = (B-n)/n |
| **n²×S** | 208 | Generational structure positions (muon's primordial mass ratio) |
| **n×L** | 80 | Geometric structure (spacetime × Riemann curvature) |
| **(n×L)²** | 6400 | Geometric structure squared (loop goes out and back) |
| **(n×L)²×S** | 83,200 | Second-order traversal structure |

**Why squared?** The g-2 measurement involves a **loop diagram** — the virtual correction goes out through geometric structure and returns. This bidirectional traversal squares the geometric term:

```
First-order (single traversal):  K/(n×L)
Second-order (loop):             (K/(n×L))² = K²/(n×L)²
With generation modulation:      K²/((n×L)² × S)
```

When measuring the muon's magnetic moment:
- The experiment probes the muon's coupling to the EM field
- The loop traverses geometric structure **twice** (out and back): (n×L)² = 6400
- The muon's generational structure modulates the effect: S = 13
- Total second-order structure: (n×L)²×S = 83,200

**Why n² appears in mass but (n×L)² in g-2?** The muon mass ratio μ/e = 208 = n²×S is a first-order ratio. The g-2 anomaly is a second-order loop correction, so the geometric structure n×L gets squared.

**Comparison with other forces:**
| Force | X (Structure) | Why This X |
|-------|---------------|------------|
| Strong | n+L = 24 | Geometry only (jets reveal arrangement, not boundary) |
| Weak mixing | n×L×B = 4480 | Full structure (Z couples to everything) |
| **g-2 anomaly** | **(n×L)²×S = 83,200** | **Geometric² × generation (loop traversal)** |

See [Strong Coupling](strong-coupling.md) for comparison.

---

## The Derivation

### Step 1: Identify the Missing Term

The SM calculation accounts for:
- QED loops (electron, muon, tau)
- Hadronic vacuum polarization
- Hadronic light-by-light
- Electroweak corrections

What's **not** accounted for: the second-order observer correction K²/X at the (n×L)²×S scale.

### Step 2: Apply the Universal Skip Ratio (Second Order)

From [Killing Form](../lie-theory/killing-form.md), all observer corrections have the form:

```
correction = K/X × direction
```

For g-2, we have a **second-order** correction because loop diagrams involve squared terms:
- K² = 4 (bidirectional observation, squared for loop)
- X = (n×L)² × S = 83,200 (geometric structure squared × generation)
- Base coupling = α² (two-photon diagram)

The structure (n×L)² × S arises because:
- (n×L)² = 6400: The loop traverses geometric structure twice (in and out)
- S = 13: The muon's generational structure modulates the effect

### Step 3: Calculate

```
Δa_μ = α² × K² / ((n×L)² × S)

Where:
  α⁻¹ = 137.036       → α² = (1/137.036)² = 5.32 × 10⁻⁵
  K = 2                (Killing form, bidirectional)
  K² = 4               (squared for second-order effect)
  n×L = 80             (geometric structure)
  (n×L)² = 6400        (geometric structure squared)
  S = 13               (structural intervals)
  (n×L)² × S = 83,200  (full denominator)

Calculation:
  Δa_μ = 5.32 × 10⁻⁵ × 4 / 83,200
       = 5.32 × 10⁻⁵ × 4.81 × 10⁻⁵
       = 2.56 × 10⁻⁹
       = 256 × 10⁻¹¹
```

**Why K² and (n×L)²?** The g-2 anomaly is a **second-order** effect:
- Two photon vertices → α² (already squared)
- Geometric traversal cost → (K/(n×L))² (squared because it's a loop correction)
- Generation structure → 1/S (single factor for the muon's generation)

### Step 4: Detection Structure Correction

The base calculation gives 256 × 10⁻¹¹. But the g-2 measurement involves detecting muon decay products, and not all products are detected.

From [Detection Structure](detection-structure.md), the T ∩ S formalism:
- Detection occurs iff T ∩ S ≠ ∅ (traverser and structure share elements)
- Escaped structure contributes to X

**Muon decay in g-2:**
```
μ⁻ → e⁻ + ν̄_e + ν_μ

Detector T = {B}              (EM-based: calorimeters, trackers)

Electron S_e = {B, L, D}     → T ∩ S_e = {B} ≠ ∅ → DETECTED
Neutrinos S_ν = {L, D}       → T ∩ S_ν = ∅       → ESCAPE
```

Neutrinos have no boundary (B) — they don't couple electromagnetically. The detector (EM-based) can't see them.

**X for detection:**
```
X_escaped = {L}               (neutrinos carry Link structure away)
X = B + L = 56 + 20 = 76     (what the detector must traverse)
```

**Why X/(X+K), not (X+K)/X?**

The sign rule says "+" (incomplete traversal) when something escapes. But the FORM of the correction depends on how missing information affects the measurement:

| Measurement Type | Missing Info | Effect | Correction Form |
|-----------------|--------------|--------|-----------------|
| Mass reconstruction (W) | INFERRED from conservation | Can increase value | × (X+K)/X > 1 |
| Precision anomaly (g-2) | LOST (carries away signal) | Reduces observable | × X/(X+K) < 1 |

For g-2, the neutrinos carry away spin-correlated information. This isn't reconstructed — it's lost. The measured anomaly is therefore **smaller** than the base prediction.

```
Detection correction = X/(X+K) = 76/78 = 0.974
```

**With detection correction:**
```
Δa_μ = 256 × 10⁻¹¹ × (76/78)
     = 250 × 10⁻¹¹
```

**Note**: This uses the same X = B + L = 76 as W → ℓν (see [Detection Structure](detection-structure.md)), but the form X/(X+K) vs (X+K)/X differs because information is lost rather than inferred.

### Result

| Quantity | Value |
|----------|-------|
| **Base (α² × K²/X)** | 256 × 10⁻¹¹ |
| **Detection correction** | 76/78 |
| **BLD Prediction** | Δa_μ = 250 × 10⁻¹¹ |
| **Observed** | Δa_μ = 251 ± 59 × 10⁻¹¹ |
| **Error** | **0.4%** (0.02σ) |

The BLD prediction falls **exactly within the experimental uncertainty**.

---

## Physical Interpretation

### Why This Works

The g-2 anomaly represents the **muon's generational traversal cost** that the SM doesn't account for:

| SM Term | What It Captures |
|---------|-----------------|
| QED loops | Electron/muon virtual pairs |
| Hadronic VP | Quark-antiquark fluctuations |
| Light-by-light | Multi-photon scattering |
| Electroweak | W, Z, H contributions |
| **Missing** | **(n×L)²×S second-order traversal cost** |

The SM calculates loop integrals but doesn't include the discrete/continuous mismatch when the muon (a generational object at scale n²×S) couples to the EM field through geometric structure (n×L), squared for the loop.

### Connection to Fine Structure

Compare with the [fine structure constant](fine-structure-consistency.md):

```
α⁻¹ accumulated correction = e²×120/(119×(n×L×B)²)
                           ≈ 3.7 × 10⁻⁷
```

The g-2 anomaly:
```
Δa_μ = α² × K²/((n×L)² × S)
     ≈ 2.56 × 10⁻⁹
```

Both are second-order corrections, but with different structures:
- **α⁻¹**: Uses e² (discrete→continuous limit) over (n×L×B)² = 20,070,400 (full geometric-boundary)
- **g-2**: Uses α² × K² over (n×L)² × S = 83,200 (geometric² × generation)

The scales differ because:
- α⁻¹ measures photon coupling to boundary (B = 56)
- g-2 measures muon (generational) coupling to photon through geometry (n×L = 80)

### Why the Muon, Not Electron?

The electron g-2 shows no significant anomaly because:

| Particle | Generational Structure | Effect |
|----------|----------------------|--------|
| Electron | Gen 1 (reference) | No traversal cost beyond QED |
| Muon | Gen 2 (n²×S positions) | Full (n×L)²×S second-order cost |
| Tau | Gen 3 (2πe rotational) | Even larger cost (but harder to measure) |

The electron is at the "junction" — the reference point. It doesn't pay generational traversal costs. The muon, being the second generation, traverses the n²×S = 208 structure through geometric coupling n×L, incurring the second-order K²/((n×L)²×S) correction.

### Tau g-2 Prediction

The tau is third-generation, using **rotational mode** (2πe) rather than discrete mode (n²S). From [Lepton Masses](lepton-masses.md), the tau's primordial multiplier is S+n = 17, while muon uses n²S = 208.

If measurable, the tau g-2 anomaly should follow a similar second-order pattern:

```
Δa_τ = α² × K² / ((n×L)² × structure_τ)

Where structure_τ differs from structure_μ:
  - Muon (discrete): S = 13 (structural intervals)
  - Tau (rotational): Likely involves S+n = 17 or similar

Estimate using generation ratio:
  Δa_τ ≈ Δa_μ × (S / (S+n))
       = 256 × 10⁻¹¹ × (13/17)
       ≈ 196 × 10⁻¹¹

Or using primordial ratio:
  Δa_τ ≈ Δa_μ × (17/208)
       ≈ 21 × 10⁻¹¹
```

**Status**: This is speculative. The tau's rotational mode may require a different formula structure entirely. Current experimental precision for tau g-2 is far from testing this — the tau lifetime (2.9×10⁻¹³ s) makes precision measurements extremely difficult.

---

## Alternative Derivation: From Second-Order Corrections

### The General Form

From [Observer Corrections](../cosmology/observer-correction.md), observer corrections follow K/X. For second-order effects (like loop diagrams), we get (K/X)²:

```
second-order correction = (K/X)² = K²/X²
```

For g-2, the muon's anomalous moment involves a loop correction at the geometric scale:

```
Δa_μ = α² × (K/(n×L))² × (1/S)
     = α² × K² / ((n×L)² × S)
```

This is α² (two-photon coupling) times (K/(n×L))² (geometric traversal squared) times 1/S (generation factor).

### Why Not e² Here?

The fine structure accumulated term uses e²:
```
α⁻¹ accumulated = e²×120/(119×(n×L×B)²)
```

But g-2 uses K directly because of **what's being measured**:

| Measurement | What It Probes | Correction Type |
|-------------|---------------|-----------------|
| **α⁻¹** | Photon coupling to boundary (B=56) | Discrete→continuous embedding → e² |
| **g-2** | Muon generational coupling to photon | Discrete structure traversal → K |

- **α⁻¹**: Measures how discrete boundary structure (B=56 modes) embeds in continuous observation. The limit process (1+1/n)^n → e is the cost of this embedding.

- **g-2**: Measures how the muon (at discrete position n²×S = 208) couples through geometric structure n×L = 80. The loop squares this to (n×L)² = 6400, modulated by S = 13. The measurement is discrete traversal — no limit process needed, hence K not e.

The muon's position in generational space is **already discrete** (n²×S = 208 positions). The loop measurement traverses geometric structure twice (out and back), with cost K² = 4 for the round trip.

### Connecting to Integer Machine

From [Integer Machine](../foundations/integer-machine.md):

```
Primordial: μ/e = n²S = 208 (exact integer)
Observed:   μ/e = 206.768... (includes K/X corrections)
```

The g-2 anomaly is **another manifestation** of this same gap. When measuring the muon's magnetic properties, the experiment traverses the same n²×S structure, incurring the same type of K/X cost — just at a different order (α² base vs linear ratio).

---

## Experimental Verification

### Current Status

| Experiment | Status | Δa_μ (× 10⁻¹¹) |
|------------|--------|----------------|
| BNL E821 (2006) | Complete | 279 ± 76 |
| Fermilab Run 1-3 (2023) | Complete | 249 ± 48 |
| Combined | — | 251 ± 41 |
| J-PARC E34 | Planned | — | **Key: different detection structure** |

### What Would Falsify This?

If the discrepancy is resolved by:
1. **Lattice QCD improvements** matching experiment → SM is complete, BLD prediction becomes a coincidence
2. **New physics** (SUSY, dark photon, etc.) → Different mechanism, BLD prediction may still hold as effective description

If the discrepancy **persists** and equals our prediction:
- BLD explains it as second-order generational traversal cost
- No new particles needed — it's observer correction at (n×L)²×S scale

### Testable Predictions

1. **Base: α² × K²/((n×L)² × S) = 256 × 10⁻¹¹** — This is DERIVED and should hold
2. **Electron g-2** should show no corresponding anomaly (no generational cost) — DERIVED
3. **Tau g-2** should show a smaller anomaly (if measurable) due to its different generational mode
4. **J-PARC** — Different experimental method will constrain the detection correction form. If J-PARC confirms ~250 with different systematics, the 76/78 form gains support. If it differs, the detection model needs refinement.

---

## Connection to Other BLD Derivations

### The K/X Pattern

| Measurement | Structure X | Correction | Result |
|-------------|------------|------------|--------|
| α⁻¹ boundary | B = 56 | K/B = 2/56 | +0.036 |
| α⁻¹ accumulated | (n×L×B)² = 20M | e²/X | −3.7×10⁻⁷ |
| m_e observer | n×L = 80 | K/(n×L) = 2/80 | ×0.975 |
| μ/e coupling | n×L×S = 1040 | 1/(n×L×S+1) | ×0.999 |
| **g-2 anomaly** | **(n×L)²×S, B+L** | **α²×K²/X × 76/78** | **+250×10⁻¹¹** |
| Dark matter | 1/(n×x²) | K×n×x² | +2% |

All use the same K/X framework at different scales. The g-2 uses K² (second-order) because loop diagrams square the traversal cost.

### Why g-2 Uses α²×K²/X

Unlike mass corrections (which are multiplicative), g-2 is an **additive** quantum correction:

```
a_μ = (α/2π) + (α/π)²×C₂ + (α/π)³×C₃ + ...
                    ↑
                    Two-loop and higher
```

The BLD correction enters at the two-loop level:
- **α²**: Two-photon vertices in the diagram
- **K²**: Second-order traversal cost (loop goes out and back)
- **(n×L)²**: Geometric structure traversed twice
- **S**: Generation structure (single factor, modulates the loop)

This explains why g-2 uses K² (second-order in Killing form) while first-order corrections like m_e use just K.

---

## Summary

```
THE MUON g-2 ANOMALY IN BLD:

Observation: SM prediction differs from experiment by ~4σ

Structure: Muon = Gen 2 = n²×S = 208 positions
           Geometric coupling = n×L = 80
           Second-order structure: (n×L)² × S = 83,200

Base:      α² × K² / ((n×L)² × S) = 256 × 10⁻¹¹

Detection: μ → e + ν_e + ν̄_μ
           Detector T = {B}, sees electron (B ∈ S_e)
           Neutrinos escape (no B in S_ν)
           X = B + L = 76, correction = 76/78

Formula:   Δa_μ = α² × K² / ((n×L)² × S) × (B+L)/(B+L+K)
                = 256 × 10⁻¹¹ × 76/78
                = 250 × 10⁻¹¹

Result:    BLD predicts 250 × 10⁻¹¹
           Experiment shows 251 ± 59 × 10⁻¹¹
           Error: 0.4% (0.02σ)

Interpretation: The anomaly is NOT new physics.
                It's the muon's second-order geometric
                traversal cost, with detection correction
                for escaping neutrino structure.

Status:    PROVISIONAL
           - Base formula (256) is DERIVED
           - Detection X = B + L = 76 is DERIVED (T ∩ S)
           - Correction form (76/78) fits but not constrained
           - Awaits J-PARC for second reference point
```

---

## References

### External Sources
- [Fermilab Muon g-2](https://muon-g-2.fnal.gov/) — Latest experimental results
- [Muon g-2 Theory Initiative (2020)](https://arxiv.org/abs/2006.04822) — Consensus SM prediction
- [PDG: Muon Anomalous Magnetic Moment](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-g-2-muon-anom-mag-moment.pdf) — Review and current values
- [Anomalous magnetic moment (Wikipedia)](https://en.wikipedia.org/wiki/Anomalous_magnetic_moment) — Overview

### Internal BLD References
- [Observer Corrections](../cosmology/observer-correction.md) — Two-reference framework, K/X derivation
- [Killing Form](../lie-theory/killing-form.md) — K = 2 derivation
- [Lepton Masses](lepton-masses.md) — n²×S generational structure
- [Fine Structure Consistency](fine-structure-consistency.md) — Accumulated corrections, α² terms
- [Integer Machine](../foundations/integer-machine.md) — Primordial integers, K/X corrections
- [Detection Structure](detection-structure.md) — T ∩ S formalism, neutrino escape
