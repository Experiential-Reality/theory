---
status: DERIVED
layer: 2
depends_on:
  - ../foundations/derivations/octonion-derivation.md
  - ../foundations/derivations/force-structure.md
  - ../lie-theory/boundary-derivation.md
  - e7-derivation.md
used_by:
  - ../../meta/proof-status.md
  - ../foundations/machine/detection-structure.md
---

# Particle Classification from BLD

**Status**: DERIVED — The Standard Model particle spectrum emerges from BLD structure.

**Core claim**: Particles are valid BLD structures with specific gauge couplings. The division algebra tower constrains which combinations can exist, predicting exactly the Standard Model.

---

## Summary

**Standard Model particle content from BLD:**

1. Particles = valid BLD structures: each defined by gauge couplings (color, weak, EM, mass) — [The Principle](#1-the-principle-particles-as-bld-structures)
2. Division algebra tower ℝ ⊂ ℂ ⊂ ℍ ⊂ 𝕆 → U(1), SU(2), SU(3) — [Enumerating Structures](#2-enumerating-valid-structures)
3. Nesting constraint: higher algebras require lower (can't have color without weak) — [The Nesting Constraint](#22-the-nesting-constraint)
4. Triality → exactly 3 generations: Spin(8) three-fold symmetry — [Generation Structure](#3-the-generation-structure)
5. B = 56 → 48 fermions + 8 gluons: boundary partitions particle content — [Complete Fermion Spectrum](#4-the-complete-fermion-spectrum)
6. Charge quantization: Q = T₃ + Y/2, fractional charges from 3 colors — [Charge Quantization](#7-charge-quantization)
7. Forbidden: 4th generation (triality=3), colored leptons (nesting), SUSY partners (tentative) — [Predictions](#8-predictions-what-can-and-cannot-exist)

| Prediction | BLD Origin | Status |
|------------|------------|--------|
| SU(3)×SU(2)×U(1) | Division algebra tower | Matches SM |
| 3 generations | Spin(8) triality | Matches SM |
| No 4th generation | Triality = 3 exactly | Matches experiment |

---

## 1. The Principle: Particles as BLD Structures

### 1.1 What Defines a Particle?

A particle is a **valid BLD structure** characterized by which components it couples to:

```
COUPLING MENU (from division algebra tower)

𝕆 (octonions)   →  SU(3) color      [8 generators, 3 colors]
ℍ (quaternions) →  SU(2) weak       [3 generators, isospin]
ℂ (complex)     →  U(1) hypercharge [1 generator, Y]
ℝ (real)        →  Gravity/mass     [n×L geometry]

PLUS: B = 56 boundary structure (EM charge after symmetry breaking)
```

Each particle is defined by a binary choice at each level: **couple or not**.

### 1.2 The Neutrino as Example

From [Force Structure](../foundations/derivations/force-structure.md), forces are K/X at different scales:

| Force | X (Structure) | K/X |
|-------|---------------|-----|
| EM | B = 56 | 2/56 |
| Weak | n×L×B = 4480 | 2/4480 |
| Strong | n+L = 24 | 2/24 |

A **neutrino** couples to weak (X = n×L×B) but NOT to EM (X = B):

```
NEUTRINO STRUCTURE

B component:  ∅  (empty — no boundary interaction)
L component:  L = 20  (propagates through spacetime)
D component:  generation (νe, νμ, ντ from n²S = 208)

┌─────────────────────────────────────────────────────────┐
│                                                         │
│     n×L = 80 (geometric structure)                      │
│     ┌─────────────────────────────────────────────┐     │
│     │                                             │     │
│     │   ○ ─ ─ L ─ ─ ○ ─ ─ L ─ ─ ○                │     │
│     │   │           │           │                │     │
│     │   L           L           L    (links only)│     │
│     │   │           │           │                │     │
│     │   ○ ─ ─ L ─ ─ ○ ─ ─ L ─ ─ ○                │     │
│     │                                             │     │
│     │   No B (boundary) edges — just L (links)   │     │
│     │                                             │     │
│     └─────────────────────────────────────────────┘     │
│                         ↑                               │
│              No boundary walls around it                │
│              (that's why EM detectors can't see it)    │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

**Why weak force can "see" neutrinos**: The W/Z bosons carry B structure and act as bridges between the neutrino's pure geometry and boundary-coupled particles.

**Neutrino mass**: The missing B coupling suppresses neutrino mass by (K/B)² × K/(n×L) ≈ 1/31,000 relative to electron. See [Neutrino Masses](neutrino-masses.md).

### 1.3 Particle Structures for Detection (S Values)

**Canonical table for T ∩ S detection.** These S values determine which particles are detected and which escape.

| Particle | S (BLD structure) | Has B? | Detected by EM? |
|----------|-------------------|--------|-----------------|
| γ (photon) | {B} | ✓ | ✓ |
| ℓ (e, μ, τ) | {B, L, D} | ✓ | ✓ |
| ν (νe, νμ, ντ) | {L, D} | ✗ | ✗ |
| q (quarks) | {B, L, D} + color | ✓ | ✓ |
| W±, Z | {B, L, D} | ✓ | ✓ |
| H (Higgs) | {B, L} | ✓ | ✓ |
| g (gluon) | {L} + color | ✗ | ✗ |

**Detection rule**: A particle is detected iff T ∩ S ≠ ∅. EM detectors have T = {B}.

**Escaped structure**: When T ∩ S = ∅, the particle escapes. Its contribution: X_escaped = S − {D}.
- Example: ν escapes EM because {B} ∩ {L,D} = ∅. Its X_escaped = {L} → L = 20.

**Apply this table**: See [Detection Structure](../foundations/machine/detection-structure.md) for the complete algorithm with worked examples.

---

## 2. Enumerating Valid Structures

### 2.1 All Possible Fermion Couplings

For fermions (spin-1/2), each coupling is binary (yes/no):

| Row | Color (SU(3)) | Weak (SU(2)) | B (EM) | n×L (mass) | Particle |
|-----|---------------|--------------|--------|------------|----------|
| 1 | ✗ | ✗ | ✗ | ✓ | Sterile neutrino (νR)? |
| 2 | ✗ | ✓ | ✗ | ✓ | **NEUTRINO (νL)** |
| 3 | ✗ | ✗ | ✓ | ✓ | *Forbidden* |
| 4 | ✗ | ✓ | ✓ | ✓ | **ELECTRON (e, μ, τ)** |
| 5 | ✓ | ✗ | ✗ | ✓ | *Forbidden* |
| 6 | ✓ | ✓ | ✗ | ✓ | *Forbidden* |
| 7 | ✓ | ✗ | ✓ | ✓ | *Forbidden* |
| 8 | ✓ | ✓ | ✓ | ✓ | **QUARK (u,d,c,s,t,b)** |

**Only 4 combinations exist in nature**: Rows 1, 2, 4, 8.

### 2.2 The Nesting Constraint

The division algebra tower explains why rows 3, 5, 6, 7 are forbidden:

```
THE NESTING RULE

Division algebras nest: ℝ ⊂ ℂ ⊂ ℍ ⊂ 𝕆

A particle coupling to a HIGHER algebra MUST couple to all LOWER:

   𝕆 (color) → requires ℍ (weak) → requires ℂ (U(1)) → requires ℝ

EXCEPTION: You can "skip" to pure geometry (ℝ only) — the sterile neutrino
```

**Why each forbidden row fails:**

| Row | Coupling | Violation |
|-----|----------|-----------|
| 3 | B without weak | Can't have EM without going through SU(2)×U(1) |
| 5 | Color without weak | Can't skip ℍ when you have 𝕆 |
| 6 | Color + weak, no B | Hypercharge forces B coupling for colored particles |
| 7 | Color + B, no weak | Same constraint as row 5 |

---

## 3. The Generation Structure

### 3.1 Triality Gives Exactly 3 Generations

From [Octonion Derivation](../foundations/derivations/octonion-derivation.md), Spin(8) has triality:

```
TRIALITY: Spin(8) has three 8-dimensional representations

     8_v (vector)  ←→  8_s (spinor+)  ←→  8_c (spinor-)
          ↑____________________↓____________________↑
                 All equivalent under triality

RESULT: Every fermion type comes in exactly 3 copies
```

| Generation 1 | Generation 2 | Generation 3 |
|--------------|--------------|--------------|
| electron (e) | muon (μ) | tau (τ) |
| νe | νμ | ντ |
| up (u) | charm (c) | top (t) |
| down (d) | strange (s) | bottom (b) |

### 3.2 The n²S = 208 Structure

Generation structure is encoded in n²S = 4² × 13 = 208:

- Each generation occupies ~69 positions in the 208-dimensional structure
- Mass ratios between generations follow from position in this structure
- See [Lepton Masses](lepton-masses.md) for the μ/e and τ/μ derivations

---

## 4. The Complete Fermion Spectrum

### 4.1 Leptons and Quarks

```
LEPTONS (no color)                 QUARKS (have color)
══════════════════                 ══════════════════

Weak doublet:                      Weak doublet:
┌─────────────┐                    ┌─────────────┐
│  ν  │  no B │                    │  u  │  Q=+⅔ │  ×3 colors
├─────┼───────┤                    ├─────┼───────┤
│  e⁻ │  Q=−1 │                    │  d  │  Q=−⅓ │  ×3 colors
└─────┴───────┘                    └─────┴───────┘
     ×3 generations                     ×3 generations

Total leptons: 2 × 3 = 6           Total quarks: 2 × 3 × 3 = 18
(+ antiparticles: 12)              (+ antiparticles: 36)

TOTAL FERMIONS: 12 + 36 = 48 (including antiparticles)
```

### 4.2 Where Does 48 Come From?

```
48 = B - 8 = 56 - 8
```

The boundary structure B = 56 partitions into:
- **48 fermion slots** (quarks + leptons with antiparticles)
- **8 gluon slots** (gauge bosons, not fermions)

Alternatively:
```
48 = 3 × 16 = 3 generations × 16 Weyl fermions per generation
```

Where 16 = one complete generation (left-handed + right-handed fermions).

---

## 5. The Boson Spectrum

### 5.1 Gauge Bosons (Spin-1)

Bosons emerge from gauge symmetries:

| Source | Bosons | Count |
|--------|--------|-------|
| SU(3) | 8 gluons (g) | 8 |
| SU(2) | W⁺, W⁻, W⁰ | 3 |
| U(1) | B⁰ (hypercharge) | 1 |
| **Total** | | **12** |

After electroweak symmetry breaking (Higgs mechanism):
- W⁰ + B⁰ → Z⁰ (massive) + γ (massless photon)

**Where is 12 in BLD?**
```
12 = n × 3 = 4 × 3  (spacetime × triality)
12 = S - 1 = 13 - 1  (structural intervals minus identity)
```

### 5.2 Scalar Boson (Spin-0)

The **Higgs (H)** has 1 physical degree of freedom:
- Higgs doublet has 4 components
- 3 are "eaten" by W±, Z to become massive
- 1 remains as the physical Higgs particle

**Where is 4 in BLD?**
```
4 = n (spacetime dimensions)
Higgs doublet lives in ℍ (quaternion, 4D)
```

### 5.3 Graviton (Spin-2)

If gravity is quantized, the graviton emerges from the ℝ level (spacetime metric):
- Degrees of freedom: n(n-1)/2 - 1 = 4×3/2 - 1 = 5 (for massless spin-2 in n=4)

---

## 6. The Complete Particle Table

| Category | Count | BLD Origin |
|----------|-------|------------|
| Quarks | 6×3=18 | 𝕆 (color) × 3 (triality) × 2 (isospin) |
| Leptons | 6 | ℍ (weak) × 3 (triality) × 2 (isospin) |
| Gluons | 8 | dim(SU(3)) = 8 |
| W±, Z | 3 | dim(SU(2)) = 3 |
| Photon | 1 | dim(U(1)) = 1 |
| Higgs | 1 | B-symmetry breaking scalar |
| Graviton | 1 | ℝ metric (if quantized) |
| **TOTAL** | **38** | (not counting antiparticles) |
| With antiparticles | **62** | (fermions doubled) |

---

## 7. Charge Quantization

### 7.1 Electric Charge Formula

```
Q = T₃ + Y/2
```

Where:
- T₃ = weak isospin = ±1/2 (from SU(2) doublet position)
- Y = hypercharge (from U(1))

### 7.2 Anomaly Cancellation

Hypercharge is quantized because SU(3)×SU(2)×U(1) must be anomaly-free:

```
Σ Y = 0  over each generation
```

For quarks (×3 colors): Y_u = +2/3, Y_d = -1/3
For leptons: Y_ν = 0, Y_e = -1

```
Sum = 3(2/3) + 3(-1/3) + 0 + (-1) = 2 - 1 - 1 = 0 ✓
```

### 7.3 The 1/3 Charge Origin

The fractional charges (±1/3, ±2/3) arise from **3 colors sharing 1 unit of charge**:

```
B = 56 partitions across gauge groups:

56 = 8 (gluons) + 48 (fermions)
48 = 3 × 16 (generations × Weyl fermions)
16 = 8 + 8 (quarks + leptons per chirality)

Quarks come in 3 colors, so charge divides by 3.
```

---

## 8. Predictions: What Can and Cannot Exist

### 8.1 Allowed by BLD (May or May Not Exist)

**1. Right-Handed Neutrinos (νR)**
- Pure geometry (n×L only), no gauge couplings
- Would explain neutrino mass via seesaw mechanism
- BLD: Row 1 in coupling table — VALID structure
- **Prediction**: Should exist, very weakly coupled (sterile)

**2. Additional Higgs Bosons**
- Two Higgs doublets (8 components → 5 physical)
- BLD: B breaks in multiple ways? Unclear constraint.
- **Prediction**: Possible but not required

### 8.2 Forbidden by BLD

**1. Fourth Generation**
- Triality gives exactly 3, not more
- BLD: FORBIDDEN by Spin(8) triality structure
- **Prediction**: NO fourth generation
- **Status**: Matches experiment ✓

**2. Colored Leptons**
- Color without full weak structure violates nesting
- BLD: FORBIDDEN by division algebra consistency
- **Prediction**: Cannot exist

**3. Other Forbidden Structures**
- Fractional charges other than ±1/3, ±2/3, ±1, 0
- More than 8 gluon colors
- Particles coupling to EM but not weak (B without SU(2))

### 8.3 The Supersymmetry Question

Standard supersymmetry doubles the particle spectrum:
- Every fermion gets a boson partner (selectron, squark, etc.)
- Every boson gets a fermion partner (photino, gluino, etc.)

**BLD perspective**: There is no obvious doubling mechanism in the division algebra tower.

```
SUSY DOUBLING vs BLD STRUCTURE

SUSY: fermion ↔ boson (doubles everything)

BLD:  Fermions = spinor representations of division algebras
      Bosons = adjoint representations of gauge groups

      These are DIFFERENT structures, not paired.
      No natural "partner" relationship in BLD.
```

**Tentative prediction**: Supersymmetric partners may not exist.

**Caveat**: This needs more rigorous analysis. SUSY could emerge from a BLD structure not yet identified.

---

## 9. Open Questions

### 9.1 The Sterile Neutrino

Row 1 in the coupling table (pure geometry, no gauge couplings) is a valid BLD structure:

```
STERILE NEUTRINO (νR)

┌─────────────────────────────────────────────────────────┐
│                                                         │
│   Couples to: NOTHING except gravity (n×L geometry)    │
│                                                         │
│   B component:  ∅  (no boundary)                       │
│   SU(2):        ∅  (no weak)                           │
│   SU(3):        ∅  (no color)                          │
│   n×L:          ✓  (has mass, propagates)              │
│                                                         │
│   This is the "ghost of ghosts" — even more invisible  │
│   than the active neutrino.                            │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

**Questions**:
1. Does BLD *require* sterile neutrinos, or just *permit* them?
2. If they exist, what determines their mass? (Seesaw scale M_R ≈ v × B/L ≈ 700 GeV?)
3. Are there 3 sterile neutrinos (one per generation) or a different number?

**Active neutrino masses**: Now DERIVED from missing B structure. See [Neutrino Masses](neutrino-masses.md).

### 9.2 Why These Gauge Groups?

The Standard Model gauge group is SU(3)×SU(2)×U(1).

**BLD derivation** (from division algebra tower):
- 𝕆 → G₂ → SU(3) (fix octonion reference)
- ℍ → SU(2) (unit quaternions)
- ℂ → U(1) (unit circle)

**Question**: Why doesn't SU(3)×SU(2)×U(1) unify into a simple group at high energy?

Possible BLD answer: The division algebras are *nested*, not *unified*. The "unification" at GUT scale may be an artifact of running couplings, not a fundamental merger.

### 9.3 Why Is the Photon Massless?

After electroweak symmetry breaking:
- W±, Z acquire mass (eat 3 Goldstone bosons)
- Photon remains massless

**BLD perspective**: The photon is the unbroken U(1) generator after SU(2)×U(1) → U(1)_EM.

**Question**: Is photon masslessness *derived* from BLD, or an input?

### 9.4 Dark Matter Candidates

BLD predicts dark matter fraction (27%) from L/D = 5. But what IS dark matter?

**Candidates consistent with BLD**:
1. **Sterile neutrinos** (Row 1 structure) — very weakly coupled
2. **Primordial black holes** — pure geometry, no gauge couplings
3. **Axions** — if they emerge from B symmetry breaking

**Question**: Does BLD predict a *specific* dark matter particle, or just the *amount*?

### 9.5 The Mass Hierarchy Problem

Particle masses span many orders of magnitude:
- Neutrinos: ~0.1 eV
- Electron: 0.511 MeV
- Top quark: 173 GeV
- Higgs: 125 GeV

**Question**: Does BLD explain WHY these specific masses, or just their ratios?

Current status:
- Mass *ratios* (μ/e, τ/μ) are derived from n²S structure
- Absolute masses require the Higgs VEV v = 246 GeV as reference
- Why v = 246 GeV? This may connect to cosmological structure.

---

## 10. Summary

### 10.1 What BLD Predicts

From BLD axioms alone:

| Prediction | BLD Origin |
|------------|------------|
| SU(3)×SU(2)×U(1) gauge group | Division algebra tower |
| Exactly 3 generations | Spin(8) triality |
| Charge quantization (±1/3, ±2/3, ±1, 0) | Anomaly cancellation + 3 colors |
| 48 fermions + 8 gluons | B = 56 boundary structure |
| 4D spacetime | n = 4 from octonion reference fixing |
| Gravity | L = 20 Riemann structure |

**The predicted particle content = Standard Model.**

### 10.2 What BLD Allows

- Right-handed (sterile) neutrinos
- Additional Higgs bosons
- Graviton (if gravity is quantized)

### 10.3 What BLD Forbids

- Fourth generation (triality = 3, exactly)
- Colored leptons (nesting violation)
- Magnetic monopoles (no topological defects in BLD?)
- Supersymmetric partners (no doubling mechanism in BLD — tentative)

---

## References

- [Octonion Derivation](../foundations/derivations/octonion-derivation.md) — Division algebra tower, triality, G₂ → SU(3)
- [Force Structure](../foundations/derivations/force-structure.md) — Forces as K/X at different scales
- [E7 Derivation](e7-derivation.md) — B = 56 from triality and Spin(8)
- [Lepton Masses](lepton-masses.md) — Generation structure n²S = 208
- [Boson Masses](boson-masses.md) — Electroweak bosons from BLD
- [Discovery Method](../foundations/discovery-method.md) — How K/X was discovered
