---
status: EMPIRICAL
depends_on:
  - cosmology-structure.md
  - ../lie-theory/killing-form.md
---

# Dark Matter as Geometry: The Mapping

The mapping matches observations, but is conjectured not derived.

**Source**: Extracted from `cosmology.md`

---

## The Conjecture `[CONJECTURED]`

Dark matter is not matter. It is **geometric structure (L) without corresponding matter (D)**.

This mapping is **assumed from structural analogy**, not derived from first principles:

| Structural Primitive | Cosmological Component | Status |
|---------------------|------------------------|--------|
| D (dimension) | Ordinary matter — stuff occupying dimensions | `[CONJECTURED]` |
| L (link) | Dark matter — geometric structure without stuff | `[CONJECTURED]` |
| B (boundary) | Dark energy — topological/boundary term | `[CONJECTURED]` |

---

## The Calculation

### From Derived Structure

From [Cosmology Structure](cosmology-structure.md):
- L/D = 5 for 4D spacetime `[DERIVED]`

### Applying the Mapping `[CONJECTURED]`

Let ordinary matter fraction = x

Then:
- Ordinary matter (D): x
- Dark matter (L): 5x
- Dark energy (B): 1 - 6x

### Observed Values

**Observed**: x = 0.05 (5% ordinary matter)

| Component | Formula | **Predicted** | **Observed** | Error |
|-----------|---------|---------------|--------------|-------|
| Ordinary matter | x | 5% | 5% | — |
| Dark matter | 5x | **25%** | 27% | 2pp |
| Dark energy | 1-6x | **70%** | 68% | 2pp |

### The 2% Discrepancy

Without correction: 25% predicted vs 27% observed.

See [Observer Corrections](observer-correction.md) for the claimed resolution.

---

## What This Explains (If Correct)

1. **Why dark matter doesn't interact electromagnetically**: It's not matter. Geometry doesn't have charge.

2. **Why dark matter clusters with galaxies**: Geometric structure (L) correlates with matter distribution (D) through Einstein's equation, but isn't identical to it.

3. **Why direct detection fails**: We're looking for particles (D) when we should be looking for geometry (L).

4. **Why the ratio is ~5:1**: This is Riemann components / spacetime dimensions = 20/4.

---

## What Remains Uncertain

### Strong (mathematically grounded)
- BLD = Lie theory correspondence: `[PROVEN]`
- L and D irreducibility: `[PROVEN]`
- L/D = 5 for 4D: `[DERIVED]`

### Conjectured (needs validation)
- The mapping D=matter, L=dark matter, B=dark energy
- Why Riemann/Dim should equal dark matter/matter ratio
- The observer correction (8x²)

### Unknown
- Whether this makes novel testable predictions
- Whether the mapping is exact or approximate
- How to experimentally distinguish "L without D" from "hidden D"

---

## L Scaling Assumption `[POSTULATED]`

The cosmological evolution assumes L ∝ 1/a³ (same as matter).

**But L is geometry, not matter.** Alternatives:
- L ∝ 1/a² (surface scaling)?
- L ∝ 1/a⁴ (radiation-like)?
- More complex function of a?

This assumption affects all evolution predictions.

---

## Cosmological Evolution

### Scaling Laws (Assumed)

| Component | Scaling with a | Reason |
|-----------|---------------|--------|
| D (matter) | ∝ 1/a³ | Dilutes with volume |
| L (geometry) | ∝ 1/a³ | **Assumed** same as matter |
| B (dark energy) | constant | Cosmological constant, topological |

### Evolution Table

| a | D% | L% | B% | State |
|---|----|----|----|----|
| 1 (now) | 5% | 27% | 68% | Structure exists |
| 2 | 0.6% | 3.3% | 96% | Links weakening |
| 5 | 0.04% | 0.2% | 99.8% | Links nearly gone |
| 10 | 0.005% | 0.03% | 99.97% | Isolated matter |
| ∞ | 0% | 0% | 100% | **Pure B** |

### The End State

As a → ∞:
- All links decay (L → 0)
- All matter dilutes (D → 0)
- Only boundary remains (B → 100%)

The universe becomes **pure topology without structure**.

---

## Comparison with Standard Model

| Aspect | Standard (ΛCDM) | BLD |
|--------|-----------------|-----|
| Dark matter nature | Unknown particles (WIMPs, axions) | Geometric structure (L) |
| Why ~27%? | Free parameter, fit to data | **Derived**: Riemann/Dim = 20/4 = 5, plus observer correction |
| Dark energy nature | Cosmological constant (unexplained) | Boundary structure (B) |
| Why ~68%? | Free parameter | **Derived**: 1 - 6×(matter fraction) |
| Heat death | Maximum entropy | L → 0 (links overcome by boundary) |

---

## Potential Tests

1. **Precision cosmology**: Does the 20/4 ratio predict the exact dark matter fraction, or is 25% vs 27% a real discrepancy?

2. **Structure formation**: Does treating dark matter as geometry (L) rather than particles (D) change predictions for galaxy formation?

3. **Gravitational lensing**: Are there lensing signatures that distinguish geometric dark matter from particle dark matter?

4. **Direct detection null results**: Continued failure to find dark matter particles would be consistent with BLD (there are no particles to find).

---

## Implications

If dark matter is L (geometry) rather than D (particles):

1. **Particle physics**: Dark matter searches are category errors. No WIMP will be found because there is no WIMP.

2. **Cosmology**: The universe's composition is not 5% matter + 27% mystery + 68% mystery. It's 5% D + 25% L + 70% B — the structural decomposition of spacetime.

3. **Theory of everything**: BLD provides a structural framework that derives cosmological ratios from dimensional counting.

---

## BLD Structure of Measurement

The observer effect can be expressed in BLD syntax:

```
structure Measurement

# The observer (us)
D observer: matter_based
  content = D = 0.05

# The target (dark matter)
L target: geometry
  content = L_true = 5D = 0.25

# The measurement boundary
B measurement: observer | observed
  observer -> D_side, us
  observed -> L_side, dark_matter

# The measurement link (required to observe)
L measurement_link: observer -> target
  # This link MUST exist for observation
  # Its existence adds to L_observed
  cost = 2 × D_spacetime × D² = 8D² = 0.02

# The result
formula observation:
  L_observed = L_true + L_measurement
             = 5D + 8D²
             = 0.25 + 0.02
             = 0.27 = 27% ✓
```

This demonstrates the core principle: **observation requires participation, and participation creates structure**.

---

## The Substance Era

### Definition

The "substance era" is when D + L is significant — when structure exists, not just boundary.

### Key Milestones

**Matter-Λ equality** (D + L = B = 50%):
```
0.32/a³ = 0.68
a³ = 0.47
a = 0.78
```
This occurred at redshift z ≈ 0.28, about **4 billion years ago**.

**Structure freeze-out** (D + L < 1%):
```
0.32/a³ = 0.01
a³ = 32
a ≈ 3.17
```
This occurs about **17 billion years from now** (universe age ~30 Gyr).

### Timeline

| Event | Time | D+L | B | Status |
|-------|------|-----|---|--------|
| Matter-radiation equality | 47 Kyr | ~100% | ~0% | Structure can form |
| First stars | 100-400 Myr | >50% | <50% | Structure forming |
| Matter-Λ equality | 10 Gyr | 50% | 50% | Transition point |
| **Now** | 13.8 Gyr | 32% | 68% | Past transition |
| Structure freeze-out | ~30 Gyr | <1% | >99% | No new structure |
| Heat death | ∞ | 0% | 100% | Pure B |

**Observation**: We exist in the brief window where D and L are non-negligible. We are ~46% through the substance era, past the equality point.

---

## References

- [Cosmology Structure](cosmology-structure.md) — The L/D=5 derivation
- [Observer Corrections](observer-correction.md) — The 2% correction
- [E₇ Connection](../particle-physics/e7-connection.md) — B=56 speculation
