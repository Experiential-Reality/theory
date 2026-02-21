---
status: FOUNDATIONAL
layer: reference
depends_on: []
used_by:
  - README.md
---

# Reading Path: Layman

> No math required. What BLD claims and why it matters.

## What Is BLD?

BLD says all structure — in physics, biology, computing, music, everything — is built from exactly three operations:

- **B (Boundary)**: Where things split. A wall separates inside from outside. A cell membrane separates the cell from its environment. A species boundary separates one kind of life from another.

- **L (Link)**: What connects across a split. A door connects rooms. A nerve connects brain to muscle. A trade route connects cities.

- **D (Dimension)**: What repeats. Floors in a building. Days in a year. Generations in a family.

That's it. Every structure you can observe is some combination of partitions (B), connections (L), and repetitions (D).

---

## Why Only Three?

You can't reduce any of them to the others:

- Splitting something doesn't connect anything (B alone isn't L)
- Connecting things doesn't split anything (L alone isn't B)
- Repeating doesn't split or connect (D alone isn't B or L)

And you can't add a fourth — any candidate turns out to be a combination of the three. This is proven formally in the [Irreducibility Proof](../mathematics/foundations/proofs/irreducibility-proof.md).

---

## What Does BLD Predict?

From these three operations plus one requirement — that structure can consistently observe itself — BLD derives five numbers:

| Number | Value | Meaning |
|--------|-------|---------|
| K | 2 | Observation is a round trip (ask + answer) |
| n | 4 | Spacetime has 4 dimensions |
| L | 20 | Curvature has 20 independent components |
| B | 56 | The boundary of existence has 56 modes |
| S | 13 | Structural intervals: (56-4)/4 |

From these five numbers, with no adjustable parameters, BLD derives over 50 quantities that match experiment:

| What | BLD Says | Nature Says | Match |
|------|----------|-------------|-------|
| Fine structure constant | 137.035999177 | 137.035999177 | exact |
| Dark matter fraction | 27.0% | 27(1)% | yes |
| Dark energy fraction | 68.0% | 68(1)% | yes |
| Amino acids in life | 20 | 20 | exact |
| Musical semitones | 12 | 12 | exact |
| Feigenbaum constant (chaos) | 4.66920 | 4.66920 | 0.00003% |
| Von Karman constant (turbulence) | 0.384 | 0.384 | exact |
| Higgs boson mass | 125.20 GeV | 125.20 GeV | yes |

Some of these (Feigenbaum, von Karman) had never been derived from first principles before — they were known only as measured numbers for decades.

---

## Why Does This Matter?

**Zero free parameters.** Most physics theories have adjustable knobs — constants you measure and plug in. BLD has none. Everything comes from the requirement that structure can observe itself.

**Cross-domain.** The same framework that predicts particle masses also predicts turbulence constants, the number of amino acids, and the number of musical semitones. If it works in one domain, it should work in all — because it's about structure itself, not about any particular kind of thing.

**Testable.** BLD predicts the Higgs self-coupling constant (kappa_lambda = 1.025), which will be measured at the Large Hadron Collider around 2030. If the measurement doesn't match, BLD is wrong.

**Machine-verified.** The mathematical derivation chain is formalized in [Lean 4](../../lean/) — a proof assistant that checks every logical step. 63 files, 14,321 lines, zero unproven steps, zero assumed axioms.

---

## Everyday Examples

**A ZIP file** compresses data using all three: B (symbols partition into frequent/rare), L (codes connect symbols to bit patterns), D (patterns repeat across the file). See [ZIP Example](../examples/zip.md).

**Spacetime** is BLD: B (lightcone separates past from future), L (forces connect particles), D (3 spatial dimensions + 1 time). See [Spacetime Example](../examples/spacetime.md).

---

## Want More?

- **Gentle next step**: [Newcomer Path](./newcomer.md) — introduces the formal concepts in ~30 minutes
- **See the predictions**: The root README has the full results tables
- **The discovery story**: [Discovery History](../meta/discovery-history.md) — how a programmer found this while optimizing GPU code

---

## See Also

- [Newcomer Path](./newcomer.md) — Next step with more detail
- [Glossary](../glossary.md) — Term definitions
- [Discovery Method](../meta/discovery-method.md) — The three questions applied to any domain
