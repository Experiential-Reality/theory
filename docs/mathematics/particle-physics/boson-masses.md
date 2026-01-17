---
status: SPECULATIVE
depends_on:
  - lepton-masses.md
  - fine-structure-consistency.md
---

# Gauge Boson and Higgs Masses

Pattern-matching, not derived.

**Note**: These formulas use S = 13, which inherits EMPIRICAL status from B = 56. See [Fine Structure Consistency](fine-structure-consistency.md) for the derivation chain.

**Source**: Extracted from `particle-masses.md`

---

## W and Z Masses `[SPECULATIVE]`

The W and Z get mass from electroweak symmetry breaking:

```
m_W = 80.4 GeV
m_Z = 91.2 GeV
v = 246 GeV
```

**Ratios:**

| Boson | Mass | Ratio to v | Approximation |
|-------|------|------------|---------------|
| W | 80.4 GeV | 0.327 | ≈ 1/3 |
| Z | 91.2 GeV | 0.371 | ≈ 1/e (where e = 2.718...) |
| v (Higgs VEV) | 246 GeV | 1 | — |

**Tentative hypotheses:**

```
m_W = v / 3 × correction
m_Z = v / e × correction
```

- The factor of 3 may relate to color or generations
- The factor of e may relate to the exponential structure of the hierarchy

**Status**: Speculative pattern-matching. No derivation from BLD principles.

---

## The Higgs Mass `[SPECULATIVE]`

**Observed**: m_H = 125 GeV

**Ratio**:
```
m_H / v = 125 / 246 = 0.508 ≈ 1/2
```

**Tentative hypothesis:**
```
m_H = v / 2
```

**Result**: Predicts 123 GeV vs 125 GeV observed (1.6% error)

**Alternative attempt:**
```
m_H / v = L / (L + n + B) = 20/80 = 0.25
```
This doesn't match (predicts 61.5 GeV).

**Status**: Not yet derived from BLD structure.

---

## Open Questions

1. **Why simple fractions?** Why do W and Z masses relate to v by approximately 1/3 and 1/e?

2. **Is m_H = v/2 meaningful?** The 1.6% error is small but not zero. Is this coincidence or structure?

3. **Electroweak breaking in BLD?** Can electroweak symmetry breaking be expressed in BLD terms?

4. **Color factor?** Does the factor of 3 in m_W relate to SU(3) color?

---

## What Would Validate This

To move from SPECULATIVE to EMPIRICAL:
1. Derive the 1/3 and 1/e from BLD structural principles
2. Explain why Higgs is approximately v/2
3. Connect to electroweak gauge structure

---

## References

- [Lepton Masses](lepton-masses.md) — Better-established mass formulas
- [Fine Structure Consistency](fine-structure-consistency.md) — Higgs VEV role
- [Quark Masses](quark-masses.md) — Other speculative mass formulas
