---
status: SPECULATIVE
depends_on:
  - lepton-masses.md
  - fine-structure-consistency.md
---

# Quark Masses from BLD Structure

Tentative formulas with ~10% errors, needs significant work.

**Note**: These formulas use S = 13, which inherits EMPIRICAL status from B = 56. See [Fine Structure Consistency](fine-structure-consistency.md) for the derivation chain.

**Source**: Extracted from `particle-masses.md`

---

## Overview

Quark masses are more complex than leptons due to:
- Color charge (SU(3) factor of 3)
- Electroweak mixing
- QCD confinement effects

The formulas below are tentative explorations, not established results.

---

## First Generation Quarks `[SPECULATIVE]`

### Up Quark

**Observed**: m_u ≈ 2.2 MeV

```
m_u / m_e ≈ 4.3 ≈ n + 1/3
```

The 1/3 may relate to the fractional electric charge (2/3 for up quark).

**Tentative formula**:
```
m_u = m_e × (n + Q_u)    where Q_u = 2/3
```

**Result**: m_u = 0.511 × 4.67 = 2.4 MeV (vs 2.2 observed, **9% error**)

### Down Quark

**Observed**: m_d ≈ 4.7 MeV

```
m_d / m_e ≈ 9.2 ≈ 2n + 1
```

**Tentative formula**:
```
m_d = m_e × (2n + Q_d)   where Q_d = 1/3 (absolute value)
```

**Result**: m_d = 0.511 × 8.33 = 4.3 MeV (vs 4.7 observed, **9% error**)

---

## Heavy Quarks `[HIGHLY SPECULATIVE]`

The following are pattern-matching attempts, not derived formulas:

| Quark | Mass | Ratio to m_e | Possible Formula | Status |
|-------|------|--------------|------------------|--------|
| Strange | 96 MeV | 188 | ≈ n² × S - n? | Tentative |
| Charm | 1.27 GeV | 2485 | ≈ n² × S × (S-n)? | Tentative |
| Bottom | 4.18 GeV | 8180 | ≈ m_τ × n + ? | Tentative |
| Top | 173 GeV | 338,500 | ≈ v × α × n? | Very tentative |

**Note**: These formulas have not been validated. Error bars would be large.

---

## What's Missing

1. **SU(3) Color Factor**: Quarks come in 3 colors. This should affect the formulas.

2. **Electroweak Mixing**: The CKM matrix relates quark generations. Not incorporated.

3. **QCD Effects**: Running masses, confinement energy not accounted for.

4. **Structural Derivation**: Unlike leptons, no clear structural interpretation exists.

---

## Open Questions

1. How does color charge enter BLD quark mass formulas?

2. Why is the top quark so much heavier than other quarks (comparable to Higgs VEV)?

3. Can CKM mixing angles be derived from BLD?

4. What is the BLD interpretation of QCD confinement?

5. **Neutrino masses**: If neutrinos have mass, where do they fit? Perhaps at a "sub-D" level?

6. **Running of constants**: α and masses "run" with energy scale. How does BLD account for renormalization?

7. **The +1 in α⁻¹**: Is this really the "observer term"? Or does it have another interpretation?

---

## References

- [Lepton Masses](lepton-masses.md) — Better-established formulas
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — SU(3) in BLD terms
