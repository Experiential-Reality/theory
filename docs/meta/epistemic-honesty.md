---
status: FOUNDATIONAL
---

# Epistemic Honesty in BLD Physics

> **Status**: Foundational (meta-document governing all physics claims)

This document defines standards for intellectual honesty in BLD physics documentation — distinguishing what is derived vs reframed, what is prediction vs explanation, and what is validated vs hypothesized.

## Summary

**Standards for intellectual honesty in BLD physics:**

1. Derivation vs Reframing: derivation produces results not assumed; reframing organizes known physics — [Core Distinction](#the-core-distinction)
2. Novel vs Post-Hoc: predictions before observation (stronger) vs explanations after (weaker) — [Novel vs Post-Hoc](#novel-prediction-vs-post-hoc-explanation)
3. Six levels: VALIDATED, DERIVED, REFRAMING, MECHANISM, HYPOTHESIS, EXPLORATORY — [Classification](#classification-scheme)
4. Required sections: status header, summary table, "What BLD Does NOT Explain", "Falsifiable Predictions" — [Marking Requirements](#marking-requirements)
5. Detecting post-hoc fitting: multiple mappings, retroactive selection, no falsification — [Warning Signs](#warning-signs)
6. Status updates: upgrade on test pass, revise on fail, note alternatives — [When to Update](#when-to-update-status)

| Category | Definition | Test |
|----------|------------|------|
| Derivation | Result not assumed as input | Could you predict without knowing physics? |
| Reframing | Known physics in BLD language | Organizational value, not predictive novelty |

---

## The Core Distinction

### Derivation vs Reframing

| Category | Definition | Example |
|----------|-----------|---------|
| **Derivation** | BLD analysis produces result not assumed as input | P9: Triality → 3 generations (3 wasn't assumed) |
| **Reframing** | Known physics expressed in BLD language | Spacetime as (B, L, D) structure (GR already known) |

**Test for derivation**: Could you predict the result without knowing physics first?
- Yes → Derivation
- No → Reframing

**Both are valuable**, but they are different:
- Derivation shows BLD has predictive power
- Reframing shows BLD provides useful organization

### Novel Prediction vs Post-Hoc Explanation

| Category | Definition | Example |
|----------|-----------|---------|
| **Novel prediction** | BLD predicts something not yet known | P9: No 4th generation (before LEP excluded it) |
| **Post-hoc explanation** | BLD explains something already observed | Why U(1)×SU(2)×SU(3)? (already known to be SM) |

**Test for novelty**: Was the result known before BLD analysis?
- No → Novel prediction (stronger)
- Yes → Post-hoc explanation (weaker but still useful)

---

## Classification Scheme

> **Note**: See [Proof Status](proof-status.md) for canonical status definitions. This document provides detailed usage guidance.
>
> The six levels below map to two axes: **Evidence Strength** (VALIDATED, DERIVED, HYPOTHESIZED, OPEN) and **Claim Type** (REFRAMING, MECHANISM). HYPOTHESIS and EXPLORATORY map to **HYPOTHESIZED**.

Every physics claim should be tagged with one of:

### Level 1: VALIDATED
- Empirical tests exist with quantitative results
- External repo with reproducible code
- Clear pass/fail criteria met

**Marker**: `> **Status**: Validated (N/N tests passing)`

**Example**: Circuits D×L scaling (R² = 1.0, bld-circuits repo)

### Level 2: DERIVED
- Follows mathematically from BLD primitives
- Does not assume the result as input
- Can be falsified by future observation

**Marker**: `> **Epistemic Status**: Derived — [brief explanation]`

**Example**: P1 (Causality) — light cone boundary derived from consistency

### Level 3: REFRAMING
- Expresses known physics in BLD language
- Correctly maps existing theory
- Provides organizational value, not predictive novelty

**Marker**: `> **Epistemic Status**: Reframing of [source]`

**Example**: Maxwell's equations as L structure (EM already understood)

### Level 4: MECHANISM
- Identifies how something works
- Specific values need further calculation
- Structure is determined, parameters are not

**Marker**: `> **Epistemic Status**: Mechanism identified — [what's missing]`

**Example**: P11 (Yukawa) — S₃ breaking explains hierarchy, specific values TBD

### Level 5: HYPOTHESIS
- BLD-motivated conjecture
- Alternative explanations exist
- Needs experimental or theoretical validation

**Marker**: `> **Epistemic Status**: Hypothesis — [alternatives]`

**Example**: P13 (Dark energy as B) — alternatives include quintessence

### Level 6: EXPLORATORY
- Early-stage investigation
- Framework only, no tests designed
- May be refined or abandoned

**Marker**: `> **Status**: Exploratory`

**Example**: Protein folding BLD analysis

---

## Marking Requirements

### For New Physics Documents

Every new physics document MUST include:

1. **Status header** at top with epistemic level
2. **Summary table** showing claim status
3. **"What BLD Does NOT Explain"** section
4. **"Falsifiable Predictions"** section (if any)
5. **Alternatives noted** for hypothesis-level claims

### Template

```markdown
# BLD for [Domain]

> **Status**: [Level] ([details])

[Introduction]

---

## Conclusion

| Finding | Status | Evidence |
|---------|--------|----------|
| ... | VALIDATED/DERIVED/etc | ... |

---

## [Main content]

---

## What BLD Does NOT Explain

1. ...
2. ...

---

## Falsifiable Predictions

| Prediction | Test | Falsification Criterion |
|------------|------|------------------------|
| ... | ... | ... |

---

## See Also

- ...
```

---

## Detecting Post-Hoc Fitting

### Warning Signs

1. **Multiple valid mappings**: Same observable could be B, L, or D
2. **Retroactive selection**: Mapping chosen after knowing the answer
3. **No falsification criterion**: Cannot specify what would prove claim wrong
4. **Vague boundaries**: "This is approximately B" without precision

### Prevention

1. Apply [Mapping Rules](../applications/physics/mapping-rules.md) BEFORE analysis
2. State falsification criterion BEFORE running test
3. Note alternatives explicitly
4. Distinguish "consistent with" from "derived from"

### Example: Good vs Bad

**Bad** (post-hoc):
> "The Standard Model gauge group SU(3)×SU(2)×U(1) emerges from BLD analysis."
> (Actually: We know SM exists, then show it fits BLD structure)

**Good** (honest):
> "BLD analysis shows SU(3)×SU(2)×U(1) is CONSISTENT with the constraints P2-P6. The specific gauge group is not uniquely determined by BLD alone — anomaly cancellation plus observed confinement selects it from a larger class."

---

## When to Update Status

| Event | Action |
|-------|--------|
| Test passes | Upgrade to VALIDATED |
| Test fails | Revise or abandon claim |
| New derivation found | Upgrade to DERIVED |
| Alternative ruled out | Upgrade from HYPOTHESIS |
| Alternative discovered | Note in document |
| Calculation completed | Upgrade MECHANISM to DERIVED (if values match) |

---

## The Honesty Checklist

Before publishing/updating physics documentation:

- [ ] Is every claim tagged with epistemic level?
- [ ] Are derivations actually derived (not assuming the answer)?
- [ ] Are reframings clearly marked as reframing?
- [ ] Are hypotheses accompanied by alternatives?
- [ ] Is there a "What BLD Does NOT Explain" section?
- [ ] Are falsification criteria specified where possible?
- [ ] Is the test status current?

---

## Examples of Honest Statements

### Strong Claim (Validated)
> "D×L scaling in circuits is **VALIDATED**: R² = 1.0 across 6 independent tests in the bld-circuits repository. Capacitance scales linearly with device count while threshold voltage remains invariant."

### Moderate Claim (Derived)
> "P9 (Triality → 3 generations) is **DERIVED** from division algebra structure. The claim is falsifiable: discovery of a 4th generation would disprove it. Current evidence (LEP neutrino counting, precision electroweak) supports the prediction."

### Honest Uncertainty (Mechanism)
> "P11 (Yukawa structure) is **MECHANISM-LEVEL**: S₃ breaking explains the qualitative hierarchy (3rd >> 2nd >> 1st), but specific mass values require calculating the S₃ breaking potential, which has not been done."

### Transparent Hypothesis (with alternatives)
> "P13 (Dark energy as de Sitter boundary) is a **HYPOTHESIS**. Alternative explanations include: quintessence (dynamical field), modified gravity, anthropic selection. No unique prediction distinguishes P13 from alternatives at present."

### Honest Reframing
> "The mapping of Maxwell's equations to BLD structure is **REFRAMING**: it organizes known EM physics in BLD language but does not derive or predict new phenomena. The gauge structure U(1) was known before BLD."

---

## Meta-Honesty

This document itself should be updated when:
- New categories of claims emerge
- Better classification criteria are found
- Community feedback suggests improvements

The goal is not to minimize claims, but to **accurately represent** what is known, derived, hypothesized, and unknown.

---

## See Also

- [Validation Roadmap](validation-roadmap.md) — Status of all claims
- [Mapping Rules](../applications/physics/mapping-rules.md) — How to assign B/L/D
- [Discovery Method](discovery-method.md) — The three questions
