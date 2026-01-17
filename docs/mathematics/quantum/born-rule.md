---
status: SPECULATIVE
depends_on:
  - ../lie-theory/killing-form.md
  - quantum-mechanics.md
  - ../foundations/irreducibility-proof.md
---

# The Born Rule from BLD Alignment

An attempt to derive P = |ψ|² from BLD alignment principles.

---

## The Goal

Derive the Born rule:

```
P(outcome) = |⟨outcome|ψ⟩|²
```

from BLD principles alone, without assuming quantum mechanics.

---

## The Problem

The Born rule is notoriously difficult to derive. Proposed approaches include:
- **Postulate**: Just assume it (standard textbook)
- **Many-worlds**: Derive from branch counting (controversial)
- **Bayesian**: Derive from rational betting (circular?)
- **Gleason's theorem**: Derive from probability measure requirements (assumes Hilbert space)

Can BLD offer a new perspective?

---

## The BLD Approach

### Step 1: Measurement as B-Partition

In BLD, measurement creates a **Boundary** — it partitions outcomes.

```
B measurement: outcome_1 | outcome_2 | ... | outcome_n
  # Partitions the state space into discrete outcomes
  # Before measurement: superposition (all D's)
  # After measurement: collapsed (single outcome)
```

**Question**: What determines which outcome occurs?

### Step 2: Alignment Cost

BLD's core principle: **Cost measures structural misalignment.**

```
cost(S₁, S₂) = how much S₁ and S₂ differ structurally
```

**Hypothesis**: Probability is related to alignment.

```
P(outcome) ∝ alignment(state, outcome)
```

The better the state aligns with an outcome, the more likely that outcome.

### Step 3: What is Alignment?

For structures S₁ and S₂:

```
alignment(S₁, S₂) = ⟨S₁|S₂⟩ (inner product)
```

The inner product measures how much two structures "overlap."

**But wait**: ⟨ψ|outcome⟩ can be complex. Probability must be real and non-negative.

### Step 4: The Squared Amplitude

To get a real, non-negative number from a complex amplitude:

```
|⟨outcome|ψ⟩|² = ⟨outcome|ψ⟩ · ⟨outcome|ψ⟩* = real, non-negative
```

**Why squared?** This is the key question.

---

## Three Possible Arguments

### Argument 1: Bidirectional Alignment (Killing Form)

**Observation**: The Killing form involves bidirectional traversal.

```
B(X, Y) = tr(ad_X ∘ ad_Y)
        = "apply X, then Y, trace what happens"
        = bidirectional traversal
```

**Hypothesis**: Probability requires bidirectional alignment.

```
Forward:  ⟨outcome|ψ⟩     — "how much does ψ project onto outcome?"
Backward: ⟨ψ|outcome⟩     — "how much does outcome project onto ψ?"

Bidirectional: ⟨outcome|ψ⟩ · ⟨ψ|outcome⟩ = |⟨outcome|ψ⟩|²
```

**Interpretation**: Measurement is an interaction. The state affects the detector AND the detector affects the state. Both directions matter.

```
P = forward × backward = amplitude × amplitude* = |amplitude|²
```

**Status**: Plausible but not rigorous.

### Argument 2: Gleason's Theorem (Mathematical)

**Gleason's theorem** (1957): Any probability measure on a Hilbert space of dimension ≥ 3 that:
1. Assigns non-negative probabilities
2. Sums to 1 over orthonormal bases
3. Is continuous (no discontinuous jumps)

must be of the form P(outcome) = ⟨outcome|ρ|outcome⟩ = |⟨outcome|ψ⟩|² for pure states.

**BLD connection**: If BLD structures form a Hilbert space (which they do via the Lie correspondence), and measurement obeys these conditions, then Born rule follows.

**Status**: This is a known result, not a new derivation. But it shows the Born rule is forced by the Hilbert space structure.

### Argument 3: Frequency from Structure (Experimental)

**Observation**: In repeated experiments, frequencies converge to |ψ|².

**BLD interpretation**: Structure determines statistics.

```
If a state ψ has amplitude α for outcome X:
  - Running the experiment once: unpredictable (single outcome)
  - Running N times: frequency → |α|² as N → ∞

Why? The structure of ψ (its D×L configuration) determines
the statistical pattern over many traversals.
```

**Analogy**: A biased coin has structure (weight distribution) that determines frequencies, even if each flip is random.

**Status**: This explains "why frequencies match |ψ|²" but doesn't derive the rule from first principles.

---

## The L-Cost Interpretation

### Measurement Has L-Cost

From [killing-form.md](../lie-theory/killing-form.md):

```
Observation requires:
- Forward link: query from observer to observed
- Backward link: response from observed to observer

Minimum L-cost = 2 (Killing form coefficient)
```

**Interpretation**: Measurement involves bidirectional L.

### Probability as L-Overlap

**Hypothesis**: P = amount of L shared between state and outcome.

```
L(ψ → outcome) = forward projection = ⟨outcome|ψ⟩
L(outcome → ψ) = backward projection = ⟨ψ|outcome⟩ = ⟨outcome|ψ⟩*

Total L-overlap = forward × backward = |⟨outcome|ψ⟩|²
```

**Analogy**: Two structures share more L when:
1. State projects strongly onto outcome (forward)
2. Outcome projects strongly onto state (backward)

The product captures "how much do they mutually align?"

---

## Connection to Uncertainty

### Uncertainty and Probability

The uncertainty principle and Born rule are related:

```
Δx · Δp ≥ ℏ/2  (uncertainty)
P(x) = |ψ(x)|²  (Born rule for position measurement)

⟨Δx²⟩ = ∫ (x - ⟨x⟩)² |ψ(x)|² dx
```

Both involve:
- The factor 2 (Killing form)
- Squared amplitudes

**Hypothesis**: Both arise from bidirectional L-cost.

```
Uncertainty: minimum L for observation = 2
Born rule: probability = bidirectional alignment = squared amplitude
```

The "2" in Δx·Δp ≥ ℏ/2 and the "square" in |ψ|² may have the same origin.

---

## Partial Success

**What the alignment interpretation gives**:
- Probability ∝ alignment (intuitive)
- Squared amplitude = bidirectional alignment (from Killing form)
- Gleason's theorem forces P = |amplitude|² (mathematical necessity)

**What it does NOT give**:
- A derivation without assuming Hilbert space structure
- An explanation of single-event probability (frequencies only)
- Why collapse happens (just what the probabilities are)

**Status**: The Born rule is **consistent with** BLD alignment principles, but not **uniquely derived** from them.

---

## Comparison with Other Approaches

| Approach | Strength | Weakness |
|----------|----------|----------|
| **Postulate** | Simple | Not explanatory |
| **Many-worlds** | No collapse | Measure problem |
| **Bayesian** | Rational | Circular? |
| **Gleason** | Rigorous | Assumes Hilbert space |
| **BLD (this)** | Structural interpretation | Not a full derivation |

BLD adds interpretive value (bidirectional alignment) but doesn't close the gap.

---

## Open Questions

### 1. Why Hilbert Space?

The Born rule follows from Hilbert space structure (Gleason's theorem). But why does nature use Hilbert spaces?

**BLD hint**: Lie groups act on Hilbert spaces via unitary representations. If BLD = Lie theory, Hilbert space may be forced.

### 2. Single Events vs. Frequencies

The Born rule gives probabilities. But what determines a single measurement outcome?

**BLD interpretation**: A single measurement creates a B (partition). Which partition occurs may be fundamentally random within the structural constraints.

### 3. Collapse Mechanism

Why does measurement collapse the state?

**BLD interpretation**: Creating B (measurement partition) forces D to "choose" one side. But WHY this specific outcome is not explained.

---

## Conclusion

The Born rule is **consistent with** BLD principles:
- Probability = alignment = inner product
- Squared amplitude = bidirectional alignment (Killing form pattern)
- Gleason's theorem forces P = |ψ|² given Hilbert space

But it is not **derived from** BLD alone. We would need to:
1. Derive Hilbert space from BLD (not done)
2. Derive single-event probabilities (not done)
3. Explain collapse (not done)

**Status**: Suggestive interpretation, not a proof. The Born rule remains one of the fundamental postulates that BLD interprets but does not derive.

---

## References

- [Killing Form](../lie-theory/killing-form.md) — Bidirectional observation cost
- [Quantum Mechanics](quantum-mechanics.md) — D-L interpretation
- [Schrödinger Derivation](schrodinger-derivation.md) — Attempt at dynamics

### External References

- Gleason, A. M. (1957). "Measures on the Closed Subspaces of a Hilbert Space"
- Zurek, W. H. (2005). "Probabilities from Entanglement, Born's Rule from Envariance"
- Saunders, S. et al. (2010). "Many Worlds? Everett, Quantum Theory, and Reality"
