---
status: DERIVED (form), OPEN (single-event)
layer: 2
depends_on:
  - ../lie-theory/killing-form.md
  - quantum-mechanics.md
  - ../foundations/irreducibility-proof.md
  - structural-observer-framework.md
used_by:
  - ../../meta/proof-status.md
  - theory-complete.md
---

# The Born Rule from BLD Alignment

**Status**: DERIVED — The FORM P = |ψ|² is derived from bidirectional alignment. Single-event interpretation remains OPEN.

---

## Quick Summary (D≈7 Human Traversal)

**Born rule derivation in 7 steps:**

1. **Measurement = B-partition** — measurement creates boundary separating outcomes
2. **Alignment determines probability** — P(outcome) ∝ alignment(state, outcome)
3. **Alignment is bidirectional** — observer queries state, state responds to observer
4. **Bidirectional = squared** — forward × backward = |amplitude|²
5. **Killing form = 2** — confirms the factor of 2 (see [Killing Form](../lie-theory/killing-form.md))
6. **Result: P = |ψ|²** — probability IS the squared amplitude
7. **Open: single events** — WHY this specific outcome is not derived

**What IS derived**: Form |ψ|², why squared, what measurement IS
**What is NOT derived**: Single-event probability, collapse mechanism

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

### Step 1: Measurement as B-Partition `[DERIVED]`

In BLD, measurement creates a **Boundary** — it partitions outcomes.

#### Formal Definition

**Before measurement**: State is a superposition
```
State ψ = α|0⟩ + β|1⟩

BLD representation:
  D = {|0⟩, |1⟩}           # basis states as dimensional locations
  L = {α, β}               # amplitudes as links (weights)
  B = ∅ (no partition)     # no boundary = all paths available
```

**Measurement apparatus**: Defines which partition
```
Measurement M in basis {|0⟩, |1⟩}

Creates B-partition:
  B = {|0⟩} | {|1⟩}        # boundary separates outcomes
```

**After measurement**: Single outcome
```
Result: |0⟩ (with probability |α|²)

BLD representation:
  D = {|0⟩}                # collapsed to single dimension
  L = {1}                  # amplitude normalized
  B = {|0⟩} | {|1⟩}        # boundary persists (outcome recorded)
```

#### Why Measurement MUST Create B

From [Irreducibility Proof](../foundations/irreducibility-proof.md):
- D and L are irreducible primitives
- Superposition = multiple D-paths weighted by L
- Measurement selects ONE D-path from the possibilities

**The selection requires a boundary**:
- Before: D-paths coexist (no B separating them)
- After: Single D-path (B separates chosen from unchosen)

Creating B is what "collapses" the state. No B → no selection → no measurement outcome.

#### What the Measurement Basis IS

The measurement basis defines WHICH B-partition is created:

| Measurement | B-Partition | What Gets Separated |
|-------------|-------------|---------------------|
| Position | {x=here} | {x≠here} | Location choices |
| Momentum | {p=this} | {p≠this} | Velocity choices |
| Spin-z | {↑} | {↓} | Spin orientation |
| Energy | {E₁} | {E₂} | ... | Energy levels |

**The apparatus determines B**. The state determines probabilities. The boundary separates what was superposed.

**Question**: Given that measurement creates B, what determines which outcome occurs?

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

## The BLD Derivation: Bidirectional Alignment `[PRIMARY]`

The bidirectional alignment argument is the BLD-native derivation. Gleason and frequency arguments are alternative perspectives that arrive at the same result.

### Why |ψ|² and NOT |ψ|, |ψ|³, or Something Else?

| Form | Problem | Why Ruled Out |
|------|---------|---------------|
| |ψ| | Not additive over orthogonal states | ||α|0⟩+|β|1⟩|| ≠ |α|+|β| |
| |ψ|³ | Depends on dimension | Violates unitarity at boundaries |
| |ψ|⁴ | Over-counts bidirectionality | Would be bidirectional-bidirectional |
| **|ψ|²** | **Correct** | **One forward + one backward = 2 factors** |

**The BLD Argument**:

From [Killing Form](../lie-theory/killing-form.md): observation is **bidirectional** (forward query + backward response = 2 links).

```
Observation = forward × backward = exactly 2 factors
            = ⟨outcome|ψ⟩ × ⟨ψ|outcome⟩
            = ⟨outcome|ψ⟩ × ⟨outcome|ψ⟩*
            = |⟨outcome|ψ⟩|²
```

The square is not arbitrary — it's the minimum complete observation (bidirectional).

### Argument 1: Bidirectional Alignment (Killing Form) `[PRIMARY]`

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

### Argument 2: Gleason's Theorem `[ALTERNATIVE PERSPECTIVE]`

**Gleason's theorem** (1957): Any probability measure on a Hilbert space of dimension ≥ 3 that:
1. Assigns non-negative probabilities
2. Sums to 1 over orthonormal bases
3. Is continuous (no discontinuous jumps)

must be of the form P(outcome) = ⟨outcome|ρ|outcome⟩ = |⟨outcome|ψ⟩|² for pure states.

**BLD connection**: If BLD structures form a Hilbert space (which they do via the Lie correspondence), and measurement obeys these conditions, then Born rule follows.

**Status**: This is a known result, not a new derivation. But it shows the Born rule is forced by the Hilbert space structure.

### Argument 3: Frequency from Structure `[ALTERNATIVE PERSPECTIVE]`

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

## The Measurement Problem: What BLD Does and Doesn't Solve

> **Honest acknowledgment**: The measurement problem is not solved by ANY interpretation of QM. BLD clarifies the STRUCTURE of measurement but not the METAPHYSICS.

### What BLD DOES Derive (5 things)

| # | Claim | How | Status |
|---|-------|-----|--------|
| 1 | Measurement is a B-partition | Outcomes are distinguished by boundary | **DERIVED** |
| 2 | Probabilities are |ψ|² | Bidirectional alignment (K=2) | **DERIVED** |
| 3 | The partition is irreducible | B cannot be expressed as L+D | **PROVEN** |
| 4 | Collapse is instantaneous | B-transitions have no intermediate | **DERIVED** |
| 5 | Outcomes are exclusive | B partitions, doesn't overlap | **DERIVED** |

### What BLD Does NOT Derive (2 things)

| # | Question | Status | Why |
|---|----------|--------|-----|
| 1 | **Why THIS outcome?** | OPEN | Given |↑⟩+|↓⟩, why do I see ↑ not ↓? |
| 2 | **Is collapse real?** | OPEN | Ontological status of the B-transition |

### Why This Is Honest

The measurement problem is OPEN in:
- Copenhagen (collapse postulated)
- Many-worlds (branch selection unexplained)
- Bohmian (hidden variables don't select)
- QBism (beliefs, not outcomes)

BLD's contribution is **structural clarity**:
- We know WHAT measurement is (B-partition)
- We know WHY probabilities are squared (bidirectional)
- We DON'T know WHY a specific outcome occurs

**This is a B (boundary) of the theory itself.** Acknowledging it is rigorous.

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

The Born rule has a BLD derivation via bidirectional alignment:

| Component | Status | Evidence |
|-----------|--------|----------|
| Measurement = B-partition | **DERIVED** | See Step 1: formal definition |
| Why squared (not linear, cubed) | **DERIVED** | Bidirectional observation = 2 factors |
| |ψ|² = forward × backward | **DERIVED** | Killing form structure |
| Hilbert space structure | **DERIVED** | From Lie correspondence |

**What BLD DOES derive**:
- Why probability involves |amplitude|² (bidirectional observation)
- What measurement IS (B-partition creation)
- Why Hilbert space (from Lie algebra unitary representations)

**What BLD does NOT derive**:
- Single-event probability (why THIS outcome vs frequency statistics)
- Collapse mechanism (why B selects this particular outcome)

**Status**: The **form** P = |ψ|² is **DERIVED** from bidirectional alignment. The **interpretation** of single events remains OPEN.

---

## References

- [Killing Form](../lie-theory/killing-form.md) — Bidirectional observation cost
- [Quantum Mechanics](quantum-mechanics.md) — D-L interpretation
- [Schrödinger Derivation](schrodinger-derivation.md) — Attempt at dynamics

### External References

- Gleason, A. M. (1957). "Measures on the Closed Subspaces of a Hilbert Space"
- Zurek, W. H. (2005). "Probabilities from Entanglement, Born's Rule from Envariance"
- Saunders, S. et al. (2010). "Many Worlds? Everett, Quantum Theory, and Reality"
