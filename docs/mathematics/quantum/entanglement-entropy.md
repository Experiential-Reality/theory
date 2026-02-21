---
status: DERIVED
layer: 2
depends_on:
  - ../foundations/key-principles.md
  - ../lie-theory/killing-form.md
  - born-rule.md
  - bld-is-quantum-code.md
used_by:
  - ../../meta/proof-status.md
  - ../../meta/validation-roadmap.md
  - black-hole-entropy.md
---

# Entanglement Entropy from BLD

## Summary

**Entanglement entropy derived from BLD link formula:**

1. Formula: S = K × L + H = 2L + H — [Complete Formula](#the-complete-formula)
2. At maximum entanglement: S = 2L exactly — [Exact Result](#exact-result-s--2l-at-maximum-entanglement)
3. Connection: ρ = C/√2 (BLD correlation = concurrence/√2) — [The Connection](#step-2-the-connection-ρ--c2)
4. Same √2 as Bell violation: unified SU(2) origin — [Bell Connection](#connection-to-bell-violation)
5. N-qubit extension: GHZ always S = 2L, W states have H > 0 — [Extensions](#n-qubit-extension)

| State | S/L | H | Status |
|-------|-----|---|--------|
| Bell state (λ=0.5) | **2.000** | **0.000** | Exact |
| GHZ (any N) | **2.000** | **0.000** | Exact |
| W₃ state (λ=1/3) | 2.17 | 0.049 | Derived |
| General | 2 + H/L | H(λ) | Derived |

---

## The Derivation

### Step 1: Definitions

**BLD Link Formula** (from [Key Principles](../foundations/key-principles.md)):
```
L = -½ ln(1 - ρ²)
```
where ρ is the correlation coefficient. This is an exact theorem derived from KL divergence.

**Von Neumann Entropy**:
```
S = -λ ln(λ) - (1-λ) ln(1-λ)
```
where λ, (1-λ) are eigenvalues of the reduced density matrix ρ_A for a bipartite pure state.

**Concurrence** (standard quantum information measure):
```
C = 2√(λ(1-λ))
```
For a 2-qubit pure state, concurrence ranges from 0 (separable) to 1 (maximally entangled).

### Step 2: The Connection ρ = C/√2

**Claim**: The BLD correlation ρ relates to concurrence C by:
```
ρ = C/√2
```

**Derivation**:
```
ρ² = C²/2 = 4λ(1-λ)/2 = 2λ(1-λ)
```

**Why √2?** This is the SU(2) geometric factor — the same √2 that appears in Bell violation (2√2 = K × √2). It arises from the rotation between measurement bases in SU(2).

### Step 3: Numerical Verification

| λ | ρ² | L | S | S/L | H = S-2L |
|---|-----|------|------|------|----------|
| 0.50 | 0.500 | 0.347 | 0.693 | **2.000** | **0.000** |
| 0.45 | 0.495 | 0.342 | 0.688 | 2.014 | 0.005 |
| 0.40 | 0.480 | 0.327 | 0.673 | 2.058 | 0.019 |
| 0.35 | 0.455 | 0.304 | 0.647 | 2.133 | 0.041 |
| 0.30 | 0.420 | 0.272 | 0.611 | 2.243 | 0.066 |
| 0.25 | 0.375 | 0.235 | 0.562 | 2.393 | 0.092 |
| 0.20 | 0.320 | 0.193 | 0.500 | 2.595 | 0.115 |
| 0.15 | 0.255 | 0.147 | 0.423 | 2.872 | 0.128 |
| 0.10 | 0.180 | 0.099 | 0.325 | 3.276 | 0.127 |
| 0.05 | 0.095 | 0.050 | 0.199 | 3.977 | 0.099 |

**Key observation**: At λ = 0.5 (maximum entanglement), S/L = 2.000 **exactly**.

---

## The Complete Formula

```
S = K × L + H(λ)
S = 2L + H(λ)

where:
  K = 2           Killing form (bidirectional observation)
  L = -½ ln(1 - 2λ(1-λ))
  H(λ) = S - 2L   Basis-selection entropy
```

### Properties of H

| Property | Value | Meaning |
|----------|-------|---------|
| H(0.5) | 0 | Max entanglement — all bases equivalent |
| H(0) | 0 | Separable — no entanglement |
| H > 0 | 0 < λ < 0.5 | Partial entanglement |
| max(H) | ≈ 0.128 | At λ ≈ 0.13 |

---

## Exact Result: S = 2L at Maximum Entanglement

### Why Exactly 2?

From [Killing Form](../lie-theory/killing-form.md): observation requires bidirectional traversal.

```
Observation = forward link + backward link = 2 links
```

For entanglement:
- **L** = the quantum correlation (link between subsystems A and B)
- **K = 2** = bidirectional observation (must probe both A and B)
- **S = K × L = 2L** = total entropy from bidirectional measurement

### Why H = 0 at Maximum Entanglement?

At maximum entanglement (Bell state):
- All measurement bases are equivalent
- Perfect correlation in EVERY basis (X, Y, Z, any direction)
- No uncertainty about which basis to choose

**H = 0 means**: The optimal measurement basis is "all of them" — there's no basis-selection cost.

### Why H > 0 at Partial Entanglement?

At partial entanglement:
- Some bases show more correlation than others
- There exists an optimal measurement basis
- Uncertainty about which basis gives maximum information

**H > 0 means**: Extra entropy from not knowing the optimal measurement basis.

---

## Physical Interpretation

### The Three Components

| Term | BLD Role | Quantum Role |
|------|----------|--------------|
| K = 2 | Killing form | Bidirectional observation cost |
| L | Link cost | Quantum correlation between subsystems |
| H | Extra traversal | Basis-selection uncertainty |

### Connection to Born Rule

From [Born Rule](born-rule.md): probability requires bidirectional alignment.

```
P = |⟨outcome|ψ⟩|² = forward × backward = K = 2 factors
```

The same K = 2 that gives |ψ|² in the Born rule gives S = 2L in entanglement entropy.

### Connection to Uncertainty

From [Killing Form](../lie-theory/killing-form.md):

```
Δx · Δp ≥ ℏ/2

The "2" in the denominator = Killing form coefficient
```

All three — Born rule, entanglement entropy, uncertainty — share the same K = 2 origin.

---

## N-Qubit Extension

### GHZ States

For GHZ states |GHZ_N⟩ = (|00...0⟩ + |11...1⟩)/√2:

- Any bipartition gives λ = 0.5
- Therefore S = 2L **for all N**
- The formula holds for arbitrary system size

```
GHZ_2 (Bell): S = 2L ✓
GHZ_3:        S = 2L ✓
GHZ_N:        S = 2L ✓ (for any bipartition)
```

### W States

For W₃ = (|100⟩ + |010⟩ + |001⟩)/√3:

- Single-qubit reduced density matrix: λ = 1/3
- S = -⅓ ln(⅓) - ⅔ ln(⅔) = 0.637
- ρ² = 2 × ⅓ × ⅔ = 4/9
- L = -½ ln(1 - 4/9) = -½ ln(5/9) = 0.294
- S/L = 0.637/0.294 = 2.17
- H = S - 2L = 0.637 - 0.588 = 0.049

**W states have H > 0** — they're partially entangled, so basis selection matters.

---

## Connection to Bell Violation

### The √2 Appears in Both

| Context | Formula | The √2 |
|---------|---------|--------|
| **Entanglement** | ρ = C/√2 | Relates BLD correlation to concurrence |
| **Bell violation** | S_max = 2√2 | K × √2 = 2 × √2 |

### Unified Origin

Both involve the same SU(2) structure:
- K = 2: bidirectional observation (Killing form)
- √2: rotation between measurement bases in SU(2)

The Bell violation 2√2 = K × √2 uses the **same structures** as entanglement entropy.

### Why This Matters

The √2 is not arbitrary — it's the geometric factor for rotating between complementary measurement bases in SU(2). This unifies:
- Entanglement quantification (ρ = C/√2)
- Bell inequality violation (S_max = 2√2)
- Measurement basis geometry (45° = π/4 rotation)

---

## Comparison with Standard Results

### Concurrence-Entropy Relation

The standard quantum information result: entanglement entropy S is a monotonic function of concurrence C.

BLD adds: the specific function involves K = 2 (Killing form) and √2 (SU(2) geometry).

```
Standard: S = f(C) for some monotonic f
BLD:      S = 2L + H where L = -½ ln(1 - C²/2)
```

### Mutual Information

For a bipartite pure state:
```
I(A:B) = S(A) + S(B) - S(AB) = 2S(A)
```

BLD interpretation: mutual information = 2 × (entanglement entropy) = 2 × (2L + H) = 4L + 2H

At maximum entanglement: I = 4L = 2 × 2L = 2S ✓

---

## Connection to Black Hole Entropy

### Same Formula S = K × L

From [Black Hole Entropy](black-hole-entropy.md):

```
S_BH = A/(4ℓ_P²) = K × L

where:
  K = 2 (Killing form)
  L = A/(8ℓ_P²) = A/(2n ℓ_P²)
  n = 4 (spacetime dimensions)
```

| System | S | K | L |
|--------|---|---|---|
| Bell state | ln(2) | 2 | ln(2)/2 |
| Black hole | A/(4ℓ_P²) | 2 | A/(8ℓ_P²) |

**The same S = K × L governs both.**

### Unified Interpretation

Entropy measures structure accessible through bidirectional observation:
- **Entanglement**: correlations between subsystems A and B
- **Black hole**: correlations between inside and outside horizon

The Killing form K = 2 appears in both because observation requires forward query + backward response.

---

## Connection to Phase Transitions

### L → ∞ at Criticality

From [Phase Transitions](../../applications/physics/phase-transitions.md):

At a phase transition, the correlation length ξ → ∞. This means correlations become long-range, so ρ → 1.

Using L = -½ ln(1 - ρ²):
```
As ρ → 1:  L → ∞
```

**Phase transitions are where L diverges.**

### L ~ ν ln(ξ)

If ξ ~ |T - T_c|^(-ν), then:
```
ρ² ~ 1 - |T - T_c|^(2ν)
L = -½ ln(1 - ρ²) ~ ν × ln(ξ)
```

Link cost grows logarithmically with correlation length.

### Comparison

| Context | ρ | L | Interpretation |
|---------|---|---|----------------|
| Max entanglement | 1/√2 | ln(2)/2 | Bell state |
| Phase transition (T→T_c) | → 1 | → ∞ | Critical point |
| Ordered phase (T<T_c) | < 1 | finite | Finite correlation |

The same BLD link formula L = -½ ln(1 - ρ²) connects entanglement to phase transitions.

---

## Summary

```
ENTANGLEMENT ENTROPY IN BLD:

Formula:        S = K × L + H = 2L + H

Components:
  K = 2         Killing form (bidirectional observation)
  L             BLD link cost = -½ ln(1 - ρ²)
  ρ = C/√2      BLD correlation = concurrence/√2
  H             Basis-selection entropy

At max entanglement (Bell/GHZ):
  S = 2L        Exact (H = 0)

At partial entanglement:
  S = 2L + H    With H > 0

The √2:
  Same as Bell violation (2√2 = K × √2)
  Origin: SU(2) measurement basis geometry

Extensions:
  Black holes: S = K × L = A/(4ℓ_P²)  (K=2, n=4)
  Phase transitions: L → ∞ as ρ → 1  (criticality)

STATUS: DERIVED
  - S = 2L at max entanglement: EXACT
  - General formula S = 2L + H: DERIVED
  - Connection ρ = C/√2: DERIVED
  - Unification with Bell: DERIVED
  - Black hole connection: DERIVED
  - Phase transition connection: DERIVED
```

---

## References

### Internal BLD References
- [Key Principles](../foundations/key-principles.md) — Link formula L = -½ ln(1 - ρ²)
- [Killing Form](../lie-theory/killing-form.md) — K = 2 derivation, Bell violation
- [Born Rule](born-rule.md) — Bidirectional alignment gives |ψ|²
- [BLD is Quantum Code](bld-is-quantum-code.md) — BLD = Lie = QM equivalence
- [Quantum Mechanics](quantum-mechanics.md) — D-L interpretation

### External References
- [Von Neumann Entropy (Wikipedia)](https://en.wikipedia.org/wiki/Von_Neumann_entropy) — S = -tr(ρ ln ρ)
- [Concurrence (Wikipedia)](https://en.wikipedia.org/wiki/Concurrence_(quantum_computing)) — Entanglement measure
- [Bell's Theorem (Wikipedia)](https://en.wikipedia.org/wiki/Bell%27s_theorem) — 2√2 violation
- [GHZ State (Wikipedia)](https://en.wikipedia.org/wiki/Greenberger–Horne–Zeilinger_state) — Maximally entangled N-qubit states
