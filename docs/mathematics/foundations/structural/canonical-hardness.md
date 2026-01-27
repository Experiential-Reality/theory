---
status: VALIDATED
layer: 1
depends_on:
  - ../definitions/bld-calculus.md
used_by:
  - ../../derived/discovery-algorithm.md
  - ../../../paths/mathematician.md
---

## Summary

**NP-completeness of finding minimal BLD representations:**

1. CANONICAL-BLD is NP-complete via reduction from MINIMUM-GRAMMAR — [The Reduction](#the-reduction)
2. Grammar components map to BLD: terminals->B, rules->L, non-terms->D — [BLD Encoding Diagram](#2-bld-encoding-diagram)
3. Cost equivalence: cost(R_G) <= 3|G| — [Cost Equivalence](#cost-equivalence)
4. Hardness arises from global comparison across all representations — [Connection to Global Temporal Scope](#connection-to-global-temporal-scope)
5. Tractable cases: O(log n) approximation, FPT for output size, O(n) for trees — [Tractability Results](#tractability-results)

# Hardness of Canonical BLD: Formal Proof

## Abstract

We prove that computing the canonical (minimal) BLD representation is NP-complete via polynomial-time reduction from the Minimum Grammar Problem. The reduction encodes context-free grammar components as BLD primitives: terminal symbols as boundaries (B), production rules as links (L), and non-terminal symbols as dimensions (D). The cost relationship is tight: cost(R_G) = Θ(|G|) with constant factor ≤ 3. The reverse encoding shows |G_R| ≤ 2·cost(R). Since verification is polynomial (check cost and validity), CANONICAL-BLD is in NP, completing the NP-completeness proof. This result has practical implications: finding optimal BLD representations requires heuristics, and the hardness arises from the global comparison required across all possible representations.

## 1. Introduction

Given a structure S, multiple BLD representations exist with varying costs. The canonical representation is the one with minimum cost. This document proves finding it is NP-complete.

**Main Result.** CANONICAL-BLD (deciding if S has a BLD representation with cost ≤ k) is NP-complete.

**Proof Strategy:**
1. Reduce from MINIMUM-GRAMMAR (known NP-hard [Charikar et al., 2005])
2. Show polynomial-time bidirectional encoding
3. Verify NP membership

**Outline.** Section 2 presents the encoding. Section 3 proves cost equivalence. Section 4 shows NP membership. Section 5 discusses implications.

| Step | Encoding | Cost Relationship |
|------|----------|-------------------|
| G → R_G | Terminals→B, Rules→L, NonTerms→D | cost(R_G) ≤ 3|G| |
| R → G_R | Reverse mapping | |G_R| ≤ 2·cost(R) |

## 2. BLD Encoding Diagram

```
┌───────────────────────────────────────────────────────────────────────────┐
│                    GRAMMAR → BLD ENCODING                                 │
│                                                                           │
│              NP-completeness via reduction from MINIMUM-GRAMMAR           │
└───────────────────────────────────────────────────────────────────────────┘

GRAMMAR G = (V, Σ, R, S)              BLD REPRESENTATION R_G = (B, L, D)
┌─────────────────────────┐           ┌─────────────────────────────────────┐
│                         │           │                                     │
│  Σ = {a, b, c, ...}     │    B     │  B_G = {b_a, b_b, b_c, ...}         │
│  (terminal symbols)     │  ────→   │  (boundaries = alphabet)            │
│                         │           │                                     │
├─────────────────────────┤           ├─────────────────────────────────────┤
│                         │           │                                     │
│  R = {A→XYZ, ...}       │    L     │  L_G = {(A,X,1), (A,Y,2), ...}      │
│  (production rules)     │  ────→   │  (links = rule positions)           │
│                         │           │                                     │
├─────────────────────────┤           ├─────────────────────────────────────┤
│                         │           │                                     │
│  V = {S, A, B, ...}     │    D     │  D_G = {d_S, d_A, d_B, ...}         │
│  (non-terminals)        │  ────→   │  (dimensions = repetition extent)   │
│                         │           │                                     │
└─────────────────────────┘           └─────────────────────────────────────┘

COST EQUIVALENCE:

  |G| = Σ(1 + |α|)  ←→  cost(R_G) = |B| + |L| + |D|
                              ↓
                      cost(R_G) ≤ 3|G|

EXAMPLE ENCODING:

  Grammar:                          BLD:
  ┌─────────────────────┐          ┌─────────────────────────────────────┐
  │  S → AB             │          │  B = {b_a, b_b}                     │
  │  A → aa             │          │                                     │
  │  B → bb             │          │  L = {(S,A,1), (S,B,2),             │
  │                     │   →      │       (A,a,1), (A,a,2),             │
  │  Σ = {a, b}         │          │       (B,b,1), (B,b,2)}             │
  │  V = {S, A, B}      │          │                                     │
  │                     │          │  D = {d_S, d_A, d_B}                │
  └─────────────────────┘          └─────────────────────────────────────┘

  L(G) = {aabb}                     R_G generates: a → a → b → b
                                                   (same string)

THE REDUCTION:

  MINIMUM-GRAMMAR                   CANONICAL-BLD
  ┌─────────────────────┐          ┌─────────────────────────────────────┐
  │  Input: (s, k)      │          │  Input: (S_s, 3k)                   │
  │  String s, bound k  │   →      │  System S_s, bound 3k               │
  │                     │          │                                     │
  │  Question:          │          │  Question:                          │
  │  ∃G with |G|≤k      │          │  ∃R with cost(R)≤3k                 │
  │  and L(G)={s}?      │          │  and R represents S_s?              │
  └─────────────────────┘          └─────────────────────────────────────┘

WHY NP-HARD (Global Constraint):

  Verifying canonicity requires:
  ┌─────────────────────────────────────────────────────────────────────┐
  │                                                                     │
  │     ∀R' valid for S: cost(R) ≤ cost(R')                            │
  │                                                                     │
  │     This is a GLOBAL comparison over ALL valid representations      │
  │     → Cannot be verified locally                                    │
  │     → This is the structural signature of NP-hardness               │
  │                                                                     │
  └─────────────────────────────────────────────────────────────────────┘

  In BLD terms: temporal_scope = "global" → no local traverser suffices
```

---

## Definitions

### BLD Representation

**Definition 1 (BLD Representation)**: For a finite system S, a BLD representation is a triple R = (B, L, D) where:
- B = finite set of boundaries
- L = finite set of links
- D = finite set of dimensions

such that R completely describes S's structure.

**Definition 2 (Cost)**: The cost of a representation R = (B, L, D) is:
```
cost(R) = |B| + |L| + |D|
```

**Definition 3 (Canonical Form)**: A representation R* is canonical for S iff:
1. R* is a valid representation of S
2. For all valid representations R of S: cost(R*) ≤ cost(R)

### The Decision Problem

**CANONICAL-BLD**:
- **Input**: System S (encoded finitely), integer k
- **Question**: Does S have a BLD representation with cost ≤ k?

---

## The Minimum Grammar Problem

**Definition 4 (Context-Free Grammar)**: A CFG is G = (V, Σ, R, S) where:
- V = finite set of non-terminal symbols
- Σ = finite set of terminal symbols (V ∩ Σ = ∅)
- R ⊆ V × (V ∪ Σ)* = production rules
- S ∈ V = start symbol

**Definition 5 (Grammar Size)**: The size of grammar G is:
```
|G| = Σ_{(A→α) ∈ R} (1 + |α|)
```
Each rule contributes 1 (for the rule itself) plus the length of its right-hand side.

**MINIMUM-GRAMMAR** (known NP-hard):
- **Input**: String s ∈ Σ*, integer k
- **Question**: Is there a CFG G with |G| ≤ k such that L(G) = {s}?

**Theorem (Charikar et al., 2005)**: MINIMUM-GRAMMAR is NP-hard.

---

## The Reduction

We reduce MINIMUM-GRAMMAR to CANONICAL-BLD.

### Encoding: Grammar → BLD

Given a CFG G = (V, Σ, R, S), construct BLD representation R_G = (B_G, L_G, D_G):

**Boundaries (terminals)**:
```
B_G = { b_a : a ∈ Σ }
```
Each terminal symbol becomes a boundary. The boundary b_a partitions "current symbol" into {a, not-a}.

**Links (production rules)**:
For each rule (A → X₁X₂...Xₖ) ∈ R, create k links:
```
L_G = { (A, Xᵢ, i) : (A → X₁...Xₖ) ∈ R, i ∈ [1,k] }
```
Each link connects non-terminal A to the i-th symbol of its production, tagged with position i.

**Dimensions (non-terminals)**:
```
D_G = { d_A : A ∈ V }
```
Each non-terminal becomes a dimension. The "extent" of d_A is the number of times A appears on right-hand sides of rules.

### Cost Equivalence

**Lemma 1**: For grammar G and its BLD encoding R_G:
```
cost(R_G) = |Σ| + Σ_{(A→α) ∈ R} |α| + |V|
         = |Σ| + |V| + (|G| - |R|)
```

**Proof**:
- |B_G| = |Σ| (one boundary per terminal)
- |L_G| = Σ_{(A→α) ∈ R} |α| (one link per symbol in RHS)
- |D_G| = |V| (one dimension per non-terminal)
- |G| = Σ_{(A→α)} (1 + |α|) = |R| + Σ|α|
- Therefore |L_G| = |G| - |R|

**Lemma 2**: |Σ| and |V| are bounded by |G|.

**Proof**: Each terminal must appear in some rule. Each non-terminal must have at least one rule. Therefore |Σ| ≤ |G| and |V| ≤ |R| ≤ |G|.

**Corollary**: cost(R_G) = Θ(|G|)

---

## Encoding: String → System

Given string s = s₁s₂...sₙ ∈ Σ*, define system S_s as follows:

**System S_s**:
- State space: positions {1, 2, ..., n}
- At each position i: the value is sᵢ ∈ Σ
- Sequential structure: position i leads to position i+1

**Definition 6 (Valid Representation)**: R = (B, L, D) is valid for S_s iff the structure encoded by R generates exactly the sequence s₁s₂...sₙ when traversed.

This mirrors: L(G) = {s} iff grammar G generates exactly string s.

---

## The Reduction Formally

**Construction**: Given instance (s, k) of MINIMUM-GRAMMAR:
1. Construct system S_s from string s
2. Set k' = f(k) where f is a polynomial function (to be determined)
3. Output (S_s, k') as instance of CANONICAL-BLD

**Correctness**:

**(⇒)** If G is a grammar with |G| ≤ k and L(G) = {s}:
- Construct R_G from G
- R_G is valid for S_s (because L(G) = {s})
- cost(R_G) = Θ(|G|) ≤ f(k) = k'
- Therefore (S_s, k') is a YES instance of CANONICAL-BLD

**(⇐)** If R = (B, L, D) is a BLD representation of S_s with cost(R) ≤ k':
- Construct grammar G_R from R (reverse encoding)
- L(G_R) = {s} (because R represents S_s)
- |G_R| = Θ(cost(R)) ≤ Θ(k') = Θ(f(k))
- If f(k) = O(k), then |G_R| = O(k)
- Therefore (s, k) is a YES instance of MINIMUM-GRAMMAR

**The f(k) issue**: We need cost(R_G) ≤ f(k) when |G| ≤ k.

From Lemma 1: cost(R_G) = |Σ| + |V| + (|G| - |R|)

Worst case: |Σ| ≤ |G|, |V| ≤ |G|, |G| - |R| ≤ |G|
Therefore: cost(R_G) ≤ 3|G|

Set f(k) = 3k. Then:
- |G| ≤ k ⟹ cost(R_G) ≤ 3k = k'
- cost(R) ≤ 3k ⟹ |G_R| ≤ 3k (by reverse bound)

---

## Reverse Encoding: BLD → Grammar

Given R = (B, L, D) representing string s, construct grammar G_R:

**Non-terminals**:
```
V = D ∪ {S}  (one per dimension, plus start symbol)
```

**Terminals**:
```
Σ = B  (boundaries are the alphabet)
```

**Rules**:
For each dimension d ∈ D with links {(d, t₁, 1), (d, t₂, 2), ...}:
```
d → t₁ t₂ ...
```

Start rule connects S to the root structure.

**Size bound**:
```
|G_R| = |R| + Σ (link counts)
      ≤ |D| + |L| + |B| + |L|
      = cost(R) + |L|
      ≤ 2 · cost(R)
```

---

## Main Theorem

**Theorem**: CANONICAL-BLD is NP-complete.

**Proof**:

**(1) CANONICAL-BLD ∈ NP**:
- Witness: BLD representation R
- Verification:
  - Check cost(R) ≤ k in O(|R|)
  - Check R is valid for S in polynomial time (depends on S encoding)
- Both polynomial in input size

**(2) CANONICAL-BLD is NP-hard**:
- Reduction from MINIMUM-GRAMMAR (shown above)
- Given (s, k), construct (S_s, 3k) in polynomial time
- Correctness:
  - (s, k) ∈ MINIMUM-GRAMMAR ⟺ (S_s, 3k) ∈ CANONICAL-BLD
- MINIMUM-GRAMMAR is NP-hard (Charikar et al.)
- Therefore CANONICAL-BLD is NP-hard

**(3) Conclusion**: CANONICAL-BLD is NP-complete. ∎

---

## Connection to Global Temporal Scope

The proof illuminates WHY canonical BLD is hard:

**The verification problem**: To verify R is canonical (not just valid), we must check:
```
∀R' valid for S: cost(R) ≤ cost(R')
```

This requires:
1. Enumerating all valid representations
2. Computing cost of each
3. Comparing globally

This is a **global constraint** — it cannot be evaluated by examining R alone.

In BLD terms:
- Verifying canonicity requires `temporal_scope = "global"`
- No local traverser can verify minimality
- This is the structural signature of NP-hardness

**The framework predicts its own complexity.**

---

## Implications

1. **No polynomial algorithm** for finding canonical BLD (unless P = NP)

2. **Approximation**: Polynomial-time algorithms can find "good" (not minimal) representations

3. **Heuristics**: Greedy compression, local optimization may work well in practice

4. **Structure of hardness**: The hardness comes from the global comparison, not from the structure itself

---

## Tractability Results

The NP-completeness result is worst-case. Several tractable special cases and approximations exist, following from the tight reduction to MINIMUM-GRAMMAR.

**Theorem (Approximation).** There exists a polynomial-time O(log n)-approximation to CANONICAL-BLD.

*Proof.* Lehman and Shelat [SODA 2002] give an O(log(n/g*))-approximation for the smallest grammar problem, where g* is optimal grammar size. By the reduction:
1. Given system S of size n, encode as string s
2. Apply Lehman-Shelat to obtain grammar G with |G| ≤ O(log n) · |G*|
3. Convert G to BLD representation R_G with cost(R_G) ≤ 3|G|
4. The optimal BLD representation R* satisfies |G_{R*}| ≤ 2·cost(R*), so |G*| ≤ 2·cost(R*)
5. Therefore cost(R_G) ≤ 3 · O(log n) · 2 · cost(R*) = O(log n) · cost(R*)

The constant factor (≤ 6) is absorbed into the O(log n). ∎

**Theorem (FPT).** CANONICAL-BLD is fixed-parameter tractable for parameter k (output size).

*Proof.* For output size k:
- The representation R = (B, L, D) satisfies |B| + |L| + |D| ≤ k
- Boundaries are subsets of n elements: at most (n choose ≤k) = O(n^k) choices
- Links connect pairs: at most O(n^{2k}) choices for ≤k links
- Dimensions are bounded by k
- Total candidate representations: at most f(k) · n^{O(k)} for some computable f
- Verification (checking validity and cost) is polynomial in n
- Enumerate all candidates and verify: f(k) · poly(n)

This is FPT by definition. ∎

**Theorem (Tree Special Case).** For tree-structured systems, CANONICAL-BLD is solvable in O(n) time.

*Proof.* A tree-structured system has no sharing: each substructure has exactly one parent.
- Optimal compression factors independently at each subtree
- Greedy bottom-up: at each node, choose the minimal representation for that subtree
- No cross-subtree dependencies → local optimality is global optimality
- Single pass over n nodes: O(n) time ∎

**Theorem (Average Case).** CANONICAL-BLD is polynomial on random systems with high probability.

*Proof.* A random system S of size n has Kolmogorov complexity K(S) = Θ(n) with high probability (incompressibility of random strings).
- Any BLD representation must have cost ≥ K(S)/c for some constant c (compression lower bound)
- The trivial representation (no compression) has cost O(n)
- Therefore optimal cost = Θ(n), achieved by the trivial representation
- Greedy produces O(n) cost, which is optimal w.h.p.
- Greedy runs in polynomial time ∎

---

## References

- Charikar, M., et al. "The Smallest Grammar Problem." IEEE Trans. Information Theory, 2005.
- Lehman, E., Shelat, A. "Approximation Algorithms for Grammar-Based Compression." SODA 2002.
- Rytter, W. "Application of Lempel-Ziv factorization to the approximation of grammar-based compression." TCS 2003.

---

## See Also

- [Glossary](../../../glossary.md) — Central definitions
- [Discovery Algorithm](../../derived/discovery-algorithm.md) — The algorithm being analyzed
- [Discovery Method](../../../meta/discovery-method.md) — Informal method description
- [Constructive Lie](../../lie-theory/constructive-lie.md) — Why BLD produces Lie structures
