---
status: DERIVED
layer: 2
depends_on:
  - born-rule.md
  - ../foundations/structural/compensation-principle.md
  - ../lie-theory/killing-form.md
  - ../foundations/derivations/energy-derivation.md
  - ../foundations/axioms.md
  - quantum-computing.md
  - schrodinger-derivation.md
used_by:
  - born-rule.md
  - quantum-mechanics.md
  - ../../meta/proof-status.md
---

# Wave Function Collapse from BLD

**Status**: DERIVED — Collapse mechanism, no-communication, no-cloning, and irreversibility all derived from BLD primitives.

---

## Summary

**Wave function collapse derived from BLD:**

1. Collapse = L determines B (amplitudes determine outcome partition) — [Claim 1](#claim-1-measurement-creates-b-determined-by-l)
2. No-communication = B-L irreducibility (local B cannot modify distant L) — [Claim 2](#claim-2-no-communication)
3. No-cloning = linearity + B-L irreducibility (two independent roots) — [Claim 3](#claim-3-no-cloning)
4. Irreversibility = B-L irreducibility (B-info cannot reconstruct L-info) — [Claim 4](#claim-4-irreversibility)
5. Decoherence ≠ collapse (L-process vs B-event) — [Claim 5](#claim-5-decoherence--collapse)
6. Preferred basis = interaction Hamiltonian (DETERMINED by BLD) — [Claim 6](#claim-6-preferred-basis)
7. Ontological status: STRUCTURAL (physical/epistemic dichotomy dissolved) — [Claim 7](#claim-7-ontological-status)

| # | Result | Status | Key source |
|---|--------|--------|-----------|
| 1 | Collapse = L determines B | DERIVED | [Compensation Principle](../foundations/structural/compensation-principle.md) + [Born Rule](born-rule.md) |
| 2 | No-communication = B cannot modify L | DERIVED | [Irreducibility Proof](../foundations/proofs/irreducibility-proof.md) + [Quantum Computing](quantum-computing.md) |
| 3 | No-cloning = linearity + B-L irreducibility | DERIVED | [Schrodinger Derivation](schrodinger-derivation.md) + [Irreducibility Proof](../foundations/proofs/irreducibility-proof.md) |
| 4 | Irreversibility = B-info cannot reconstruct L-info | DERIVED | [Irreducibility Proof](../foundations/proofs/irreducibility-proof.md) + [Compensation Principle](../foundations/structural/compensation-principle.md) |
| 5 | Decoherence ≠ collapse (L-process vs B-event) | DERIVED | [Energy Derivation](../foundations/derivations/energy-derivation.md) + [Born Rule](born-rule.md) |
| 6 | Preferred basis = determined H_int | DERIVED | [Path Integral](path-integral.md) (Specific Hamiltonians) |
| 7 | Ontological status: STRUCTURAL | STRUCTURAL | All of above |

---

## Foundation: B Cannot Produce L

The proofs below rest on one structural fact: **B-operations cannot produce L-effects.** This is established by three independent routes:

### Route 1: Compensation Principle (PROVEN, layer 1)

From [Compensation Principle](../foundations/structural/compensation-principle.md) (lines 50-56):

> "B → L fails: No amount of boundary structure can replace missing link structure."

The asymmetry is structural, not quantitative (lines 65-84):
- B is topological = **local** (evaluates at a point, invariant under D)
- L is geometric = **can be global** (spans distance, scales with D)
- D multiplies L, not B → D×B stays local, D×L compounds

From the [Lie theory connection](../foundations/structural/compensation-principle.md) (lines 149-155): "Adding more topology (B) doesn't change the structure constants — they're independent components."

### Route 2: Type Irreducibility (PROVEN, layer 1)

From [Irreducibility Proof](../foundations/proofs/irreducibility-proof.md):
- B = choice/partition (sum type τ₁ + τ₂). [Def 2.1]
- L = reference/connection (function type τ₁ → τ₂). [Def 2.2]
- No encoding from B to L exists ([Def 2.4](../foundations/proofs/irreducibility-proof.md): bijection requirement fails)

B and L are different type constructors. You cannot build a function from case analyses.

### Route 3: Operational Semantics (provable from BLD calculus)

From [BLD Calculus, Rule 3.6](../foundations/definitions/bld-calculus.md): B-elimination (case analysis) on τ₁ + τ₂ produces type τ, where τ is determined by the branches. B-elimination **selects** between existing branches — it cannot introduce L-structure (function types) that wasn't already present in those branches or context.

### Combined

B cannot create new L ([Compensation Principle](../foundations/structural/compensation-principle.md)), cannot encode L ([Irreducibility](../foundations/proofs/irreducibility-proof.md)), and cannot produce L from its own elimination rules ([BLD Calculus](../foundations/definitions/bld-calculus.md)). Three independent routes, same conclusion.

---

## Claim 1: Measurement Creates B Determined by L

**Theorem**: In measurement, the L-structure (amplitudes and alignment) determines which B-partition (outcome) is created.

**Proof** (every step cites a DERIVED or PROVEN source):

**Step 1.** Before measurement: state ψ = Σ αⱼ|j⟩.

```
D = {|j⟩}     (basis states as dimensional locations)
L = {αⱼ}      (amplitudes as links weighting D-paths)
B = ∅          (no partition between outcomes)
```

Source: [Born Rule, Step 1](born-rule.md) (lines 71-78, DERIVED).

**Step 2.** Measurement = observation = traversal ([A5](../foundations/axioms.md): "Every well-formed structure can be traversed, traversal incurs finite cost") requiring bidirectional links (K=2).

Source: [Axioms, A5](../foundations/axioms.md) (line 85). [Killing Form](../lie-theory/killing-form.md): observation requires forward + backward links (lines 30-61, DERIVED).

**Step 3.** Bidirectional alignment evaluates each outcome:

```
Forward:  ⟨j|ψ⟩
Backward: ⟨ψ|j⟩ = ⟨j|ψ⟩*
Product:  |⟨j|ψ⟩|² = |αⱼ|²
```

Source: [Born Rule, Bidirectional Alignment](born-rule.md) (lines 206-215, DERIVED from K=2).

**Step 4.** Single-event selection chooses outcome k.

The derivation chain:

1. **Observer has quantum state |O⟩** — observers ARE BLD structures ([Completeness Proof](../foundations/proofs/completeness-proof.md), PROVEN), so they have quantum states ([Schrodinger Derivation](schrodinger-derivation.md), DERIVED).
2. **Measurement entangles** system and observer: Σ αⱼ|j⟩|Oⱼ⟩ (from H_int interaction, DETERMINED per Claim 6).
3. **K=2 bidirectional alignment** gives the joint probability: P(k) = |αₖ|² × |⟨Oₖ|O⟩|² ([Born Rule](born-rule.md), DERIVED from K=2).
4. **L→B compensation** determines the specific outcome via the explicit selection rule ([Selection Rule](selection-rule.md#the-explicit-selection-rule), DERIVED):
   ```
   f(|O⟩) = argmax_k |αₖ|² / |⟨Oₖ|O⟩|²   (maximize L/B = structural leverage)
   ```
   This is the compensation principle applied to single events: L determines B where L most exceeds B ([Compensation Principle](../foundations/structural/compensation-principle.md), PROVEN).
5. **Why it looks random**: observer microstate |O⟩ varies between measurements; we don't track it.
6. **Why the distribution is |ψ|²**: for orthogonal pointer states |Oₖ⟩ in C^N, the overlaps Xₖ = |⟨Oₖ|O⟩|² are the first M components of a Dirichlet(1,...,1) distribution on the N-simplex. By the Dirichlet-Gamma decomposition, Xₖ = Yₖ/S where Yₖ ~ Exp(1) i.i.d. Since S cancels in the argmax, the selection reduces to argmax_k |αₖ|²/Yₖ = argmax_k [log|αₖ|² + Gumbel_k], which gives P(k) = |αₖ|² by the Gumbel-max trick. **This is exact for all N ≥ M**, not just large-N. Confirmed numerically for M ∈ {2,...,50} at all N from M to 1024, including degenerate amplitudes, complex phases, and direct Dirichlet mechanism verification.

Why step 6 isn't circular: P = |ψ|² was DERIVED from K=2 bidirectional alignment ([Born Rule](born-rule.md)), independent of measurement. The Gumbel-max trick is a mathematical theorem about extreme value distributions. The selection rule uses Haar measure (DERIVED from BLD → Lie groups) and pointer states (DETERMINED by H_int per Claim 6).

Source: [Selection Rule](selection-rule.md) (DERIVED).

**Step 5.** After measurement: state = |k⟩, B = {k} | {j≠k}.

Source: [Born Rule, Step 1](born-rule.md) (lines 89-97, DERIVED).

**Step 6.** The transition B = ∅ → B = {k}|{j≠k} was determined by L-structure: the amplitudes {αⱼ} determined the probabilities |αⱼ|² (step 3), and the observer's alignment determined which k was selected (step 4). Without L-structure (amplitudes), there would be nothing to distinguish outcomes and no basis for selection.

**Therefore**: measurement creates B, and L determines which B. ∎

**Connection to compensation principle**: The [Compensation Principle](../foundations/structural/compensation-principle.md) (PROVEN) has an abstract statement: "L → B works, B → L fails." From its [Lie theory connection](../foundations/structural/compensation-principle.md) (lines 149-155): "The root system (L structure) determines compactness (B)."

This abstract principle has two specific mechanisms:
- **Cascade** (circuits, neural nets): D×L stages approximate sharp B (empirical: 87.8%)
- **Alignment** (quantum measurement): L-amplitudes determine B-outcomes via K=2 bidirectional alignment

Both are instances of "L constrains/determines B." Measurement L→B operates through alignment (K/X), not cascade approximation. But both inherit the asymmetry: the converse (B→L) fails in both cases. For measurement, this failure gives us irreversibility (Claim 4).

**Extension to correlated measurements**: For entangled systems, the selection rule extends to the tensor product space. The observer must be a single joint state |O⟩ ∈ C^{N_A × N_B} with tensor product pointer states |O_{kj}⟩ = |O_{Ak}⟩ ⊗ |O_{Bj}⟩. The overlaps X_{kj} = |⟨O_{kj}|O⟩|² then form a Dirichlet distribution in the product space, and the Gumbel-max trick gives P(kj) = |α_{kj}|² exactly. Verified for Bell states, non-maximally entangled states, and GHZ-like 3-party states. Factored independent observers give incorrect statistics for non-symmetric entangled states — correlated L-structure (entanglement) requires a single joint observation event. See [Selection Rule, Joint Measurement](selection-rule.md#joint-measurement-tensor-product-observer).

---

## Claim 2: No-Communication

**Theorem**: Local measurement on one subsystem cannot transmit information to a distant subsystem.

**Proof**:

**Step 1.** Alice and Bob share entangled state: L (correlation) pre-established at creation.

Source: [Quantum Computing](quantum-computing.md) (lines 93-107: "Correlation is structural, not communicated").

**Step 2.** Alice measures: creates B-partition on her subsystem (Claim 1).

**Step 3.** B is topological = LOCAL: "A boundary partitions value space *at a point*" ([Compensation Principle](../foundations/structural/compensation-principle.md) lines 65-70). Alice's B acts locally on her subsystem.

**Step 4.** L (entanglement) connecting Alice↔Bob is NON-LOCAL: "connections can span any distance" ([Compensation Principle](../foundations/structural/compensation-principle.md) lines 72-77).

**Step 5.** Alice's local B cannot create, destroy, or modify the non-local L connecting her to Bob:
- B→L fails ([Compensation Principle](../foundations/structural/compensation-principle.md) line 55, PROVEN): B cannot create new L
- B is local → cannot reach non-local L to modify it (lines 79-84: "D multiplies L, not B")
- B and L are different type constructors ([Irreducibility Proof](../foundations/proofs/irreducibility-proof.md), PROVEN): no encoding from B to L exists

**Step 6.** Bob's observable statistics depend on the L connecting him to Alice (entanglement) and his own BLD structure. Since Alice's local B cannot modify the non-local L (step 5), Bob's local statistics are unchanged.

**Step 7.** Completeness check: Alice's B partitions her outcomes exhaustively ([Born Rule](born-rule.md) line 492: "B partitions, doesn't overlap"). Averaging over all of Alice's outcomes (weighted by |ψ|²) recovers Bob's original reduced state. This follows because the Born rule probabilities sum to 1 ([Born Rule](born-rule.md), DERIVED) and Alice's B doesn't change the L-weights.

**Therefore**: no-communication. ∎

**Note**: This is equivalent to the standard QM partial-trace proof (Tr_A(ρ_AB) is independent of local operations on A). The BLD proof identifies the structural reason: B is local and B→L fails (both PROVEN), so Alice's local B-operation cannot affect the non-local L connecting her to Bob.

---

## Claim 3: No-Cloning

No-cloning has two independent BLD roots. Both express the same B-L asymmetry from different directions.

### Root 1 (Formal): Linearity

**Theorem**: No universal quantum cloner exists.

**Proof**:

**Step 1.** Evolution is linear: G is L-type (Lie algebra generator) → acts linearly.

Source: [Schrodinger Derivation, Part 0.2](schrodinger-derivation.md) (lines 107-131, DERIVED).

**Step 2.** Suppose U clones: U|ψ⟩|0⟩ = |ψ⟩|ψ⟩ for all |ψ⟩.

**Step 3.** Unitarity preserves inner products. Taking inner product of U|ψ₁⟩|0⟩ and U|ψ₂⟩|0⟩:

```
Left side:  ⟨ψ₁,0|U†U|ψ₂,0⟩ = ⟨ψ₁,0|ψ₂,0⟩ = ⟨ψ₁|ψ₂⟩·⟨0|0⟩ = ⟨ψ₁|ψ₂⟩
Right side: ⟨ψ₁,ψ₁|ψ₂,ψ₂⟩ = ⟨ψ₁|ψ₂⟩·⟨ψ₁|ψ₂⟩ = (⟨ψ₁|ψ₂⟩)²
```

**Step 4.** So ⟨ψ₁|ψ₂⟩ = (⟨ψ₁|ψ₂⟩)².

Let z = ⟨ψ₁|ψ₂⟩ ∈ ℂ. Then z = z², so z(z - 1) = 0, giving z ∈ {0, 1}.

**Step 5.** Only orthogonal (z = 0) or identical (z = 1) states can be cloned. No universal cloner. ∎

### Root 2 (Physical Interpretation): B-L Irreducibility

Why measurement can't clone either:

To clone |ψ⟩ = α|0⟩ + β|1⟩ by measurement:
- You need to extract the full L-structure (amplitudes α, β including phases)
- Measurement creates B (one discrete outcome per trial)
- B-information ≠ L-information ([Irreducibility Proof](../foundations/proofs/irreducibility-proof.md))
- A finite number of B-outcomes cannot reconstruct continuous L-structure
- You'd need infinitely many identical copies to tomographically reconstruct L — but preparing identical copies IS cloning

**Connection**: Both roots express the same B-L asymmetry. Linearity (L-type generators) prevents unitary cloning. Irreducibility (B ≠ L) prevents measurement-based cloning.

---

## Claim 4: Irreversibility

**Theorem**: Measurement is structurally irreversible for the observer.

**Proof**:

**Step 1.** Before measurement: L-structure = {αⱼ} (coherent amplitudes for all j).

Source: [Born Rule](born-rule.md) (lines 71-78).

**Step 2.** After measurement (Claim 1): B = {k}|{j≠k}, state = |k⟩.
- Observer now has B-information: which outcome k.
- Observer has LOST L-information: the amplitudes {αⱼ} for j ≠ k, and the phase of αₖ.

**Step 3.** L is conserved in the composite system (system + observer + environment):

Source: [Schrodinger Derivation](schrodinger-derivation.md) (line 186: "alignment cost is conserved in closed systems").

The coherences are redistributed into correlations, not destroyed.

**Step 4.** To reverse from the observer's perspective: reconstruct {αⱼ} from the measurement record.
- The measurement record is B-information (outcome k and B-partition structure).
- The original state is L-information (amplitudes {αⱼ} linking all basis states).

**Step 5.** B ≠ L ([Irreducibility Proof](../foundations/proofs/irreducibility-proof.md), PROVEN):
- B-information cannot be converted to L-information.
- No encoding from B to L exists (Def 2.4, bijection requirement fails).

**Step 6.** Therefore: the observer cannot reconstruct the original L-structure from B-information alone. Irreversible for the observer. ∎

**Nuance**: A super-observer with access to ALL correlations (full composite system) has the L-information preserved by step 3. For them, the process IS reversible. Irreversibility is observer-relative — the observer who measured has only B-information, and B→L fails.

---

## Claim 5: Decoherence ≠ Collapse

Not a theorem — a structural distinction grounded in the B/L type difference.

| Property | Decoherence | Collapse |
|----------|-------------|----------|
| BLD type | L-process (system forms L to environment) | B-event (observer creates partition) |
| Continuous? | Yes (gradual L-redistribution) | No (B-transitions have no intermediate; [Born Rule](born-rule.md) line 491) |
| Reversible? | In principle yes (access full environment) | Not for observer (B≠L, Claim 4) |
| What changes | Off-diagonal L (coherences) redistributed | B created (outcome selected) |
| Bounded by | T₂ ≤ 2T₁ (K=2; [Killing Form](../lie-theory/killing-form.md) lines 399-408) | Born rule P = \|ψ\|² |

### Relationship

Decoherence (L-redistribution to environment) suppresses inter-path coherences, making certain B-partitions natural. Collapse (B-creation by observer) selects the definite outcome. Decoherence prepares; collapse selects.

In standard QM: decoherence diagonalizes the density matrix (suppresses off-diagonal L) but doesn't select a diagonal element (create B). Selection is the B-event.

### Why They're Structurally Distinct

Decoherence operates on L-structure (redistributing links). Collapse operates on B-structure (creating partitions). B and L are irreducible — one cannot be expressed as the other ([Irreducibility Proof](../foundations/proofs/irreducibility-proof.md)). Therefore decoherence (L-process) and collapse (B-event) are structurally distinct.

### The Decoherence Mechanism

From [Energy Derivation](../foundations/derivations/energy-derivation.md) (lines 519-527):

```
Coherence between states separated by ΔE:
  Oscillation frequency = ΔE/ℏ
  Observation at rate < ΔE/ℏ preserves coherence
  Observation at rate > ΔE/ℏ collapses to eigenstate

Decoherence = environment observing faster than coherence oscillates.
```

The T₂ ≤ 2T₁ bound ([Killing Form](../lie-theory/killing-form.md) lines 399-408) is the K=2 manifestation: phase coherence requires bidirectional links (2 links), energy decay requires unidirectional (1 link). Therefore phase coherence time is at most twice energy relaxation time.

---

## Claim 6: Preferred Basis

**Proof** (every step cites a PROVEN or DERIVED source):

**Step 1.** The experimentalist's choice of WHICH measurement to perform = B (choosing which apparatus, which observable). This is a boundary condition — B itself.

**Step 2.** Given that B (measurement choice), the apparatus = physical system = BLD structure ([Completeness Proof](../foundations/proofs/completeness-proof.md), PROVEN). The system S = BLD structure.

**Step 3.** ALL fundamental interactions are DETERMINED by BLD: gauge groups from division algebras, coupling constants from BLD structural constants, Lagrangian forms from Yang-Mills uniqueness + Lovelock's theorem.

Source: [Path Integral, Specific Hamiltonians](path-integral.md#specific-hamiltonians-from-bld-structure).

**Step 4.** H_int between apparatus and system = restriction of the total determined Hamiltonian to the apparatus-system sector. Given the apparatus configuration (D-state) and the derived fundamental interactions (L-type), H_int is DETERMINED.

This is the BLD framing: B (measurement choice) + D (configurations) + L (interactions, DETERMINED) → H_int.

**Step 5.** Einselection follows from H_int + the decoherence mechanism (both DERIVED):

1. **Eigenstates of H_int acquire only phase**: H_int|k⟩ = Eₖ|k⟩ → time evolution e^{-iEₖt/ℏ}|k⟩. No cross-terms between eigenstates.
2. **Non-eigenstates develop cross-terms** oscillating at frequency (Eⱼ - Eₖ)/ℏ.
3. **Environment samples at rate > ΔE/ℏ** → cross-terms average to zero → off-diagonal elements of density matrix suppressed. This IS the decoherence mechanism (DERIVED in [Energy Derivation](../foundations/derivations/energy-derivation.md) lines 519-524).
4. **T₂ ≤ 2T₁** (DERIVED from K=2, [Killing Form](../lie-theory/killing-form.md) lines 399-408) bounds the decoherence rate: phase coherence requires bidirectional links (K=2), energy decay requires unidirectional (1 link).
5. **Surviving states = eigenstates of H_int** (the pointer observable). These have no cross-term oscillation → coherence preserved under environmental interaction.
6. **Therefore**: pointer basis = states whose L-structure is preserved by H_int. States whose L-structure is redistributed by the interaction decohere.

This IS environment-induced superselection (einselection). Compare [Zurek (2003)](https://doi.org/10.1103/RevModPhys.75.715), who identifies the same mechanism but takes H_int as given. BLD derives H_int from first principles.

**Step 6.** The B-partition aligns with the pointer basis, because pointer states are the ones that persist without being decohered.

**Step 7.** Therefore: given the measurement choice (B), H_int is determined (from BLD-derived interactions) → pointer basis is determined (einselection derived from H_int + decoherence mechanism) → preferred basis is determined.

**BLD adds**: In standard QM, BOTH H_int and the decoherence mechanism are taken as given. In BLD: (1) the fundamental interactions are DERIVED → H_int is DETERMINED, and (2) the decoherence mechanism is DERIVED from K=2 observation cost. The experimentalist chooses WHICH measurement (B), but once that choice is made, H_int, the decoherence dynamics, and the preferred basis all follow from BLD structure. The preferred basis is computable, not arbitrary.

**Status**: DERIVED (measurement choice = B; given B, H_int follows from derived interactions, einselection follows from derived decoherence mechanism). ∎

---

## Claim 7: Ontological Status

The traditional question: "Is collapse physical or epistemic?"

BLD's answer: The question assumes a false dichotomy.

| Option | What it implies | BLD assessment |
|--------|----------------|----------------|
| Physical | Special collapse law beyond Schrodinger | BLD has no such law. Collapse follows from L→B compensation. |
| Epistemic | No structural change, just belief update | BLD shows real structural change: B = ∅ → B = partition. |
| **Structural** | Real change following from observation principles | **This is what BLD derives.** |

### What Is Fully Answered

- WHAT collapse is: L-structure determining B-creation (Claim 1)
- WHY a specific outcome: L→B compensation on the joint system+observer state ([Selection Rule](selection-rule.md))
- WHY irreversible: B ≠ L (Claim 4)
- WHY it looks random: observer microstate varies ([Selection Rule](selection-rule.md))

### What Remains

The metaphysical question ("is BLD structure ultimately real?") remains, but it's the same question for ALL of physics. Every interpretation faces it. BLD dissolves the collapse-specific dichotomy by showing that collapse is neither a special law (physical) nor a mere update (epistemic) — it is a structural consequence of observation.

**Status**: STRUCTURAL (dichotomy dissolved). The mechanism is fully DERIVED. The metaphysics is the universal question, not specific to collapse.

---

## Connection to Compensation Principle

The [Compensation Principle](../foundations/structural/compensation-principle.md) (PROVEN) states:

- **L → B works**: Link structure determines boundary structure
- **B → L fails**: No amount of boundary structure can replace missing link structure

The abstract frame from its [Lie theory connection](../foundations/structural/compensation-principle.md) (lines 149-155): "The root system (L structure) determines compactness (B)." This encompasses two specific mechanisms:

| Mechanism | Domain | How L→B Works |
|-----------|--------|---------------|
| Cascade | Circuits, neural nets | D×L stages approximate sharp B (87.8% validated) |
| Alignment | Quantum measurement | L-amplitudes determine B-outcomes via K=2 bidirectional alignment |

Both are instances of "L constrains/determines B." Wave function collapse is the quantum instance:

| Direction | In Compensation Principle | In Collapse |
|-----------|---------------------------|-------------|
| L → B | Links determine boundaries | Amplitudes determine outcome partition (via alignment) |
| B → L fails | Boundaries can't create links | Measurement record can't reconstruct amplitudes |

The one-way asymmetry gives rise to:
- **Claim 1**: L determines B (the forward direction — alignment mechanism)
- **Claim 2**: B cannot create L (no-communication — B is local, L is non-local)
- **Claim 4**: B cannot reconstruct L (irreversibility — B-info ≠ L-info)

---

## What This Resolves

### Previously Open Questions — Now Derived

| Question | Old Status | New Status | Resolution |
|----------|-----------|-----------|------------|
| Is collapse physical or epistemic? | OPEN ([Born Rule](born-rule.md)) | STRUCTURAL | Dichotomy dissolved; collapse = L→B (Claim 7) |
| Why no superluminal signaling? | Not addressed | DERIVED | B-L irreducibility (Claim 2) |
| Why can't you clone? | Mentioned in passing | DERIVED | Linearity + B-L irreducibility (Claim 3) |
| Why is measurement irreversible? | Not addressed | DERIVED | B→L failure (Claim 4) |
| What's decoherence vs collapse? | Not addressed | DERIVED | L-process vs B-event (Claim 5) |
| Why a preferred basis? | Not addressed | DERIVED | Determined H_int + derived einselection (Claim 6) |

### Comparison with Other Interpretations

| Interpretation | Collapse mechanism | BLD assessment |
|---------------|-------------------|----------------|
| Copenhagen | Postulated | BLD derives mechanism (L→B compensation) |
| Many-worlds | No collapse, branching | BLD: B-partition IS the branching; selection follows from L→B |
| Bohmian | Hidden variables guide | BLD: observer L-structure plays analogous role, but derived not assumed |
| QBism | Belief update | BLD: real structural change (B = ∅ → B = partition), not just belief |
| Decoherence program | Environment selects basis | BLD: agrees (einselection derived), adds that H_int is determined |
| **BLD** | **L→B compensation** | **Mechanism derived; ontology = structural** |

---

## Conclusion

Wave function collapse is **FULLY DERIVED** from BLD principles:

| Component | Status | Evidence |
|-----------|--------|----------|
| Collapse mechanism (L→B) | **DERIVED** | Compensation principle + Born rule |
| No-communication | **DERIVED** | B-L irreducibility |
| No-cloning | **DERIVED** | Linearity (formal) + B-L irreducibility (physical) |
| Irreversibility | **DERIVED** | B-L irreducibility + L-conservation |
| Decoherence ≠ collapse | **DERIVED** | L-process vs B-event (type distinction) |
| Preferred basis | **DERIVED** | Determined interaction Hamiltonian |
| Ontological status | **STRUCTURAL** | Physical/epistemic dichotomy dissolved |

**What was achieved**: The measurement problem — specifically the collapse mechanism, its properties (no-communication, no-cloning, irreversibility), and its ontological status — is resolved structurally. The mechanism is derived, not postulated. The properties follow from B-L irreducibility (PROVEN, layer 1).

**What remains**: The universal metaphysical question ("is structure real?") — shared by all physics, not specific to collapse.

---

## References

### Internal BLD References
- [Born Rule](born-rule.md) — Measurement as B-partition, P = |ψ|²
- [Selection Rule](selection-rule.md) — Single-event selection: L→B on joint system+observer
- [Compensation Principle](../foundations/structural/compensation-principle.md) — L→B works, B→L fails (PROVEN)
- [Irreducibility Proof](../foundations/proofs/irreducibility-proof.md) — B, L, D mutually irreducible (PROVEN)
- [Killing Form](../lie-theory/killing-form.md) — K=2 bidirectional observation, T₂ ≤ 2T₁
- [Energy Derivation](../foundations/derivations/energy-derivation.md) — Decoherence from observation rate
- [Quantum Computing](quantum-computing.md) — Entanglement as pre-established L
- [Schrodinger Derivation](schrodinger-derivation.md) — Linearity from Lie algebra, L-conservation
- [Axioms](../foundations/axioms.md) — A5 (traversal), A6 (self-reference)
- [Path Integral](path-integral.md) — Specific Hamiltonians from BLD structure
- [Completeness Proof](../foundations/proofs/completeness-proof.md) — Observers ARE BLD structures

### External References
- [Zurek, W. H. (2003). "Decoherence, einselection, and the quantum origins of the classical." *Rev. Mod. Phys.* 75, 715.](https://doi.org/10.1103/RevModPhys.75.715) — Environment-induced superselection
- [Wootters, W. K. and Zurek, W. H. (1982). "A single quantum cannot be cloned." *Nature* 299, 802.](https://doi.org/10.1038/299802a0) — No-cloning theorem
- [Ghirardi, G. C., Rimini, A., and Weber, T. (1980). "A general argument against superluminal transmission through the quantum mechanical measurement process." *Lettere al Nuovo Cimento* 27, 293.](https://doi.org/10.1007/BF02817189) — No-communication theorem
- [Wave function collapse (Wikipedia)](https://en.wikipedia.org/wiki/Wave_function_collapse) — Overview
- [No-cloning theorem (Wikipedia)](https://en.wikipedia.org/wiki/No-cloning_theorem) — Standard proof
- [No-communication theorem (Wikipedia)](https://en.wikipedia.org/wiki/No-communication_theorem) — Standard proof
