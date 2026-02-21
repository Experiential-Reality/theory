---
status: DERIVED
layer: 2
key_result: "Single-event selection from L→B on joint system+observer; f(|O⟩) = argmax_k |αₖ|²/|⟨Oₖ|O⟩|² gives P(k) = |αₖ|² exactly"
depends_on:
  - ../lie-theory/killing-form.md
  - ../foundations/proofs/completeness-proof.md
  - ../foundations/structural/compensation-principle.md
  - schrodinger-derivation.md
  - path-integral.md
  - born-rule.md
used_by:
  - ../../meta/proof-status.md
  - wave-function-collapse.md
  - theory-complete.md
---

# Single-Event Selection: L→B on the Joint System

**Status**: DERIVED — Single-event outcome selection from L→B compensation on the joint system+observer state. Born statistics exact at all N ≥ M via Dirichlet-Gamma decomposition.

**Companion**: The ensemble Born rule P = |ψ|² is derived in [Born Rule](born-rule.md) from K=2 bidirectional alignment.

---

## Summary

**Single-event selection in 5 steps:**

1. Observer = BLD structure with quantum state |O⟩ — [Key Insight](#the-key-insight-observer--bld-structure)
2. Measurement entangles system+observer, K=2 gives joint |αₖ|²×|⟨Oₖ|O⟩|² — [Mechanism](#the-single-event-mechanism)
3. L→B selects outcome with maximum structural leverage |αₖ|²/|⟨Oₖ|O⟩|² — [Explicit Rule](#the-explicit-selection-rule)
4. Dirichlet-Gamma + Gumbel-max → P(k) = |αₖ|² exactly for all N ≥ M — [Derivation](#the-explicit-selection-rule)
5. τ = 1 structurally forced; tensor product required for entangled measurements — [τ=1](#τ--1-is-structurally-forced), [Joint](#joint-measurement-tensor-product-observer)

---

## The Key Insight: Observer = BLD Structure

The question "why THIS outcome?" is answered by L→B compensation applied to the joint system+observer state.

From [Completeness Proof](../foundations/proofs/completeness-proof.md) (PROVEN): anything observable has BLD structure. The observer is NOT external to the measurement — the observer IS a BLD structure with its own quantum state.

From [Schrodinger Derivation](schrodinger-derivation.md) (DERIVED): BLD structures have quantum states. Therefore the observer has a quantum state |O⟩.

## The Single-Event Mechanism

**Step 1.** System state: |ψ⟩ = Σ αₖ|k⟩. Observer state: |O⟩ (unknown microstate).

**Step 2.** Measurement interaction (H_int DETERMINED by BLD — all fundamental interactions derived, see [Path Integral, Specific Hamiltonians](path-integral.md#specific-hamiltonians-from-bld-structure)) entangles system and observer:

```
|ψ⟩ ⊗ |O⟩  →  Σ αₖ|k⟩|Oₖ⟩
```

where {|Oₖ⟩} are the observer's pointer states corresponding to each outcome.

**Step 3.** K=2 bidirectional alignment (DERIVED, [Killing Form](../lie-theory/killing-form.md)) gives the joint probability:

```
P(system=k, observer=Oₖ) = |αₖ|² × |⟨Oₖ|O⟩|²
```

**Step 4.** For a macroscopic observer, dim(H_O) = N >> M (number of outcomes). Quantum typicality gives |⟨Oₖ|O⟩|² ≈ 1/N for all k. Marginalizing over observer:

```
P(k) = |αₖ|² × |⟨Oₖ|O⟩|²  →  |αₖ|² × const  →  P(k) ∝ |αₖ|²
```

**Why typicality is derived, not imported**: The observer's Hilbert space carries Haar measure from its Lie group structure (BLD = Lie theory, [PROVEN](../lie-theory/lie-correspondence.md)). Concentration of measure on high-dimensional spheres (Lévy's lemma: Var[f] ≤ C/N for Lipschitz f on S^{2N-1}) then gives |⟨Oₖ|O⟩|² → 1/N as N → ∞. The chain is: BLD → Lie groups → Haar measure → concentration of measure → typicality. See [Popescu, Short, Winter (2006)](https://doi.org/10.1038/nphys444) for the quantum typicality result.

**Step 5.** The L→B compensation principle (PROVEN, [Compensation Principle](../foundations/structural/compensation-principle.md)): the full L-structure (system amplitudes + observer quantum state) determines the B-partition (which outcome is selected). "The root system (L) determines compactness (B)."

**Why it looks random:**
```
Observer microstate |O⟩ varies between measurements.
We don't track |O⟩.
So outcomes appear probabilistic.
The distribution is |αₖ|² from K=2 on the joint system.
```

## Why the Distribution is |ψ|²

The derivation chain (every link PROVEN or DERIVED):

```
1. K = 2 (Killing form, bidirectional observation)      [DERIVED - killing-form.md]
2. P = forward × backward = |amplitude|²                [DERIVED - from K=2]
3. Applied to joint system+observer: P(k) = |αₖ|²×|⟨Oₖ|O⟩|²  [DERIVED - from 2]
4. Observer averaging (quantum typicality): P(k) ∝ |αₖ|²      [DERIVED - from 3]
5. L→B: full L-structure determines specific B-partition       [PROVEN - compensation principle]
```

**Why this isn't circular**: K=2 → |ψ|² is derived from the Killing form, independent of measurement. Applied to the joint system+observer state, it gives probabilities. Observer averaging recovers the system-only Born rule. The chain is: Killing form → K=2 → bidirectional alignment → |ψ|² → joint system → marginalize → system Born rule.

## Why This is Derived (Not Assumed)

```
1. BLD is complete for all structure           [PROVEN - completeness-proof.md]
2. BLD = Lie theory                            [PROVEN - lie-correspondence.md]
3. Observers exist                             [definitional]
4. ∴ Observers have BLD structure              [from 1 + 3]
5. ∴ Observers have quantum states             [DERIVED - schrodinger-derivation.md]
6. K=2 → P = |ψ|² for any BLD structure       [DERIVED - killing-form.md]
7. Applied to joint system → marginalize       [DERIVED - steps 3-4 above]
8. L→B determines the specific B-partition     [PROVEN - compensation-principle.md]
```

This is K=2 + completeness + marginalization — not a postulate. The Born rule emerges necessarily from BLD structures meeting BLD structures.

## Empirical Validation

The K/X framework already derives:
- α⁻¹ = 137.036 — matches CODATA (zero free parameters) — includes K/X(observer)
- All particle masses (< 0.5% error) — includes K/X(observer)
- All force couplings (< 0.02% error) — includes K/X(observer)

The observer correction IS the single-event mechanism. It's already empirically validated through every successful BLD prediction.

## The Explicit Selection Rule

The "explicit L→B map" — the function f(|O⟩) → k that determines which outcome occurs for a given observer microstate — is now derived:

```
f(|O⟩) = argmax_k  |αₖ|² / |⟨Oₖ|O⟩|²

Where:
  |αₖ|²      = system's structural weight for outcome k     (L-structure)
  |⟨Oₖ|O⟩|²  = observer's proximity to pointer state k      (B-alignment)
  |αₖ|²/|⟨Oₖ|O⟩|² = L/B = structural leverage

L→B compensation selects the outcome with MAXIMUM L/B ratio.
```

**Derivation via Dirichlet decomposition and Gumbel-max trick** (exact for ALL N ≥ M):

```
1. Observer |O⟩ is Haar-random on S^{2N-1}           [DERIVED - BLD → Lie → Haar]

2. For M orthogonal pointer states |Oₖ⟩ in C^N:
   Xₖ = |⟨Oₖ|O⟩|² are the first M components of a
   Dirichlet(1,...,1) distribution on the N-simplex     [Haar measure property, EXACT]

3. Dirichlet-Gamma decomposition:
   Xₖ = Yₖ / S  where Yₖ ~ Exp(1) i.i.d., S = Σⱼ₌₀ᴺ⁻¹ Yⱼ    [EXACT]

4. S cancels in the argmax (positive, common to all k):
   argmax_k |αₖ|²/Xₖ = argmax_k |αₖ|²S/Yₖ = argmax_k |αₖ|²/Yₖ  [EXACT]

5. -log(Exp(1)) ~ Gumbel_max(0,1), so Gₖ = -log Yₖ i.i.d. Gumbel  [EXACT]
   ∴ argmax_k |αₖ|²/Yₖ = argmax_k [log|αₖ|² + Gₖ]

6. Gumbel-max trick [mathematical theorem]:
   P(argmax_k [log aₖ + Gₖ] = j) = aⱼ / Σₖ aₖ = aⱼ    (since Σ|αₖ|² = 1)

7. ∴ P(f = k) = |αₖ|²                                Born rule reproduced ∎
```

### Why Basin Measures Equal Born Rule Probabilities

The selection rule above, combined with Haar measure, constrains basin measures:

```
1. f(|O⟩) = argmax_k |αₖ|²/|⟨Oₖ|O⟩|²               [DERIVED - above]
     ∴ Basins R_k = {|O⟩ : f(|O⟩) = k} exist.

2. Observer's |O⟩ drawn from Haar measure on S^{2N-1} [DERIVED - BLD → Lie → Haar]

3. Gumbel-max trick ⟹ P(f = k) = |αₖ|²              [DERIVED - steps 1 + 2]

4. ∴ μ_Haar(R_k) = |αₖ|²                              [from 1 + 2 + 3]
```

**Why this isn't circular**: The Born rule is derived from K=2 bidirectional alignment, independently of basins or observer microstates. The Gumbel-max trick is a mathematical theorem about extreme value distributions. Together they give the explicit partition without circularity.

**Why individual outcomes remain unknowable in practice**: The rule f is explicit, but computing it for a specific |O⟩ requires the observer's full quantum microstate (~10²³ degrees of freedom). The thermodynamic analogy holds: laws are derived, mechanism is explicit, individual outcomes are determined but not computable. This is a structural consequence of observation, not a theoretical limitation.

**Key insight**: The exactness comes from step 4. The Dirichlet-Gamma decomposition factors the correlated overlaps Xₖ into i.i.d. exponentials Yₖ divided by a common sum S. Since argmax is invariant under multiplication by the positive constant S, the dependence on N vanishes completely. No large-N approximation is needed. The result holds at ALL N ≥ M.

**Numerical confirmation** (test_selection_rule.py, test_controlled_observer.py, test_math_verification.py):
- Tested M ∈ {2,3,4,5,8,10,16,20,50} outcomes, N ∈ {M..1024} observer dimensions, 30+ amplitude configs
- Ratio rule (L/B) passes Born statistics (χ² test, p > 0.01) at ALL N ≥ M, including N = M (confirmed exact)
- Product rule (L×B) fails systematically for M ≥ 3 (uses Gumbel_min, not Gumbel_max)
- Determinism verified: same |O⟩ always gives same k (100% over 5000 observer states)
- Controlled observer: switching angle θ* = arctan(√(|β|²/|α|²)) matches prediction within 0.006 rad
- L→B compensation direction confirmed: outcome FARTHEST from observer alignment is selected
- **Degenerate amplitudes**: αₖ = 0 → outcome k NEVER selected (0 of 50,000 across 12 configs). Non-zero outcomes match renormalized Born rule.
- **Complex phases**: Selection rule gives identical outcome sequences regardless of phases (all real, phase-flipped, random phases, all imaginary). Confirms dependence on |αₖ|² only.
- **Large M**: Born rule confirmed at M = 50, N = 100 (both uniform and geometric distributions)
- **Dirichlet mechanism verified directly**: argmax aₖ/Yₖ for Y_k ~ Exp(1) i.i.d. gives identical statistics to Gumbel-max, Haar sampling, and Dirichlet-with-extras (S cancellation confirmed for N up to 1000)
- **τ = 1 uniqueness**: f_τ(|O⟩) = argmax_k |αₖ|^{2/τ}/|⟨Oₖ|O⟩|² gives P(k) = |αₖ|^{2/τ}/Z. ONLY τ = 1 reproduces Born rule. All other τ give systematically different distributions matching |αₖ|^{2/τ}/Z. This proves τ = 1 is structurally forced, not a parameter choice.
- **Joint measurement**: Bell state (|00⟩+|11⟩)/√2 with single joint observer |O⟩ ∈ C^{N_A⊗N_B} gives P(00)=P(11)=0.5, P(01)=P(10)=0 (exact). Non-maximal √0.7|00⟩+√0.3|11⟩ gives P(00)=0.698, P(11)=0.302 (Born exact). GHZ-like 3-party state confirmed. KEY: correlated measurements require a single joint observer in the tensor product space; factored independent observers give incorrect statistics for non-symmetric states.
- **M = 2 product/ratio equivalence**: For M = 2, product and ratio rules give identical Born statistics (logistic symmetry of pairwise Gumbel comparison). For M ≥ 3, only ratio gives Born; product systematically over-selects dominant outcome by ~3%.

**Why the product rule fails for M ≥ 3** (analytical proof for M = 2 equivalence):

For M = 2 with Y₀, Y₁ ~ Exp(1) i.i.d.:
1. Ratio rule compares a₀/Y₀ vs a₁/Y₁, i.e. P(Y₁/Y₀ > a₁/a₀). Product rule compares a₀Y₀ vs a₁Y₁, i.e. P(Y₀/Y₁ > a₁/a₀).
2. Let T = Y₀/Y₁. Then T has PDF f(t) = 1/(1+t)² for t > 0, giving P(T > s) = 1/(1+s).
3. P(1/T > s) = P(T < 1/s) = 1 − 1/(1+1/s) = 1/(1+s). So P(T > s) = P(1/T > s) for all s > 0. ∎
4. Equivalently: D = G₀ − G₁ ~ Logistic(0,1) is symmetric about 0. The ratio and product rules compare D to thresholds c and −c respectively, giving identical probabilities.

For M ≥ 3, the product rule probabilities have a closed form via inclusion-exclusion:
```
P_product(k) = Σ_{S⊆{0,...,M-1}\{k}} (-1)^|S| / (1 + Σ_{j∈S} aₖ/aⱼ)
```
For a = (0.5, 0.3, 0.2): P_product(0) = 1 − 1/(1+5/3) − 1/(1+5/2) + 1/(1+5/3+5/2) ≈ 0.533 ≠ 0.500 = a₀. The symmetry is an M = 2 accident: for M = 2, the only comparison is pairwise, and T vs 1/T have identical exceedance. For M ≥ 3, the joint order statistics break this symmetry.

**BLD interpretation**: L→B compensation selects the outcome with maximum structural leverage — the branch where system weight (L) most exceeds observer alignment (B). This is the compensation principle applied to single events: L determines B where L most exceeds B.

**Compensation direction**: When |O⟩ is near pointer state |Oⱼ⟩, B_j is large (high alignment), making L_j/B_j small. The selection favors outcomes FARTHEST from the observer's current alignment — where B is weakest relative to L. Confirmed numerically: for M = 2 with |O(θ)⟩ interpolating between pointer states, the switching angle θ* = arctan(√(|α₁|²/|α₀|²)) matches prediction exactly.

**Cross-domain connection**: The selection rule is mathematically identical to the Gumbel-Softmax trick (Jang et al. 2017, Maddison et al. 2017) used in ML for differentiable discrete sampling at temperature τ = 1. In ML, Gumbel noise is added artificially to logits. In BLD, the observer's Haar-random microstate provides the noise naturally via the Dirichlet-Gamma decomposition. Both are instances of L→B compensation: continuous structure determining discrete partition.

## τ = 1 Is Structurally Forced

The Gumbel-max trick at temperature τ gives a generalized selection rule:

```
f_τ(|O⟩) = argmax_k |αₖ|^{2/τ} / |⟨Oₖ|O⟩|²

This yields P(k) = |αₖ|^{2/τ} / Σⱼ |αⱼ|^{2/τ}
```

Only τ = 1 gives P(k) = |αₖ|². All other τ values give systematically different distributions:
- τ < 1: sharpened (favors dominant outcome)
- τ > 1: flattened (more uniform)

Verified numerically: τ ∈ {0.5, 0.8, 1.0, 1.2, 1.5, 2.0, 3.0} all match their predicted |αₖ|^{2/τ}/Z distributions. Only τ = 1.0 passes the Born rule χ² test.

**Why τ = 1 and not something else**: The selection rule uses the raw ratio |αₖ|²/|⟨Oₖ|O⟩|². There is no temperature parameter in the physics — the overlaps |⟨Oₖ|O⟩|² come directly from the Haar-random observer state. The exponent 2 in |αₖ|² comes from K = 2 (bidirectional observation, [Killing Form](../lie-theory/killing-form.md)). The exponent 2 in |⟨Oₖ|O⟩|² comes from the same K = 2 applied to the observer-pointer alignment. The ratio L/B = |αₖ|²/|⟨Oₖ|O⟩|² has matching exponents, giving τ = 1 identically.

## Joint Measurement: Tensor Product Observer

For correlated (entangled) measurements, the selection rule extends to the tensor product space:

```
For system |ψ⟩_AB = Σ_{kj} α_{kj} |k⟩_A|j⟩_B:

Observer: |O⟩ ∈ C^{N_A × N_B}   (single joint observer)
Pointer states: |O_{kj}⟩ = |O_{Ak}⟩ ⊗ |O_{Bj}⟩   (tensor products)
Overlaps: X_{kj} = |⟨O_{kj}|O⟩|²   (Dirichlet in product space)

f(|O⟩) = argmax_{kj} |α_{kj}|² / X_{kj}   →   P(kj) = |α_{kj}|²
```

Verified numerically:
- Bell state (|00⟩+|11⟩)/√2: P(00) = P(11) = 0.50, P(01) = P(10) = 0 (exact)
- Non-maximal √0.7|00⟩+√0.3|11⟩: P(00) = 0.70, P(11) = 0.30 (Born exact)
- GHZ-like 3-party state: Born exact for all components

**Why factored observers fail**: Two independent observers |O_A⟩ ∈ C^{N_A}, |O_B⟩ ∈ C^{N_B} with overlaps X_{Ak} × X_{Bj} do NOT give Dirichlet components in the product space. Products of independent Dirichlet components are not Dirichlet, so the Gumbel-max trick does not apply. For the symmetric Bell state, P(00) = P(11) = 0.5 is saved by symmetry. For non-symmetric states (e.g., √0.7|00⟩+√0.3|11⟩), factored observers give P(00) ≈ 0.64 instead of 0.70 — systematic error.

**BLD interpretation**: Entanglement means the system's L-structure connects subsystems. The observation that resolves this L-structure must itself be a single structure in the product space — a joint observer, not two independent ones. This is the tensor product structure of quantum mechanics doing real work: correlated L requires correlated B-partition, which requires a single observation event in the joint space.

## Factored Observer: Analytical Error Formula

The systematic error from factored (independent) observers has a closed form. For diagonal state √a₀₀|00⟩ + √a₁₁|11⟩ with two independent observers:

1. Each observer's Dirichlet normalizations S_A, S_B cancel in the argmax (positive constants), leaving a comparison of raw Exp(1) variables. The result is N-independent.
2. Taking logs: the comparison becomes P(L_A + L_B > −c) where L_A = G_{A0} − G_{A1}, L_B = G_{B0} − G_{B1} are i.i.d. Logistic(0,1), and c = log(a₀₀/a₁₁).
3. The CDF of L_A + L_B (sum of two i.i.d. Logistic distributions) is computed by convolution:

```
P_factored(00) = (1 − r + r·log r) / (1 − r)²
where r = a₁₁/a₀₀
```

**Limiting cases**: r → 0 gives P → 1; r → 1 gives P → 1/2 (by L'Hôpital); r = 1 gives P = 1/2 exactly (symmetric case).

**Verified**: For a₀₀ = 0.7, a₁₁ = 0.3: r = 3/7, P_factored ≈ 0.638 (vs Born 0.70). The error |P_factored − P_Born| grows with asymmetry, reaching ~0.09 at a₀₀ = 0.85 before declining. Matches Monte Carlo at all tested a₀₀ ∈ {0.55, 0.60, ..., 0.90} within 0.006.

**Why factored observers produce this specific error**: A single Logistic comparison yields exact Born statistics (the Gumbel-max trick). But the sum of two i.i.d. Logistic(0,1) is NOT Logistic — convolution spreads the distribution, reducing its sensitivity to the threshold c. The result always biases toward P = 1/2 (the symmetric case), underestimating the dominant outcome's probability.

## Pointer Non-Orthogonality: Testable Prediction

**On pointer orthogonality** (quantified prediction): The Born rule is exact when pointer states are orthogonal (the Dirichlet-Gamma argument requires this). Pointer orthogonality follows from einselection: H_int eigenstates decohere non-eigenstates at rate > ΔE/ℏ (Claim 6 of [Wave Function Collapse](wave-function-collapse.md)). For macroscopic apparatus with strong decoherence, pointer states are highly orthogonal. For few-body systems with weak decoherence, pointer non-orthogonality produces measurable deviations from Born statistics:

For M = 2 with |O₁⟩ = √ε|O₀⟩ + √(1−ε)|O₀⊥⟩ and Haar-random |O⟩, the deviation has an exact N-independent integral formula. The Dirichlet normalization S cancels in the argmax (as in the orthogonal case), so the result depends only on the 2D subspace spanned by {|O₀⟩, |O₀⊥⟩}. Projecting onto this subspace with z₀ = ⟨O₀|O⟩, z₂ = ⟨O₀⊥|O⟩ (i.i.d. standard complex Gaussians), the selection rule reduces to a quadratic in t = |z₂/z₀|:

```
Q(t,θ) = (1−ε)t² + 2√(ε(1−ε))·t·cos θ + ε − a₁/a₀ > 0

P(f=0) = (1/2π) ∫₀²π I(θ) dθ       [EXACT, N-independent]
```

where I(θ) has three cases (A = 1−ε, B = 2√(ε(1−ε))·cos θ, C = ε − a₁/a₀, disc = B² − 4AC):
- disc < 0: I(θ) = 1 (no real roots, Q > 0 always since A > 0)
- disc ≥ 0, C ≤ 0: I(θ) = 1/(1 + t₊²) where t₊ = (−B + √disc)/(2A) (Vieta: roots have opposite signs)
- disc ≥ 0, C > 0: Vieta gives roots with same sign. If t₊ ≤ 0: I(θ) = 1. If t₊ > 0: I(θ) = t₋²/(1+t₋²) + 1/(1+t₊²) where t₋ = (−B − √disc)/(2A).

**At ε = 0**: C = −a₁/a₀ < 0, B = 0, t₊ = √(a₁/a₀), I(θ) = a₀ for all θ. So P(f=0) = a₀ (Born rule recovered).

**Taylor expansion**: Δ(ε) = c₁·ε + c₂·ε² + O(ε³) where:
```
c₁ = a₀·a₁·(a₀ − a₁)
```
For α² = (0.7, 0.3): c₁ = 0.7 × 0.3 × 0.4 = 0.084. Confirmed by finite differences on the integral. The coefficient c₁ vanishes when a₀ = a₁ (no preferred direction to bias toward) and when either aₖ = 0 (trivial case). Approximate polynomial fit over [0, 0.5]: Δ(ε) ≈ 0.093ε² + 0.078ε (RMS = 0.0017). Exact integral verified against Monte Carlo for ε ∈ [0, 0.95].

**Physical measurement simulation**: The formula is also verified against pointer states generated by physical interaction Hamiltonians H_int = σ_z ⊗ P (P = random Hermitian), where the overlap ε emerges from the coupling strength gτ rather than being constructed as a test parameter. 192 test points across 4 apparatus dimensions (N_A ∈ {4,8,16,32}), 36 random Hamiltonians, and 8 coupling strengths all match the integral formula within 3σ (max |P_MC − P_int| = 0.004). The formula depends only on ε, not on how pointer states were generated — confirmed for pointer states related by exp(2igτP), not just by the √ε construction.

The deviation always biases toward the dominant outcome (the outcome with larger |αₖ|²). For M = 3 with pairwise overlap ε, Born rule fails chi-squared test at ε ≥ 0.10, with chi-squared growing rapidly (12.4 at ε=0.10, 214.6 at ε=0.30). This is testable in controlled quantum systems with weak decoherence — a falsifiable prediction unique to BLD.

## What This Resolves

| Question | Answer |
|----------|--------|
| Why THIS outcome? | L→B: full L-structure (system + observer) determines B-partition |
| Why does it look random? | Observer microstate varies, we don't track it |
| Why |ψ|² distribution? | K=2 on joint system + observer averaging |
| Why τ = 1 exactly? | K=2 gives matching exponents in L/B ratio; no free parameter |
| Why tensor product? | Correlated L-structure requires single joint observation |
| Is collapse real? | L→B compensation IS the event; "collapse" is L determining B |

## Testability

Three levels of verification:

1. **Statistics** (CONFIRMED): Born rule P(k) = |αₖ|² from Haar-averaged selection rule. Confirmed numerically for M ∈ {2,3,4,5,8,10,16,20,50} at ALL N ≥ M, including M = N (tightest case). The result is exact (Dirichlet decomposition), not approximate. Degenerate amplitudes (αₖ = 0), complex phases, and large M all verified.

2. **Determinism** (VERIFIED IN SIMULATION): Same |O⟩ always gives same k. Controlled |O⟩ → predictable k with switching angles matching theory. Demonstrated in test_controlled_observer.py.

3. **Hardware determinism** (STRUCTURALLY INACCESSIBLE): Macroscopic observer has N ~ 10²³ DOF. Controlling |O⟩ requires measuring the observer without disturbing it — measurement on the observer creates a new +1 (the observer-inside-measurement constraint appears as the +1 in α⁻¹ = n×L + B + 1 + 2/B). Same structural reason as the second law: deterministic laws, incomputable individual outcomes.

---

## References

### Internal
- [Born Rule](born-rule.md) — Ensemble derivation: P = |ψ|² from K=2 bidirectional alignment
- [Killing Form](../lie-theory/killing-form.md) — Bidirectional observation cost (K=2)
- [Compensation Principle](../foundations/structural/compensation-principle.md) — L→B works, B→L fails (PROVEN)
- [Completeness Proof](../foundations/proofs/completeness-proof.md) — Observers ARE BLD structures
- [Schrödinger Derivation](schrodinger-derivation.md) — Observers have quantum states
- [Path Integral](path-integral.md) — Specific Hamiltonians from BLD structure
- [Wave Function Collapse](wave-function-collapse.md) — Collapse = L→B compensation

### External
- [Popescu, Short, Winter (2006)](https://doi.org/10.1038/nphys444) — Quantum typicality from entanglement
- [Jang et al. (2017)](https://arxiv.org/abs/1611.01144) — Gumbel-Softmax trick in ML
- [Maddison et al. (2017)](https://arxiv.org/abs/1611.00712) — Concrete distribution
