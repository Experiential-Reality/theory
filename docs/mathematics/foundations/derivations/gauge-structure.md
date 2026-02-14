---
status: DERIVED
layer: 1
key_result: "Gauge algebra = u(4) = su(4) ⊕ u(1) (Pati-Salam); |Y_lep|/|Y_quark| = 3; e_R in S²(8_v)"
depends_on:
  - equation-of-motion.md
  - octonion-derivation.md
  - ../../lie-theory/killing-form.md
used_by:
  - ../../particle-physics/e7-derivation.md
  - weak-origin.md
  - generation-hierarchy.md
---

## Summary

**Gauge structure of so(8) — from BLD to Pati-Salam:**

1. The 12 gauge generators (su(3) + su(2) + u(1)) generate u(4) = su(4) ⊕ u(1), not the SM direct product — [§1](#1-the-gauge-algebra-is-u4)
2. SM hypercharge from centralizer of su(3): |Y_lep|/|Y_quark| = 3 exact — [§2](#2-sm-hypercharge)
3. The quaternionic su(2) mixes quarks and leptons — it is leptoquark, not weak — [§3](#3-the-su2-is-leptoquark)
4. e_R found in S²(8_v) = 35_v with |Y| = 1, from lepton ⊗ lepton — [§4](#4-e-r-in-s²8-v)
5. The complement of u(4) is 12-dim, all color triplets: |Y| = {2/3, 1/3} = u_R, d_R — [§5](#5-the-complement)

| Result | Formula | Value | Test File |
|--------|---------|-------|-----------|
| Gauge algebra | 12 gens → u(4) = su(4) ⊕ u(1) | dim 16 | test_eom_hypercharge |
| Charge ratio | \|Y_lep\|/\|Y_quark\| | 3 exact | test_eom_hypercharge |
| Centralizer | centralizer of su(3) in so(8) | dim 2 (abelian) | test_eom_hypercharge |
| e_R location | S²(8_v), su(3) singlet | \|Y\| = 1 | test_eom_hypercharge |
| No weak su(2) | centralizer dim < 3 | impossible | test_eom_hypercharge |

# Gauge Structure: u(4) from so(8)

## Abstract

The [equation of motion](equation-of-motion.md) establishes so(8) as the dynamical algebra. Here we derive its internal gauge structure. The 12 generators conventionally identified as su(3) × su(2) × u(1) do not form a direct product — they generate u(4) = su(4) ⊕ u(1), the Pati-Salam color-lepton algebra. The SM hypercharge emerges from the centralizer of su(3), with the charge ratio |Y_lep|/|Y_quark| = 3 forced by octonion geometry. The right-handed electron (e_R, |Y| = 1) is absent from all fundamental and adjoint representations of so(8), but appears in S²(8_v) = 35_v as a lepton ⊗ lepton state.

## 1. The Gauge Algebra is u(4)

From [octonion-derivation.md](octonion-derivation.md), the gauge generators of so(8) decompose as:

- **su(3)**: 8 generators from G₂ stabilizer of e₁ (octonion derivations preserving a fixed imaginary unit)
- **su(2)**: 3 generators from quaternionic left multiplication on Im(ℍ) ⊂ Im(𝕆)
- **u(1)**: 1 generator E₀₁ (rotation in the e₀-e₁ plane)

These 12 generators span a subalgebra of so(8). But they do not close as a direct product.

**Cross-brackets leak.** Computing [su(3), su(2)] gives nonzero elements. The su(3) and su(2) generators do not commute — they cannot be independent factors of a direct product.

**Closure at dimension 16.** Starting from the 12 generators and computing all iterated brackets, the algebra closes at dimension 16. The [Killing form](../../lie-theory/killing-form.md) of this 16-dim algebra has:

- 15 equal nonzero eigenvalues (-8): the simple part = su(4)
- 1 zero eigenvalue: the center = u(1)

Therefore: **gauge algebra = u(4) = su(4) ⊕ u(1)**.

**The Pati-Salam pattern.** SU(4) ⊃ SU(3) × U(1)_{B-L}. The fourth color is lepton number. The su(3) color algebra embeds naturally in su(4) as a subalgebra, with the orthogonal u(1) being baryon-minus-lepton number.

## 2. SM Hypercharge

The centralizer of su(3) in so(8) — all generators commuting with the 8 color generators — is 2-dimensional:

```
centralizer = span{E₀₁, J}
```

where J = -(1/√3)(E₂₄ + E₃₇ + E₅₆). The index pairs (2,4), (3,7), (5,6) are the Fano triple complements through e₁. Both generators are abelian: [E₀₁, J] = 0.

**B-L hypercharge.** The combination

```
Y_{B-L} = (√3/2) E₀₁ + (1/2) J
```

commutes with su(3) but not su(2). The ratio \|Y_lep\|/\|Y_quark\| = 3 is exact, forced by the number of Fano triples through e₁ (three triples, each contributing one quark color).

**SM normalization.** Y_SM = Y_{B-L}/√3 gives the Standard Model hypercharge assignments:

| Rep | Lepton \|Y_SM\| | Quark \|Y_SM\| | Ratio |
|-----|-----------------|----------------|-------|
| 8_v | 1/2 | 1/6 | 3 |
| 8_s | 1/2 | 1/6 | 3 |
| 8_c | 0 | 1/3 | — |

- **8_v, 8_s** (left-handed): |Y| = {1/2 (lepton), 1/6 (quark)} — matches SM left-handed doublets
- **8_c** (right-handed): |Y| = {1/3, 0} — matches right-handed d-quarks and neutrinos

**Signed charges and Pati-Salam 4 ⊕ 4̄.** The u(4) center Y_c has eigenvalues ±i/2 (×4 each) on 8_v, splitting it into particle (4) and antiparticle (4̄):

- **4**: Y_SM = {-1/2 (lepton), -1/6 (quark ×3)} = 1_{-1/2} ⊕ 3_{-1/6}
- **4̄**: Y_SM = {+1/6 (antiquark ×3), +1/2 (antilepton)} = 3̄_{+1/6} ⊕ 1_{+1/2}

Within each 4, lepton and quarks carry the same sign. This is the Pati-Salam fundamental: lepton = fourth color.

**Triality invariant.** Tr(Y_SM²) is the same for all three 8-dim representations (8_v, 8_s, 8_c), as required by the S₃ outer automorphism of D₄.

## 3. The su(2) is Leptoquark

The quaternionic su(2) generators embed entirely inside su(4) (zero projection onto the u(1) center). The su(2) acts on the fundamental 4 of su(4) as 4 → 2 ⊕ 1 ⊕ 1: one (lepton, quark) doublet and two singlets. The Casimir eigenvalues on the 4 are {-3, -3, 0, 0}.

**Key test.** The su(2) Casimir is not diagonal in the su(3) eigenbasis (off-diagonal norm ≈ 1.05). This means su(2) **mixes quarks and leptons**. It is a leptoquark gauge symmetry, not the SM weak SU(2)_L.

**No su(2) commutes with su(3) in so(8).** The centralizer of su(3) is 2-dimensional (§2). Since dim(su(2)) = 3 > 2, no su(2) subalgebra can fit in the centralizer. The SM gauge group SU(3) × SU(2) × U(1) as a direct product cannot be embedded in SO(8).

This is the fundamental structural constraint: u(4) is the maximal gauge algebra, and any su(2) inside su(4) necessarily does not commute with su(3). The SM weak SU(2) must originate elsewhere — see [weak-origin.md](weak-origin.md).

## 4. e_R in S²(8_v)

The right-handed electron requires \|Y_SM\| = 1. Searching all fundamental and adjoint representations of so(8):

| Representation | dim | Max \|Y\| | e_R? |
|---------------|-----|-----------|------|
| 8_v | 8 | 1/2 | No |
| 8_s | 8 | 1/2 | No |
| 8_c | 8 | 1/3 | No |
| adjoint 28 | 28 | 2/3 | No |

\|Y\| = 1 is absent from all fundamental representations. The right-handed electron requires a **higher representation**.

**Symmetric square.** The symmetric tensor product S²(8_v) = 35_v + 1 decomposes under su(3) × u(1)_Y as:

| Multiplet | dim | \|Y_SM\| | SM match |
|-----------|-----|----------|----------|
| (1, 1) | 2 | 1 | **e_R, ē_R** |
| (3, 2/3) | 6 | 2/3 | — |
| (3, 1/3) | 6 | 1/3 | — |
| (6, 1/3) | 12 | 1/3 | — |
| (8, 0) | 8 | 0 | — |
| (1, 0) | 2 | 0 | trace |

The \|Y\| = 1 states are su(3) singlets arising from lepton ⊗ lepton: Y = 1/2 + 1/2 = 1.

**Triality asymmetry.** S²(8_v) and S²(8_s) both contain \|Y\| = 1 states. S²(8_c) does not (max \|Y\| = 2/3). This is consistent with 8_v, 8_s being left-handed sectors (whose symmetric product can yield e_R) and 8_c being right-handed.

## 5. The Complement

The complement of u(4) in so(8) has dimension 28 - 16 = 12. All 12 complement generators are color triplets or antitriplets:

| Multiplet | dim | \|Y_SM\| | SM match |
|-----------|-----|----------|----------|
| color triplet | 6 | 2/3 | u_R (right-handed up quarks) |
| color antitriplet | 6 | 1/3 | d_R (right-handed down quarks) |

The full adjoint 28 therefore decomposes as:

```
28 = 16 (u(4): gauge) + 6 (|Y|=2/3: u_R) + 6 (|Y|=1/3: d_R)
```

The complement transforms under the adjoint action of u(4) — these are the leptoquark gauge bosons of Pati-Salam unification, mediating lepton-quark transitions at the GUT scale.

## Conclusion

The gauge structure of so(8) is not the SM direct product but the Pati-Salam algebra u(4) = su(4) ⊕ u(1). This is a stronger unification: quarks and leptons share a single su(4) multiplet, with the charge ratio 3:1 forced by octonion geometry. The right-handed electron requires the symmetric square S²(8_v), indicating composite or higher-representation structure. The absence of any su(2) commuting with su(3) inside so(8) drives the identification of weak SU(2) with quaternion derivations in [weak-origin.md](weak-origin.md).

## Open Questions

1. **SU(4) → SU(3) × U(1)_{B-L} breaking mechanism.** The Pati-Salam pattern is algebraically clear, but the breaking that separates quarks from leptons at low energy is not yet derived from BLD.
2. **Is e_R in S²(8_v) a composite state?** The symmetric product suggests a bound-state interpretation — e_R as lepton ⊗ lepton. This would have implications for the electron mass derivation.

## References

### External

1. J. C. Pati, A. Salam, "Lepton number as the fourth 'color'", *Phys. Rev. D* **10**, 275 (1974).

### Internal

- [Equation of Motion](equation-of-motion.md) — dynamical framework, curvature, geodesics
- [Octonion Derivation](octonion-derivation.md) — G₂ → su(3), Fano triples
- [Killing Form](../../lie-theory/killing-form.md) — bi-invariant metric on so(8)
- [Weak Origin](weak-origin.md) — where SU(2)_L actually comes from
- [Generation Hierarchy](generation-hierarchy.md) — mass scale from Casimir bridge
