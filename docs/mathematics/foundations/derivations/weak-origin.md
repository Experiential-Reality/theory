---
status: DERIVED
layer: 1
key_result: "Weak SU(2) = der(ℍ) = so(3), lives in E₇ not so(8); S = K² + (n-1)² Pythagorean"
depends_on:
  - equation-of-motion.md
  - gauge-structure.md
  - octonion-derivation.md
used_by:
  - ../../particle-physics/e7-derivation.md
  - ../../../meta/proof-status.md
---

## Summary

**Origin of the weak force — from quaternion derivations to E₇:**

1. der(ℍ) = so(3) ≅ su(2): the weak gauge algebra is the derivation algebra of the quaternions — [§1](#1-derℍ--so3--weak-gauge-algebra)
2. Division algebra tower gives gauge dimensions [0, 1, 3, 8], sum = 12 — [§2](#2-division-algebra-tower)
3. S = K² + (n-1)² = 4 + 9 = 13: Pythagorean decomposition with unique solution — [§3](#3-pythagorean-s-decomposition)
4. E₇ Tits construction places weak SU(2) above so(8): 3 + 52 + 78 = 133 — [§4](#4-e₇-tits-construction)

| Result | Formula | Value | Test File |
|--------|---------|-------|-----------|
| Weak gauge dim | dim(der(ℍ)) | 3 = dim(SU(2)) | test_eom_weak |
| Gauge tower | [0, 1, 3, 8] | sum = 12 | test_eom_weak |
| Pythagorean S | K² + (n-1)² | 13, unique | test_eom_weak |
| E₇ dimension | 3 + 52 + 78 | 133 | test_eom_weak |

# Weak Origin: der(ℍ) and E₇

## Abstract

[Gauge structure](gauge-structure.md) shows that no su(2) commutes with su(3) inside so(8) — the SM weak force cannot come from the dynamical algebra alone. Here we derive its origin: the weak SU(2) is the derivation algebra of the quaternions, der(ℍ) = so(3) ≅ su(2). This algebra lives in E₇ via the Tits construction, not inside so(8). The structural constant S = 13 decomposes as a Pythagorean sum K² + (n-1)² = 4 + 9, linking observation cost to weak force dimension and yielding the Weinberg angle sin²θ_W = 3/S.

## 1. der(ℍ) = so(3) = Weak Gauge Algebra

A derivation of an algebra A is a linear map D: A → A satisfying the Leibniz rule D(xy) = D(x)y + xD(y). For the quaternions ℍ = span{1, i, j, k}, the derivation algebra is computed by:

1. Writing the multiplication table as a 4×4×4 structure constant tensor c_{ab}^d
2. Imposing the Leibniz constraint: D(e_a · e_b) = D(e_a) · e_b + e_a · D(e_b) for all basis elements
3. This gives a 27×9 linear system (27 constraints on 9 entries of a 3×3 matrix acting on Im(ℍ))

The constraint matrix has rank 6, so the null space has dimension **3**.

**Inner derivations generate der(ℍ).** For a ∈ Im(ℍ), the map D_a(x) = ax - xa is a derivation. Explicitly:

```
D_i(i) = 0,    D_i(j) = 2k,    D_i(k) = -2j
D_j(i) = -2k,  D_j(j) = 0,     D_j(k) = 2i
D_k(i) = 2j,   D_k(j) = -2i,   D_k(k) = 0
```

Each D_a rotates the two imaginary units orthogonal to a — these are so(3) rotations. The Lie bracket [D_i, D_j] ∝ D_k is cyclic, with 6 nonzero structure constants of equal magnitude. The Killing form is proportional to the identity (semisimple, compact).

**The key identity:** n - 1 = 3 = dim(Im(ℍ)) = dim(der(ℍ)) = dim(SU(2)). The number of spatial dimensions equals the weak gauge dimension.

## 2. Division Algebra Tower

Each division algebra contributes a gauge symmetry through its derivation algebra:

| Algebra | dim | der(A) | dim(der) | Gauge group | dim | Force |
|---------|-----|--------|----------|-------------|-----|-------|
| ℝ | 1 | 0 | 0 | — | 0 | gravity |
| ℂ | 2 | 0 | 0 | U(1) | 1 | EM |
| ℍ | 4 | so(3) | 3 | SU(2) | 3 | weak |
| 𝕆 | 8 | G₂ | 14 | SU(3) | 8 | strong |

**Derivation dimensions:** [0, 0, 3, 14]. The gauge dimensions [0, 1, 3, 8] differ because:

- ℂ has der(ℂ) = 0 but the unit circle S¹ gives U(1) with 1 generator
- 𝕆 has der(𝕆) = G₂ with 14 generators, but fixing a reference direction in Im(𝕆) breaks G₂ to its stabilizer SU(3) with 8 generators (14 - 8 = 6 = dim(S⁶))

**Total gauge dimension:** 0 + 1 + 3 + 8 = **12** = dim(su(3) × su(2) × u(1)). The SM gauge group dimension is the sum over the division algebra tower.

## 3. Pythagorean S Decomposition

The structural constant S = (B - n)/n = 13 admits a Pythagorean decomposition:

```
S = K² + (n-1)² = 4 + 9 = 13
```

This yields two mixing angles as fractions of S:

- **Weinberg angle:** sin²θ_W = dim(SU(2))/S = 3/13 = 0.2308 (structural value)
- **Solar neutrino mixing:** sin²θ₁₂ = K²/S = 4/13 = 0.3077

With the L cost correction: sin²θ_W = 3/S + K/(nLB) = 0.231215, matching the PDG value 0.23121 ± 0.00004.

**Uniqueness.** Sweeping all parameter combinations n = 2..20, K = 1..5 with B = (n-1)(L-1) - 1 and S = (B-n)/n: only **(n, K) = (4, 2)** satisfies S = K² + (n-1)². The Pythagorean identity is unique to BLD.

## 4. E₇ Tits Construction

The Tits construction builds exceptional Lie algebras from pairs of division algebras and Jordan algebras:

```
E₇ = der(ℍ) + der(J₃(𝕆)) + Im(ℍ) ⊗ J₃(𝕆)₀
   = 3        + 52          + 78
   = 133
```

where:

- **der(ℍ) = 3**: the weak gauge algebra from §1
- **der(J₃(𝕆)) = F₄ = 52 = B - n**: the exceptional Jordan algebra's automorphism group. Note 52 = B - n = 56 - 4.
- **Im(ℍ) ⊗ J₃(𝕆)₀ = 3 × 26 = 78**: three copies of the traceless Jordan matrices. Note 26 = 27 - 1 (one generation minus observer).

BLD constants appear throughout: fund(E₇) = 56 = B.

**E₈ branching.** At the next level:

```
E₈ = n(B + n + K) = 4 × 62 = 248
E₈ → E₇ × SU(2): 248 = 133 + 3 + 2×56
```

The E₈ decomposition contains an explicit SU(2) factor of dimension 3 = dim(der(ℍ)).

**Resolution of the paradox.** From [gauge-structure.md](gauge-structure.md), no su(2) commutes with su(3) inside so(8) (centralizer dimension = 2 < 3). The weak SU(2) lives in E₇ as der(ℍ), a **summand** of the Tits construction — above so(8), not inside it. For comparison, E₆ = der(ℂ) + F₄ + Im(ℂ) × J₃(𝕆)₀ = 0 + 52 + 26 = 78 has der(ℂ) = 0: no weak force at the E₆ level.

## Conclusion

The complete gauge structure of BLD spans two algebraic levels:

- **so(8) level:** u(4) = su(4) ⊕ u(1) — Pati-Salam color-lepton unification ([gauge-structure.md](gauge-structure.md))
- **E₇ level:** der(ℍ) = so(3) ≅ su(2) — weak gauge from quaternion derivations

The division algebra tower provides all four forces, with the Pythagorean identity S = K² + (n-1)² connecting the structural constant to the Weinberg angle. The BLD constants B = 56, n = 4, K = 2 appear as dimensions of exceptional algebraic structures (fund(E₇), F₄ = B - n, E₈ = n(B + n + K)), indicating deep compatibility between the BLD framework and the exceptional algebra hierarchy.

## Open Questions

1. **Chirality.** Why is the weak SU(2) left-handed? The triality → chirality connection (8_v/8_s vs 8_c) provides the left/right distinction, but the mechanism coupling der(ℍ) specifically to left-handed representations is not yet derived.
2. **Coupling mechanism.** How does der(ℍ) in E₇ couple to the fermion representations in so(8)? The Tits construction places them in the same algebra, but the physical coupling requires a concrete embedding.
3. **Electroweak breaking.** The mechanism SU(2)_L × U(1)_Y → U(1)_EM from BLD structural principles remains open.

## References

### External

1. J. Tits, "Algèbres alternatives, algèbres de Jordan et algèbres de Lie exceptionnelles", *Indag. Math.* **28**, 223–237 (1966).

### Internal

- [Equation of Motion](equation-of-motion.md) — dynamical framework on so(8)
- [Gauge Structure](gauge-structure.md) — u(4) = su(4) ⊕ u(1), no weak su(2) in so(8)
- [Octonion Derivation](octonion-derivation.md) — G₂ → su(3), division algebra structure
- [Generation Hierarchy](generation-hierarchy.md) — Casimir bridge, mass scale from S
- [E₇ Derivation](../../particle-physics/e7-derivation.md) — E₇ structure in particle physics
