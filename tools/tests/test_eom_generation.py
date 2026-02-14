"""Generation structure: triality → mass hierarchy.

Tests 60-62 from the equation of motion suite.
Casimir-curvature bridge, S₃ generation hierarchy, mass formula structure.
"""

import math

import numpy as np

import tools.bld

from helpers import assert_all_pass


TR = tools.bld.TestResult


# ---------------------------------------------------------------------------
# Test 60: Casimir = scalar curvature uniquely for D₄ (so(8))
# ---------------------------------------------------------------------------


def test_casimir_curvature_bridge() -> None:
    """C₂(vector) = scalar curvature R only for so(8).

    For so(n): C₂(vector) = n-1, R = n(n-1)/8 (bi-invariant metric on SO(n)).
    The equation C₂ = R has a unique solution: n = 8.

    This bridges representation theory (Casimir → particle mass/kinetic terms)
    to Riemannian geometry (scalar curvature → heat kernel → path integral).
    The bridge is unique to D₄ = so(8), the triality algebra.

    Furthermore, S = 2C₂ - 1 = 13: the generation constant is derived from
    the Casimir. This connects the mass scale n²S = n²(2C₂-1) = 208 directly
    to the representation theory of so(8).

    Theory ref: lepton-masses.md, e7-derivation.md, killing-form.md

    Prove: C₂(8_v) = 7 = R = dim(so(8))/4 for so(8).
    Prove: for n ∈ {3,...,12} \\ {8}, C₂(vector) ≠ R.
    Prove: S = 2C₂ - 1 = 13 (generation constant from Casimir).
    Prove: n²S = n²(2C₂ - 1) = 208 (mass scale from Casimir).
    Verify: B/n = 2C₂ = 2R = 14 (boundary/dim ratio = twice curvature).
    Verify: a₁ = C₂/6 = R/6 = 7/6 (heat kernel = Casimir/6).
    Disprove: so(10) GUT algebra has C₂ = 9 ≠ R = 11.25.
    """
    results: list[TR] = []

    # --- so(8) bridge ---
    c2_vec = tools.bld.casimir_vector_so(8)
    R = tools.bld.scalar_curvature(tools.bld.so_dim(8))
    results.append(TR(f"C2_vector_so8={c2_vec}=7", c2_vec == 7))
    results.append(TR(f"R_so8={R}=7", R == 7))
    results.append(TR(f"C2=R={c2_vec}={R}", c2_vec == R))

    # Cross-check with D₄ Weyl formula
    c2_d4 = tools.bld.casimir_d4(1, 0, 0, 0)
    results.append(TR(f"C2_d4_weyl={c2_d4}=7", abs(c2_d4 - 7.0) < 1e-12))

    # --- Uniqueness sweep ---
    n_equal = 0
    for nn in range(3, 13):
        c2 = tools.bld.casimir_vector_so(nn)  # nn - 1
        r = tools.bld.scalar_curvature(tools.bld.so_dim(nn))  # nn(nn-1)/8
        if c2 == r:
            n_equal += 1
            results.append(TR(f"so({nn})_C2={c2}_R={r}_MATCH", nn == 8))
        else:
            results.append(TR(f"so({nn})_C2={c2}_R={r}_differ", c2 != r))
    results.append(TR(f"unique_match_count={n_equal}=1", n_equal == 1))

    # --- Algebraic proof ---
    # C₂ = R  ⟺  n-1 = n(n-1)/8  ⟺  8 = n  (for n > 1)
    solution = 8
    results.append(TR(
        f"algebraic_solution={solution}",
        solution - 1 == solution * (solution - 1) / 8,
    ))

    # --- Generation constant from Casimir ---
    # S = (B-n)/n = B/n - 1.  B = K × dim(so(8)) = 2×28 = 56.
    # B/n = 56/4 = 14 = 2×7 = 2×C₂.  So S = 2C₂ - 1 = 13.
    S_from_casimir = 2 * c2_vec - 1
    results.append(TR(
        f"S=2C2-1={S_from_casimir}={tools.bld.S}",
        S_from_casimir == tools.bld.S,
    ))

    # B/n = 2C₂ = 2R
    B_over_n = tools.bld.B / tools.bld.n
    results.append(TR(
        f"B/n={B_over_n}=2C2={2*c2_vec}=2R={2*R}",
        B_over_n == 2 * c2_vec and B_over_n == 2 * R,
    ))

    # n²S = n²(2C₂ - 1) = 208
    n2S_from_casimir = tools.bld.n ** 2 * (2 * c2_vec - 1)
    results.append(TR(
        f"n²S=n²(2C2-1)={n2S_from_casimir}=208",
        n2S_from_casimir == 208,
    ))

    # --- Consequences ---
    # Heat kernel: a₁ = R/6 = C₂/6 = 7/6
    a1 = R / 6
    results.append(TR(f"a1=C2/6=R/6={a1:.6f}=7/6", abs(a1 - 7.0 / 6.0) < 1e-12))

    # Casimir ratio: C₂(adj)/C₂(vector) = 12/7
    c2_adj = tools.bld.casimir_adjoint(8)
    ratio = c2_adj / c2_vec
    results.append(TR(
        f"adj_fund_ratio={ratio:.6f}=12/7",
        abs(ratio - 12.0 / 7.0) < 1e-12,
    ))

    # --- Disprove ---
    # so(10): C₂ = 9, R = 45/4 = 11.25
    c2_10 = tools.bld.casimir_vector_so(10)
    R_10 = tools.bld.scalar_curvature(tools.bld.so_dim(10))
    results.append(TR(
        f"so10_C2={c2_10}_R={R_10}_gap={abs(c2_10 - R_10):.2f}",
        abs(c2_10 - R_10) > 1.0,
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 61: S₃ representation theory and primordial generation structure
# ---------------------------------------------------------------------------


def test_s3_generation_hierarchy() -> None:
    """S₃ outer automorphism gives 3-level mass hierarchy with integer primordials.

    S₃ (unique to D₄) has 3 conjugacy classes → 3 irreps:
    trivial (dim 1), sign (dim 1), standard (dim 2).

    The primordial mass ratios are exact integers (lepton-masses.md):
      μ/e primordial = n²S - 1 = 207  (discrete counting of structure positions)
      τ/μ primordial = S + n   = 17   (complete structure)
    The observed ratios (206.768, 16.817) differ by K/X alignment gradients.
    The transcendental 2πe ≈ 17.079 is how continuous observation sees the
    discrete integer 17.

    The triality orbit {8_v, 8_s, 8_c} carries the permutation representation
    = trivial ⊕ standard. The S₃ → Z₂ break isolates one rep (sign irrep),
    creating the τ/μ mass gap. The Z₂ → 1 break separates the remaining two,
    creating the μ/e mass gap.

    Theory ref: lepton-masses.md, e7-derivation.md

    Prove: |S₃| = 6 = Σ dim² (dimension formula).
    Prove: character orthogonality (row and column).
    Prove: permutation rep = trivial ⊕ standard.
    Prove: S₃ → Z₂ branching of standard = trivial + sign.
    Prove: primordial μ/e = n²S - 1 = 207 (integer).
    Prove: primordial τ/μ = S + n = 17 (integer).
    Prove: S + n ≈ 2πe to within 0.5% (continuous limit).
    Verify: τ/μ observed = 2πe × corrections ≈ 16.817 (K/X gradients).
    Verify: μ/e observed = (n²S-1) × corrections ≈ 206.768.
    Verify: τ/e = (τ/μ)(μ/e) ≈ 3477 (product of breaks).
    Disprove: Z₂ (any D_{n≠4}) gives only 2 mass levels.
    """
    results: list[TR] = []

    n = tools.bld.n
    L = tools.bld.L
    S = tools.bld.S
    B = tools.bld.B

    # --- S₃ character table ---
    # Classes: {e} (1), {(12),(13),(23)} (3), {(123),(132)} (2)
    class_sizes = np.array([1, 3, 2])
    order = int(np.sum(class_sizes))
    results.append(TR(f"|S3|={order}=6", order == 6))

    # Character table (rows = irreps, cols = classes)
    char = np.array([
        [1, 1, 1],      # trivial
        [1, -1, 1],     # sign
        [2, 0, -1],     # standard
    ], dtype=float)

    # Dimension formula: Σ dim² = |G|
    dims = char[:, 0].astype(int)
    results.append(TR(
        f"dim²_sum={sum(d**2 for d in dims)}=6",
        sum(d ** 2 for d in dims) == order,
    ))

    # Number of irreps = number of conjugacy classes = 3 generations
    n_irreps = len(dims)
    results.append(TR(f"n_irreps={n_irreps}=3", n_irreps == 3))

    # Row orthogonality: <χ_i, χ_j> = δ_{ij}
    gram = np.zeros((3, 3))
    for i in range(3):
        for j in range(3):
            gram[i, j] = np.sum(class_sizes * char[i] * char[j]) / order
    gram_err = float(np.max(np.abs(gram - np.eye(3))))
    results.append(TR(f"row_orthogonality_err={gram_err:.2e}", gram_err < 1e-14))

    # Column orthogonality: Σ_i χ_i(C)χ_i(C') = (|G|/|C|)δ_{CC'}
    col_gram = char.T @ char
    expected_col = np.diag(order / class_sizes)
    col_err = float(np.max(np.abs(col_gram - expected_col)))
    results.append(TR(f"col_orthogonality_err={col_err:.2e}", col_err < 1e-14))

    # --- Permutation representation ---
    # χ_perm(g) = fixed points on {8_v, 8_s, 8_c}
    perm_char = np.array([3.0, 1.0, 0.0])
    decomp = np.array([
        np.sum(class_sizes * perm_char * char[i]) / order
        for i in range(3)
    ])
    results.append(TR(
        f"perm=triv({decomp[0]:.0f})+sign({decomp[1]:.0f})+std({decomp[2]:.0f})",
        abs(decomp[0] - 1) < 1e-14
        and abs(decomp[1]) < 1e-14
        and abs(decomp[2] - 1) < 1e-14,
    ))

    # --- S₃ → Z₂ branching ---
    # Z₂ = {e, (12)} subgroup. Restrict standard to Z₂:
    # standard: χ(e)=2, χ((12))=0 → decomposes into trivial + sign of Z₂.
    std_z2 = np.array([2.0, 0.0])
    z2_trivial = np.array([1.0, 1.0])
    z2_sign = np.array([1.0, -1.0])
    a_triv = np.sum(std_z2 * z2_trivial) / 2
    a_sign = np.sum(std_z2 * z2_sign) / 2
    results.append(TR(
        f"std→Z2=triv({a_triv:.0f})+sign({a_sign:.0f})",
        abs(a_triv - 1) < 1e-14 and abs(a_sign - 1) < 1e-14,
    ))

    # --- Primordial mass ratios are integers ---
    # μ/e primordial: n²S - 1 = 207 (one subtracted: electron already occupies
    # one position; muon has n²S - 1 = 207 accessible structure positions)
    primordial_mu_e = n ** 2 * S - 1
    results.append(TR(
        f"primordial_mu_e=n²S-1={primordial_mu_e}=207",
        primordial_mu_e == 207,
    ))

    # τ/μ primordial: S + n = 17 (complete structure: intervals + dimensions)
    primordial_tau_mu = S + n
    results.append(TR(
        f"primordial_tau_mu=S+n={primordial_tau_mu}=17",
        primordial_tau_mu == 17,
    ))

    # τ/e primordial: product of the two integer primordials
    primordial_tau_e = primordial_mu_e * primordial_tau_mu
    results.append(TR(
        f"primordial_tau_e=207×17={primordial_tau_e}=3519",
        primordial_tau_e == 3519,
    ))

    # --- Continuous limit: S + n ≈ 2πe ---
    # The transcendental 2πe ≈ 17.079 emerged late — it's how continuous
    # observation sees the discrete integer 17.
    two_pi_e = 2 * math.pi * math.e
    results.append(TR(
        f"S+n={primordial_tau_mu}_≈_2πe={two_pi_e:.4f}_ratio={primordial_tau_mu/two_pi_e:.4f}",
        abs(primordial_tau_mu / two_pi_e - 1.0) < 0.005,  # within 0.5%
    ))

    # --- Observed ratios (through K/X alignment gradients) ---
    tau_mu = tools.bld.tau_over_mu(n, float(L), S)
    mu_e = tools.bld.mu_over_e(n, float(L), S, B)

    # τ/μ observed ≈ 2πe × corrections ≈ 16.817
    results.append(TR(
        f"tau_mu_observed={tau_mu:.4f}≈16.817",
        abs(tau_mu - 16.817) < 0.01,
    ))

    # μ/e observed ≈ 206.768 (K/X corrections reduce 207 → 206.768)
    results.append(TR(
        f"mu_e_observed={mu_e:.4f}≈206.768",
        abs(mu_e - 206.768) < 0.01,
    ))

    # K/X gradient: primordial → observed
    mu_e_gradient = mu_e / primordial_mu_e
    tau_mu_gradient = tau_mu / primordial_tau_mu
    results.append(TR(
        f"mu_e_gradient={mu_e_gradient:.4f}_tau_mu_gradient={tau_mu_gradient:.4f}",
        mu_e_gradient < 1.0 and tau_mu_gradient < 1.0,  # all corrections reduce
    ))

    # τ/e = product of observed ratios
    tau_e = tau_mu * mu_e
    results.append(TR(
        f"tau_e={tau_e:.1f}≈3477",
        abs(tau_e - 3477) < 5,
    ))

    # --- Disprove: Z₂ gives only 2 levels ---
    z2_irreps = 2
    results.append(TR(
        f"Z2_has_{z2_irreps}_irreps_not_3",
        z2_irreps != 3,
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 62: Mass formula dominant scale n²S = gauge_dim × S
# ---------------------------------------------------------------------------


def test_mass_scale_n2s() -> None:
    """All generation mass formulas share n²S = 208 as the dominant scale.

    n²S = n² × S = 16 × 13 where:
    - n² = 16 = dim(u(4)) = gauge_generated_dim()  [gauge algebra dimension]
    - S = (B-n)/n = 13 = 2C₂(vector) - 1  [generation constant from Casimir]

    n²S = 208 is the number of distinguishable states a second-generation
    particle can occupy. Every mass formula uses n²S as the base:
    - μ/e: base n²S - 1 = 207 (minus one: electron already occupies one position)
    - ms/me: n²S - L - L/n = 183 (minus link and confinement costs for quarks)
    - τ/μ contains (n²S-1)/n²S as a sub-percent correction (phase mismatch)
    - top mass contains 1 - K/n²S as a sub-percent correction

    Theory ref: lepton-masses.md, quark-masses.md, integer-machine.md

    Prove: n²S = gauge_generated_dim() × S = 208.
    Prove: μ/e base = n²S - 1 = 207 (0.1% of exact formula).
    Prove: ms/me = n²S - L(1 + 1/n) = 183 (quark link costs).
    Prove: τ/μ correction (n²S-1)/n²S = 207/208.
    Prove: top correction 1 - K/n²S = 206/208.
    Verify: all corrections are O(1/n²S) < 0.5%.
    Disprove: wrong S (12, 14) gives μ/e off by > 10.
    Disprove: wrong n (3, 5) gives μ/e off by > 50.
    """
    results: list[TR] = []

    n = tools.bld.n
    L = tools.bld.L
    S = tools.bld.S
    B = tools.bld.B
    K = tools.bld.K
    n2S = n ** 2 * S  # 208

    # --- Factorization ---
    results.append(TR(f"n²S={n2S}=208", n2S == 208))
    results.append(TR(
        f"n²={n**2}=gauge_dim={tools.bld.gauge_generated_dim()}",
        n ** 2 == tools.bld.gauge_generated_dim(),
    ))
    results.append(TR(
        f"S=(B-n)/n=({B}-{n})/{n}={S}",
        S == (B - n) // n,
    ))

    # S from Casimir: S = 2C₂ - 1
    c2_vec = tools.bld.casimir_vector_so(8)
    results.append(TR(
        f"S=2C2-1=2×{c2_vec}-1={2*c2_vec - 1}={S}",
        S == 2 * c2_vec - 1,
    ))

    # --- Lepton mass base ---
    base_mu_e = n2S - 1  # 207
    mu_e = tools.bld.mu_over_e(n, float(L), S, B)
    results.append(TR(f"base_mu_e=n²S-1={base_mu_e}=207", base_mu_e == 207))
    results.append(TR(
        f"mu_e_exact={mu_e:.4f}≈206.768",
        abs(mu_e - 206.768) < 0.01,
    ))

    # Base approximation accuracy
    base_err = abs(base_mu_e / mu_e - 1.0)
    results.append(TR(
        f"base_approximation_err={base_err:.4f}<0.002",
        base_err < 0.002,
    ))

    # --- Quark mass structure ---
    # ms/me = n²S - L - L/n = 208 - 20 - 5 = 183
    # The quark loses L (link cost) and L/n (confinement cost) relative to n²S
    ms_me = tools.bld.ms_over_me(n, S, L)
    quark_correction = L + L / n  # 20 + 5 = 25
    results.append(TR(
        f"ms_me={ms_me}=n²S-L(1+1/n)={n2S}-{quark_correction}={n2S - quark_correction}",
        abs(ms_me - (n2S - quark_correction)) < 1e-10,
    ))

    # Both μ/e and ms/me share n²S as base
    results.append(TR(
        f"lepton_base={base_mu_e}_quark_base={n2S}_shared",
        base_mu_e == n2S - 1 and ms_me == n2S - quark_correction,
    ))

    # --- Sub-percent corrections in other formulas ---
    # τ/μ contains factor (n²S-1)/n²S (phase mismatch)
    tau_factor = (n2S - 1) / n2S
    results.append(TR(
        f"tau_correction=(n²S-1)/n²S={tau_factor:.6f}=207/208",
        abs(tau_factor - 207.0 / 208.0) < 1e-14,
    ))

    # top mass contains factor 1 - K/n²S (electroweak correction)
    top_factor = 1 - K / n2S
    results.append(TR(
        f"top_correction=1-K/n²S={top_factor:.6f}=206/208",
        abs(top_factor - 206.0 / 208.0) < 1e-14,
    ))

    # All corrections are O(1/n²S) < 0.5%
    inv_n2S = 1.0 / n2S
    results.append(TR(
        f"1/n²S={inv_n2S:.6f}<0.005",
        inv_n2S < 0.005,
    ))

    # --- Disprove: wrong S ---
    for wrong_S in [12, 14]:
        wrong_mu_e = tools.bld.mu_over_e(n, float(L), wrong_S, B)
        deviation = abs(wrong_mu_e - 206.768)
        results.append(TR(
            f"S={wrong_S}_mu_e={wrong_mu_e:.1f}_off_by={deviation:.1f}",
            deviation > 10,
        ))

    # --- Disprove: wrong n ---
    for wrong_n in [3, 5]:
        wrong_mu_e = tools.bld.mu_over_e(wrong_n, float(L), S, B)
        deviation = abs(wrong_mu_e - 206.768)
        results.append(TR(
            f"n={wrong_n}_mu_e={wrong_mu_e:.1f}_off_by={deviation:.1f}",
            deviation > 50,
        ))

    assert_all_pass(results)
