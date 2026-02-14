"""Renormalization group running tests on so(8).

Tests 30-32, 39, 57-59 from the equation of motion suite.
RG endpoints, lambda cascade, monotonicity, SM comparison,
boundary coupling algebra, heat kernel properties, spectral transition.
"""

import math

import numpy as np
import numpy.linalg as la

import tools.bld

from helpers import assert_all_pass


TR = tools.bld.TestResult
SO8 = tools.bld.SO8


# ---------------------------------------------------------------------------
# Test 30: RG endpoint derivation — α⁻¹=25 at GUT, 137 at low energy
# ---------------------------------------------------------------------------


def test_rg_endpoints(so8: SO8) -> None:
    """Coupling constants at high and low energy from BLD structure.

    At GUT scale: all boundary modes transparent, only geometry scatters.
      α⁻¹(GUT) = n + L + 1 = 25

    At low energy (M_Z): all boundary modes opaque, full structure scatters.
      α⁻¹(M_Z) = nL + B + 1 + corrections ≈ 137

    Prove: g(0)=1 → α⁻¹=137 (all modes opaque at low energy).
    Prove: g(n_c)=0 → α⁻¹=25 (all modes transparent at high energy).
    Verify: matches bld.alpha_inv() and bld.alpha_inv_gut().
    """
    results: list[TR] = []

    B_ = tools.bld.B
    L_ = tools.bld.L
    n_ = tools.bld.n
    K_ = tools.bld.K

    # GUT endpoint: only geometry
    alpha_gut = tools.bld.alpha_inv_gut(n_, L_)
    results.append(TR(f"alpha_gut={alpha_gut}=25", alpha_gut == 25))

    # Low energy endpoint
    alpha_low = tools.bld.alpha_inv(n_, float(L_), B_, K_)
    exp_alpha = 137.035999
    results.append(TR(
        f"alpha_low={alpha_low:.6f}≈137.036",
        abs(alpha_low - exp_alpha) < 0.001,
    ))

    # The difference = contribution of boundary modes
    boundary_contrib = alpha_low - alpha_gut
    # Base difference: (nL + B + 1) - (n + L + 1) = nL + B - n - L = 80 + 56 - 4 - 20 = 112
    base_diff = n_ * L_ + B_ - n_ - L_
    results.append(TR(
        f"boundary_base_diff={base_diff}=112",
        base_diff == 112,
    ))

    # The actual difference includes corrections (slightly different from 112)
    results.append(TR(
        f"boundary_contrib={boundary_contrib:.4f}≈112+corr",
        abs(boundary_contrib - 112) < 0.1,  # corrections are small
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 31: λ cascade algebraic relations
# ---------------------------------------------------------------------------


def test_lambda_cascade_relations(so8: SO8) -> None:
    """The λ cascade fundamental relations are algebraically consistent.

    Prove: λ² × (n×L) = K²     (the defining relation)
    Prove: n_c = B/K - K = 26   (critical cascade steps)
    Prove: B = K × (n_c + K)    (boundary count from cascade)
    Verify: these three are mutually consistent.
    Disprove: wrong K or wrong B breaks all three.
    """
    results: list[TR] = []

    B_ = tools.bld.B
    L_ = tools.bld.L
    n_ = tools.bld.n
    K_ = tools.bld.K
    lam = tools.bld.LAMBDA
    lam_sq = lam ** 2

    # Relation 1: λ² × (n × L) = K²
    lhs1 = lam_sq * (n_ * L_)
    rhs1 = K_ ** 2
    results.append(TR(
        f"lambda_sq*nL={lhs1:.6f}=K²={rhs1}",
        abs(lhs1 - rhs1) < tools.bld.FLOAT_EPSILON,
    ))

    # Relation 2: n_c = B/K - K = 26
    n_c = B_ // K_ - K_  # integer arithmetic
    results.append(TR(f"n_c={n_c}=26", n_c == 26))

    # Relation 3: B = K × (n_c + K)
    B_computed = K_ * (n_c + K_)
    results.append(TR(
        f"B=K*(n_c+K)={B_computed}={B_}",
        B_computed == B_,
    ))

    # Mutual consistency: substitute relation 2 into relation 3
    # B = K * (B/K - K + K) = K * (B/K) = B  ✓  (tautology)
    # But the NON-trivial check: given λ² = K²/(nL) and B = K(n_c + K),
    # derive n_c:
    # From λ² = K²/(nL), the cascade has n_c steps of λ⁻¹ each.
    # λ^{-2·n_c} × v² = M_P² implies a relation.
    # For now, just verify the integer relations are consistent.
    results.append(TR(
        f"n_c_from_B={B_ // K_ - K_}=n_c_from_formula={n_c}",
        B_ // K_ - K_ == n_c,
    ))

    # Disprove: wrong K breaks all relations
    K_wrong = 3
    lhs_wrong = lam_sq * (n_ * L_)
    rhs_wrong = K_wrong ** 2
    results.append(TR(
        f"wrong_K={K_wrong}_breaks_rel1",
        abs(lhs_wrong - rhs_wrong) > 0.1,
    ))

    B_wrong = K_wrong * (n_c + K_wrong)
    results.append(TR(
        f"wrong_K_wrong_B={B_wrong}≠{B_}",
        B_wrong != B_,
    ))

    # Disprove: wrong B breaks relation 2
    B_wrong2 = 58
    n_c_wrong = B_wrong2 // K_ - K_
    results.append(TR(
        f"wrong_B={B_wrong2}_n_c={n_c_wrong}≠26",
        n_c_wrong != 26,
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 32: RG monotonicity across candidate transition functions
# ---------------------------------------------------------------------------


def test_rg_monotonic(so8: SO8) -> None:
    """α⁻¹(k) is monotonically decreasing as energy increases (k → n_c).

    Three candidate transition functions g(k):
      - Exponential: g(k) = exp(-k/τ)
      - Linear: g(k) = 1 - k/n_c
      - Step: g(k) = (n_c - k)/n_c rounded to thresholds

    Prove: for all candidates, α⁻¹(k) is monotonically decreasing.
    Verify: g(k) ∈ [0, 1] for all k ∈ [0, n_c].
    Verify: g(0) = 1 and g(n_c) ≈ 0 for all candidates.
    """
    results: list[TR] = []

    n_ = tools.bld.n
    L_ = tools.bld.L
    B_ = tools.bld.B
    n_c = B_ // tools.bld.K - tools.bld.K  # 26

    alpha_gut = float(tools.bld.alpha_inv_gut(n_, L_))
    alpha_low = tools.bld.alpha_inv(n_, float(L_), B_, tools.bld.K)
    delta = alpha_low - alpha_gut  # ≈ 112

    def alpha_from_g(g: float) -> float:
        return alpha_gut + delta * g

    # Candidate 1: exponential g(k) = exp(-k/τ) with τ chosen so g(n_c) ≈ 0
    tau = n_c / 5.0  # exp(-5) ≈ 0.007, close enough to 0
    g_exp = [math.exp(-k / tau) for k in range(n_c + 1)]

    # Candidate 2: linear g(k) = 1 - k/n_c
    g_lin = [1 - k / n_c for k in range(n_c + 1)]

    # Candidate 3: quadratic g(k) = (1 - k/n_c)²
    g_quad = [(1 - k / n_c) ** 2 for k in range(n_c + 1)]

    for name, g_vals in [("exp", g_exp), ("linear", g_lin), ("quadratic", g_quad)]:
        # Check g(0) = 1
        results.append(TR(
            f"{name}_g(0)={g_vals[0]:.4f}=1",
            abs(g_vals[0] - 1.0) < 1e-10,
        ))

        # Check g(n_c) ≈ 0 (within 0.01)
        results.append(TR(
            f"{name}_g(n_c)={g_vals[-1]:.4f}≈0",
            g_vals[-1] < 0.01,
        ))

        # Check g ∈ [0, 1] for all k
        all_in_range = all(0 - 1e-10 <= g <= 1 + 1e-10 for g in g_vals)
        results.append(TR(f"{name}_g∈[0,1]", all_in_range))

        # Check α⁻¹ monotonically decreasing (as k increases = energy increases)
        alphas = [alpha_from_g(g) for g in g_vals]
        monotonic = all(
            alphas[k] >= alphas[k + 1] - 1e-10 for k in range(len(alphas) - 1)
        )
        results.append(TR(f"{name}_alpha_monotonic", monotonic))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 39: RG comparison to SM running (investigation, not assertion)
# ---------------------------------------------------------------------------


def test_rg_comparison_sm(so8: SO8) -> None:
    """Compare BLD cascade candidates to SM 1-loop electromagnetic running.

    This is an INVESTIGATION: we compare three candidate g(k) functions
    to SM running to document the best fit. We do NOT assert which is correct.

    Prove: cascade_energy(0) = V_EW.
    Prove: cascade_energy(n_c) is near Planck scale.
    Verify: SM 1-loop α⁻¹(M_Z) = 127.9 (boundary condition).
    Verify: compute L² residual for each candidate vs SM running.
    """
    results: list[TR] = []

    # Prove: cascade_energy(0) = V_EW
    e0 = tools.bld.cascade_energy(0)
    results.append(TR(
        f"cascade_e0={e0:.4f}=V_EW",
        abs(e0 - tools.bld.V_EW) < 1e-10,
    ))

    # Prove: cascade_energy(n_c=26) is near Planck scale (10^18 – 10^20 GeV)
    n_c = (tools.bld.B // tools.bld.K) - tools.bld.K  # 26
    e_nc = tools.bld.cascade_energy(n_c)
    planck = tools.bld.planck_mass(
        tools.bld.V_EW, tools.bld.LAMBDA ** 2,
        tools.bld.n, float(tools.bld.L), tools.bld.K, tools.bld.B,
    )
    results.append(TR(
        f"cascade_e26={e_nc:.2e}_near_Planck={planck:.2e}",
        1e18 <= e_nc <= 1e20,
    ))

    # Verify: SM 1-loop boundary condition
    sm_mz = tools.bld.sm_alpha_inv_em_1loop(91.1876)
    results.append(TR(
        f"SM_alpha_inv_MZ={sm_mz:.1f}",
        abs(sm_mz - 127.9) < 0.01,
    ))

    # BLD endpoints
    alpha_low = tools.bld.alpha_inv(
        tools.bld.n, float(tools.bld.L), tools.bld.B, tools.bld.K,
    )  # ~137.036
    alpha_gut = tools.bld.alpha_inv_gut(tools.bld.n, tools.bld.L)  # 25

    # Three candidate interpolations g(k) from test_rg_monotonic
    lam = tools.bld.LAMBDA
    def g_exp(k: int) -> float:
        """Exponential: α⁻¹(k) = 25 + 112 × (1 - exp(-k/n_c)) / (1 - exp(-1))."""
        ratio = (1.0 - math.exp(-k / n_c)) / (1.0 - math.exp(-1.0))
        return alpha_gut + (alpha_low - alpha_gut) * ratio

    def g_linear(k: int) -> float:
        """Linear: α⁻¹(k) = 25 + 112 × k/n_c."""
        return alpha_gut + (alpha_low - alpha_gut) * k / n_c

    def g_quad(k: int) -> float:
        """Quadratic: α⁻¹(k) = 25 + 112 × (k/n_c)²."""
        return alpha_gut + (alpha_low - alpha_gut) * (k / n_c) ** 2

    # Compute L² residual of each candidate vs SM 1-loop at cascade energies
    # Only compare in overlap region where SM is reliable: M_Z to ~1000 GeV
    # (k values where energy is in this range)
    residuals = {"exp": 0.0, "linear": 0.0, "quad": 0.0}
    n_points = 0
    for k in range(n_c + 1):
        mu_k = tools.bld.cascade_energy(k)
        if mu_k < 80.0 or mu_k > 2000.0:  # outside SM reliable range
            continue
        sm_val = tools.bld.sm_alpha_inv_em_1loop(mu_k)
        residuals["exp"] += (g_exp(k) - sm_val) ** 2
        residuals["linear"] += (g_linear(k) - sm_val) ** 2
        residuals["quad"] += (g_quad(k) - sm_val) ** 2
        n_points += 1

    # Verify: at least some cascade steps fall in SM range
    results.append(TR(f"cascade_points_in_SM_range={n_points}", n_points >= 1))

    # Document: which candidate fits best (smallest residual)
    if n_points > 0:
        best = min(residuals, key=residuals.get)
        results.append(TR(
            f"best_candidate={best}_residual={residuals[best]:.4f}",
            True,  # investigation, not assertion
        ))

        # All three should be "wrong" in different ways — none is exact SM
        # This is expected: BLD g(k) is NOT SM running; it's a cascade structure
        # Document: the gap between BLD cascade and SM continuous running
        for name, res in residuals.items():
            results.append(TR(
                f"L2_{name}={res:.4f}",
                True,  # document only
            ))

    # Verify: BLD endpoints bracket SM values
    # At low energy (~EW scale), BLD gives ~137, SM gives ~128 at M_Z
    # This ~7% gap is expected: SM runs from M_Z, BLD from V_EW with different physics
    results.append(TR(
        "BLD_low_energy_above_SM",
        alpha_low > sm_mz,
    ))

    # At GUT scale: SM EM running INCREASES α⁻¹ (screening), while BLD
    # gives unified α⁻¹ = 25. These measure DIFFERENT things:
    # SM: individual U(1)_Y coupling; BLD: unified coupling.
    # Document the divergence; this gap is expected.
    sm_gut = tools.bld.sm_alpha_inv_em_1loop(1e16)
    results.append(TR(
        f"SM_EM_at_GUT={sm_gut:.1f}_diverges_from_BLD_unified={alpha_gut}",
        sm_gut > alpha_gut,  # SM EM screening > BLD unified
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 57: Boundary coupling algebra — B×K = nL + B - n - L = 112
# ---------------------------------------------------------------------------


def test_boundary_coupling_algebra(so8: SO8) -> None:
    """The boundary contribution to α⁻¹ is exactly B×K = 112.

    Prove: B×K = nL + B - n - L = 112 (algebraic identity).
    Prove: B = (n-1)(L-1) - 1 = 56 (B determined by n, L alone).
    Prove: K = 2 (derived: nL - n - L = B, so BK = 2B, K = 2).
    Verify: BK ≈ α⁻¹(low) - α⁻¹(GUT) (with small corrections).
    Disprove: wrong n or L breaks B = (n-1)(L-1) - 1.
    """
    results: list[TR] = []

    B_ = tools.bld.B
    L_ = tools.bld.L
    n_ = tools.bld.n
    K_ = tools.bld.K

    # Prove: B×K = nL + B - n - L
    bk = B_ * K_
    nL_plus_B_minus_n_minus_L = n_ * L_ + B_ - n_ - L_
    results.append(TR(
        f"BK={bk}=nL+B-n-L={nL_plus_B_minus_n_minus_L}",
        bk == nL_plus_B_minus_n_minus_L,
    ))

    # Prove: B×K = 112
    results.append(TR(f"BK={bk}=112", bk == 112))

    # Prove: B = (n-1)(L-1) - 1
    b_from_nL = (n_ - 1) * (L_ - 1) - 1
    results.append(TR(
        f"B=(n-1)(L-1)-1={b_from_nL}={B_}",
        b_from_nL == B_,
    ))

    # Prove: nL - n - L = B (the key identity connecting multiplicative/additive)
    nL_minus_n_minus_L = n_ * L_ - n_ - L_
    results.append(TR(
        f"nL-n-L={nL_minus_n_minus_L}=B={B_}",
        nL_minus_n_minus_L == B_,
    ))

    # Prove: K = (nL + B - n - L) / B = 2B / B = 2
    k_derived = nL_plus_B_minus_n_minus_L // B_
    results.append(TR(
        f"K_derived={k_derived}=K={K_}",
        k_derived == K_,
    ))

    # Verify: BK ≈ α⁻¹(low) - α⁻¹(GUT)
    alpha_low = tools.bld.alpha_inv(n_, float(L_), B_, K_)
    alpha_gut = float(tools.bld.alpha_inv_gut(n_, L_))
    diff = alpha_low - alpha_gut
    results.append(TR(
        f"alpha_diff={diff:.4f}≈BK={bk}",
        abs(diff - bk) < 0.1,  # corrections are small
    ))

    # Disprove: wrong n breaks the identity
    for n_wrong in [3, 5, 6]:
        b_wrong = (n_wrong - 1) * (L_ - 1) - 1
        results.append(TR(
            f"n={n_wrong}_B_wrong={b_wrong}!=56",
            b_wrong != B_,
        ))

    # Disprove: wrong L breaks the identity
    for L_wrong in [10, 15, 25]:
        b_wrong = (n_ - 1) * (L_wrong - 1) - 1
        results.append(TR(
            f"L={L_wrong}_B_wrong={b_wrong}!=56",
            b_wrong != B_,
        ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 58: Heat kernel on SO(8) — basic properties
# ---------------------------------------------------------------------------


def test_heat_kernel_properties(so8: SO8) -> None:
    """Heat kernel trace Z(t) on SO(8) has correct structural properties.

    Prove: Z(t) > 0 for all t >= 0 (positive definite sum).
    Prove: Z(t) monotonically decreasing (dZ/dt < 0 for t > 0).
    Prove: Z(large_t) -> 1 (only trivial rep survives).
    Verify: Z(0) = 1 + sum d_R^2 from direct enumeration.
    Verify: spectral convergence (Z at fixed t stabilizes with max_label_sum).
    """
    results: list[TR] = []

    max_ls = 4

    # Prove: Z(0) = 1 + sum of d_R^2 (manual enumeration)
    z0 = tools.bld.heat_kernel_trace(0.0, max_label_sum=max_ls)
    manual_sum = 1.0  # trivial
    for a1 in range(max_ls + 1):
        for a2 in range(max_ls + 1 - a1):
            for a3 in range(max_ls + 1 - a1 - a2):
                for a4 in range(max_ls + 1 - a1 - a2 - a3):
                    if a1 == a2 == a3 == a4 == 0:
                        continue
                    d = tools.bld.weyl_dimension_d4(a1, a2, a3, a4)
                    manual_sum += d * d
    results.append(TR(
        f"Z(0)={z0:.0f}=manual={manual_sum:.0f}",
        abs(z0 - manual_sum) < 1e-6,
    ))

    # Prove: Z(t) > 0 for a range of t values
    t_values = [0.0, 0.001, 0.01, 0.1, 0.5, 1.0, 5.0, 10.0, 100.0]
    z_values = [tools.bld.heat_kernel_trace(t, max_label_sum=max_ls) for t in t_values]
    all_positive = all(z > 0 for z in z_values)
    results.append(TR("Z(t)>0_all_t", all_positive))

    # Prove: Z(t) monotonically decreasing
    monotonic = all(
        z_values[i] > z_values[i + 1] - 1e-10
        for i in range(len(z_values) - 1)
    )
    results.append(TR("Z(t)_monotonic_decreasing", monotonic))

    # Prove: Z(large_t) -> 1 (only trivial rep contribution)
    z_large = tools.bld.heat_kernel_trace(100.0, max_label_sum=max_ls)
    results.append(TR(
        f"Z(100)={z_large:.6f}->1",
        abs(z_large - 1.0) < 1e-6,
    ))

    # Verify: spectral convergence — Z at fixed t stabilizes with max_label_sum
    # Use t=1.0 where exp(-C₂) suppresses all but the lowest few reps
    t_test = 1.0
    z_prev = tools.bld.heat_kernel_trace(t_test, max_label_sum=2)
    converging = True
    for mls in [3, 4, 5]:
        z_curr = tools.bld.heat_kernel_trace(t_test, max_label_sum=mls)
        if abs(z_curr - z_prev) > abs(z_prev) * 0.01:
            converging = False
        z_prev = z_curr
    results.append(TR("spectral_convergence_at_t=1.0", converging))

    # Verify: the three lowest-Casimir reps dominate at moderate t
    # C2 = 7 for 8_v, 8_c, 8_s -> contribution = 3 x 64 x exp(-7t)
    # C2 = 12 for adjoint -> 784 x exp(-12t)
    t_mod = 1.0
    z_total = tools.bld.heat_kernel_trace(t_mod, max_label_sum=max_ls)
    lowest_contrib = 3 * 64 * math.exp(-7 * t_mod)  # three 8-dim reps
    adjoint_contrib = 784 * math.exp(-12 * t_mod)
    leading_fraction = (lowest_contrib + adjoint_contrib + 1) / z_total
    results.append(TR(
        f"leading_fraction_at_t=1={leading_fraction:.4f}",
        leading_fraction > 0.99,  # leading reps dominate
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 59: Spectral transition shape from heat kernel
# ---------------------------------------------------------------------------


def test_spectral_transition_shape(so8: SO8) -> None:
    """Heat kernel transition function g_HK(k) shape and properties.

    Define g_HK(k) = 1 - Z_red(t_k)/Z_red(0) where t_k = t_0 x lam^{2k}
    and Z_red = Z - 1 (excluding trivial rep).

    Prove: g_HK(k) is monotonically decreasing for t_0 > 0.
    Prove: g_HK(0) ~ 1 and g_HK(n_c) ~ 0 for t_0 = 1.
    Verify: transition width ~ 5 cascade steps (from C2_min and step factor 20).
    Verify: g_HK is sharper than all three test-32 candidates.
    Investigation: document the effective transition step k* where g crosses 0.5.
    """
    results: list[TR] = []

    B_ = tools.bld.B
    K_ = tools.bld.K
    n_c = B_ // K_ - K_  # 26
    lam_sq = tools.bld.LAMBDA ** 2  # 1/20
    max_ls = 5

    # Z_red(t) = Z(t) - 1 (exclude trivial)
    z_red_0 = tools.bld.heat_kernel_trace(0.0, max_label_sum=max_ls) - 1.0

    def g_hk(k: int, t0: float) -> float:
        t_k = t0 * (lam_sq ** k)  # t0 x 20^{-k}
        z_k = tools.bld.heat_kernel_trace(t_k, max_label_sum=max_ls) - 1.0
        return 1.0 - z_k / z_red_0

    # Compute g_HK(k) for t0 = 1.0
    t0 = 1.0
    g_vals = [g_hk(k, t0) for k in range(n_c + 1)]

    # Prove: g_HK(0) ~ 1
    results.append(TR(
        f"g_HK(0)={g_vals[0]:.6f}~1",
        abs(g_vals[0] - 1.0) < 0.01,
    ))

    # Prove: g_HK(n_c) ~ 0
    results.append(TR(
        f"g_HK({n_c})={g_vals[n_c]:.6f}~0",
        abs(g_vals[n_c]) < 1e-6,
    ))

    # Prove: monotonically decreasing
    mono = all(
        g_vals[k] >= g_vals[k + 1] - 1e-12
        for k in range(len(g_vals) - 1)
    )
    results.append(TR("g_HK_monotonic", mono))

    # Verify: transition width ~ 5 steps
    # Find k* where g crosses 0.5
    k_star = None
    for k in range(n_c):
        if g_vals[k] >= 0.5 and g_vals[k + 1] < 0.5:
            k_star = k
            break
    results.append(TR(
        f"transition_k_star={k_star}",
        k_star is not None and k_star <= 5,
    ))

    # Verify: transition width (k where g drops from 0.9 to 0.1)
    k_90 = None
    k_10 = None
    for k in range(n_c + 1):
        if k_90 is None and g_vals[k] < 0.9:
            k_90 = k
        if k_10 is None and g_vals[k] < 0.1:
            k_10 = k
    width = k_10 - k_90 if k_90 is not None and k_10 is not None else None
    results.append(TR(
        f"transition_width={width}_steps",
        width is not None and width <= 5,
    ))

    # Verify: g_HK is sharper than test-32 candidates at k=5
    # Test-32 linear: g_lin(5) = 1 - 5/26 ~ 0.808
    # Test-32 quadratic: g_quad(5) = (1 - 5/26)^2 ~ 0.652
    # Test-32 exponential: g_exp(5) = exp(-5/(26/5)) ~ 0.382
    g_lin_5 = 1 - 5 / n_c
    g_quad_5 = (1 - 5 / n_c) ** 2
    g_exp_5 = math.exp(-5 / (n_c / 5))
    results.append(TR(
        f"g_HK(5)={g_vals[5]:.6f}<lin={g_lin_5:.3f}",
        g_vals[5] < g_lin_5,
    ))
    results.append(TR(
        f"g_HK(5)={g_vals[5]:.6f}<quad={g_quad_5:.3f}",
        g_vals[5] < g_quad_5,
    ))
    results.append(TR(
        f"g_HK(5)={g_vals[5]:.6f}<exp={g_exp_5:.3f}",
        g_vals[5] < g_exp_5,
    ))

    # Prove: result is robust across t0 values
    for t0_test in [0.1, 0.5, 2.0, 10.0]:
        g0 = g_hk(0, t0_test)
        g_nc = g_hk(n_c, t0_test)
        results.append(TR(
            f"t0={t0_test}_g(0)={g0:.4f}_g(nc)={g_nc:.2e}",
            g0 > 0.99 and abs(g_nc) < 1e-4,
        ))

    assert_all_pass(results)
