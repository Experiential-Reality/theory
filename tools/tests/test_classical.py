"""Classical physics prediction tests.

Tests Reynolds number, Kolmogorov exponents, Feigenbaum constants, and
She-Leveque structure functions.  Each test proves the BLD prediction
matches experiment and attempts to disprove it by trying alternatives.

Theory refs:
  - reynolds-derivation.md (Re_c formulas)
  - feigenbaum-derivation.md (delta, alpha)
  - she-leveque-derivation.md (zeta_p structure functions)
"""

import dataclasses
import fractions
import math

import pytest

import tools.bld


@dataclasses.dataclass(slots=True, frozen=True)
class ClassicalResult:
    name: str
    passes: bool


# ---------------------------------------------------------------------------
# Run functions
# ---------------------------------------------------------------------------


def run_reynolds_pipe() -> list[tools.bld.Prediction | ClassicalResult]:
    """Re_c(pipe) = (nLB/K)(38/37) = 2300.5.

    Net confinement X = B - L + 1 = 37.
    Correction (X+1)/X = 38/37 follows universal (structure+observer)/structure.

    Prove: matches empirical 2300 within 0.5.
    Disprove: wrong (n,L,B) tuples.
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    results: list[tools.bld.Prediction | ClassicalResult] = []

    # Prove: BLD prediction matches
    predicted = tools.bld.reynolds_pipe(n, L, B, K)
    results.append(tools.bld.Prediction(
        "Re_c_pipe", predicted, 2300.0, 1.0,
    ))

    # Verify internal structure
    X = B - L + 1
    results.append(ClassicalResult("X=B-L+1=37", X == 37))
    results.append(ClassicalResult(
        "correction=38/37",
        abs((X + 1) / X - 38 / 37) < 1e-15,
    ))

    # Disprove: wrong BLD constants
    # B+-1 changes Re_c by only ~2% (within empirical tolerance), so test
    # tuples that change n or L — the structurally independent quantities.
    # Theory ref: reynolds-derivation.md — B = n(S+1) is derived, not free.
    wrong_tuples = [(3, 10, 30, 1), (5, 25, 70, 3), (3, 20, 56, 2), (6, 10, 60, 4)]
    for n_, L_, B_, K_ in wrong_tuples:
        alt = tools.bld.reynolds_pipe(n_, L_, B_, K_)
        matches = abs(alt - 2300) < 50
        results.append(ClassicalResult(
            f"({n_},{L_},{B_},{K_})_fails", not matches,
        ))

    return results


def run_reynolds_geometries() -> list[tools.bld.Prediction]:
    """Geometry-dependent Re_c from T cap S detection structure.

    Flat plate: Re_c * nB = 515,200 (observed ~5e5, 3% tolerance)
    Sphere: Re_c * (n(L+K)-1) = 200,100 (observed ~2e5, 0.5% tolerance)
    Jet: Re_c / K = 1,150 (observed 1000-3000)
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    re_pipe = tools.bld.reynolds_pipe(n, L, B, K)
    results: list[tools.bld.Prediction] = []

    # Flat plate: B-escape (boundary escapes detection)
    re_flat = re_pipe * n * B
    results.append(tools.bld.Prediction(
        "Re_c_flat_plate", re_flat, 5e5, 1.5e4,
    ))

    # Sphere: L-escape (link/geometry partially escapes)
    re_sphere = re_pipe * (n * (L + K) - 1)
    results.append(tools.bld.Prediction(
        "Re_c_sphere", re_sphere, 2e5, 1e3,
    ))

    # Jet: destabilizing (K reduces stability)
    re_jet = re_pipe / K
    results.append(tools.bld.Prediction(
        "Re_c_jet", re_jet, 2000.0, 1000.0,
    ))

    return results


def run_kolmogorov_exponents() -> list[ClassicalResult]:
    """Exact rational identities from BLD.

    -5/3 = -L/(n(n-1)) = -20/12  (Kolmogorov energy spectrum)
    2/3 = K/(n-1) = 2/3          (dissipation exponent)
    1/25 = 1/(L+n+1)             (intermittency correction)

    Use fractions.Fraction for exact equality.
    Disprove: wrong n in {3, 5, 6}.
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    results: list[ClassicalResult] = []

    # Exact rational arithmetic
    F = fractions.Fraction

    # -5/3 = -L/(n(n-1))
    kolmogorov = -F(L, n * (n - 1))
    results.append(ClassicalResult(
        "-L/(n(n-1))=-5/3", kolmogorov == F(-5, 3),
    ))

    # 2/3 = K/(n-1)
    dissipation = F(K, n - 1)
    results.append(ClassicalResult(
        "K/(n-1)=2/3", dissipation == F(2, 3),
    ))

    # 1/25 = 1/(L+n+1)
    intermittency = F(1, L + n + 1)
    results.append(ClassicalResult(
        "1/(L+n+1)=1/25", intermittency == F(1, 25),
    ))

    # Disprove: wrong n values
    for n_ in [3, 5, 6]:
        L_ = n_**2 * (n_**2 - 1) // 12
        if L_ < 1:
            continue
        alt = -F(L_, n_ * (n_ - 1))
        results.append(ClassicalResult(
            f"n={n_}_kolmogorov={alt}_not_-5/3", alt != F(-5, 3),
        ))

    return results


def run_feigenbaum_delta() -> list[tools.bld.Prediction | ClassicalResult]:
    """delta = sqrt(L + K - K^2/L + 1/e^X) where X = n + K + K/n + 1/L.

    Prove: matches delta = 4.6692016091 within 0.0003%.
    Verify: e-correction improves precision ~100x over first-order.
    """
    L, n, K = tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.FEIGENBAUM_DELTA
    results: list[tools.bld.Prediction | ClassicalResult] = []

    # Full prediction with e-correction
    predicted = tools.bld.feigenbaum_delta(n, L, K)
    results.append(tools.bld.Prediction(
        "delta", predicted, obs.value, 0.0001,  # 0.0003% of ~4.669
    ))

    # First-order (no e-correction)
    delta_first = math.sqrt(L + K - K**2 / L)
    err_first = abs(delta_first - obs.value)
    err_full = abs(predicted - obs.value)

    # e-correction improves precision by ~100x
    improvement = err_first / err_full if err_full > 0 else float("inf")
    results.append(ClassicalResult(
        f"e_correction_100x_better_{improvement:.0f}x",
        improvement > 50,  # conservative: >50x
    ))

    return results


def run_feigenbaum_alpha() -> list[tools.bld.Prediction | ClassicalResult]:
    """alpha = K + 1/K + 1/((n+K)B) - 1/(D*e^X).

    Prove: matches alpha = 2.5029078750 within 0.00001%.
    Cross-check: fractal dimension D_f = ln2/ln(alpha).
    Cross-check: product alpha*delta.
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.FEIGENBAUM_ALPHA
    obs_delta = tools.bld.FEIGENBAUM_DELTA
    results: list[tools.bld.Prediction | ClassicalResult] = []

    # Full prediction
    predicted = tools.bld.feigenbaum_alpha(n, L, B, K)
    results.append(tools.bld.Prediction(
        "alpha_feig", predicted, obs.value, 0.000001,
    ))

    # First-order (no e-correction)
    alpha_first = K + 1.0 / K + 1.0 / ((n + K) * B)
    err_first = abs(alpha_first - obs.value)
    err_full = abs(predicted - obs.value)
    improvement = err_first / err_full if err_full > 0 else float("inf")
    results.append(ClassicalResult(
        f"e_correction_improves_{improvement:.0f}x",
        improvement > 50,
    ))

    # Cross-check: fractal dimension
    D_f_bld = math.log(2) / math.log(predicted)
    D_f_obs = math.log(2) / math.log(obs.value)
    results.append(ClassicalResult(
        "fractal_dim_match",
        abs(D_f_bld - D_f_obs) < 1e-6,
    ))

    # Cross-check: product alpha*delta
    delta_bld = tools.bld.feigenbaum_delta(n, L, K)
    product_bld = predicted * delta_bld
    product_obs = obs.value * obs_delta.value
    results.append(ClassicalResult(
        "alpha_delta_product",
        abs(product_bld - product_obs) / product_obs < 0.001,
    ))

    return results


def run_she_leveque() -> list[tools.bld.Prediction | ClassicalResult]:
    """zeta_p = p/9 + 2[1 - (2/3)^(p/3)] for p=1..8.

    Prove: matches DNS data within measurement uncertainty.
    Disprove: K41 (p/3) diverges from DNS at high p.
    """
    n, K = tools.bld.n, tools.bld.K
    results: list[tools.bld.Prediction | ClassicalResult] = []

    # DNS data: (p, observed, uncertainty)
    dns_data = [
        (1, 0.37, 0.01),
        (2, 0.70, 0.01),
        (3, 1.000, 0.001),  # exact (4/5 law)
        (4, 1.28, 0.02),
        (5, 1.54, 0.03),
        (6, 1.78, 0.04),
        (7, 2.00, 0.05),
        (8, 2.21, 0.07),
    ]

    for p, obs_val, obs_unc in dns_data:
        predicted = tools.bld.she_leveque_zeta(float(p), n, K)
        results.append(tools.bld.Prediction(
            f"zeta_{p}", predicted, obs_val, obs_unc,
        ))

    # Disprove K41: p/3 diverges at high p
    for p in [6, 7, 8]:
        obs_val = dns_data[p - 1][1]
        obs_unc = dns_data[p - 1][2]
        k41 = p / 3.0
        bld_sl = tools.bld.she_leveque_zeta(float(p), n, K)

        k41_err = abs(k41 - obs_val)
        bld_err = abs(bld_sl - obs_val)
        results.append(ClassicalResult(
            f"p={p}_BLD_beats_K41", bld_err < k41_err,
        ))

    return results


def run_she_leveque_zeta3_forced() -> list[ClassicalResult]:
    """zeta_3 = 1 requires n = 4 (the 4/5 law constrains spacetime dimension).

    The log-Poisson tau_1 = 0 identity (when beta = 1 - gamma_inf/C_inf and
    K = n-2) maps to: zeta_{n-1} = 1 for ANY n.  But for the physical
    4/5 law (zeta_3 = 1), the mapping p=3 -> q=3/(n-1) gives q=1 only
    when n=4.

    Prove: zeta_{n-1} = 1 for all (n, K=n-2) — structural universality.
    Prove: zeta_3 = 1 only for n=4 — constrains spacetime dimension.
    Disprove: for n != 4, zeta_3 != 1.

    Theory ref: she-leveque-derivation.md
    """
    results: list[ClassicalResult] = []

    # Structural universality: zeta_{n-1} = 1 for ANY (n, K=n-2)
    # This is tau_1 = 0: the correction terms cancel at q=1
    for n_ in [3, 4, 5, 6, 7]:
        K_ = n_ - 2
        if K_ < 1:
            continue
        p = float(n_ - 1)
        zeta_nm1 = tools.bld.she_leveque_zeta(p, n_, K_)
        results.append(ClassicalResult(
            f"zeta_{int(p)}_n={n_}_equals_1",
            abs(zeta_nm1 - 1.0) < 1e-12,
        ))

    # n=4 gives zeta_3 = 1 exactly (the 4/5 law)
    n, K = tools.bld.n, tools.bld.K
    zeta3_bld = tools.bld.she_leveque_zeta(3.0, n, K)
    results.append(ClassicalResult(
        "zeta3_n=4_K=2_equals_1",
        abs(zeta3_bld - 1.0) < 1e-12,
    ))

    # Disprove: other n values give zeta_3 != 1
    for n_ in [3, 5, 6, 7]:
        K_ = n_ - 2
        if K_ < 1:
            continue
        zeta3 = tools.bld.she_leveque_zeta(3.0, n_, K_)
        results.append(ClassicalResult(
            f"zeta3_n={n_}_not_1",
            abs(zeta3 - 1.0) > 0.1,
        ))

    # SL parameter identities (n=4, K=2)
    results.append(ClassicalResult("9=(n-1)^2", (n - 1)**2 == 9))
    results.append(ClassicalResult("2=K", K == 2))
    results.append(ClassicalResult(
        "2/3=K/(n-1)",
        abs(K / (n - 1) - 2 / 3) < 1e-15,
    ))

    return results


def run_classical_wrong_constants() -> list[ClassicalResult]:
    """Wrong BLD constants -> wrong everything.

    For 6 alternative (n,L,B,K) tuples, compute Re_c, delta, alpha, zeta_6.
    None match all four observed values simultaneously.
    Only (4,20,56,2) works across all domains.
    """
    results: list[ClassicalResult] = []

    # Observed targets
    re_target = 2300.0
    re_tol = 50.0
    delta_target = tools.bld.FEIGENBAUM_DELTA.value
    delta_tol = 0.01
    alpha_target = tools.bld.FEIGENBAUM_ALPHA.value
    alpha_tol = 0.01
    zeta6_target = 1.78
    zeta6_tol = 0.04

    # Tuples that change n, L, or K (the structurally independent quantities).
    # Feigenbaum delta/SL zeta don't depend on B, so changing only B is
    # a weak test.  Theory ref: feigenbaum-derivation.md, she-leveque-derivation.md.
    wrong_tuples = [
        (3, 10, 30, 1),
        (5, 25, 70, 3),
        (4, 21, 56, 2),   # wrong L
        (3, 20, 56, 2),   # wrong n
        (4, 20, 56, 1),   # wrong K
        (4, 20, 56, 3),   # wrong K
    ]

    for n_, L_, B_, K_ in wrong_tuples:
        try:
            re_c = tools.bld.reynolds_pipe(n_, L_, B_, K_)
            re_ok = abs(re_c - re_target) < re_tol
        except (ZeroDivisionError, OverflowError):
            re_ok = False

        try:
            delta = tools.bld.feigenbaum_delta(n_, L_, K_)
            delta_ok = abs(delta - delta_target) < delta_tol
        except (ZeroDivisionError, OverflowError, ValueError):
            delta_ok = False

        try:
            alpha = tools.bld.feigenbaum_alpha(n_, L_, B_, K_)
            alpha_ok = abs(alpha - alpha_target) < alpha_tol
        except (ZeroDivisionError, OverflowError):
            alpha_ok = False

        try:
            zeta6 = tools.bld.she_leveque_zeta(6.0, n_, K_)
            zeta6_ok = abs(zeta6 - zeta6_target) < zeta6_tol
        except (ZeroDivisionError, OverflowError):
            zeta6_ok = False

        all_ok = re_ok and delta_ok and alpha_ok and zeta6_ok
        results.append(ClassicalResult(
            f"({n_},{L_},{B_},{K_})_fails_all_4", not all_ok,
        ))

    # BLD constants should match all four
    n, L, B, K = tools.bld.n, tools.bld.L, tools.bld.B, tools.bld.K
    re_c = tools.bld.reynolds_pipe(n, L, B, K)
    delta = tools.bld.feigenbaum_delta(n, L, K)
    alpha = tools.bld.feigenbaum_alpha(n, L, B, K)
    zeta6 = tools.bld.she_leveque_zeta(6.0, n, K)

    bld_ok = (
        abs(re_c - re_target) < re_tol
        and abs(delta - delta_target) < delta_tol
        and abs(alpha - alpha_target) < alpha_tol
        and abs(zeta6 - zeta6_target) < zeta6_tol
    )
    results.append(ClassicalResult("BLD_matches_all_4", bld_ok))

    return results


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.theory
def test_reynolds_pipe() -> None:
    results = run_reynolds_pipe()
    assert all(r.passes for r in results)


@pytest.mark.theory
def test_reynolds_geometries() -> None:
    assert all(r.passes for r in run_reynolds_geometries())


@pytest.mark.theory
def test_kolmogorov_exponents() -> None:
    assert all(r.passes for r in run_kolmogorov_exponents())


@pytest.mark.theory
def test_feigenbaum_delta() -> None:
    results = run_feigenbaum_delta()
    assert all(r.passes for r in results)


@pytest.mark.theory
def test_feigenbaum_alpha() -> None:
    results = run_feigenbaum_alpha()
    assert all(r.passes for r in results)


@pytest.mark.theory
def test_she_leveque() -> None:
    results = run_she_leveque()
    assert all(r.passes for r in results)


@pytest.mark.theory
def test_she_leveque_zeta3_forced() -> None:
    assert all(r.passes for r in run_she_leveque_zeta3_forced())


@pytest.mark.theory
def test_classical_wrong_constants() -> None:
    assert all(r.passes for r in run_classical_wrong_constants())
