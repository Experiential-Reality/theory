"""Classical physics prediction tests.

Tests Reynolds number, Kolmogorov exponents, Feigenbaum constants, and
She-Leveque structure functions.  Each test proves the BLD prediction
matches experiment and attempts to disprove it by trying alternatives.

Theory refs:
  - reynolds-derivation.md (Re_c formulas)
  - feigenbaum-derivation.md (delta, alpha)
  - she-leveque-derivation.md (zeta_p structure functions)
"""

import fractions
import math

import numpy as np
import pytest

import tools.bld


TR = tools.bld.TestResult


# ---------------------------------------------------------------------------
# Run functions
# ---------------------------------------------------------------------------


def run_reynolds_pipe() -> list[tools.bld.Prediction | TR]:
    """Re_c(pipe) = (nLB/K)(38/37) = 2300.5.

    Net confinement X = B - L + 1 = 37.
    Correction (X+1)/X = 38/37 follows universal (structure+observer)/structure.

    Prove: matches empirical 2300 within 0.5.
    Disprove: wrong (n,L,B) tuples.
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.RE_PIPE_OBSERVED
    results: list[tools.bld.Prediction | TR] = []

    # Prove: BLD prediction matches
    predicted = tools.bld.reynolds_pipe(n, L, B, K)
    results.append(tools.bld.Prediction(
        "Re_c_pipe", predicted, obs.value, obs.uncertainty,
    ))

    # Verify internal structure
    X = B - L + 1
    results.append(TR("X=B-L+1=37", X == 37))
    results.append(TR(
        "correction=38/37",
        abs((X + 1) / X - 38 / 37) < tools.bld.FLOAT_EPSILON,
    ))

    # Disprove: wrong BLD constants
    # B+-1 changes Re_c by only ~2% (within empirical tolerance), so test
    # tuples that change n or L -- the structurally independent quantities.
    # Theory ref: reynolds-derivation.md -- B = n(S+1) is derived, not free.
    wrong_tuples = [(3, 10, 30, 1), (5, 25, 70, 3), (3, 20, 56, 2), (6, 10, 60, 4)]
    for n_, L_, B_, K_ in wrong_tuples:
        alt = tools.bld.reynolds_pipe(n_, L_, B_, K_)
        matches = abs(alt - obs.value) < 50
        results.append(TR(
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

    obs_flat = tools.bld.RE_FLAT_PLATE
    obs_sphere = tools.bld.RE_SPHERE
    obs_jet = tools.bld.RE_JET

    re_flat = tools.bld.reynolds_flat_plate(re_pipe, n, B)
    results.append(tools.bld.Prediction(
        "Re_c_flat_plate", re_flat, obs_flat.value, obs_flat.uncertainty,
    ))

    re_sphere = tools.bld.reynolds_sphere(re_pipe, n, L, K)
    results.append(tools.bld.Prediction(
        "Re_c_sphere", re_sphere, obs_sphere.value, obs_sphere.uncertainty,
    ))

    re_jet = tools.bld.reynolds_jet(re_pipe, K)
    results.append(tools.bld.Prediction(
        "Re_c_jet", re_jet, obs_jet.value, obs_jet.uncertainty,
    ))

    return results


def run_kolmogorov_exponents() -> list[TR]:
    """Exact rational identities from BLD.

    -5/3 = -L/(n(n-1)) = -20/12  (Kolmogorov energy spectrum)
    2/3 = K/(n-1) = 2/3          (dissipation exponent)
    1/25 = 1/(L+n+1)             (intermittency correction)

    Use fractions.Fraction for exact equality.
    Disprove: wrong n in {3, 5, 6}.
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    results: list[TR] = []

    # Exact rational arithmetic
    F = fractions.Fraction

    # -5/3 = -L/(n(n-1))
    kolmogorov = -F(L, n * (n - 1))
    results.append(TR(
        "-L/(n(n-1))=-5/3", kolmogorov == F(-5, 3),
    ))

    # 2/3 = K/(n-1)
    dissipation = F(K, n - 1)
    results.append(TR(
        "K/(n-1)=2/3", dissipation == F(2, 3),
    ))

    # 1/25 = 1/(L+n+1)
    intermittency = F(1, L + n + 1)
    results.append(TR(
        "1/(L+n+1)=1/25", intermittency == F(1, 25),
    ))

    # Disprove: wrong n values
    for n_ in [3, 5, 6]:
        L_ = n_**2 * (n_**2 - 1) // 12
        if L_ < 1:
            continue
        alt = -F(L_, n_ * (n_ - 1))
        results.append(TR(
            f"n={n_}_kolmogorov={alt}_not_-5/3", alt != F(-5, 3),
        ))

    return results


def run_feigenbaum_delta() -> list[tools.bld.Prediction | TR]:
    """delta = sqrt(L + K - K^2/L + 1/e^X) where X = n + K + K/n + 1/L.

    Prove: matches delta = 4.6692016091 within 0.0003%.
    Verify: e-correction improves precision ~100x over first-order.
    """
    L, n, K = tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.FEIGENBAUM_DELTA
    results: list[tools.bld.Prediction | TR] = []

    # Full prediction with e-correction
    predicted = tools.bld.feigenbaum_delta(n, L, K)
    results.append(tools.bld.Prediction(
        "delta", predicted, obs.value, tools.bld.FEIGENBAUM_DELTA_TOL,
    ))

    # First-order (no e-correction)
    delta_first = math.sqrt(L + K - K**2 / L)
    err_first = abs(delta_first - obs.value)
    err_full = abs(predicted - obs.value)

    # e-correction improves precision by ~100x
    improvement = err_first / err_full if err_full > 0 else float("inf")
    results.append(TR(
        f"e_correction_100x_better_{improvement:.0f}x",
        improvement > tools.bld.IMPROVEMENT_THRESHOLD,
    ))

    return results


def run_feigenbaum_alpha() -> list[tools.bld.Prediction | TR]:
    """alpha = K + 1/K + 1/((n+K)B) - 1/(D*e^X).

    Prove: matches alpha = 2.5029078750 within 0.00001%.
    Cross-check: fractal dimension D_f = ln2/ln(alpha).
    Cross-check: product alpha*delta.
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.FEIGENBAUM_ALPHA
    obs_delta = tools.bld.FEIGENBAUM_DELTA
    results: list[tools.bld.Prediction | TR] = []

    # Full prediction
    predicted = tools.bld.feigenbaum_alpha(n, L, B, K)
    results.append(tools.bld.Prediction(
        "alpha_feig", predicted, obs.value, tools.bld.FEIGENBAUM_ALPHA_TOL,
    ))

    # First-order (no e-correction)
    alpha_first = K + 1.0 / K + 1.0 / ((n + K) * B)
    err_first = abs(alpha_first - obs.value)
    err_full = abs(predicted - obs.value)
    improvement = err_first / err_full if err_full > 0 else float("inf")
    results.append(TR(
        f"e_correction_improves_{improvement:.0f}x",
        improvement > tools.bld.IMPROVEMENT_THRESHOLD,
    ))

    # Cross-check: fractal dimension
    D_f_bld = math.log(2) / math.log(predicted)
    D_f_obs = math.log(2) / math.log(obs.value)
    results.append(TR(
        "fractal_dim_match",
        abs(D_f_bld - D_f_obs) < 1e-6,
    ))

    # Cross-check: product alpha*delta
    delta_bld = tools.bld.feigenbaum_delta(n, L, K)
    product_bld = predicted * delta_bld
    product_obs = obs.value * obs_delta.value
    results.append(TR(
        "alpha_delta_product",
        abs(product_bld - product_obs) / product_obs < 0.001,
    ))

    return results


def run_she_leveque() -> list[tools.bld.Prediction | TR]:
    """zeta_p = p/9 + 2[1 - (2/3)^(p/3)] for p=1..8.

    Vectorized: evaluate all p values and K41 comparison in numpy broadcasts.
    Prove: matches DNS data within measurement uncertainty.
    Disprove: K41 (p/3) diverges from DNS at high p.
    """
    n, K = tools.bld.n, tools.bld.K
    results: list[tools.bld.Prediction | TR] = []

    # DNS data: from module constants
    p_vals = np.arange(1, 9, dtype=np.float64)
    obs_vals = np.array(tools.bld.SL_DNS_ZETA)
    obs_uncs = np.array(tools.bld.SL_DNS_UNC)

    # Vectorized BLD She-Leveque: zeta_p = p/(n-1)^2 + K[1 - (K/(n-1))^(p/(n-1))]
    bld_zeta = p_vals / (n - 1)**2 + K * (1 - (K / (n - 1))**(p_vals / (n - 1)))

    for i in range(8):
        results.append(tools.bld.Prediction(
            f"zeta_{int(p_vals[i])}", float(bld_zeta[i]),
            float(obs_vals[i]), float(obs_uncs[i]),
        ))

    # Disprove K41: vectorized comparison at p=6,7,8
    high_p = np.array([6, 7, 8], dtype=np.float64)
    high_idx = high_p.astype(int) - 1
    k41 = high_p / 3.0
    bld_high = high_p / (n - 1)**2 + K * (1 - (K / (n - 1))**(high_p / (n - 1)))
    k41_err = np.abs(k41 - obs_vals[high_idx])
    bld_err = np.abs(bld_high - obs_vals[high_idx])

    for i, p in enumerate([6, 7, 8]):
        results.append(TR(
            f"p={p}_BLD_beats_K41", bool(bld_err[i] < k41_err[i]),
        ))

    return results


def run_she_leveque_zeta3_forced() -> list[TR]:
    """zeta_3 = 1 requires n = 4 (the 4/5 law constrains spacetime dimension).

    The log-Poisson tau_1 = 0 identity (when beta = 1 - gamma_inf/C_inf and
    K = n-2) maps to: zeta_{n-1} = 1 for ANY n.  But for the physical
    4/5 law (zeta_3 = 1), the mapping p=3 -> q=3/(n-1) gives q=1 only
    when n=4.

    Prove: zeta_{n-1} = 1 for all (n, K=n-2) -- structural universality.
    Prove: zeta_3 = 1 only for n=4 -- constrains spacetime dimension.
    Disprove: for n != 4, zeta_3 != 1.

    Theory ref: she-leveque-derivation.md
    """
    results: list[TR] = []

    # Structural universality: zeta_{n-1} = 1 for ANY (n, K=n-2)
    # This is tau_1 = 0: the correction terms cancel at q=1
    for n_ in [3, 4, 5, 6, 7]:
        K_ = n_ - 2
        if K_ < 1:
            continue
        p = float(n_ - 1)
        zeta_nm1 = tools.bld.she_leveque_zeta(p, n_, K_)
        results.append(TR(
            f"zeta_{int(p)}_n={n_}_equals_1",
            abs(zeta_nm1 - 1.0) < 1e-12,
        ))

    # n=4 gives zeta_3 = 1 exactly (the 4/5 law)
    n, K = tools.bld.n, tools.bld.K
    zeta3_bld = tools.bld.she_leveque_zeta(3.0, n, K)
    results.append(TR(
        "zeta3_n=4_K=2_equals_1",
        abs(zeta3_bld - 1.0) < 1e-12,
    ))

    # Disprove: other n values give zeta_3 != 1
    for n_ in [3, 5, 6, 7]:
        K_ = n_ - 2
        if K_ < 1:
            continue
        zeta3 = tools.bld.she_leveque_zeta(3.0, n_, K_)
        results.append(TR(
            f"zeta3_n={n_}_not_1",
            abs(zeta3 - 1.0) > 0.1,
        ))

    # SL parameter identities (n=4, K=2)
    results.append(TR("9=(n-1)^2", (n - 1)**2 == 9))
    results.append(TR("2=K", K == 2))
    results.append(TR(
        "2/3=K/(n-1)",
        abs(K / (n - 1) - 2 / 3) < tools.bld.FLOAT_EPSILON,
    ))

    return results


# Dispatch table for classical wrong-constant checks.
# Each entry: (name, formula(n_, L_, B_, K_) -> float, target, tolerance)
_CLASSICAL_CHECKS: tuple[tuple[str, object, float, float], ...] = (
    ("re_c", lambda n_, L_, B_, K_: tools.bld.reynolds_pipe(n_, L_, B_, K_),
     tools.bld.RE_PIPE_OBSERVED.value, 50.0),
    ("delta", lambda n_, L_, B_, K_: tools.bld.feigenbaum_delta(n_, L_, K_),
     tools.bld.FEIGENBAUM_DELTA.value, 0.01),
    ("alpha", lambda n_, L_, B_, K_: tools.bld.feigenbaum_alpha(n_, L_, B_, K_),
     tools.bld.FEIGENBAUM_ALPHA.value, 0.01),
    ("zeta6", lambda n_, L_, B_, K_: tools.bld.she_leveque_zeta(6.0, n_, K_),
     tools.bld.SL_DNS_ZETA[5], tools.bld.SL_DNS_UNC[5]),
)


def _check_classical_tuple(n_: int, L_: int, B_: int, K_: int) -> bool:
    """Check if a (n, L, B, K) tuple matches all 4 classical predictions."""
    for _name, fn, target, tol in _CLASSICAL_CHECKS:
        try:
            if abs(fn(n_, L_, B_, K_) - target) >= tol:
                return False
        except (ZeroDivisionError, OverflowError, ValueError):
            return False
    return True


def run_classical_wrong_constants() -> list[TR]:
    """Wrong BLD constants -> wrong everything.

    Systematic grid: n in 2..8, K in 1..6, L from Riemann identity,
    B = n(S+1) where S = K^2+(n-1)^2.  Evaluate Re_c, delta, alpha, zeta_6
    for all structurally consistent tuples.  Only (4,20,56,2) matches all four.

    Theory ref: feigenbaum/SL depend on (n,L,K) not B, so the grid must
    vary the structurally independent quantities.
    """
    results: list[TR] = []

    # Systematic grid: derive (L, B) from (n, K) via BLD identities
    n_tested = 0
    n_passed = 0
    for n_ in range(2, 9):
        for K_ in range(1, 7):
            L_ = n_**2 * (n_**2 - 1) // 12
            if L_ < 1:
                continue
            S_ = K_**2 + (n_ - 1)**2
            B_ = n_ * (S_ + 1)

            n_tested += 1
            if _check_classical_tuple(n_, L_, B_, K_):
                n_passed += 1

    # Exactly one tuple should pass: (4,20,56,2)
    results.append(TR(
        f"BLD_unique_in_{n_tested}_tuples({n_passed}_match)",
        n_passed == 1,
    ))

    # Verify BLD itself passes
    n, L, B, K = tools.bld.n, tools.bld.L, tools.bld.B, tools.bld.K
    results.append(TR("BLD_matches_all_4", _check_classical_tuple(n, L, B, K)))

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
