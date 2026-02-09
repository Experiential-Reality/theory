"""Cosmological predictions from BLD theory — attempt to disprove.

Each test is structured as a falsification attempt: compute predictions from
BLD constants, compare against observations, and try to break the theory by
showing alternative constants work equally well or that the formulas are
overfitting.

Theory refs: dark-matter-mapping.md, hubble-tension.md, sigma8-tension.md
"""

import tools.bld

from helpers import assert_all_pass

TR = tools.bld.TestResult


# ---------------------------------------------------------------------------
# Positive: do BLD predictions match observations?
# ---------------------------------------------------------------------------


def run_dark_matter_fractions() -> list[tools.bld.Prediction]:
    """BLD predicts cosmic composition from x = baryon fraction alone."""
    x = tools.bld.OMEGA_BARYON.value
    dm = tools.bld.dark_matter_fraction(x, tools.bld.n, tools.bld.L, tools.bld.K)
    de = tools.bld.dark_energy_fraction(x, tools.bld.n, tools.bld.L, tools.bld.K)
    return [
        tools.bld.Prediction("dark_matter", dm,
                             tools.bld.OMEGA_DARK_MATTER.value,
                             tools.bld.OMEGA_DARK_MATTER.uncertainty),
        tools.bld.Prediction("dark_energy", de,
                             tools.bld.OMEGA_DARK_ENERGY.value,
                             tools.bld.OMEGA_DARK_ENERGY.uncertainty),
    ]


def run_hubble_tension() -> tools.bld.Prediction:
    """BLD predicts H₀(local) = H₀(CMB) × 13/12."""
    h0 = tools.bld.hubble_local(
        tools.bld.H0_CMB.value, tools.bld.K, tools.bld.n, tools.bld.L,
    )
    return tools.bld.Prediction("hubble_local", h0,
                                tools.bld.H0_LOCAL.value,
                                tools.bld.H0_LOCAL.uncertainty)


def run_sigma8_tension() -> list[tools.bld.Prediction]:
    """BLD predicts σ₈ at CMB and local scales."""
    s8_cmb = tools.bld.sigma8_cmb(tools.bld.L, tools.bld.n, tools.bld.K)
    s8_loc = tools.bld.sigma8_local(tools.bld.L, tools.bld.n, tools.bld.K)
    return [
        tools.bld.Prediction("sigma8_cmb", s8_cmb,
                             tools.bld.SIGMA8_CMB.value,
                             tools.bld.SIGMA8_CMB.uncertainty),
        tools.bld.Prediction("sigma8_local", s8_loc,
                             tools.bld.SIGMA8_LOCAL.value,
                             tools.bld.SIGMA8_LOCAL.uncertainty),
    ]


# ---------------------------------------------------------------------------
# Exact algebraic structure — falsifiable as measurements tighten
# ---------------------------------------------------------------------------


def run_exact_rational_fractions() -> list[TR]:
    """BLD predictions are exact rational fractions, not fits.

    Hubble:    1 + K/(n+L) = 1 + 2/24 = 13/12
    σ₈(prim):  L/(n+L) = 20/24 = 5/6
    σ₈(CMB):   (5/6)(78/80) = 13/16
    σ₈(local): (13/16)(38/40) = 247/320

    If any measured value drifts outside these fractions by more than its
    uncertainty, the theory is falsified.
    """
    eps = tools.bld.FLOAT_EPSILON
    factor = 1.0 + tools.bld.K / (tools.bld.n + tools.bld.L)
    s8p = tools.bld.sigma8_primordial(tools.bld.L, tools.bld.n)
    s8c = tools.bld.sigma8_cmb(tools.bld.L, tools.bld.n, tools.bld.K)
    s8l = tools.bld.sigma8_local(tools.bld.L, tools.bld.n, tools.bld.K)
    return [
        TR("hubble_factor_13/12", abs(factor - 13 / 12) < eps, factor),
        TR("sigma8_primordial_5/6", abs(s8p - 5 / 6) < eps, s8p),
        TR("sigma8_cmb_13/16", abs(s8c - 13 / 16) < eps, s8c),
        TR("sigma8_local_247/320", abs(s8l - 247 / 320) < eps, s8l),
    ]


# ---------------------------------------------------------------------------
# Negative: attempt to disprove by finding alternative constants that work
# ---------------------------------------------------------------------------


def run_hubble_x_uniqueness() -> TR:
    """Try to break Hubble prediction by finding a better X among all composites.

    The theory says X = n+L.  Sweep every BLD composite: if any composite
    produces a closer match to H₀(local) than n+L does, the theory's
    structural argument for X = n+L is undermined.
    """
    h0_cmb = tools.bld.H0_CMB.value
    h0_obs = tools.bld.H0_LOCAL.value
    correct_x = tools.bld.n + tools.bld.L
    best_err = abs(h0_cmb * (1.0 + tools.bld.K / correct_x) - h0_obs)
    composites = tools.bld.bld_composites(
        tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S,
    )
    for name, x_val in composites.items():
        if x_val <= 0 or x_val == correct_x:
            continue
        err = abs(h0_cmb * (1.0 + tools.bld.K / x_val) - h0_obs)
        if err < best_err:
            return TR(f"n+L_beaten_by_{name}({x_val})", False, err)
    return TR("n+L_is_best", True, best_err)


def run_cross_domain_k() -> list[TR]:
    """Try to break cross-domain consistency by varying K.

    K=2 must simultaneously satisfy:
    - α⁻¹ within CODATA uncertainty (particle physics)
    - H₀(local) within SH0ES uncertainty (cosmology)
    - dark matter fraction within Planck uncertainty (cosmology)

    If K=1 or K=3 also works, the theory isn't uniquely constrained.
    """
    x = tools.bld.OMEGA_BARYON.value
    results = []
    for k_test in (1, 2, 3):
        alpha = tools.bld.alpha_inv(tools.bld.n, tools.bld.L, tools.bld.B, k_test)
        alpha_ok = (abs(alpha - tools.bld.ALPHA_INV.value)
                    < tools.bld.SIGMA_THRESHOLD * tools.bld.ALPHA_INV.uncertainty)

        h0 = tools.bld.hubble_local(tools.bld.H0_CMB.value, k_test, tools.bld.n, tools.bld.L)
        h0_ok = abs(h0 - tools.bld.H0_LOCAL.value) < tools.bld.H0_LOCAL.uncertainty

        dm = tools.bld.dark_matter_fraction(x, tools.bld.n, tools.bld.L, k_test)
        dm_ok = abs(dm - tools.bld.OMEGA_DARK_MATTER.value) < tools.bld.OMEGA_DARK_MATTER.uncertainty

        all_pass = alpha_ok and h0_ok and dm_ok
        expected = (k_test == 2)
        results.append(TR(f"K={k_test}", all_pass == expected))
    return results


def run_observer_correction_necessity() -> list[TR]:
    """Try to disprove the observer correction term K*n*x² in dark matter.

    Without it (linear model: dark_matter = 5x), the prediction is 0.245.
    With it (quadratic: 5x + 8x²), the prediction shifts to ~0.264.
    Test that the linear model is worse — the observer correction is necessary.
    """
    x = tools.bld.OMEGA_BARYON.value
    obs = tools.bld.OMEGA_DARK_MATTER.value
    linear_only = (tools.bld.L / tools.bld.n) * x
    with_correction = tools.bld.dark_matter_fraction(
        x, tools.bld.n, tools.bld.L, tools.bld.K,
    )
    linear_err = abs(linear_only - obs)
    corrected_err = abs(with_correction - obs)
    return [
        TR("linear_worse", linear_err > corrected_err, linear_err),
        TR("correction_improves",
           corrected_err < tools.bld.OMEGA_DARK_MATTER.uncertainty,
           corrected_err),
    ]


def run_overconstrained() -> TR:
    """BLD is overconstrained: 7 predictions from 3 constants (n, L, K).

    dark_matter, dark_energy, H₀(local), σ₈(CMB), σ₈(local), Hubble
    factor, σ₈(primordial) — all from n=4, L=20, K=2.

    A generic model with 3 free parameters could fit at most 3 data points.
    BLD fits 5 independent observations (dark_matter, H₀, σ₈(CMB),
    σ₈(local), dark_energy) with 0 free parameters.

    Count how many pass — all 5 must pass for the theory to survive.
    """
    x = tools.bld.OMEGA_BARYON.value
    checks = [
        ("dm", tools.bld.dark_matter_fraction(x, tools.bld.n, tools.bld.L, tools.bld.K),
         tools.bld.OMEGA_DARK_MATTER),
        ("de", tools.bld.dark_energy_fraction(x, tools.bld.n, tools.bld.L, tools.bld.K),
         tools.bld.OMEGA_DARK_ENERGY),
        ("h0", tools.bld.hubble_local(tools.bld.H0_CMB.value, tools.bld.K, tools.bld.n, tools.bld.L),
         tools.bld.H0_LOCAL),
        ("s8c", tools.bld.sigma8_cmb(tools.bld.L, tools.bld.n, tools.bld.K),
         tools.bld.SIGMA8_CMB),
        ("s8l", tools.bld.sigma8_local(tools.bld.L, tools.bld.n, tools.bld.K),
         tools.bld.SIGMA8_LOCAL),
    ]
    n_pass = sum(
        1 for _, pred, obs in checks
        if abs(pred - obs.value) < tools.bld.SIGMA_THRESHOLD * obs.uncertainty
    )
    return TR("overconstrained_5_of_5", n_pass == len(checks), n_pass)


def run_wrong_constants() -> list[TR]:
    """Perturb each BLD constant ±1.  All perturbations must break something.

    If a perturbation still satisfies all cosmological predictions, the
    theory is underdetermined at that constant.
    """
    x = tools.bld.OMEGA_BARYON.value
    perturbations = [
        ("n=3", 3, tools.bld.L, tools.bld.K),
        ("n=5", 5, tools.bld.L, tools.bld.K),
        ("L=19", tools.bld.n, 19, tools.bld.K),
        ("L=21", tools.bld.n, 21, tools.bld.K),
        ("K=1", tools.bld.n, tools.bld.L, 1),
        ("K=3", tools.bld.n, tools.bld.L, 3),
    ]
    results = []
    for name, n_, L_, K_ in perturbations:
        dm = tools.bld.dark_matter_fraction(x, n_, L_, K_)
        h0 = tools.bld.hubble_local(tools.bld.H0_CMB.value, K_, n_, L_)
        s8 = tools.bld.sigma8_cmb(L_, n_, K_)
        dm_ok = abs(dm - tools.bld.OMEGA_DARK_MATTER.value) < tools.bld.OMEGA_DARK_MATTER.uncertainty
        h0_ok = abs(h0 - tools.bld.H0_LOCAL.value) < tools.bld.H0_LOCAL.uncertainty
        s8_ok = abs(s8 - tools.bld.SIGMA8_CMB.value) < tools.bld.SIGMA8_CMB.uncertainty
        results.append(TR(f"wrong_{name}", not (dm_ok and h0_ok and s8_ok)))
    return results


def run_formula_consistency() -> list[TR]:
    """dark_energy must equal 1 - x - dark_matter for all x, not just observed.

    Tests algebraic consistency of the two formulas across a range of baryon
    fractions.  If the formulas are independently wrong but happen to agree
    at x=0.049, sweeping other x values would expose the inconsistency.
    """
    results = []
    for x in (0.01, 0.049, 0.10, 0.20):
        dm = tools.bld.dark_matter_fraction(x, tools.bld.n, tools.bld.L, tools.bld.K)
        de = tools.bld.dark_energy_fraction(x, tools.bld.n, tools.bld.L, tools.bld.K)
        residual = abs(x + dm + de - 1.0)
        results.append(TR(f"partition_x={x}", residual < tools.bld.FLOAT_EPSILON, residual))
    return results


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_dark_matter_fractions() -> None:
    assert_all_pass(run_dark_matter_fractions())


def test_hubble_tension() -> None:
    pred = run_hubble_tension()
    assert pred.passes, (pred.predicted, pred.observed, pred.sigma)


def test_sigma8_tension() -> None:
    assert_all_pass(run_sigma8_tension())


def test_exact_rational_fractions() -> None:
    assert_all_pass(run_exact_rational_fractions())


def test_hubble_x_uniqueness() -> None:
    result = run_hubble_x_uniqueness()
    assert result.passes, result.name


def test_cross_domain_k() -> None:
    assert_all_pass(run_cross_domain_k())


def test_observer_correction_necessity() -> None:
    assert_all_pass(run_observer_correction_necessity())


def test_overconstrained() -> None:
    result = run_overconstrained()
    assert result.passes, f"only {int(result.value)} of 5 predictions match"


def test_wrong_constants() -> None:
    assert_all_pass(run_wrong_constants())


def test_formula_consistency() -> None:
    assert_all_pass(run_formula_consistency())
