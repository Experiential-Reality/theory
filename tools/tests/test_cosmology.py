"""Cosmological predictions from BLD theory — attempt to disprove.

Each test is structured as a falsification attempt: compute predictions from
BLD constants, compare against observations, and try to break the theory by
showing alternative constants work equally well or that the formulas are
overfitting.

Theory refs: dark-matter-mapping.md, hubble-tension.md, sigma8-tension.md,
             baryon-asymmetry.md, hubble-absolute.md
"""

import numpy as np

import tools.bld

from helpers import assert_all_pass

TR = tools.bld.TestResult


# Positive: do BLD predictions match observations?


def test_dark_matter_fractions() -> None:
    """BLD predicts cosmic composition from x = baryon fraction alone."""
    x = tools.bld.OMEGA_BARYON.value
    dm = tools.bld.dark_matter_fraction(x, tools.bld.n, tools.bld.L, tools.bld.K)
    de = tools.bld.dark_energy_fraction(x, tools.bld.n, tools.bld.L, tools.bld.K)
    results = [
        tools.bld.Prediction("dark_matter", dm,
                             tools.bld.OMEGA_DARK_MATTER.value,
                             tools.bld.OMEGA_DARK_MATTER.uncertainty),
        tools.bld.Prediction("dark_energy", de,
                             tools.bld.OMEGA_DARK_ENERGY.value,
                             tools.bld.OMEGA_DARK_ENERGY.uncertainty),
    ]
    assert_all_pass(results)


def test_hubble_tension() -> None:
    """BLD predicts H₀(local) = H₀(CMB) × 13/12."""
    h0 = tools.bld.hubble_local(
        tools.bld.H0_CMB.value, tools.bld.K, tools.bld.n, tools.bld.L,
    )
    pred = tools.bld.Prediction("hubble_local", h0,
                                tools.bld.H0_LOCAL.value,
                                tools.bld.H0_LOCAL.uncertainty)
    assert pred.passes, (pred.predicted, pred.observed, pred.sigma)


def test_sigma8_tension() -> None:
    """BLD predicts σ₈ at CMB and local scales."""
    s8_cmb = tools.bld.sigma8_cmb(tools.bld.L, tools.bld.n, tools.bld.K)
    s8_loc = tools.bld.sigma8_local(tools.bld.L, tools.bld.n, tools.bld.K)
    results = [
        tools.bld.Prediction("sigma8_cmb", s8_cmb,
                             tools.bld.SIGMA8_CMB.value,
                             tools.bld.SIGMA8_CMB.uncertainty),
        tools.bld.Prediction("sigma8_local", s8_loc,
                             tools.bld.SIGMA8_LOCAL.value,
                             tools.bld.SIGMA8_LOCAL.uncertainty),
    ]
    assert_all_pass(results)


# Exact algebraic structure — falsifiable as measurements tighten


def test_exact_rational_fractions() -> None:
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
    results = [
        TR("hubble_factor_13/12", abs(factor - 13 / 12) < eps, factor),
        TR("sigma8_primordial_5/6", abs(s8p - 5 / 6) < eps, s8p),
        TR("sigma8_cmb_13/16", abs(s8c - 13 / 16) < eps, s8c),
        TR("sigma8_local_247/320", abs(s8l - 247 / 320) < eps, s8l),
    ]
    assert_all_pass(results)


# Negative: attempt to disprove by finding alternative constants that work


def test_hubble_x_uniqueness() -> None:
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
            result = TR(f"n+L_beaten_by_{name}({x_val})", False, err)
            assert result.passes, result.name
    result = TR("n+L_is_best", True, best_err)
    assert result.passes, result.name


def test_cross_domain_k() -> None:
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
    assert_all_pass(results)


def test_observer_correction_necessity() -> None:
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
    results = [
        TR("linear_worse", linear_err > corrected_err, linear_err),
        TR("correction_improves",
           corrected_err < tools.bld.OMEGA_DARK_MATTER.uncertainty,
           corrected_err),
    ]
    assert_all_pass(results)


def test_overconstrained() -> None:
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
    result = TR("overconstrained_5_of_5", n_pass == len(checks), n_pass)
    assert result.passes, f"only {int(result.value)} of 5 predictions match"


def test_wrong_constants() -> None:
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
    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Baryon asymmetry and H₀ absolute value
# ---------------------------------------------------------------------------


def test_baryon_asymmetry() -> None:
    """BLD predicts eta = (K/B)(1/L)^6 × S/(S-1) ≈ 6.05e-10.

    Prove: matches Planck 2018 within 3σ.
    Disprove: exhaustive sweep over Lorentz exponents d = 1..12.
    Only d = 6 = n(n-1)/2 = dim(SO(3,1)) gives eta within 3σ.
    """
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S
    obs = tools.bld.ETA_BARYON
    tol = tools.bld.SIGMA_THRESHOLD * obs.uncertainty
    results: list[tools.bld.Prediction | TR] = []

    # Prove: BLD prediction matches
    eta = tools.bld.baryon_asymmetry(K, B, L, n, S)
    results.append(tools.bld.Prediction(
        "eta", eta, obs.value, obs.uncertainty,
    ))

    # Exact fraction: 13/21,504,000,000
    exact = 13 / 21_504_000_000
    results.append(TR(
        "eta_exact_fraction", abs(eta - exact) < tools.bld.FLOAT_EPSILON, eta,
    ))

    # Disprove: sweep Lorentz exponent d = 1..12
    d_vals = np.arange(1, 13, dtype=np.float64)
    eta_d = (K / B) * (1.0 / L) ** d_vals * S / (S - 1)
    within = np.abs(eta_d - obs.value) < tol
    matching_d = d_vals[within].astype(int)

    results.append(TR(
        f"exponent_unique_in_1..12({len(matching_d)}_match)",
        len(matching_d) == 1 and matching_d[0] == n * (n - 1) // 2,
    ))

    assert_all_pass(results)


def test_baryon_correction_cross_constraint() -> None:
    """The correction factor p/(p-1) is not unique from η alone — ~8 integers
    p ∈ [9,16] all give η within 3σ.  This is expected: K/B × (1/L)^6 ≈ 5.6e-10
    and observed η ≈ 6.1e-10, so any factor in [1.06, 1.13] works.

    The REAL constraint: p must also satisfy the BLD structural identity
    p = K² + (n-1)².  Only p = 13 satisfies BOTH η ∈ 3σ AND the identity.

    This tests that η is not an independent free parameter — it's locked to
    the same S that determines neutrino mixing, Cabibbo angle, and mp/me.
    """
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S
    obs = tools.bld.ETA_BARYON
    tol = tools.bld.SIGMA_THRESHOLD * obs.uncertainty
    lorentz_dim = n * (n - 1) // 2
    base = (K / B) * (1 / L) ** lorentz_dim
    results: list[TR] = []

    # Phase 1: how many p in p/(p-1) give η ∈ 3σ?  (expect several)
    p = np.arange(2, 101, dtype=np.float64)
    eta_p = base * p / (p - 1)
    within_p = np.abs(eta_p - obs.value) < tol
    n_match_eta = int(within_p.sum())
    results.append(TR(
        f"eta_alone_admits_{n_match_eta}_values", n_match_eta > 1,
    ))

    # Phase 2: which also satisfy p = K² + (n-1)²?
    identity_ok = np.abs(K**2 + (n - 1) ** 2 - p) < tools.bld.IDENTITY_TOLERANCE
    both_ok = within_p & identity_ok
    matching_p = p[both_ok].astype(int)

    results.append(TR(
        f"eta+identity_unique({len(matching_p)}_match)",
        len(matching_p) == 1 and matching_p[0] == S,
    ))

    # Phase 3: verify S=13 also satisfies sin²θ₁₂ = K²/S
    obs_s12 = tools.bld.SIN2_THETA_12
    s12_ok = abs(K**2 / S - obs_s12.value) < (
        tools.bld.SIGMA_THRESHOLD * obs_s12.uncertainty
    )
    results.append(TR("S=13_also_fixes_theta12", s12_ok))

    assert_all_pass(results)


def test_baryon_wrong_constants() -> None:
    """η alone is underdetermined — ~13 (K,B,L,n) tuples give η ∈ 3σ.

    This is expected: η ∝ K/B linearly, so B±1 shifts η by only ±1.8%,
    well within the 3σ window of ±28%.  Different (K,L) combos compensate.

    The REAL test: η AND α⁻¹ together must uniquely pick (2, 56, 20, 4).
    α⁻¹ is B-sensitive at the single-integer level (base = nL + B + 1),
    so the combination is far more constraining than either alone.

    Sweep K∈{1,2,3}, B∈[40,70], L∈{18..22}, n∈{3,4,5}.
    Phase 1: confirm η alone is NOT unique (honest weakness).
    Phase 2: confirm η + α⁻¹ together ARE unique (overconstrained system).
    """
    obs_eta = tools.bld.ETA_BARYON
    obs_alpha = tools.bld.ALPHA_INV
    tol_eta = tools.bld.SIGMA_THRESHOLD * obs_eta.uncertainty
    tol_alpha = tools.bld.SIGMA_THRESHOLD * obs_alpha.uncertainty
    results: list[TR] = []

    K_vals = np.array([1, 2, 3], dtype=np.float64)
    B_vals = np.arange(40, 71, dtype=np.float64)
    L_vals = np.array([18, 19, 20, 21, 22], dtype=np.float64)
    n_vals = np.array([3, 4, 5], dtype=np.float64)

    # 4D meshgrid
    K_g, B_g, L_g, n_g = np.meshgrid(K_vals, B_vals, L_vals, n_vals, indexing="ij")
    d_g = n_g * (n_g - 1) / 2
    S_g = (B_g - n_g) / n_g
    valid = S_g > 1

    # η prediction (vectorised)
    eta_g = np.where(
        valid,
        (K_g / B_g) * (1.0 / L_g) ** d_g * S_g / (S_g - 1),
        np.inf,
    )
    eta_ok = np.abs(eta_g - obs_eta.value) < tol_eta

    # Phase 1: η alone admits multiple tuples
    n_eta_match = int(eta_ok.sum())
    results.append(TR(
        f"eta_alone_admits_{n_eta_match}_tuples", n_eta_match > 1,
    ))

    # α⁻¹ prediction (vectorised — same formula as bld.alpha_inv, broadcast)
    nL_g = n_g * L_g
    base_g = nL_g + B_g + 1
    bq = K_g / B_g
    os_ = n_g / ((n_g - 1) * nL_g * B_g)
    rs = -(n_g - 1) / (nL_g**2 * B_g)
    rb = -1 / (nL_g * B_g**2)
    e2 = np.e**2
    denom = (2 * B_g + n_g + K_g + 1) * nL_g**2 * B_g**2
    acc = np.where(np.abs(denom) > 1e-30, -e2 * (2 * B_g + n_g + K_g + 2) / denom, 0.0)
    alpha_g = base_g + bq + os_ + rs + rb + acc
    alpha_ok = np.abs(alpha_g - obs_alpha.value) < tol_alpha

    # Phase 2: η + α⁻¹ together
    both_ok = eta_ok & alpha_ok & valid
    matches = np.argwhere(both_ok)
    matching_tuples = [
        (int(K_vals[m[0]]), int(B_vals[m[1]]), int(L_vals[m[2]]), int(n_vals[m[3]]))
        for m in matches
    ]
    bld_tuple = (tools.bld.K, tools.bld.B, tools.bld.L, tools.bld.n)

    results.append(TR(
        f"eta+alpha_unique({len(matching_tuples)}_match)",
        len(matching_tuples) == 1 and matching_tuples[0] == bld_tuple,
    ))

    assert_all_pass(results)


def test_hubble_absolute() -> None:
    """BLD predicts H₀(CMB) = v × λ^68 ≈ 67.2 km/s/Mpc.

    Prove: matches Planck 2018 within 3σ for both CMB and local.
    Disprove: sweep cascade exponents 50..90.  Only 68 = B+L-Kn works.
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    v = tools.bld.V_EW
    lam = tools.bld.LAMBDA
    obs_cmb = tools.bld.H0_CMB
    obs_local = tools.bld.H0_LOCAL
    tol_cmb = tools.bld.SIGMA_THRESHOLD * obs_cmb.uncertainty
    tol_local = tools.bld.SIGMA_THRESHOLD * obs_local.uncertainty
    results: list[tools.bld.Prediction | TR] = []

    # Prove: H₀(CMB) matches Planck
    h0_cmb = tools.bld.hubble_absolute_km_s_mpc(v, lam, B, L, n, K)
    results.append(tools.bld.Prediction(
        "H0_CMB", h0_cmb, obs_cmb.value, obs_cmb.uncertainty,
    ))

    # Prove: H₀(local) = H₀(CMB,derived) × 13/12 matches SH0ES
    h0_local = h0_cmb * (1 + K / (n + L))
    results.append(tools.bld.Prediction(
        "H0_local", h0_local, obs_local.value, obs_local.uncertainty,
    ))

    # Disprove: sweep cascade exponents 50..90
    exps = np.arange(50, 91, dtype=np.float64)
    # H₀ = v × λ^exp, converted to km/s/Mpc
    h0_sweep = v * lam ** exps / tools.bld.HBAR_GEV_S * tools.bld.MPC_KM
    within_cmb = np.abs(h0_sweep - obs_cmb.value) < tol_cmb
    matching_exps = exps[within_cmb].astype(int)

    results.append(TR(
        f"exponent_unique_in_50..90({len(matching_exps)}_match)",
        len(matching_exps) == 1 and matching_exps[0] == B + L - K * n,
    ))

    # Structural: verify 68 = B + L - Kn from BLD constants
    cascade = B + L - K * n
    results.append(TR(
        f"68=B+L-Kn={cascade}", cascade == 68,
    ))

    assert_all_pass(results)


def test_hubble_cascade_structural() -> None:
    """The cascade exponent 68 is the ONLY structurally motivated BLD composite
    that gives H₀ within 3σ.

    Sweep all composites from bld_composites() (sums, products, differences,
    powers of B, L, n, K, S).  The claim is: only B+L-Kn = 68 works.

    Also compare to the particle cascade exponent B/2-K = 26: verify these
    are structurally distinct (different modes used).
    """
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S
    v = tools.bld.V_EW
    lam = tools.bld.LAMBDA
    obs = tools.bld.H0_CMB
    tol = tools.bld.SIGMA_THRESHOLD * obs.uncertainty
    results: list[TR] = []

    # Build structurally motivated exponent candidates
    composites = tools.bld.bld_composites(B, L, n, K, S)
    # Add specific cascade candidates not in composites
    composites["B+L-Kn"] = B + L - K * n           # 68 — the claim
    composites["B/2-K"] = B // 2 - K               # 26 — Planck cascade
    composites["B+L-K"] = B + L - K                 # 74
    composites["B+L-n"] = B + L - n                 # 72
    composites["B-Kn"] = B - K * n                  # 48
    composites["B+L+Kn"] = B + L + K * n            # 84

    names = list(composites.keys())
    vals = np.array([composites[nm] for nm in names], dtype=np.float64)

    # Filter to positive exponents (negative or zero give nonsense)
    pos = vals > 0
    h0 = np.where(
        pos,
        v * lam ** vals / tools.bld.HBAR_GEV_S * tools.bld.MPC_KM,
        np.inf,
    )
    within = np.abs(h0 - obs.value) < tol
    matching_names = [names[i] for i in range(len(names)) if within[i]]

    results.append(TR(
        f"B+L-Kn_unique_in_{len(composites)}_composites({len(matching_names)}_match)",
        len(matching_names) == 1 and matching_names[0] == "B+L-Kn",
    ))

    # Structural: particle cascade (26) and cosmological cascade (68) are distinct
    results.append(TR(
        "particle≠cosmological", (B // 2 - K) != (B + L - K * n),
    ))

    assert_all_pass(results)


def test_baryon_hubble_cross_constraint() -> None:
    """The structural identity B = n(S+1) from octonions makes η uniquely
    determine S — and that same S independently satisfies sin²θ₁₂.

    The derivation chain: traverse(-B,B) → closure requires octonions →
    Aut(𝕆) = G₂ → Spin(8) → B = 56 → S = (B-n)/n = 13.

    When B is FREE, η admits ~8 correction factors (test_baryon_correction).
    When B is TIED to S via B = n(S+1), η becomes η ∝ S/((S+1)(S-1))
    and the denominator's quadratic growth pins S uniquely.

    Sweep S = 2..50:
    Phase 1: η with B=n(S+1) uniquely pins S=13 (octonion coupling)
    Phase 2: sin²θ₁₂ = K²/S independently admits S∈{12,13,14}
    Phase 3: both agree on S=13 — overconstrained, not underdetermined
    Phase 4: the resulting 13/12 = S/(S-1) = 1+K/(n+L) = Hubble factor
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    obs_eta = tools.bld.ETA_BARYON
    obs_s12 = tools.bld.SIN2_THETA_12
    tol_eta = tools.bld.SIGMA_THRESHOLD * obs_eta.uncertainty
    tol_s12 = tools.bld.SIGMA_THRESHOLD * obs_s12.uncertainty
    results: list[TR] = []

    S_vals = np.arange(2, 51, dtype=np.float64)
    lorentz_dim = n * (n - 1) // 2

    # η with B tied to S via octonion identity B = n(S+1)
    B_vals = n * (S_vals + 1)
    eta_vals = (K / B_vals) * (1.0 / L) ** lorentz_dim * S_vals / (S_vals - 1)
    eta_ok = np.abs(eta_vals - obs_eta.value) < tol_eta

    # sin²θ₁₂ = K²/S (particle physics, independent of η)
    s12_vals = K**2 / S_vals
    s12_ok = np.abs(s12_vals - obs_s12.value) < tol_s12

    # Phase 1: η with B=n(S+1) is highly constraining — pins S uniquely
    matching_eta = S_vals[eta_ok].astype(int)
    results.append(TR(
        f"eta+octonion_pins_S({len(matching_eta)}_match)",
        len(matching_eta) == 1 and matching_eta[0] == tools.bld.S,
    ))

    # Phase 2: sin²θ₁₂ admits a few S values (weaker constraint alone)
    matching_s12 = S_vals[s12_ok].astype(int)
    results.append(TR(
        f"s12_admits_{len(matching_s12)}_values",
        len(matching_s12) >= 1 and tools.bld.S in matching_s12,
    ))

    # Phase 3: both agree on S=13 (overconstrained)
    both_ok = eta_ok & s12_ok
    matching_both = S_vals[both_ok].astype(int)
    results.append(TR(
        f"eta+s12_agree({len(matching_both)}_match)",
        len(matching_both) == 1 and matching_both[0] == tools.bld.S,
    ))

    # Phase 4: S/(S-1) = 1 + K/(n+L) — algebraic identity, not coincidence
    factor_gen = tools.bld.S / (tools.bld.S - 1)
    factor_obs = 1 + K / (n + L)
    results.append(TR(
        "S/(S-1)=1+K/(n+L)",
        abs(factor_gen - factor_obs) < tools.bld.FLOAT_EPSILON,
    ))

    assert_all_pass(results)


def test_formula_consistency() -> None:
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
    assert_all_pass(results)
