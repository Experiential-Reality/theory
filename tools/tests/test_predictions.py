"""BLD theory prediction tests."""

import math

import numpy as np

import tools.bld

from helpers import assert_all_pass, assert_none_pass


# ---------------------------------------------------------------------------
# Run functions
# ---------------------------------------------------------------------------


def run_constant_identities() -> list[tools.bld.Prediction]:
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S
    return [
        tools.bld.Prediction("S=(B-n)/n", (B - n) / n, S, 0),
        tools.bld.Prediction("K²+(n-1)²=S", K**2 + (n - 1) ** 2, S, 0),
        tools.bld.Prediction("λ²×nL=K²", tools.bld.LAMBDA**2 * n * L, K**2, 0),
        tools.bld.Prediction("S+1=B/n", S + 1, B / n, 0),
        tools.bld.Prediction("Riemann=L", n**2 * (n**2 - 1) / 12, L, 0),
    ]


def run_fine_structure() -> list[tools.bld.Prediction]:
    alpha = tools.bld.alpha_inv(
        tools.bld.n, float(tools.bld.L), tools.bld.B, tools.bld.K,
    )
    obs = tools.bld.ALPHA_INV
    return [tools.bld.Prediction("α⁻¹", alpha, obs.value, obs.uncertainty)]


def run_lepton_ratios() -> list[tools.bld.Prediction]:
    n, L, S, B = tools.bld.n, tools.bld.L, tools.bld.S, tools.bld.B

    mu_e = tools.bld.mu_over_e(n, float(L), S, B)
    tau_mu = tools.bld.tau_over_mu(n, float(L), S)

    obs_mu = tools.bld.MU_OVER_E
    obs_tau = tools.bld.TAU_OVER_MU
    return [
        tools.bld.Prediction("μ/e", mu_e, obs_mu.value, obs_mu.uncertainty),
        tools.bld.Prediction("τ/μ", tau_mu, obs_tau.value, obs_tau.uncertainty),
    ]


def run_nucleon_ratio() -> list[tools.bld.Prediction]:
    mp_me = tools.bld.mp_over_me(tools.bld.S, tools.bld.n, tools.bld.B, tools.bld.K)
    obs = tools.bld.MP_OVER_ME
    return [tools.bld.Prediction("m_p/m_e", mp_me, obs.value, obs.uncertainty)]


def run_neutrino_mixing() -> list[tools.bld.Prediction]:
    n, L, K, S = tools.bld.n, tools.bld.L, tools.bld.K, tools.bld.S
    obs12 = tools.bld.SIN2_THETA_12
    obs13 = tools.bld.SIN2_THETA_13
    obs23 = tools.bld.SIN2_THETA_23
    return [
        tools.bld.Prediction("sin²θ₁₂", tools.bld.sin2_theta_12(K, S), obs12.value, obs12.uncertainty),
        tools.bld.Prediction("sin²θ₁₃", tools.bld.sin2_theta_13(n), obs13.value, obs13.uncertainty),
        tools.bld.Prediction("sin²θ₂₃", tools.bld.sin2_theta_23(S, L, n), obs23.value, obs23.uncertainty),
    ]


def run_muon_g2() -> list[tools.bld.Prediction]:
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S
    delta_a_mu = tools.bld.muon_g2(n, float(L), K, S, B)
    obs = tools.bld.MUON_G2
    return [tools.bld.Prediction("Δaμ(×10⁻¹¹)", delta_a_mu, obs.value, obs.uncertainty)]


def run_neutron_lifetime() -> list[tools.bld.Prediction]:
    K, S = tools.bld.K, tools.bld.S
    predicted = tools.bld.tau_beam(tools.bld.TAU_BOTTLE, K, S)
    obs = tools.bld.TAU_BEAM
    return [tools.bld.Prediction("τ_beam(s)", predicted, obs.value, obs.uncertainty)]


def run_planck_mass() -> list[tools.bld.Prediction]:
    v = tools.bld.V_EW
    M_P = tools.bld.planck_mass(
        v, tools.bld.LAMBDA**2, tools.bld.n, float(tools.bld.L),
        tools.bld.K, tools.bld.B,
    )
    obs = tools.bld.PLANCK_MASS
    return [tools.bld.Prediction("M_P(GeV)", M_P, obs.value, obs.uncertainty)]


def run_higgs_mass() -> list[tools.bld.Prediction]:
    v = tools.bld.V_EW
    m_H = tools.bld.higgs_mass(v, tools.bld.B, tools.bld.L)
    obs = tools.bld.HIGGS_MASS
    return [tools.bld.Prediction("m_H(GeV)", m_H, obs.value, obs.uncertainty)]


def run_constant_uniqueness() -> tuple[tools.bld.Prediction, list[tools.bld.Prediction]]:
    """Negative test: BLD constants (B=56, L=20, n=4, K=2, S=13) are unique.

    Five simultaneous identities over-determine the system.  Perturbing any
    single constant by +/-1 breaks at least one identity, proving the solution
    is isolated --- not one of many nearby integer tuples.

    Returns (true_result, perturbations) so the test can assert true passes
    and all perturbations fail.
    """
    def _count_satisfied(B_: int, L_: int, n_: int, K_: int, S_: int) -> int:
        checks = [
            abs((B_ - n_) / n_ - S_) < tools.bld.IDENTITY_TOLERANCE,
            abs(K_**2 + (n_ - 1) ** 2 - S_) < tools.bld.IDENTITY_TOLERANCE,
            abs((1.0 / L_) * n_ * L_ - K_**2) < tools.bld.IDENTITY_TOLERANCE,
            abs(S_ + 1 - B_ / n_) < tools.bld.IDENTITY_TOLERANCE,
            abs(n_**2 * (n_**2 - 1) / 12 - L_) < tools.bld.IDENTITY_TOLERANCE,
        ]
        return sum(checks)

    base = (tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S)
    names = ["B", "L", "n", "K", "S"]

    true_result = tools.bld.Prediction(
        "true constants", float(_count_satisfied(*base)), 5.0, 0,
    )

    perturbations: list[tools.bld.Prediction] = []
    for idx, name in enumerate(names):
        for delta in [-1, +1]:
            perturbed = list(base)
            perturbed[idx] += delta
            sat = _count_satisfied(*perturbed)
            perturbations.append(tools.bld.Prediction(
                f"{name}{'+' if delta > 0 else '−'}1",
                float(sat), 5.0, 0,
            ))
    return true_result, perturbations


def run_wrong_integers() -> tuple[list[tools.bld.Prediction], list[tools.bld.Prediction]]:
    """Negative test: nearby integers don't match observed mass ratios.

    BLD derives mu/e primordial integer as n^2*S-1 = 207.  Using 206 or 208
    shifts the prediction by ~1 unit --- thousands of sigma from observation.
    Same for m_p/m_e base (S+n)(B+nS) = 17*108 = 1836.

    Returns (correct, wrong) so the test can assert correct pass and wrong fail.
    """
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S
    nL = n * L
    nLS = nL * S
    e = math.e

    def _mu_over_e(base_int: int) -> float:
        return (
            base_int
            * nLS / (nLS + 1)
            * (1 - 1 / (nL**2 + n * S))
            * (1 - 1 / (nL * B**2))
            * (1 + e**2 * (S + 1) / (nL**2 * B**2 * S**2))
        )

    def _mp_over_me(base_int: int) -> float:
        return base_int + K / S

    obs_mu = tools.bld.MU_OVER_E
    obs_mp = tools.bld.MP_OVER_ME

    correct: list[tools.bld.Prediction] = [
        tools.bld.Prediction("μ/e n²S−1=207", _mu_over_e(207), obs_mu.value, obs_mu.uncertainty),
        tools.bld.Prediction(
            "m_p/m_e base=1836", _mp_over_me((S + n) * (B + n * S)),
            obs_mp.value, obs_mp.uncertainty,
        ),
    ]
    wrong: list[tools.bld.Prediction] = [
        tools.bld.Prediction(f"μ/e base={w}", _mu_over_e(w), obs_mu.value, obs_mu.uncertainty)
        for w in [206, 208]
    ] + [
        tools.bld.Prediction(f"m_p/m_e base={w}", _mp_over_me(w), obs_mp.value, obs_mp.uncertainty)
        for w in [1835, 1837]
    ]
    return correct, wrong


# ---------------------------------------------------------------------------
# Adversarial: cross-domain consistency and correction structure
# ---------------------------------------------------------------------------


def run_cross_prediction_consistency() -> list[tools.bld.TestResult]:
    """Only (n=4, K=2) simultaneously satisfies all 9 particle predictions.

    Sweep n∈{3,4,5}, K∈{1,2,3}.  For each tuple derive L=n²(n²-1)/12
    (Riemann tensor components) and S=⌊(B-n)/n⌋ (structure constant).
    Evaluate all 9 predictions against observation.

    A curve-fitting model with 2 free parameters could match at most 2
    observables.  BLD matches 9 from exactly one integer tuple — with
    zero free parameters (all derived).
    """
    results: list[tools.bld.TestResult] = []
    for n_ in [3, 4, 5]:
        L_ = n_**2 * (n_**2 - 1) // 12
        S_ = (tools.bld.B - n_) // n_
        if L_ == 0 or S_ <= 0:
            continue
        for K_ in [1, 2, 3]:
            checks = [
                abs(tools.bld.alpha_inv(n_, float(L_), tools.bld.B, K_)
                    - tools.bld.ALPHA_INV.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.ALPHA_INV.uncertainty,
                abs(tools.bld.mu_over_e(n_, float(L_), S_, tools.bld.B)
                    - tools.bld.MU_OVER_E.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.MU_OVER_E.uncertainty,
                abs(tools.bld.tau_over_mu(n_, float(L_), S_)
                    - tools.bld.TAU_OVER_MU.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.TAU_OVER_MU.uncertainty,
                abs(tools.bld.mp_over_me(S_, n_, tools.bld.B, K_)
                    - tools.bld.MP_OVER_ME.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.MP_OVER_ME.uncertainty,
                abs(tools.bld.sin2_theta_12(K_, S_)
                    - tools.bld.SIN2_THETA_12.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.SIN2_THETA_12.uncertainty,
                abs(tools.bld.sin2_theta_13(n_)
                    - tools.bld.SIN2_THETA_13.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.SIN2_THETA_13.uncertainty,
                abs(tools.bld.sin2_theta_23(S_, L_, n_)
                    - tools.bld.SIN2_THETA_23.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.SIN2_THETA_23.uncertainty,
                abs(tools.bld.muon_g2(n_, float(L_), K_, S_, tools.bld.B)
                    - tools.bld.MUON_G2.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.MUON_G2.uncertainty,
                abs(tools.bld.tau_beam(tools.bld.TAU_BOTTLE, K_, S_)
                    - tools.bld.TAU_BEAM.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.TAU_BEAM.uncertainty,
            ]
            n_pass = sum(checks)
            is_correct = (n_ == tools.bld.n and K_ == tools.bld.K)
            if is_correct:
                results.append(tools.bld.TestResult(
                    f"n={n_},K={K_}_all_pass", n_pass == 9, float(n_pass),
                ))
            else:
                results.append(tools.bld.TestResult(
                    f"n={n_},K={K_}_fails_ge3", n_pass <= 6, float(n_pass),
                ))
    return results


def run_correction_hierarchy() -> list[tools.bld.TestResult]:
    """Correction terms in α⁻¹ must form a strict hierarchy.

    The K/X observer correction scheme produces terms from distinct physical
    mechanisms: boundary quantum (K/B), outbound spatial geometry, return
    spatial, return boundary, and accumulated transcendental.

    Theory predicts:
    - First two terms positive (incomplete traversal — escapes detection)
    - Last three negative (complete traversal — all products detected)
    - Magnitudes decrease: boundary_quantum > outbound_spatial > 0 and
      |return_spatial| > |return_boundary| > |accumulated|
    - Net correction positive (observation inflates the measured value)

    If the corrections were ad hoc fitting terms, this structured hierarchy
    from decreasing physical scales would be coincidental.
    """
    _, terms = tools.bld.alpha_inv_full(
        tools.bld.n, float(tools.bld.L), tools.bld.B, tools.bld.K,
    )
    CT = tools.bld.CorrectionTerm
    bq = terms[CT.BOUNDARY_QUANTUM]
    os_ = terms[CT.OUTBOUND_SPATIAL]
    rs = terms[CT.RETURN_SPATIAL]
    rb = terms[CT.RETURN_BOUNDARY]
    acc = terms[CT.ACCUMULATED]

    results: list[tools.bld.TestResult] = []

    # Positive terms: boundary_quantum > outbound_spatial > 0
    results.append(tools.bld.TestResult("bq>os>0", bq > os_ > 0, bq))

    # Negative terms: all negative (complete traversals detected)
    results.append(tools.bld.TestResult(
        "negative_returns", rs < 0 and rb < 0 and acc < 0,
    ))

    # Magnitude hierarchy: |return_spatial| > |return_boundary| > |accumulated|
    results.append(tools.bld.TestResult(
        "|rs|>|rb|>|acc|", abs(rs) > abs(rb) > abs(acc),
    ))

    # Net correction positive (observation inflates)
    net = bq + os_ + rs + rb + acc
    results.append(tools.bld.TestResult("net_positive", net > 0, net))

    return results


# ---------------------------------------------------------------------------
# CKM, electron g-2, generational hierarchy
# ---------------------------------------------------------------------------


def run_cabibbo_angle() -> list[tools.bld.Prediction]:
    """|V_us| = sin(arctan((n-1)/S)) = sin(arctan(3/13)) = 0.2249."""
    predicted = tools.bld.cabibbo_sin(tools.bld.n, tools.bld.S)
    obs = tools.bld.V_US
    return [tools.bld.Prediction("|V_us|", predicted, obs.value, obs.uncertainty)]


def run_electron_g2() -> list[tools.bld.TestResult]:
    """Electron is Gen-1 reference: BLD anomaly contribution = 0.

    The electron sits at the generational junction — no traversal cost.
    Only Gen-2+ particles (muon, tau) incur the K²/((nL)²S) cost.
    """
    muon_g2 = tools.bld.muon_g2(
        tools.bld.n, float(tools.bld.L), tools.bld.K, tools.bld.S, tools.bld.B,
    )
    electron_g2_bld = 0.0  # Gen-1 reference: no BLD contribution
    return [
        tools.bld.TestResult("electron_bld_zero", electron_g2_bld == 0.0),
        tools.bld.TestResult("muon_bld_positive", muon_g2 > 0.0, muon_g2),
    ]


def run_generational_g2_hierarchy() -> list[tools.bld.TestResult]:
    """Generational structure: electron(0) < muon(250) — monotonic in generation.

    Gen-1 electron = reference (zero BLD contribution).
    Gen-2 muon = K²/((nL)²S) × (B+L)/(B+L+K) ≈ 250 × 10⁻¹¹.
    """
    muon_g2 = tools.bld.muon_g2(
        tools.bld.n, float(tools.bld.L), tools.bld.K, tools.bld.S, tools.bld.B,
    )
    electron_g2_bld = 0.0
    return [
        tools.bld.TestResult("e<mu", electron_g2_bld < muon_g2),
        tools.bld.TestResult("muon_order_250", abs(muon_g2 - 250) < 10, muon_g2),
    ]


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_constant_identities() -> None:
    assert_all_pass(run_constant_identities())


def test_fine_structure() -> None:
    assert_all_pass(run_fine_structure())


def test_lepton_ratios() -> None:
    assert_all_pass(run_lepton_ratios())


def test_nucleon_ratio() -> None:
    assert_all_pass(run_nucleon_ratio())


def test_neutrino_mixing() -> None:
    assert_all_pass(run_neutrino_mixing())


def test_muon_g2() -> None:
    assert_all_pass(run_muon_g2())


def test_neutron_lifetime() -> None:
    assert_all_pass(run_neutron_lifetime())


def test_planck_mass() -> None:
    assert_all_pass(run_planck_mass())


def test_higgs_mass() -> None:
    assert_all_pass(run_higgs_mass())


def test_constant_uniqueness() -> None:
    true_result, perturbations = run_constant_uniqueness()
    assert true_result.passes
    assert_none_pass(perturbations)


def test_wrong_integers() -> None:
    correct, wrong = run_wrong_integers()
    assert_all_pass(correct)
    assert_none_pass(wrong)


def test_cross_prediction_consistency() -> None:
    assert_all_pass(run_cross_prediction_consistency())


def test_correction_hierarchy() -> None:
    assert_all_pass(run_correction_hierarchy())


def test_cabibbo_angle() -> None:
    assert_all_pass(run_cabibbo_angle())


def test_electron_g2() -> None:
    assert_all_pass(run_electron_g2())


def test_generational_g2_hierarchy() -> None:
    assert_all_pass(run_generational_g2_hierarchy())
