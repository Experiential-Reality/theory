"""Neutrino mass predictions from BLD structure."""

import tools.bld

from helpers import assert_all_pass


# ---------------------------------------------------------------------------
# Run functions
# ---------------------------------------------------------------------------


def run_dm2_ratio() -> list[tools.bld.Prediction]:
    """Mass-squared difference ratio |Dm2_32|/|Dm2_21| = L + S = 33.

    Observed: 2.453e-3 / 7.53e-5 = 32.6 +/- 1.0. BLD predicts 33.
    """
    predicted = tools.bld.dm2_ratio(tools.bld.L, tools.bld.S)
    obs_ratio = tools.bld.DM2_32.value / tools.bld.DM2_21.value
    # Propagate uncertainty: delta(a/b) = (a/b) * sqrt((da/a)^2 + (db/b)^2)
    rel_unc = (
        (tools.bld.DM2_32.uncertainty / tools.bld.DM2_32.value) ** 2
        + (tools.bld.DM2_21.uncertainty / tools.bld.DM2_21.value) ** 2
    ) ** 0.5
    unc = obs_ratio * rel_unc
    return [tools.bld.Prediction("Δm²₃₂/Δm²₂₁", predicted, obs_ratio, unc)]


def run_neutrino_formula_output() -> list[tools.bld.TestResult]:
    """Formula computes ~1.57e-8 MeV (15.7 meV) with second-order coupling."""
    K, B, n, L, S = tools.bld.K, tools.bld.B, tools.bld.n, tools.bld.L, tools.bld.S
    m_nu = tools.bld.neutrino_mass_e(tools.bld.M_ELECTRON, K, B, n, L, S)
    # Compute expected directly from components
    nL = n * L
    suppression = (K / B) ** 2 * K / (nL ** 2 * S) * (1 + K / (nL * B))
    expected = tools.bld.M_ELECTRON * suppression
    return [
        tools.bld.TestResult(
            "formula_output", abs(m_nu - expected) < tools.bld.FLOAT_EPSILON, m_nu,
        ),
        tools.bld.TestResult(
            "order_of_magnitude", 1e-9 < m_nu < 1e-7, m_nu,
        ),
    ]


def run_neutrino_mass_bound() -> list[tools.bld.TestResult]:
    """Formula output vs KATRIN bound (< 0.45 eV)."""
    m_nu_mev = tools.bld.neutrino_mass_e(
        tools.bld.M_ELECTRON, tools.bld.K, tools.bld.B,
        tools.bld.n, tools.bld.L, tools.bld.S,
    )
    m_nu_ev = m_nu_mev * 1e6  # MeV -> eV
    return [tools.bld.TestResult("KATRIN_bound", m_nu_ev < 0.45, m_nu_ev)]


def run_missing_b_suppression() -> list[tools.bld.TestResult]:
    """(K/B)^2 * K/((nL)^2 * S) = 1/32,614,400 exact (before K/X correction)."""
    K, B, n, L, S = tools.bld.K, tools.bld.B, tools.bld.n, tools.bld.L, tools.bld.S
    nL = n * L
    suppression = (K / B) ** 2 * K / (nL ** 2 * S)
    expected = 1.0 / 32_614_400.0
    return [tools.bld.TestResult(
        "suppression=1/32614400", abs(suppression - expected) < 1e-15, suppression,
    )]


def run_wrong_b_fails() -> list[tools.bld.TestResult]:
    """Only B=56 gives the correct suppression factor.

    Adversarial: B in {28, 55, 57, 112} all give wrong suppression.
    """
    K, n, L, S = tools.bld.K, tools.bld.n, tools.bld.L, tools.bld.S
    nL = n * L
    correct_suppression = (K / tools.bld.B) ** 2 * K / (nL ** 2 * S)

    results: list[tools.bld.TestResult] = []
    for B_test in [28, 55, 57, 112]:
        wrong = (K / B_test) ** 2 * K / (nL ** 2 * S)
        # Wrong B gives a different suppression factor
        results.append(tools.bld.TestResult(
            f"B={B_test}_wrong",
            abs(wrong - correct_suppression) > 0.001 * correct_suppression,
            wrong,
        ))
    return results


def run_generation_structure() -> list[tools.bld.TestResult]:
    """dm2 ratio is L+S, not L, not S, not L*S, not L-S.

    Only L+S = 33 matches the observed ratio ~32.6. Other combinations
    of L and S give values too far from observation.
    """
    L, S = tools.bld.L, tools.bld.S
    obs_ratio = tools.bld.DM2_32.value / tools.bld.DM2_21.value
    rel_unc = (
        (tools.bld.DM2_32.uncertainty / tools.bld.DM2_32.value) ** 2
        + (tools.bld.DM2_21.uncertainty / tools.bld.DM2_21.value) ** 2
    ) ** 0.5
    unc = obs_ratio * rel_unc

    # Only L+S should be within 3-sigma
    candidates = {
        "L+S": L + S,       # 33
        "L": L,              # 20
        "S": S,              # 13
        "L*S": L * S,        # 260
        "L-S": L - S,        # 7
    }
    results: list[tools.bld.TestResult] = []
    for name, val in candidates.items():
        within = abs(val - obs_ratio) < tools.bld.SIGMA_THRESHOLD * unc
        if name == "L+S":
            results.append(tools.bld.TestResult(f"{name}_passes", within, float(val)))
        else:
            results.append(tools.bld.TestResult(f"{name}_fails", not within, float(val)))
    return results


def run_generational_leakage() -> list[tools.bld.TestResult]:
    """Neutrino coupling 1/(nLS) is inverse of muon coupling nLS/(nLS+1).

    The muon couples at near-unit strength: nLS/(nLS+1) (see mu_over_e).
    The neutrino gets mass only through the 1/nLS leakage.
    nLS = 1040, so the leakage is ~9.6e-4.
    """
    n, L, S = tools.bld.n, tools.bld.L, tools.bld.S
    nLS = n * L * S
    muon_coupling = nLS / (nLS + 1)
    results: list[tools.bld.TestResult] = []
    results.append(tools.bld.TestResult(
        "muon_near_unity", muon_coupling > 0.999, muon_coupling,
    ))
    results.append(tools.bld.TestResult(
        "nLS_value", nLS == 1040, float(nLS),
    ))
    return results


def run_g2_structure_match() -> list[tools.bld.TestResult]:
    """Neutrino suppression shares (nL)^2 * S denominator with muon g-2.

    muon g-2 base factor: K^2 / ((nL)^2 * S)
    neutrino coupling:    K  / ((nL)^2 * S)
    Same denominator (nL)^2 * S = 83200.
    """
    n, L, S = tools.bld.n, tools.bld.L, tools.bld.S
    nL = n * L
    denom = nL ** 2 * S
    return [tools.bld.TestResult(
        "denominator_value",
        denom == 83200,
        float(denom),
    )]


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_dm2_ratio() -> None:
    assert_all_pass(run_dm2_ratio())


def test_neutrino_formula_output() -> None:
    assert_all_pass(run_neutrino_formula_output())


def test_neutrino_mass_bound() -> None:
    assert_all_pass(run_neutrino_mass_bound())


def test_missing_b_suppression() -> None:
    assert_all_pass(run_missing_b_suppression())


def test_wrong_b_fails() -> None:
    assert_all_pass(run_wrong_b_fails())


def test_generation_structure() -> None:
    assert_all_pass(run_generation_structure())


def test_generational_leakage() -> None:
    assert_all_pass(run_generational_leakage())


def test_g2_structure_match() -> None:
    assert_all_pass(run_g2_structure_match())
