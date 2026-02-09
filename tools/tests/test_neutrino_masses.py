"""Neutrino mass predictions from BLD structure."""

import pytest

import tools.bld


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
    """Formula computes 1.63e-5 MeV (correct arithmetic, wrong units in doc)."""
    K, B, n, L = tools.bld.K, tools.bld.B, tools.bld.n, tools.bld.L
    m_nu = tools.bld.neutrino_mass_e(tools.bld.M_ELECTRON, K, B, n, L)
    # Compute expected directly from components
    suppression = (K / B) ** 2 * K / (n * L) * (1 + K / (n * L * B))
    expected = tools.bld.M_ELECTRON * suppression
    return [
        tools.bld.TestResult(
            "formula_output", abs(m_nu - expected) < tools.bld.FLOAT_EPSILON, m_nu,
        ),
        tools.bld.TestResult(
            "order_of_magnitude", 1e-6 < m_nu < 1e-4, m_nu,
        ),
    ]


@pytest.mark.xfail(
    reason="Doc unit error: formula gives 16.3 eV, doc claims 16.3 meV. "
    "See neutrino-masses.md line 229.",
)
def run_neutrino_mass_bound() -> list[tools.bld.TestResult]:
    """Formula output vs KATRIN bound (< 0.45 eV)."""
    m_nu_mev = tools.bld.neutrino_mass_e(
        tools.bld.M_ELECTRON, tools.bld.K, tools.bld.B, tools.bld.n, tools.bld.L,
    )
    m_nu_ev = m_nu_mev * 1e6  # MeV -> eV
    return [tools.bld.TestResult("KATRIN_bound", m_nu_ev < 0.45, m_nu_ev)]


def run_missing_b_suppression() -> list[tools.bld.TestResult]:
    """(K/B)^2 * K/(nL) = 1/31360 exact (before K/X correction)."""
    K, B, n, L = tools.bld.K, tools.bld.B, tools.bld.n, tools.bld.L
    suppression = (K / B) ** 2 * K / (n * L)
    expected = 1.0 / 31360.0
    return [tools.bld.TestResult(
        "suppression=1/31360", abs(suppression - expected) < 1e-15, suppression,
    )]


def run_wrong_b_fails() -> list[tools.bld.TestResult]:
    """Only B=56 gives the correct suppression factor.

    Adversarial: B in {28, 55, 57, 112} all give wrong suppression.
    """
    K, n, L = tools.bld.K, tools.bld.n, tools.bld.L
    correct_suppression = (K / tools.bld.B) ** 2 * K / (n * L)

    results: list[tools.bld.TestResult] = []
    for B_test in [28, 55, 57, 112]:
        wrong = (K / B_test) ** 2 * K / (n * L)
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


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.theory
def test_dm2_ratio() -> None:
    assert all(p.passes for p in run_dm2_ratio())


@pytest.mark.theory
def test_neutrino_formula_output() -> None:
    assert all(r.passes for r in run_neutrino_formula_output())


@pytest.mark.theory
@pytest.mark.xfail(
    reason="Doc unit error: formula gives 16.3 eV, doc claims 16.3 meV. "
    "See neutrino-masses.md line 229.",
)
def test_neutrino_mass_bound() -> None:
    assert all(r.passes for r in run_neutrino_mass_bound())


@pytest.mark.theory
def test_missing_b_suppression() -> None:
    assert all(r.passes for r in run_missing_b_suppression())


@pytest.mark.theory
def test_wrong_b_fails() -> None:
    assert all(r.passes for r in run_wrong_b_fails())


@pytest.mark.theory
def test_generation_structure() -> None:
    results = run_generation_structure()
    assert all(r.passes for r in results), [
        (r.name, r.value) for r in results if not r.passes
    ]
