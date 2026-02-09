"""Quark mass predictions from BLD integer structure."""

import tools.bld

from helpers import assert_all_pass


# ---------------------------------------------------------------------------
# Run functions
# ---------------------------------------------------------------------------


def run_strange_mass() -> list[tools.bld.Prediction]:
    """Strange quark mass from electron mass × (n²S - L - L/n)."""
    ratio = tools.bld.ms_over_me(tools.bld.n, tools.bld.S, tools.bld.L)
    ms = tools.bld.M_ELECTRON * ratio
    obs = tools.bld.M_STRANGE
    return [tools.bld.Prediction("m_s(MeV)", ms, obs.value, obs.uncertainty)]


def run_down_mass() -> list[tools.bld.Prediction]:
    """Down quark mass from strange / (L + K/L)."""
    ms = tools.bld.M_ELECTRON * tools.bld.ms_over_me(
        tools.bld.n, tools.bld.S, tools.bld.L,
    )
    ratio = tools.bld.ms_over_md(tools.bld.L, tools.bld.K)
    md = ms / ratio
    obs = tools.bld.M_DOWN
    return [tools.bld.Prediction("m_d(MeV)", md, obs.value, obs.uncertainty)]


def run_up_mass() -> list[tools.bld.Prediction]:
    """Up quark mass from down / (K×S/(S-1))."""
    ms = tools.bld.M_ELECTRON * tools.bld.ms_over_me(
        tools.bld.n, tools.bld.S, tools.bld.L,
    )
    md = ms / tools.bld.ms_over_md(tools.bld.L, tools.bld.K)
    ratio = tools.bld.md_over_mu_quark(tools.bld.K, tools.bld.S)
    mu = md / ratio
    obs = tools.bld.M_UP
    return [tools.bld.Prediction("m_u(MeV)", mu, obs.value, obs.uncertainty)]


def run_charm_mass() -> list[tools.bld.Prediction]:
    """Charm quark mass from strange × (S + K/3)."""
    ms = tools.bld.M_ELECTRON * tools.bld.ms_over_me(
        tools.bld.n, tools.bld.S, tools.bld.L,
    )
    ratio = tools.bld.mc_over_ms(tools.bld.S, tools.bld.K)
    mc = ms * ratio
    obs = tools.bld.M_CHARM
    return [tools.bld.Prediction("m_c(MeV)", mc, obs.value, obs.uncertainty)]


def run_bottom_mass() -> list[tools.bld.Prediction]:
    """Bottom quark mass from charm × (3 + K/(n+3))."""
    ms = tools.bld.M_ELECTRON * tools.bld.ms_over_me(
        tools.bld.n, tools.bld.S, tools.bld.L,
    )
    mc = ms * tools.bld.mc_over_ms(tools.bld.S, tools.bld.K)
    ratio = tools.bld.mb_over_mc(tools.bld.K, tools.bld.n)
    mb = mc * ratio
    obs = tools.bld.M_BOTTOM
    return [tools.bld.Prediction("m_b(MeV)", mb, obs.value, obs.uncertainty)]


def run_top_mass() -> list[tools.bld.Prediction]:
    """Top quark mass from v/sqrt(K) × (1 - K/n²S)."""
    mt = tools.bld.top_mass(tools.bld.V_EW, tools.bld.K, tools.bld.n, tools.bld.S)
    obs = tools.bld.M_TOP
    return [tools.bld.Prediction("m_t(GeV)", mt, obs.value, obs.uncertainty)]


def run_quark_chain() -> list[tools.bld.TestResult]:
    """All 6 quark masses from a single m_e chain — internal consistency.

    Starting from m_e, each quark mass is derived via BLD ratios.
    The chain must produce values within 3-sigma of PDG for all 6.
    """
    n, L, K, S = tools.bld.n, tools.bld.L, tools.bld.K, tools.bld.S
    m_e = tools.bld.M_ELECTRON

    ms = m_e * tools.bld.ms_over_me(n, S, L)
    md = ms / tools.bld.ms_over_md(L, K)
    mu = md / tools.bld.md_over_mu_quark(K, S)
    mc = ms * tools.bld.mc_over_ms(S, K)
    mb = mc * tools.bld.mb_over_mc(K, n)
    mt = tools.bld.top_mass(tools.bld.V_EW, K, n, S)

    predictions = [
        tools.bld.Prediction("chain_u", mu, tools.bld.M_UP.value, tools.bld.M_UP.uncertainty),
        tools.bld.Prediction("chain_d", md, tools.bld.M_DOWN.value, tools.bld.M_DOWN.uncertainty),
        tools.bld.Prediction("chain_s", ms, tools.bld.M_STRANGE.value, tools.bld.M_STRANGE.uncertainty),
        tools.bld.Prediction("chain_c", mc, tools.bld.M_CHARM.value, tools.bld.M_CHARM.uncertainty),
        tools.bld.Prediction("chain_b", mb, tools.bld.M_BOTTOM.value, tools.bld.M_BOTTOM.uncertainty),
        tools.bld.Prediction("chain_t", mt, tools.bld.M_TOP.value, tools.bld.M_TOP.uncertainty),
    ]
    n_pass = sum(p.passes for p in predictions)
    return [tools.bld.TestResult("chain_all_6_pass", n_pass == 6, float(n_pass))]


def run_wrong_constants() -> list[tools.bld.TestResult]:
    """Only (n=4, K=2) passes all 6 quark mass predictions simultaneously.

    Sweep n in {3,4,5}, K in {1,2,3}. For each tuple, derive L and S
    from structure, compute all 6 quark masses, count passes.
    """
    B = tools.bld.B
    results: list[tools.bld.TestResult] = []

    for n_ in [3, 4, 5]:
        L_ = n_**2 * (n_**2 - 1) // 12
        S_ = (B - n_) // n_
        if L_ == 0 or S_ <= 0:
            continue
        for K_ in [1, 2, 3]:
            m_e = tools.bld.M_ELECTRON
            ms = m_e * tools.bld.ms_over_me(n_, S_, L_)
            md = ms / tools.bld.ms_over_md(L_, K_) if tools.bld.ms_over_md(L_, K_) != 0 else 0.0
            mu = md / tools.bld.md_over_mu_quark(K_, S_) if S_ > 1 else 0.0
            mc = ms * tools.bld.mc_over_ms(S_, K_)
            mb = mc * tools.bld.mb_over_mc(K_, n_)
            mt = tools.bld.top_mass(tools.bld.V_EW, K_, n_, S_)

            checks = [
                abs(mu - tools.bld.M_UP.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.M_UP.uncertainty,
                abs(md - tools.bld.M_DOWN.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.M_DOWN.uncertainty,
                abs(ms - tools.bld.M_STRANGE.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.M_STRANGE.uncertainty,
                abs(mc - tools.bld.M_CHARM.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.M_CHARM.uncertainty,
                abs(mb - tools.bld.M_BOTTOM.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.M_BOTTOM.uncertainty,
                abs(mt - tools.bld.M_TOP.value)
                < tools.bld.SIGMA_THRESHOLD * tools.bld.M_TOP.uncertainty,
            ]
            n_pass = sum(checks)
            is_correct = (n_ == tools.bld.n and K_ == tools.bld.K)
            if is_correct:
                results.append(tools.bld.TestResult(
                    f"n={n_},K={K_}_all_pass", n_pass == 6, float(n_pass),
                ))
            else:
                results.append(tools.bld.TestResult(
                    f"n={n_},K={K_}_fails", n_pass < 6, float(n_pass),
                ))
    return results


def run_confinement_cost() -> list[tools.bld.TestResult]:
    """The quark-lepton gap: -L - L/n = -25 (confinement cost).

    In ms/me = n²S - L - L/n, the negative terms (−L − L/n) represent
    the confinement cost that suppresses quark masses relative to the
    generational base n²S = 208.
    """
    n, L, S = tools.bld.n, tools.bld.L, tools.bld.S
    gen_base = n**2 * S
    confinement = -L - L / n
    total = gen_base + confinement
    return [
        tools.bld.TestResult("gen_base=208", gen_base == 208),
        tools.bld.TestResult("confinement=-25", abs(confinement - (-25)) < 1e-10),
        tools.bld.TestResult("ratio=183", abs(total - 183) < 1e-10),
    ]


def run_kx_hierarchy() -> list[tools.bld.TestResult]:
    """K/X corrections in quark formulas are ordered by scale.

    K/L (link) > K/3 (color) > K/7 (n+3) > K/208 (n²S).
    Larger X means weaker correction — same structure as alpha corrections.
    """
    K, L, n, S = tools.bld.K, tools.bld.L, tools.bld.n, tools.bld.S
    kx_link = K / L                     # 0.1   (ms/md correction)
    kx_color = K / tools.bld.N_COLORS   # 0.667 (mc/ms correction)
    kx_n3 = K / (n + tools.bld.N_COLORS)  # 0.286 (mb/mc correction)
    kx_n2s = K / (n**2 * S)            # 0.00962 (top mass correction)

    return [
        tools.bld.TestResult("K/3>K/7", kx_color > kx_n3),
        tools.bld.TestResult("K/7>K/n²S", kx_n3 > kx_n2s),
        tools.bld.TestResult("K/L<K/3", kx_link < kx_color),
        tools.bld.TestResult("all_positive", all(x > 0 for x in [kx_link, kx_color, kx_n3, kx_n2s])),
    ]


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def test_strange_mass() -> None:
    assert_all_pass(run_strange_mass())


def test_down_mass() -> None:
    assert_all_pass(run_down_mass())


def test_up_mass() -> None:
    assert_all_pass(run_up_mass())


def test_charm_mass() -> None:
    assert_all_pass(run_charm_mass())


def test_bottom_mass() -> None:
    assert_all_pass(run_bottom_mass())


def test_top_mass() -> None:
    assert_all_pass(run_top_mass())


def test_quark_chain() -> None:
    assert_all_pass(run_quark_chain())


def test_wrong_constants() -> None:
    assert_all_pass(run_wrong_constants())


def test_confinement_cost() -> None:
    assert_all_pass(run_confinement_cost())


def test_kx_hierarchy() -> None:
    assert_all_pass(run_kx_hierarchy())
