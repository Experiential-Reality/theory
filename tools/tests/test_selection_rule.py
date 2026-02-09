"""Selection rule verification and tests."""

import enum
import typing

import numpy as np
import pytest
import scipy.stats

import tools.bld
import tools.quantum


# ---------------------------------------------------------------------------
# Enums, constants, and verification functions
# ---------------------------------------------------------------------------


class RuleName(enum.StrEnum):
    PRODUCT = "A_product"
    RATIO = "B_ratio"
    MAX_OVERLAP = "C_max_overlap"
    CDF_PARTITION = "D_cdf_partition"
    BORN_SAMPLE = "E_born_sample"


CONFIGS = [
    (2, "equal", [0.5, 0.5]),
    (2, "80/20", [0.8, 0.2]),
    (2, "95/5", [0.95, 0.05]),
    (3, "equal", [1 / 3, 1 / 3, 1 / 3]),
    (3, "50/30/20", [0.5, 0.3, 0.2]),
    (3, "70/20/10", [0.7, 0.2, 0.1]),
    (4, "equal", [0.25, 0.25, 0.25, 0.25]),
    (4, "hierarchical", [0.5, 0.25, 0.15, 0.1]),
    (5, "equal", [0.2, 0.2, 0.2, 0.2, 0.2]),
    (5, "steep", [0.5, 0.2, 0.15, 0.1, 0.05]),
]

N_OBS_VALUES = [4, 8, 16, 32]


def _run_rule_tests(
    rng: np.random.Generator,
    rule: typing.Callable = tools.quantum.selection_rule,
    *,
    m_filter: int | None = None,
) -> list[tools.quantum.StatTest]:
    results = []
    for M, _desc, alphas in CONFIGS:
        if m_filter is not None and M != m_filter:
            continue
        a = np.array(alphas)
        for N_obs in N_OBS_VALUES:
            if N_obs < M:
                continue
            n = min(50000, 20000 if N_obs >= 32 else 50000)
            pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
            outcome = tools.quantum.run_selection_mc(pointers, a, n, rng, rule=rule)
            results.append(tools.quantum.chi2_test(outcome.counts, a, n))
    return results


def run_born_tests(rng: np.random.Generator) -> list[tools.quantum.StatTest]:
    return _run_rule_tests(rng)


def run_product_tests(rng: np.random.Generator) -> list[tools.quantum.StatTest]:
    return _run_rule_tests(rng, rule=tools.quantum.rule_product, m_filter=2)


def run_all_rules(
    rng: np.random.Generator,
) -> list[dict]:
    all_results = []
    for M, desc, alphas in CONFIGS:
        a = np.array(alphas)
        for N_obs in N_OBS_VALUES:
            if N_obs < M:
                continue

            n = min(50000, 20000 if N_obs >= 32 else 50000)
            pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
            P = np.array(pointers.states)

            observers = tools.bld.haar_random_states(N_obs, n, rng)
            ovlps = tools.quantum.overlaps_batch(P, observers)
            safe = np.maximum(ovlps, tools.quantum.SAFE_FLOOR)

            choices_product = np.argmax(a[:, None] * ovlps, axis=0)
            choices_ratio = np.argmax(a[:, None] / safe, axis=0)
            choices_max = np.argmax(ovlps, axis=0)

            u = (np.angle(observers[:, 0]) + np.pi) / (2 * np.pi)
            cumsum = np.cumsum(a)
            choices_cdf = np.minimum(np.searchsorted(cumsum, u, side='right'), M - 1)

            choices_born = rng.choice(M, size=n, p=a)

            rules = {
                RuleName.PRODUCT: np.bincount(choices_product, minlength=M).astype(float),
                RuleName.RATIO: np.bincount(choices_ratio, minlength=M).astype(float),
                RuleName.MAX_OVERLAP: np.bincount(choices_max, minlength=M).astype(float),
                RuleName.CDF_PARTITION: np.bincount(choices_cdf, minlength=M).astype(float),
                RuleName.BORN_SAMPLE: np.bincount(choices_born, minlength=M).astype(float),
            }

            entry = {"M": M, "desc": desc, "N_obs": N_obs, "results": {}}
            for name, counts in rules.items():
                stat = tools.quantum.chi2_test(counts, a, n)
                entry["results"][name] = {
                    "frequencies": counts / n,
                    "expected": a.copy(),
                    "chi2": stat.chi2_stat,
                    "p_value": stat.p_value,
                    "matches_born": stat.passes,
                }
            all_results.append(entry)

    return all_results


def run_overlap_distribution_test(
    rng: np.random.Generator,
) -> tools.quantum.StatTest:
    min_p = 1.0
    for N_obs in [8, 16, 32, 64, 128]:
        M_test = min(3, N_obs)
        pointers = tools.quantum.make_orthogonal_pointers(M_test, N_obs, rng)
        P = np.array(pointers.states)

        observers = tools.bld.haar_random_states(N_obs, 20000, rng)
        ovlps = tools.quantum.overlaps_batch(P, observers)

        b = N_obs - 1
        for k in range(min(M_test, 3)):
            g = -np.log(np.maximum(ovlps[k], tools.quantum.SAFE_FLOOR))
            _stat, p = scipy.stats.kstest(
                g, lambda y, b=b: (1 - np.exp(-np.clip(y, 0, 500))) ** b,
            )
            min_p = min(min_p, p)

    return tools.quantum.StatTest(0.0, min_p, min_p > 0.01)


def run_independence_test(
    rng: np.random.Generator,
) -> tools.quantum.StatTest:
    max_corr = 0.0
    for N_obs in [8, 16, 32, 64]:
        M_test = min(3, N_obs)
        pointers = tools.quantum.make_orthogonal_pointers(M_test, N_obs, rng)
        P = np.array(pointers.states)
        n_samples = 10000

        observers = tools.bld.haar_random_states(N_obs, n_samples, rng)
        ovlps = tools.quantum.overlaps_batch(P, observers)
        G = -np.log(np.maximum(ovlps, tools.quantum.SAFE_FLOOR)).T

        corr = np.corrcoef(G.T)
        off_diag = corr[np.triu_indices_from(corr, k=1)]
        max_corr = max(max_corr, float(np.max(np.abs(off_diag))))

    return tools.quantum.StatTest(max_corr, 0.0, max_corr < 0.1)


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.theory
def test_ratio_rule_born(rng: np.random.Generator) -> None:
    assert all(t.passes for t in run_born_tests(rng))


@pytest.mark.theory
def test_product_rule(rng: np.random.Generator) -> None:
    assert all(t.passes for t in run_product_tests(rng))


@pytest.mark.theory
def test_overlap_distribution(rng: np.random.Generator) -> None:
    assert run_overlap_distribution_test(rng).passes


@pytest.mark.theory
def test_independence(rng: np.random.Generator) -> None:
    assert run_independence_test(rng).passes
