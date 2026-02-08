"""Selection rule verification."""

import enum
import sys
import typing

import numpy as np
import scipy.stats

from . import quantum


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
    rule: typing.Callable = quantum.selection_rule,
    *,
    m_filter: int | None = None,
) -> list[quantum.StatTest]:
    results = []
    for M, _desc, alphas in CONFIGS:
        if m_filter is not None and M != m_filter:
            continue
        a = np.array(alphas)
        for N_obs in N_OBS_VALUES:
            if N_obs < M:
                continue
            n = min(50000, 20000 if N_obs >= 32 else 50000)
            pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
            outcome = quantum.run_selection_mc(pointers, a, n, rng, rule=rule)
            results.append(quantum.chi2_test(outcome.counts, a, n))
    return results


def run_born_tests(rng: np.random.Generator) -> list[quantum.StatTest]:
    return _run_rule_tests(rng)


def run_product_tests(rng: np.random.Generator) -> list[quantum.StatTest]:
    return _run_rule_tests(rng, rule=quantum.rule_product, m_filter=2)


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
            pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
            P = np.array(pointers.states)

            observers = quantum.haar_random_states(N_obs, n, rng)
            ovlps = quantum.overlaps_batch(P, observers)
            safe = np.maximum(ovlps, quantum.SAFE_FLOOR)

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
                stat = quantum.chi2_test(counts, a, n)
                entry["results"][name] = {
                    "frequencies": counts / n,
                    "expected": a.copy(),
                    "chi2": stat.chi2_stat,
                    "p_value": stat.p_value,
                    "matches_born": stat.passes,
                }
            all_results.append(entry)

    return all_results


def run_overlap_distribution_test(rng: np.random.Generator) -> float:
    min_p = 1.0
    for N_obs in [8, 16, 32, 64, 128]:
        M_test = min(3, N_obs)
        pointers = quantum.make_orthogonal_pointers(M_test, N_obs, rng)
        P = np.array(pointers.states)

        observers = quantum.haar_random_states(N_obs, 20000, rng)
        ovlps = quantum.overlaps_batch(P, observers)

        b = N_obs - 1
        for k in range(min(M_test, 3)):
            g = -np.log(np.maximum(ovlps[k], quantum.SAFE_FLOOR))
            _stat, p = scipy.stats.kstest(
                g, lambda y, b=b: (1 - np.exp(-np.clip(y, 0, 500))) ** b,
            )
            min_p = min(min_p, p)

    return min_p


def run_independence_test(rng: np.random.Generator) -> float:
    max_corr = 0.0
    for N_obs in [8, 16, 32, 64]:
        M_test = min(3, N_obs)
        pointers = quantum.make_orthogonal_pointers(M_test, N_obs, rng)
        P = np.array(pointers.states)
        n_samples = 10000

        observers = quantum.haar_random_states(N_obs, n_samples, rng)
        ovlps = quantum.overlaps_batch(P, observers)
        G = -np.log(np.maximum(ovlps, quantum.SAFE_FLOOR)).T

        corr = np.corrcoef(G.T)
        off_diag = corr[np.triu_indices_from(corr, k=1)]
        max_corr = max(max_corr, float(np.max(np.abs(off_diag))))

    return max_corr


def main() -> int:
    rng = np.random.default_rng(42)

    print("=" * 80)
    print("BLD SELECTION RULE TEST: Does L/B = structural leverage predict k?")
    print("=" * 80)
    print()
    print("PREDICTION: Rule B (ratio = L/B) gives Born statistics for ALL M")
    print("            Rule A (product) works for M=2 only, fails M>=3")
    print("            Rule C (max overlap) gives ~1/M (ignores amplitudes)")
    print()

    all_results = run_all_rules(rng)

    for r in all_results:
        print(f"\n--- M={r['M']} ({r['desc']}), N_obs={r['N_obs']} ---")
        a = r["results"][RuleName.RATIO]["expected"]
        print(f"  Expected: {[round(x, 4) for x in a]}")

        for name, data in sorted(r["results"].items()):
            status = "PASS" if data["matches_born"] else "FAIL"
            print(
                f"  {name:18s}: freq={np.round(data['frequencies'], 4)}, "
                f"chi2={data['chi2']:8.2f}, p={data['p_value']:.4f} [{status}]"
            )

    print("\n" + "=" * 80)
    print("SUMMARY: Pass rates by rule")
    print("=" * 80)

    for name in RuleName:
        passes = sum(
            1 for r in all_results if r["results"][name]["matches_born"]
        )
        total = len(all_results)
        m2_pass = sum(
            1 for r in all_results
            if r["M"] == 2 and r["results"][name]["matches_born"]
        )
        m2_total = sum(1 for r in all_results if r["M"] == 2)
        m3plus_pass = sum(
            1 for r in all_results
            if r["M"] >= 3 and r["results"][name]["matches_born"]
        )
        m3plus_total = sum(1 for r in all_results if r["M"] >= 3)

        print(
            f"  {name:18s}: {passes:2d}/{total} total, "
            f"{m2_pass}/{m2_total} M=2, {m3plus_pass}/{m3plus_total} M>=3"
        )

    print("\n" + "=" * 80)
    print("KEY RESULT: Product (A) vs Ratio (B) for M >= 3")
    print("=" * 80)

    for r in all_results:
        if r["M"] < 3:
            continue
        ra = r["results"][RuleName.PRODUCT]
        rb = r["results"][RuleName.RATIO]
        print(
            f"  M={r['M']}, N={r['N_obs']:4d} ({r['desc']:12s}): "
            f"Product p={ra['p_value']:.4f}"
            f"[{'OK' if ra['matches_born'] else 'FAIL'}] "
            f"Ratio p={rb['p_value']:.4f}"
            f"[{'OK' if rb['matches_born'] else 'FAIL'}]"
        )
        if not ra["matches_born"]:
            print(
                f"    Product bias: expected={np.round(ra['expected'], 3)}, "
                f"got={np.round(ra['frequencies'], 3)}"
            )

    print("\n" + "=" * 80)
    print("OVERLAP DISTRIBUTION TEST: Is -log|<O_k|O>|^2 ~ -log(Beta(1, N-1))?")
    print("=" * 80)

    overlap_p = run_overlap_distribution_test(rng)
    status = "PASS" if overlap_p > 0.01 else "FAIL"
    print(f"  Min KS p-value: {overlap_p:.4f} [{status}]")

    print("\n" + "=" * 80)
    print("INDEPENDENCE TEST: Correlation of G_k across outcomes")
    print("=" * 80)

    max_corr = run_independence_test(rng)
    status = "PASS" if max_corr < 0.1 else "FAIL"
    print(f"  Max |off-diag corr|: {max_corr:.4f} [{status}]")

    print("\n" + "=" * 80)
    print("VERDICT")
    print("=" * 80)

    ratio_all_pass = all(
        r["results"][RuleName.RATIO]["matches_born"] for r in all_results
    )
    product_m3_any_fail = any(
        not r["results"][RuleName.PRODUCT]["matches_born"]
        for r in all_results
        if r["M"] >= 3
    )

    if ratio_all_pass:
        print("  RATIO RULE (L/B) REPRODUCES BORN STATISTICS FOR ALL M")
    else:
        ratio_fails = [
            r for r in all_results
            if not r["results"][RuleName.RATIO]["matches_born"]
        ]
        print(f"  RATIO RULE FAILED {len(ratio_fails)} tests")

    if product_m3_any_fail:
        print("  PRODUCT RULE FAILS FOR M>=3 (as predicted)")
    else:
        print("  WARNING: Product rule did not fail for M>=3")

    return 0 if ratio_all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
