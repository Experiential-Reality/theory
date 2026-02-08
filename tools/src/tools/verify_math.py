"""Comprehensive mathematical verification of the BLD selection rule."""

import itertools
import sys

import numpy as np
import scipy.stats

from . import quantum

def run_degenerate_amplitudes(rng: np.random.Generator) -> list[quantum.StatTest]:
    configs = [
        (3, [0.6, 0.4, 0.0]),
        (4, [0.5, 0.3, 0.2, 0.0]),
        (4, [0.5, 0.5, 0.0, 0.0]),
        (5, [0.9, 0.1, 0.0, 0.0, 0.0]),
    ]
    results = []
    for M, alphas in configs:
        a = np.array(alphas)
        nonzero = np.where(a > 0)[0]
        zero = np.where(a == 0)[0]
        a_renorm = a[nonzero] / a[nonzero].sum()

        for N_obs in [8, 32, 128]:
            if N_obs < M:
                continue
            n = 100000
            pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
            P = np.array(pointers.states)
            observers = quantum.haar_random_states(N_obs, n, rng)
            ovlps = quantum.overlaps_batch(P, observers)
            safe = np.maximum(ovlps, quantum.SAFE_FLOOR)
            choices = np.argmax(a[:, None] / safe, axis=0)
            counts = np.bincount(choices, minlength=M).astype(float)

            zero_selected = counts[zero].sum()
            if zero_selected > 0:
                results.append(quantum.StatTest(float("inf"), 0.0, False))
                continue
            results.append(quantum.chi2_test(counts[nonzero], a_renorm, n))
    return results


def run_m_equals_n(rng: np.random.Generator) -> list[quantum.StatTest]:
    configs = [
        (2, [0.5, 0.5]),
        (2, [0.8, 0.2]),
        (3, [1 / 3, 1 / 3, 1 / 3]),
        (3, [0.5, 0.3, 0.2]),
        (4, [0.25, 0.25, 0.25, 0.25]),
        (4, [0.6, 0.2, 0.15, 0.05]),
        (5, [0.2, 0.2, 0.2, 0.2, 0.2]),
        (5, [0.5, 0.2, 0.15, 0.1, 0.05]),
        (8, [1 / 8] * 8),
        (8, [0.3, 0.2, 0.15, 0.1, 0.08, 0.07, 0.06, 0.04]),
        (16, [1 / 16] * 16),
    ]
    results = []
    for M, alphas in configs:
        a = np.array(alphas)
        n = 20000 if M >= 16 else 100000 if M >= 8 else 50000
        pointers = quantum.make_orthogonal_pointers(M, M, rng)
        outcome = quantum.run_selection_mc(pointers, a, n, rng)
        results.append(quantum.chi2_test(outcome.counts, a, n))
    return results


def run_complex_phases(rng: np.random.Generator) -> list[quantum.StatTest]:
    M = 3
    N_obs = 32
    n = 80000
    target = np.array([0.5, 0.3, 0.2])

    phase_configs = [
        np.sqrt(target).astype(complex),
        np.array([
            np.sqrt(0.5),
            np.sqrt(0.3) * np.exp(1j * np.pi),
            np.sqrt(0.2),
        ]),
        np.array([
            np.sqrt(0.5) * np.exp(1j * np.pi / 4),
            np.sqrt(0.3) * np.exp(1j * 2 * np.pi / 3),
            np.sqrt(0.2) * np.exp(1j * 5 * np.pi / 7),
        ]),
        np.sqrt(target) * 1j,
    ]

    pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
    P = np.array(pointers.states)
    fixed_rng = np.random.default_rng(12345)
    observers = quantum.haar_random_states(N_obs, n, fixed_rng)
    ovlps = quantum.overlaps_batch(P, observers)

    results = []
    reference_choices = None
    for alpha_complex in phase_configs:
        a_sq = np.abs(alpha_complex) ** 2
        safe = np.maximum(ovlps, quantum.SAFE_FLOOR)
        choices = np.argmax(a_sq[:, None] / safe, axis=0)

        if reference_choices is None:
            reference_choices = choices
            counts = np.bincount(choices, minlength=M).astype(float)
            results.append(quantum.chi2_test(counts, target, n))
        else:
            identical = bool(np.array_equal(choices, reference_choices))
            results.append(quantum.StatTest(0.0, 1.0, identical))

    return results


def run_nonorthogonal_pointers(rng: np.random.Generator) -> list[quantum.StatTest]:
    N_obs = 32
    alpha_sq = np.array([0.7, 0.3])
    n = 100000
    results = []

    for eps in np.arange(0.0, 0.51, 0.1):
        if eps < 1e-10:
            pointers = quantum.make_orthogonal_pointers(2, N_obs, rng)
        else:
            pointers = quantum.make_nonorthogonal_pointers_m2(N_obs, eps, rng)

        p_expected = quantum.p_nonorthogonal(0.7, 0.3, eps)
        expected = np.array([p_expected, 1.0 - p_expected])

        outcome = quantum.run_selection_mc(pointers, alpha_sq, n, rng)
        results.append(quantum.chi2_test(outcome.counts, expected, n))
    return results


def run_large_m(rng: np.random.Generator) -> list[quantum.StatTest]:
    configs = [
        (10, 20, np.ones(10) / 10),
        (10, 20, None),
        (20, 40, np.ones(20) / 20),
        (20, 40, None),
        (50, 100, np.ones(50) / 50),
        (50, 100, None),
    ]
    results = []
    for M, N_obs, alphas in configs:
        if alphas is None:
            raw = np.array([2.0 ** (-k) for k in range(M)])
            alphas = raw / raw.sum()
        n = 50000 if M <= 20 else 100000
        pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
        outcome = quantum.run_selection_mc(pointers, alphas, n, rng)
        results.append(quantum.chi2_test(outcome.counts, alphas, n))
    return results


def run_dirichlet_decomposition(rng: np.random.Generator) -> list[quantum.StatTest]:
    M = 3
    a = np.array([0.5, 0.3, 0.2])
    n = 100000
    results = []

    Y = rng.exponential(1.0, size=(n, M))
    choices = np.argmax(a[None, :] / Y, axis=1)
    counts = np.bincount(choices, minlength=M).astype(float)
    results.append(quantum.chi2_test(counts, a, n))

    for N_total in [3, 10, 100, 1000]:
        Y = rng.exponential(1.0, size=(n, N_total))
        S = Y.sum(axis=1, keepdims=True)
        X = Y[:, :M] / S
        choices = np.argmax(a[None, :] / X, axis=1)
        counts = np.bincount(choices, minlength=M).astype(float)
        results.append(quantum.chi2_test(counts, a, n))

    G = rng.gumbel(0, 1, size=(n, M))
    choices = np.argmax(np.log(a)[None, :] + G, axis=1)
    counts = np.bincount(choices, minlength=M).astype(float)
    results.append(quantum.chi2_test(counts, a, n))

    # Haar-random
    pointers = quantum.make_orthogonal_pointers(M, 32, rng)
    outcome = quantum.run_selection_mc(pointers, a, n, rng)
    results.append(quantum.chi2_test(outcome.counts, a, n))

    return results


def run_tau_uniqueness(rng: np.random.Generator) -> list[quantum.StatTest]:
    M = 3
    N_obs = 64
    a = np.array([0.5, 0.3, 0.2])
    n = 50000
    pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
    P = np.array(pointers.states)
    observers = quantum.haar_random_states(N_obs, n, rng)
    ovlps = quantum.overlaps_batch(P, observers)
    results = []

    for tau in [0.5, 0.8, 1.0, 1.2, 1.5, 2.0, 3.0]:
        weights = np.power(a, 1.0 / tau)
        expected = weights / weights.sum()

        safe = np.maximum(ovlps, quantum.SAFE_FLOOR)
        w = np.power(np.maximum(a, quantum.SAFE_FLOOR), 1.0 / tau)
        choices = np.argmax(w[:, None] / safe, axis=0)
        counts = np.bincount(choices, minlength=M).astype(float)

        results.append(quantum.chi2_test(counts, expected, n))

        if abs(tau - 1.0) > 1e-10:
            born_test = quantum.chi2_test(counts, a, n)
            results.append(quantum.StatTest(
                born_test.chi2_stat, born_test.p_value, not born_test.passes,
            ))
    return results


def run_joint_measurement(rng: np.random.Generator) -> list[quantum.StatTest]:
    M_A, M_B = 2, 2
    N_A, N_B = 8, 8
    n = 100000
    results = []

    pointers_A = quantum.make_orthogonal_pointers(M_A, N_A, rng)
    pointers_B = quantum.make_orthogonal_pointers(M_B, N_B, rng)

    joint_pointers = []
    joint_labels = []
    for k in range(M_A):
        for j in range(M_B):
            joint_pointers.append(np.kron(pointers_A.states[k], pointers_B.states[j]))
            joint_labels.append((k, j))

    joint_ps = quantum.PointerSet(
        tuple(joint_pointers), quantum.PointerKind.ORTHOGONAL,
    )

    for alpha_matrix in [
        np.array([[0.5, 0.0], [0.0, 0.5]]),
        np.array([[0.7, 0.0], [0.0, 0.3]]),
    ]:
        a_flat = np.array([alpha_matrix[k, j] for k, j in joint_labels])
        outcome = quantum.run_selection_mc(joint_ps, a_flat, n, rng)

        nonzero = a_flat > 0
        a_nz = a_flat[nonzero] / a_flat[nonzero].sum()
        results.append(quantum.chi2_test(outcome.counts[nonzero], a_nz, n))

    # GHZ-like
    N_party = 4
    M_party = 3
    N_ghz = N_party ** 3

    ptrs = [quantum.make_orthogonal_pointers(M_party, N_party, rng) for _ in range(3)]
    ghz_pointers = []
    ghz_labels = []
    for i in range(M_party):
        for j in range(M_party):
            for k in range(M_party):
                ghz_pointers.append(
                    np.kron(np.kron(ptrs[0].states[i], ptrs[1].states[j]), ptrs[2].states[k])
                )
                ghz_labels.append((i, j, k))

    ghz_a = np.zeros(len(ghz_pointers))
    for idx, (i, j, k) in enumerate(ghz_labels):
        if i == j == k == 0:
            ghz_a[idx] = 0.5
        elif i == j == k == 1:
            ghz_a[idx] = 0.3
        elif i == j == k == 2:
            ghz_a[idx] = 0.2

    ghz_ps = quantum.PointerSet(tuple(ghz_pointers), quantum.PointerKind.ORTHOGONAL)
    outcome = quantum.run_selection_mc(ghz_ps, ghz_a, 50000, rng)

    nonzero = ghz_a > 0
    a_nz = ghz_a[nonzero] / ghz_a[nonzero].sum()
    results.append(quantum.chi2_test(outcome.counts[nonzero], a_nz, 50000))

    return results


def run_m2_symmetry(rng: np.random.Generator) -> list[quantum.StatTest]:
    n = 80000
    results = []

    for alpha_sq_0 in [0.5, 0.6, 0.7, 0.8, 0.9]:
        a = np.array([alpha_sq_0, 1 - alpha_sq_0])
        for N_obs in [4, 16, 64]:
            pointers = quantum.make_orthogonal_pointers(2, N_obs, rng)
            P = np.array(pointers.states)
            observers = quantum.haar_random_states(N_obs, n, rng)
            ovlps = quantum.overlaps_batch(P, observers)

            safe = np.maximum(ovlps, quantum.SAFE_FLOOR)
            ratio_choices = np.argmax(a[:, None] / safe, axis=0)
            product_choices = np.argmax(a[:, None] * ovlps, axis=0)

            counts_ratio = np.bincount(ratio_choices, minlength=2).astype(float)
            counts_product = np.bincount(product_choices, minlength=2).astype(float)

            results.append(quantum.chi2_test(counts_ratio, a, n))
            results.append(quantum.chi2_test(counts_product, a, n))

    return results


def run_m2_product_ratio_proof(rng: np.random.Generator) -> list[quantum.StatTest]:
    n = 200000
    results = []

    Y0 = rng.exponential(1.0, size=n)
    Y1 = rng.exponential(1.0, size=n)
    T = Y0 / Y1

    for s in [0.5, 1.0, 2.0, 5.0]:
        p_T = np.mean(T > s)
        p_inv = np.mean(1.0 / T > s)
        p_exact = 1.0 / (1.0 + s)
        tol = 3.0 / np.sqrt(n)
        ok = abs(p_T - p_exact) < tol and abs(p_inv - p_exact) < tol
        results.append(quantum.StatTest(abs(p_T - p_exact), p_exact, ok))

    # M=3 closed-form counterexample
    a3 = np.array([0.5, 0.3, 0.2])

    def p_product_closed_form(a, k):
        others = [j for j in range(len(a)) if j != k]
        total = 0.0
        for size in range(len(others) + 1):
            for S in itertools.combinations(others, size):
                sign = (-1) ** len(S)
                denom = 1.0 + sum(a[k] / a[j] for j in S)
                total += sign / denom
        return total

    p_analytical = np.array([p_product_closed_form(a3, k) for k in range(3)])

    Y = rng.exponential(1.0, size=(n, 3))
    choices = np.argmax(a3[None, :] * Y, axis=1)
    counts_mc = np.bincount(choices, minlength=3).astype(float)
    p_mc = counts_mc / n

    for k in range(3):
        ok = abs(p_analytical[k] - p_mc[k]) < 0.006
        results.append(quantum.StatTest(abs(p_analytical[k] - p_mc[k]), p_mc[k], ok))

    return results


def run_factored_observer_analytical(rng: np.random.Generator) -> list[quantum.StatTest]:
    n = 100000
    results = []

    def p_factored_analytical(r):
        if abs(r - 1.0) < 1e-10:
            return 0.5
        return (1.0 - r + r * np.log(r)) / (1.0 - r) ** 2

    YA = rng.exponential(1.0, size=(n, 2))
    YB = rng.exponential(1.0, size=(n, 2))

    for a00 in [0.55, 0.60, 0.65, 0.70, 0.75, 0.80, 0.85, 0.90]:
        a11 = 1.0 - a00
        r = a11 / a00
        p_anal = p_factored_analytical(r)

        wins = a00 / (YA[:, 0] * YB[:, 0]) > a11 / (YA[:, 1] * YB[:, 1])
        p_mc = float(np.mean(wins))
        ok = abs(p_anal - p_mc) < 0.006
        results.append(quantum.StatTest(abs(p_anal - p_mc), p_mc, ok))

    return results


def run_nonorthogonal_analytical(rng: np.random.Generator) -> list[quantum.StatTest]:
    a0, a1 = 0.7, 0.3
    alpha_sq = np.array([a0, a1])
    n = 100000
    results = []

    for eps in [0.0, 0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.50, 0.70, 0.90]:
        p_int = quantum.p_nonorthogonal(a0, a1, eps)

        N_obs = 32
        if eps < 1e-10:
            pointers = quantum.make_orthogonal_pointers(2, N_obs, rng)
        else:
            pointers = quantum.make_nonorthogonal_pointers_m2(N_obs, eps, rng)

        outcome = quantum.run_selection_mc(pointers, alpha_sq, n, rng)
        p_mc = outcome.counts[0] / n

        ok = abs(p_int - p_mc) < 0.006
        results.append(quantum.StatTest(abs(p_int - p_mc), p_mc, ok))

    # N-independence
    eps_test = 0.20
    p_int = quantum.p_nonorthogonal(a0, a1, eps_test)
    for N_obs in [4, 8, 32, 128]:
        pointers = quantum.make_nonorthogonal_pointers_m2(N_obs, eps_test, rng)
        outcome = quantum.run_selection_mc(pointers, alpha_sq, n, rng)
        p_mc = outcome.counts[0] / n
        ok = abs(p_int - p_mc) < 0.006
        results.append(quantum.StatTest(abs(p_int - p_mc), p_mc, ok))

    # Taylor c1
    h = 1e-5
    for a0_t, a1_t in [(0.7, 0.3), (0.8, 0.2), (0.6, 0.4), (0.9, 0.1), (0.5, 0.5)]:
        p_h = quantum.p_nonorthogonal(a0_t, a1_t, h)
        c1_num = (p_h - a0_t) / h
        c1_formula = a0_t * a1_t * (a0_t - a1_t)
        ok = abs(c1_num - c1_formula) < 0.001
        results.append(quantum.StatTest(abs(c1_num - c1_formula), c1_formula, ok))

    return results

def main() -> int:
    rng = np.random.default_rng(42)

    print("=" * 80)
    print("COMPREHENSIVE MATHEMATICAL VERIFICATION")
    print("=" * 80)

    tests = [
        ("1. Degenerate amplitudes", run_degenerate_amplitudes),
        ("2. M = N boundary", run_m_equals_n),
        ("3. Complex phases", run_complex_phases),
        ("4. Non-orthogonal pointers", run_nonorthogonal_pointers),
        ("5. Large M", run_large_m),
        ("6. Dirichlet decomposition", run_dirichlet_decomposition),
        ("7. Tau uniqueness", run_tau_uniqueness),
        ("8. Joint measurement", run_joint_measurement),
        ("9. M=2 symmetry", run_m2_symmetry),
        ("10. M=2 product/ratio proof", run_m2_product_ratio_proof),
        ("11. Factored observer analytical", run_factored_observer_analytical),
        ("12. Non-orthogonal analytical", run_nonorthogonal_analytical),
    ]

    all_pass = True
    for name, fn in tests:
        print(f"\n--- {name} ---")
        results = fn(rng)
        passes = sum(1 for r in results if r.passes)
        total = len(results)
        ok = all(r.passes for r in results)
        if not ok:
            all_pass = False
        status = "PASS" if ok else "FAIL"
        print(f"  {passes}/{total} sub-tests passed [{status}]")

    print(f"\n{'=' * 80}")
    print(f"VERDICT: {'ALL PASS' if all_pass else 'SOME FAILED'}")
    print(f"{'=' * 80}")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
