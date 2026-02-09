"""Comprehensive mathematical verification of the BLD selection rule."""

import itertools

import numpy as np
import scipy.stats

import tools.bld
import tools.quantum

from helpers import assert_all_pass


def test_degenerate_amplitudes(rng: np.random.Generator) -> None:
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
            pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
            P = np.array(pointers.states)
            observers = tools.bld.haar_random_states(N_obs, n, rng)
            ovlps = tools.quantum.overlaps_batch(P, observers)
            safe = np.maximum(ovlps, tools.quantum.SAFE_FLOOR)
            choices = np.argmax(a[:, None] / safe, axis=0)
            counts = np.bincount(choices, minlength=M).astype(float)

            zero_selected = counts[zero].sum()
            if zero_selected > 0:
                results.append(tools.quantum.StatTest(float("inf"), 0.0, False))
                continue
            results.append(tools.quantum.chi2_test(counts[nonzero], a_renorm, n))
    assert_all_pass(results)


def test_m_equals_n(rng: np.random.Generator) -> None:
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
        pointers = tools.quantum.make_orthogonal_pointers(M, M, rng)
        outcome = tools.quantum.run_selection_mc(pointers, a, n, rng)
        results.append(tools.quantum.chi2_test(outcome.counts, a, n))
    assert_all_pass(results)


def test_complex_phases(rng: np.random.Generator) -> None:
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

    pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
    P = np.array(pointers.states)
    fixed_rng = np.random.default_rng(12345)
    observers = tools.bld.haar_random_states(N_obs, n, fixed_rng)
    ovlps = tools.quantum.overlaps_batch(P, observers)

    results = []
    reference_choices = None
    for alpha_complex in phase_configs:
        a_sq = np.abs(alpha_complex) ** 2
        safe = np.maximum(ovlps, tools.quantum.SAFE_FLOOR)
        choices = np.argmax(a_sq[:, None] / safe, axis=0)

        if reference_choices is None:
            reference_choices = choices
            counts = np.bincount(choices, minlength=M).astype(float)
            results.append(tools.quantum.chi2_test(counts, target, n))
        else:
            identical = bool(np.array_equal(choices, reference_choices))
            results.append(tools.quantum.StatTest(0.0, 1.0, identical))

    assert_all_pass(results)


def test_nonorthogonal_pointers(rng: np.random.Generator) -> None:
    N_obs = 32
    alpha_sq = np.array([0.7, 0.3])
    n = 100000
    results = []

    for eps in np.arange(0.0, 0.51, 0.1):
        if eps < 1e-10:
            pointers = tools.quantum.make_orthogonal_pointers(2, N_obs, rng)
        else:
            pointers = tools.quantum.make_nonorthogonal_pointers_m2(N_obs, eps, rng)

        p_expected = tools.quantum.p_nonorthogonal(0.7, 0.3, eps)
        expected = np.array([p_expected, 1.0 - p_expected])

        outcome = tools.quantum.run_selection_mc(pointers, alpha_sq, n, rng)
        results.append(tools.quantum.chi2_test(outcome.counts, expected, n))
    assert_all_pass(results)


def test_large_m(rng: np.random.Generator) -> None:
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
        pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
        outcome = tools.quantum.run_selection_mc(pointers, alphas, n, rng)
        results.append(tools.quantum.chi2_test(outcome.counts, alphas, n))
    assert_all_pass(results)


def test_dirichlet_decomposition(rng: np.random.Generator) -> None:
    M = 3
    a = np.array([0.5, 0.3, 0.2])
    n = 100000
    results = []

    Y = rng.exponential(1.0, size=(n, M))
    choices = np.argmax(a[None, :] / Y, axis=1)
    counts = np.bincount(choices, minlength=M).astype(float)
    results.append(tools.quantum.chi2_test(counts, a, n))

    for N_total in [3, 10, 100, 1000]:
        Y = rng.exponential(1.0, size=(n, N_total))
        S = Y.sum(axis=1, keepdims=True)
        X = Y[:, :M] / S
        choices = np.argmax(a[None, :] / X, axis=1)
        counts = np.bincount(choices, minlength=M).astype(float)
        results.append(tools.quantum.chi2_test(counts, a, n))

    G = rng.gumbel(0, 1, size=(n, M))
    choices = np.argmax(np.log(a)[None, :] + G, axis=1)
    counts = np.bincount(choices, minlength=M).astype(float)
    results.append(tools.quantum.chi2_test(counts, a, n))

    # Haar-random
    pointers = tools.quantum.make_orthogonal_pointers(M, 32, rng)
    outcome = tools.quantum.run_selection_mc(pointers, a, n, rng)
    results.append(tools.quantum.chi2_test(outcome.counts, a, n))

    assert_all_pass(results)


def test_tau_uniqueness(rng: np.random.Generator) -> None:
    M = 3
    N_obs = 64
    a = np.array([0.5, 0.3, 0.2])
    n = 50000
    pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
    P = np.array(pointers.states)
    observers = tools.bld.haar_random_states(N_obs, n, rng)
    ovlps = tools.quantum.overlaps_batch(P, observers)
    results = []

    for tau in [0.5, 0.8, 1.0, 1.2, 1.5, 2.0, 3.0]:
        weights = np.power(a, 1.0 / tau)
        expected = weights / weights.sum()

        safe = np.maximum(ovlps, tools.quantum.SAFE_FLOOR)
        w = np.power(np.maximum(a, tools.quantum.SAFE_FLOOR), 1.0 / tau)
        choices = np.argmax(w[:, None] / safe, axis=0)
        counts = np.bincount(choices, minlength=M).astype(float)

        results.append(tools.quantum.chi2_test(counts, expected, n))

        if abs(tau - 1.0) > 1e-10:
            born_test = tools.quantum.chi2_test(counts, a, n)
            results.append(tools.quantum.StatTest(
                born_test.chi2_stat, born_test.p_value, not born_test.passes,
            ))
    assert_all_pass(results)


def test_joint_measurement(rng: np.random.Generator) -> None:
    M_A, M_B = 2, 2
    N_A, N_B = 8, 8
    n = 100000
    results = []

    pointers_A = tools.quantum.make_orthogonal_pointers(M_A, N_A, rng)
    pointers_B = tools.quantum.make_orthogonal_pointers(M_B, N_B, rng)

    joint_pointers = []
    joint_labels = []
    for k in range(M_A):
        for j in range(M_B):
            joint_pointers.append(np.kron(pointers_A.states[k], pointers_B.states[j]))
            joint_labels.append((k, j))

    joint_ps = tools.quantum.PointerSet(
        tuple(joint_pointers), tools.quantum.PointerKind.ORTHOGONAL,
    )

    for alpha_matrix in [
        np.array([[0.5, 0.0], [0.0, 0.5]]),
        np.array([[0.7, 0.0], [0.0, 0.3]]),
    ]:
        a_flat = np.array([alpha_matrix[k, j] for k, j in joint_labels])
        outcome = tools.quantum.run_selection_mc(joint_ps, a_flat, n, rng)

        nonzero = a_flat > 0
        a_nz = a_flat[nonzero] / a_flat[nonzero].sum()
        results.append(tools.quantum.chi2_test(outcome.counts[nonzero], a_nz, n))

    # GHZ-like
    N_party = 4
    M_party = 3
    N_ghz = N_party ** 3

    ptrs = [tools.quantum.make_orthogonal_pointers(M_party, N_party, rng) for _ in range(3)]
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

    ghz_ps = tools.quantum.PointerSet(tuple(ghz_pointers), tools.quantum.PointerKind.ORTHOGONAL)
    outcome = tools.quantum.run_selection_mc(ghz_ps, ghz_a, 50000, rng)

    nonzero = ghz_a > 0
    a_nz = ghz_a[nonzero] / ghz_a[nonzero].sum()
    results.append(tools.quantum.chi2_test(outcome.counts[nonzero], a_nz, 50000))

    assert_all_pass(results)


def test_m2_symmetry(rng: np.random.Generator) -> None:
    n = 80000
    results = []

    for alpha_sq_0 in [0.5, 0.6, 0.7, 0.8, 0.9]:
        a = np.array([alpha_sq_0, 1 - alpha_sq_0])
        for N_obs in [4, 16, 64]:
            pointers = tools.quantum.make_orthogonal_pointers(2, N_obs, rng)
            P = np.array(pointers.states)
            observers = tools.bld.haar_random_states(N_obs, n, rng)
            ovlps = tools.quantum.overlaps_batch(P, observers)

            safe = np.maximum(ovlps, tools.quantum.SAFE_FLOOR)
            ratio_choices = np.argmax(a[:, None] / safe, axis=0)
            product_choices = np.argmax(a[:, None] * ovlps, axis=0)

            counts_ratio = np.bincount(ratio_choices, minlength=2).astype(float)
            counts_product = np.bincount(product_choices, minlength=2).astype(float)

            results.append(tools.quantum.chi2_test(counts_ratio, a, n))
            results.append(tools.quantum.chi2_test(counts_product, a, n))

    assert_all_pass(results)


def test_m2_product_ratio_proof(rng: np.random.Generator) -> None:
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
        results.append(tools.quantum.StatTest(abs(p_T - p_exact), p_exact, ok))

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
        results.append(tools.quantum.StatTest(abs(p_analytical[k] - p_mc[k]), p_mc[k], ok))

    assert_all_pass(results)


def test_factored_observer_analytical(rng: np.random.Generator) -> None:
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
        results.append(tools.quantum.StatTest(abs(p_anal - p_mc), p_mc, ok))

    assert_all_pass(results)


def test_nonorthogonal_analytical(rng: np.random.Generator) -> None:
    a0, a1 = 0.7, 0.3
    alpha_sq = np.array([a0, a1])
    n = 100000
    results = []

    for eps in [0.0, 0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.50, 0.70, 0.90]:
        p_int = tools.quantum.p_nonorthogonal(a0, a1, eps)

        N_obs = 32
        if eps < 1e-10:
            pointers = tools.quantum.make_orthogonal_pointers(2, N_obs, rng)
        else:
            pointers = tools.quantum.make_nonorthogonal_pointers_m2(N_obs, eps, rng)

        outcome = tools.quantum.run_selection_mc(pointers, alpha_sq, n, rng)
        p_mc = outcome.counts[0] / n

        ok = abs(p_int - p_mc) < 0.006
        results.append(tools.quantum.StatTest(abs(p_int - p_mc), p_mc, ok))

    # N-independence
    eps_test = 0.20
    p_int = tools.quantum.p_nonorthogonal(a0, a1, eps_test)
    for N_obs in [4, 8, 32, 128]:
        pointers = tools.quantum.make_nonorthogonal_pointers_m2(N_obs, eps_test, rng)
        outcome = tools.quantum.run_selection_mc(pointers, alpha_sq, n, rng)
        p_mc = outcome.counts[0] / n
        ok = abs(p_int - p_mc) < 0.006
        results.append(tools.quantum.StatTest(abs(p_int - p_mc), p_mc, ok))

    # Taylor c1
    h = 1e-5
    for a0_t, a1_t in [(0.7, 0.3), (0.8, 0.2), (0.6, 0.4), (0.9, 0.1), (0.5, 0.5)]:
        p_h = tools.quantum.p_nonorthogonal(a0_t, a1_t, h)
        c1_num = (p_h - a0_t) / h
        c1_formula = a0_t * a1_t * (a0_t - a1_t)
        ok = abs(c1_num - c1_formula) < 0.001
        results.append(tools.quantum.StatTest(abs(c1_num - c1_formula), c1_formula, ok))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Adversarial: noise distribution and power uniqueness
# ---------------------------------------------------------------------------


def test_wrong_noise_distribution(rng: np.random.Generator) -> None:
    """The ratio rule ≡ argmax(log α + Gumbel).  Wrong noise breaks Born.

    Haar-random overlaps are exponentially distributed (from unitary
    invariance).  The ratio argmax(α/overlap) is equivalent to
    argmax(log α + Gumbel) via the Gumbel max trick.  This Gumbel
    structure is what makes the rule recover Born probabilities.

    Replace Gumbel with Gaussian, uniform, or Laplace noise.  For M=3,
    the resulting probabilities are NOT Born — the noise distribution
    matters structurally.
    """
    M = 3
    n = 100000
    alphas = np.array([0.5, 0.3, 0.2])
    log_alphas = np.log(alphas)

    results: list[tools.bld.TestResult] = []

    # Gumbel (correct): should recover Born
    gumbel = rng.gumbel(0, 1, size=(n, M))
    choices_g = np.argmax(log_alphas[None, :] + gumbel, axis=1)
    counts_g = np.bincount(choices_g, minlength=M).astype(float)
    stat_g = tools.quantum.chi2_test(counts_g, alphas, n)
    results.append(tools.bld.TestResult("gumbel_recovers_born", stat_g.passes))

    # Gaussian (wrong): lighter tails bias toward max α
    gaussian = rng.standard_normal((n, M))
    choices_n = np.argmax(log_alphas[None, :] + gaussian, axis=1)
    counts_n = np.bincount(choices_n, minlength=M).astype(float)
    stat_n = tools.quantum.chi2_test(counts_n, alphas, n)
    results.append(tools.bld.TestResult("gaussian_fails_born", not stat_n.passes))

    # Uniform (wrong): bounded support, no tail structure
    uniform = rng.uniform(-2, 2, size=(n, M))
    choices_u = np.argmax(log_alphas[None, :] + uniform, axis=1)
    counts_u = np.bincount(choices_u, minlength=M).astype(float)
    stat_u = tools.quantum.chi2_test(counts_u, alphas, n)
    results.append(tools.bld.TestResult("uniform_fails_born", not stat_u.passes))

    # Laplace (wrong): different tail decay rate
    laplace = rng.laplace(0, 1, size=(n, M))
    choices_l = np.argmax(log_alphas[None, :] + laplace, axis=1)
    counts_l = np.bincount(choices_l, minlength=M).astype(float)
    stat_l = tools.quantum.chi2_test(counts_l, alphas, n)
    results.append(tools.bld.TestResult("laplace_fails_born", not stat_l.passes))

    assert_all_pass(results)


def test_non_reciprocal_selection_fails(rng: np.random.Generator) -> None:
    """The selection rule uses α/overlap¹.  Power p≠1 must break Born.

    The 1/overlap (p=1) power comes from the exponential distribution of
    Haar-random overlaps.  Using α/overlap^p for p≠1 changes the effective
    noise distribution and breaks the Gumbel max trick equivalence.

    If α/overlap^p worked for any p, the specific reciprocal relationship
    (p=1) wouldn't be structurally determined by the Haar measure.
    """
    M = 3
    N_obs = 64
    n = 100000
    alphas = np.array([0.5, 0.3, 0.2])
    pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
    P = np.array(pointers.states)
    observers = tools.bld.haar_random_states(N_obs, n, rng)
    ovlps = tools.quantum.overlaps_batch(P, observers)
    safe = np.maximum(ovlps, tools.quantum.SAFE_FLOOR)

    results: list[tools.bld.TestResult] = []

    # p=1 (correct): should recover Born
    choices_1 = np.argmax(alphas[:, None] / safe, axis=0)
    counts_1 = np.bincount(choices_1, minlength=M).astype(float)
    stat_1 = tools.quantum.chi2_test(counts_1, alphas, n)
    results.append(tools.bld.TestResult("p=1_recovers_born", stat_1.passes))

    # p=0.5 (wrong): sub-reciprocal, more overlap influence
    choices_05 = np.argmax(alphas[:, None] / safe ** 0.5, axis=0)
    counts_05 = np.bincount(choices_05, minlength=M).astype(float)
    stat_05 = tools.quantum.chi2_test(counts_05, alphas, n)
    results.append(tools.bld.TestResult("p=0.5_fails_born", not stat_05.passes))

    # p=2 (wrong): super-reciprocal, less overlap influence
    choices_2 = np.argmax(alphas[:, None] / safe ** 2, axis=0)
    counts_2 = np.bincount(choices_2, minlength=M).astype(float)
    stat_2 = tools.quantum.chi2_test(counts_2, alphas, n)
    results.append(tools.bld.TestResult("p=2_fails_born", not stat_2.passes))

    assert_all_pass(results)
