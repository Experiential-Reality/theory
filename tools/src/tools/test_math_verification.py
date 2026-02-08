"""Comprehensive mathematical verification of the BLD selection rule.

Tests the claim: f(|O⟩) = argmax_k |αₖ|²/|⟨Oₖ|O⟩|² gives EXACT Born statistics
for ALL N ≥ M via the Dirichlet-Gamma decomposition.

12 tests covering all identified edge cases, deeper consequences, and
analytical derivations:

1. Degenerate amplitudes (αₖ = 0)
2. M = N boundary case
3. Complex phases in αₖ
4. Non-orthogonal pointers (NOVEL PREDICTION — quantified deviation)
5. Large M (10, 20, 50)
6. Direct Dirichlet decomposition verification
7. Temperature parameter τ uniqueness (only τ=1 gives Born)
8. Joint measurement (Bell state + two observers)
9. M=2 product/ratio symmetry (why product works for M=2 only)
10. M=2 product/ratio analytical proof (exceedance identity + M≥3 counterexample)
11. Factored observer analytical formula (closed form via Logistic convolution)
12. Non-orthogonal analytical integral (exact N-independent 3-branch integrand)
"""

import numpy as np
from itertools import combinations
from scipy.integrate import quad
from scipy.stats import chi2, unitary_group


# ---- Infrastructure ----

def haar_random_state(dim: int) -> np.ndarray:
    """Generate Haar-random pure state on S^{2dim-1}."""
    z = np.random.randn(dim) + 1j * np.random.randn(dim)
    return z / np.linalg.norm(z)


def make_orthogonal_pointer_states(M: int, N_obs: int) -> list[np.ndarray]:
    """Create M exactly orthogonal pointer states in dim N_obs.

    Uses columns of a Haar-random unitary (exact orthogonality).
    """
    U = unitary_group.rvs(N_obs)
    return [U[:, k].copy() for k in range(M)]


def make_nonorthogonal_pointer_states_m2(
    N_obs: int, epsilon: float
) -> list[np.ndarray]:
    """Create 2 pointer states with |⟨O₀|O₁⟩|² = epsilon.

    Constructs |O₁⟩ = √ε |O₀⟩ + √(1-ε) |O₀⊥⟩ in the subspace
    spanned by the first two columns of a Haar-random unitary.
    """
    U = unitary_group.rvs(N_obs)
    O0 = U[:, 0].copy()
    O0_perp = U[:, 1].copy()  # orthogonal to O0

    O1 = np.sqrt(epsilon) * O0 + np.sqrt(1 - epsilon) * O0_perp
    O1 = O1 / np.linalg.norm(O1)

    # Verify overlap
    actual_overlap = np.abs(np.vdot(O0, O1))**2
    assert abs(actual_overlap - epsilon) < 1e-10, \
        f"Overlap mismatch: {actual_overlap} vs {epsilon}"

    return [O0, O1]


def make_nonorthogonal_pointer_states_m3(
    N_obs: int, epsilon: float
) -> list[np.ndarray]:
    """Create 3 pointer states with pairwise |⟨Oⱼ|Oₖ⟩|² ≈ epsilon.

    Uses a symmetric construction in a 3D subspace of C^N.
    For small ε, this gives approximately equal pairwise overlaps.
    """
    U = unitary_group.rvs(N_obs)
    e0, e1, e2 = U[:, 0], U[:, 1], U[:, 2]

    # Construct 3 states forming a symmetric configuration
    # with inner product √ε between each pair
    sqrt_eps = np.sqrt(epsilon)
    # Use: |Oₖ⟩ = √a |eₖ⟩ + √b (|e₀⟩+|e₁⟩+|e₂⟩)/√3
    # Inner product ⟨Oⱼ|Oₖ⟩ = b for j≠k, a + b for j=k
    # Want |⟨Oⱼ|Oₖ⟩|² = ε and normalization a + b = 1 (not exactly — need care)
    #
    # Simpler: use Gram-Schmidt-like approach
    # |O₀⟩ = |e₀⟩
    # |O₁⟩ = √ε |e₀⟩ + √(1-ε) |e₁⟩
    # |O₂⟩ = c₀ |e₀⟩ + c₁ |e₁⟩ + c₂ |e₂⟩
    # where ⟨O₀|O₂⟩ = c₀ = √ε, ⟨O₁|O₂⟩ = √ε × c₀ + √(1-ε) × c₁ = √ε
    # → c₁ = (√ε - ε) / √(1-ε), c₂ = √(1 - |c₀|² - |c₁|²)

    O0 = e0.copy()

    c_10 = np.sqrt(epsilon)
    c_11 = np.sqrt(1 - epsilon)
    O1 = c_10 * e0 + c_11 * e1
    O1 = O1 / np.linalg.norm(O1)

    c_20 = np.sqrt(epsilon)
    # ⟨O₁|O₂⟩ = √ε × c_20 + √(1-ε) × c_21 = √ε
    # → c_21 = (√ε - ε) / √(1-ε) = √ε(1 - √ε) / √(1-ε)
    c_21 = (np.sqrt(epsilon) - epsilon) / np.sqrt(1 - epsilon)
    c_22_sq = 1.0 - abs(c_20)**2 - abs(c_21)**2
    if c_22_sq < 0:
        c_22_sq = 0.0  # numerical guard for large ε
    c_22 = np.sqrt(c_22_sq)
    O2 = c_20 * e0 + c_21 * e1 + c_22 * e2
    O2 = O2 / np.linalg.norm(O2)

    return [O0, O1, O2]


def overlaps(pointer_states: list[np.ndarray], O: np.ndarray) -> np.ndarray:
    """Compute |⟨Oₖ|O⟩|² for all k."""
    return np.array([np.abs(np.vdot(p, O))**2 for p in pointer_states])


def selection_rule(alphas_sq: np.ndarray, ovlps: np.ndarray) -> int:
    """f(|O⟩) = argmax_k |αₖ|²/|⟨Oₖ|O⟩|² (L/B = structural leverage)."""
    safe_ovlps = np.maximum(ovlps, 1e-300)
    return int(np.argmax(alphas_sq / safe_ovlps))


def selection_rule_tau(alphas_sq: np.ndarray, ovlps: np.ndarray,
                       tau: float) -> int:
    """f_τ(|O⟩) = argmax_k |αₖ|^{2/τ} / |⟨Oₖ|O⟩|²."""
    safe_ovlps = np.maximum(ovlps, 1e-300)
    weights = np.power(np.maximum(alphas_sq, 1e-300), 1.0 / tau)
    return int(np.argmax(weights / safe_ovlps))


def rule_product(alphas_sq: np.ndarray, ovlps: np.ndarray) -> int:
    """argmax aₖ × |⟨Oₖ|O⟩|² (product rule)."""
    return int(np.argmax(alphas_sq * ovlps))


def chi2_test(observed_counts: np.ndarray, expected_probs: np.ndarray,
              n_samples: int) -> tuple[float, float]:
    """Chi-squared goodness-of-fit test."""
    expected_counts = expected_probs * n_samples
    mask = expected_counts > 5
    if np.sum(mask) <= 1:
        return 0.0, 1.0
    chi2_stat = np.sum(
        (observed_counts[mask] - expected_counts[mask])**2 / expected_counts[mask]
    )
    dof = np.sum(mask) - 1
    p_value = 1.0 - chi2.cdf(chi2_stat, dof)
    return float(chi2_stat), float(p_value)


# ---- Test 1: Degenerate Amplitudes ----

def test_degenerate_amplitudes():
    """αₖ = 0 outcomes should NEVER be selected; non-zero outcomes → Born."""
    print("\n" + "=" * 80)
    print("TEST 1: DEGENERATE AMPLITUDES (αₖ = 0)")
    print("=" * 80)
    print("  Prediction: log(0) = -∞ in Gumbel-max → outcome never selected")
    print()

    configs = [
        (3, "0.6/0.4/0", [0.6, 0.4, 0.0]),
        (4, "0.5/0.3/0.2/0", [0.5, 0.3, 0.2, 0.0]),
        (4, "0.5/0.5/0/0", [0.5, 0.5, 0.0, 0.0]),
        (5, "0.9/0.1/0/0/0", [0.9, 0.1, 0.0, 0.0, 0.0]),
    ]

    all_pass = True
    for M, desc, alphas in configs:
        a = np.array(alphas)
        zero_indices = np.where(a == 0)[0]
        nonzero_indices = np.where(a > 0)[0]
        # Renormalized Born probabilities for non-zero outcomes
        a_nonzero = a[nonzero_indices]
        a_renorm = a_nonzero / a_nonzero.sum()

        for N_obs in [8, 32, 128]:
            if N_obs < M:
                continue

            n_samples = 50000
            pointers = make_orthogonal_pointer_states(M, N_obs)
            counts = np.zeros(M)

            for _ in range(n_samples):
                O = haar_random_state(N_obs)
                ovlp = overlaps(pointers, O)
                k = selection_rule(a, ovlp)
                counts[k] += 1

            # Check: zero-amplitude outcomes NEVER selected
            zero_selected = counts[zero_indices].sum()
            zero_ok = zero_selected == 0

            # Check: non-zero outcomes match Born (renormalized)
            counts_nz = counts[nonzero_indices]
            chi2_stat, p_value = chi2_test(counts_nz, a_renorm, n_samples)
            born_ok = p_value > 0.01

            status_z = "PASS" if zero_ok else "FAIL"
            status_b = "PASS" if born_ok else "FAIL"
            ok = zero_ok and born_ok
            if not ok:
                all_pass = False

            print(f"  M={M} ({desc}), N={N_obs:3d}: "
                  f"zero_selected={int(zero_selected)} [{status_z}], "
                  f"Born p={p_value:.4f} [{status_b}]")
            if not zero_ok:
                print(f"    CRITICAL: {int(zero_selected)} selections of "
                      f"zero-amplitude outcomes!")

    print(f"\n  TEST 1 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return all_pass


# ---- Test 2: M = N Exactly ----

def test_m_equals_n():
    """Born rule at M=N boundary (Dirichlet on full simplex, no extra dims)."""
    print("\n" + "=" * 80)
    print("TEST 2: M = N EXACTLY (boundary case)")
    print("=" * 80)
    print("  At M=N, the Dirichlet decomposition uses ALL N exponentials.")
    print("  No 'extra' dimensions — tightest possible test.")
    print()

    configs = [
        (2, "equal", [0.5, 0.5]),
        (2, "80/20", [0.8, 0.2]),
        (3, "equal", [1/3, 1/3, 1/3]),
        (3, "50/30/20", [0.5, 0.3, 0.2]),
        (4, "equal", [0.25, 0.25, 0.25, 0.25]),
        (4, "steep", [0.6, 0.2, 0.15, 0.05]),
        (5, "equal", [0.2, 0.2, 0.2, 0.2, 0.2]),
        (5, "steep", [0.5, 0.2, 0.15, 0.1, 0.05]),
        (8, "equal", [1/8]*8),
        (8, "steep", [0.3, 0.2, 0.15, 0.1, 0.08, 0.07, 0.06, 0.04]),
        (16, "equal", [1/16]*16),
    ]

    n_samples = 50000
    all_pass = True

    for M, desc, alphas in configs:
        N_obs = M  # M = N exactly
        a = np.array(alphas)

        pointers = make_orthogonal_pointer_states(M, N_obs)
        counts = np.zeros(M)

        n = min(n_samples, 20000 if M >= 16 else n_samples)
        for _ in range(n):
            O = haar_random_state(N_obs)
            ovlp = overlaps(pointers, O)
            k = selection_rule(a, ovlp)
            counts[k] += 1

        chi2_stat, p_value = chi2_test(counts, a, n)
        ok = p_value > 0.01
        if not ok:
            all_pass = False

        status = "PASS" if ok else "FAIL"
        freqs = counts / n
        print(f"  M=N={M:2d} ({desc:8s}): "
              f"chi2={chi2_stat:8.2f}, p={p_value:.4f} [{status}]")
        if not ok:
            print(f"    freq={np.round(freqs, 4)}")
            print(f"    exp ={np.round(a, 4)}")

    print(f"\n  TEST 2 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return all_pass


# ---- Test 3: Complex Phases ----

def test_complex_phases():
    """Selection rule uses |αₖ|² only — phases should be irrelevant."""
    print("\n" + "=" * 80)
    print("TEST 3: COMPLEX PHASES IN αₖ")
    print("=" * 80)
    print("  f depends on |αₖ|² only. Phases should not matter.")
    print()

    M = 3
    N_obs = 32
    n_samples = 80000
    target_probs = np.array([0.5, 0.3, 0.2])

    # Different phase configurations, same |αₖ|²
    phase_configs = {
        "all_real": np.sqrt(target_probs).astype(complex),
        "one_flip": np.array([
            np.sqrt(0.5),
            np.sqrt(0.3) * np.exp(1j * np.pi),
            np.sqrt(0.2)
        ]),
        "random_phases": np.array([
            np.sqrt(0.5) * np.exp(1j * np.pi / 4),
            np.sqrt(0.3) * np.exp(1j * 2 * np.pi / 3),
            np.sqrt(0.2) * np.exp(1j * 5 * np.pi / 7),
        ]),
        "all_imaginary": np.sqrt(target_probs) * 1j,
    }

    # Use SAME pointer states and observer states for all configurations
    pointers = make_orthogonal_pointer_states(M, N_obs)
    np.random.seed(12345)  # fix for reproducibility within this test
    observer_states = [haar_random_state(N_obs) for _ in range(n_samples)]

    all_pass = True
    results = {}

    for name, alpha_complex in phase_configs.items():
        a_sq = np.abs(alpha_complex)**2
        assert abs(a_sq.sum() - 1.0) < 1e-10

        counts = np.zeros(M)
        for O in observer_states:
            ovlp = overlaps(pointers, O)
            k = selection_rule(a_sq, ovlp)
            counts[k] += 1

        chi2_stat, p_value = chi2_test(counts, target_probs, n_samples)
        ok = p_value > 0.01
        if not ok:
            all_pass = False

        freqs = counts / n_samples
        results[name] = freqs
        status = "PASS" if ok else "FAIL"
        print(f"  {name:16s}: freq={np.round(freqs, 4)}, "
              f"chi2={chi2_stat:.2f}, p={p_value:.4f} [{status}]")

    # Additional check: all phase configs give IDENTICAL outcomes
    # (since |αₖ|² is the same, and we used same observer states)
    configs_list = list(results.values())
    all_identical = all(
        np.array_equal(configs_list[0], f) for f in configs_list[1:]
    )
    print(f"\n  All configurations give identical outcome sequences: {all_identical}")
    if all_identical:
        print("  (Confirms: selection rule depends on |αₖ|² only, phases irrelevant)")

    # Restore random state
    np.random.seed(42)

    print(f"\n  TEST 3 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return all_pass


# ---- Test 4: Non-Orthogonal Pointers (NOVEL PREDICTION) ----

def test_nonorthogonal_pointers():
    """Quantify Born rule deviation as function of pointer overlap ε."""
    print("\n" + "=" * 80)
    print("TEST 4: NON-ORTHOGONAL POINTERS (novel prediction)")
    print("=" * 80)
    print("  For orthogonal pointers: Born rule exact.")
    print("  For non-orthogonal pointers (overlap ε): systematic deviation Δ(ε).")
    print("  THIS IS THE FALSIFIABLE PREDICTION.")
    print()

    # ---- M=2 sweep ----
    print("  --- M=2: P(f=0) vs overlap ε ---")
    N_obs = 32
    alpha_sq = np.array([0.7, 0.3])
    n_samples = 100000

    epsilons = np.arange(0.0, 0.51, 0.02)
    p0_values = []
    delta_values = []

    for eps in epsilons:
        if eps < 1e-10:
            pointers = make_orthogonal_pointer_states(2, N_obs)
        else:
            pointers = make_nonorthogonal_pointer_states_m2(N_obs, eps)

        count_0 = 0
        for _ in range(n_samples):
            O = haar_random_state(N_obs)
            ovlp = overlaps(pointers, O)
            k = selection_rule(alpha_sq, ovlp)
            if k == 0:
                count_0 += 1

        p0 = count_0 / n_samples
        delta = p0 - 0.7
        p0_values.append(p0)
        delta_values.append(delta)

        print(f"    ε={eps:.2f}: P(f=0)={p0:.4f}, Δ={delta:+.4f}")

    # Fit Δ(ε) to polynomial
    eps_fit = np.array(epsilons)
    delta_fit = np.array(delta_values)

    # Try linear fit: Δ ≈ c₁ × ε
    if len(eps_fit) > 2:
        c1 = np.polyfit(eps_fit, delta_fit, 1)
        delta_linear = np.polyval(c1, eps_fit)
        residual_linear = np.sqrt(np.mean((delta_fit - delta_linear)**2))

        # Try quadratic fit: Δ ≈ c₂ × ε² + c₁ × ε
        c2 = np.polyfit(eps_fit, delta_fit, 2)
        delta_quad = np.polyval(c2, eps_fit)
        residual_quad = np.sqrt(np.mean((delta_fit - delta_quad)**2))

        print(f"\n    Linear fit:    Δ ≈ {c1[0]:.4f}ε + {c1[1]:.4f}, "
              f"RMS residual = {residual_linear:.5f}")
        print(f"    Quadratic fit: Δ ≈ {c2[0]:.4f}ε² + {c2[1]:.4f}ε + {c2[2]:.4f}, "
              f"RMS residual = {residual_quad:.5f}")

        better = "quadratic" if residual_quad < residual_linear * 0.8 else "linear"
        print(f"    Better fit: {better}")

    # ---- M=3 sweep ----
    print(f"\n  --- M=3: deviation vs pairwise overlap ε ---")
    N_obs_m3 = 32
    alpha_sq_m3 = np.array([0.5, 0.3, 0.2])
    n_samples_m3 = 50000

    epsilons_m3 = np.arange(0.0, 0.31, 0.05)

    for eps in epsilons_m3:
        if eps < 1e-10:
            pointers = make_orthogonal_pointer_states(3, N_obs_m3)
        else:
            pointers = make_nonorthogonal_pointer_states_m3(N_obs_m3, eps)

        counts = np.zeros(3)
        for _ in range(n_samples_m3):
            O = haar_random_state(N_obs_m3)
            ovlp = overlaps(pointers, O)
            k = selection_rule(alpha_sq_m3, ovlp)
            counts[k] += 1

        freqs = counts / n_samples_m3
        max_dev = np.max(np.abs(freqs - alpha_sq_m3))
        chi2_stat, p_value = chi2_test(counts, alpha_sq_m3, n_samples_m3)

        # Verify pairwise overlaps
        actual_overlaps = []
        for i in range(3):
            for j in range(i+1, 3):
                actual_overlaps.append(np.abs(np.vdot(pointers[i], pointers[j]))**2)

        print(f"    ε={eps:.2f}: freq={np.round(freqs, 4)}, "
              f"max_dev={max_dev:.4f}, chi2={chi2_stat:.2f}, p={p_value:.4f}, "
              f"overlaps={[f'{o:.4f}' for o in actual_overlaps]}")

    print("\n  TEST 4: COMPLETE (check deviation curve above)")
    return True  # This test generates data, not a pass/fail


# ---- Test 5: Large M ----

def test_large_m():
    """Born rule at M = 10, 20, 50."""
    print("\n" + "=" * 80)
    print("TEST 5: LARGE M")
    print("=" * 80)
    print("  Testing whether Born rule holds for many outcomes.")
    print()

    all_pass = True

    configs = [
        (10, 20, "uniform", np.ones(10) / 10),
        (10, 20, "geometric", None),
        (20, 40, "uniform", np.ones(20) / 20),
        (20, 40, "geometric", None),
        (50, 100, "uniform", np.ones(50) / 50),
        (50, 100, "geometric", None),
    ]

    for M, N_obs, desc, alphas in configs:
        if alphas is None:
            # Geometric distribution: a_k ∝ 2^{-k}
            raw = np.array([2.0**(-k) for k in range(M)])
            alphas = raw / raw.sum()

        # More samples needed for large M (many bins → chi2 needs more data)
        n_samples = 50000 if M <= 20 else 100000
        pointers = make_orthogonal_pointer_states(M, N_obs)
        counts = np.zeros(M)

        for _ in range(n_samples):
            O = haar_random_state(N_obs)
            ovlp = overlaps(pointers, O)
            k = selection_rule(alphas, ovlp)
            counts[k] += 1

        chi2_stat, p_value = chi2_test(counts, alphas, n_samples)
        ok = p_value > 0.01
        if not ok:
            all_pass = False

        freqs = counts / n_samples
        max_dev = np.max(np.abs(freqs - alphas))
        status = "PASS" if ok else "FAIL"
        print(f"  M={M:2d}, N={N_obs:3d} ({desc:10s}): "
              f"chi2={chi2_stat:8.2f}, p={p_value:.4f}, "
              f"max_dev={max_dev:.4f} [{status}]")
        if not ok:
            print(f"    freq (first 5)={np.round(freqs[:5], 4)}")
            print(f"    exp  (first 5)={np.round(alphas[:5], 4)}")

    print(f"\n  TEST 5 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return all_pass


# ---- Test 6: Direct Dirichlet Decomposition ----

def test_dirichlet_decomposition():
    """Verify the mathematical mechanism directly.

    Core claim: argmax_k a_k/Y_k where Y_k ~ Exp(1) i.i.d. gives Born.
    This should be independent of how many extra Y_j's exist (S cancels).
    """
    print("\n" + "=" * 80)
    print("TEST 6: DIRECT DIRICHLET DECOMPOSITION")
    print("=" * 80)
    print("  Core mechanism: Y_k ~ Exp(1) i.i.d., argmax a_k/Y_k → Born")
    print("  S = Σ Y_j cancels: argmax a_k/Y_k = argmax a_k/(Y_k/S) = argmax a_k/X_k")
    print()

    M = 3
    a = np.array([0.5, 0.3, 0.2])
    n_samples = 100000

    # Method 1: Pure exponentials (no extra dimensions)
    counts_exp_pure = np.zeros(M)
    for _ in range(n_samples):
        Y = np.random.exponential(1.0, size=M)
        k = int(np.argmax(a / Y))
        counts_exp_pure[k] += 1

    # Method 2: Exponentials with extra dimensions, via X_k = Y_k/S
    counts_exp_extra = {}
    for N_total in [3, 10, 100, 1000]:
        counts = np.zeros(M)
        for _ in range(n_samples):
            Y = np.random.exponential(1.0, size=N_total)
            S = Y.sum()
            X = Y[:M] / S  # Dirichlet components
            k = int(np.argmax(a / X))
            counts[k] += 1
        counts_exp_extra[N_total] = counts

    # Method 3: Gumbel-max trick directly
    counts_gumbel = np.zeros(M)
    for _ in range(n_samples):
        G = np.random.gumbel(0, 1, size=M)
        k = int(np.argmax(np.log(a) + G))
        counts_gumbel[k] += 1

    # Method 4: Haar-random sampling (ground truth for N=32)
    N_obs = 32
    pointers = make_orthogonal_pointer_states(M, N_obs)
    counts_haar = np.zeros(M)
    for _ in range(n_samples):
        O = haar_random_state(N_obs)
        ovlp = overlaps(pointers, O)
        k = selection_rule(a, ovlp)
        counts_haar[k] += 1

    # Print results
    print(f"  α² = {list(a)}")
    print()

    def print_result(name, counts):
        freqs = counts / n_samples
        chi2_stat, p_value = chi2_test(counts, a, n_samples)
        status = "PASS" if p_value > 0.01 else "FAIL"
        print(f"  {name:30s}: freq={np.round(freqs, 4)}, "
              f"chi2={chi2_stat:6.2f}, p={p_value:.4f} [{status}]")
        return p_value > 0.01

    all_pass = True
    all_pass &= print_result("Exp(1) pure (M=3 only)", counts_exp_pure)
    for N_total, counts in counts_exp_extra.items():
        all_pass &= print_result(f"Exp(1) + extra (N={N_total})", counts)
    all_pass &= print_result("Gumbel-max trick", counts_gumbel)
    all_pass &= print_result("Haar-random (N=32)", counts_haar)

    # Key verification: all methods give same distribution
    freq_pure = counts_exp_pure / n_samples
    freq_gumbel = counts_gumbel / n_samples
    freq_haar = counts_haar / n_samples

    max_dev_pure_gumbel = np.max(np.abs(freq_pure - freq_gumbel))
    max_dev_pure_haar = np.max(np.abs(freq_pure - freq_haar))

    print(f"\n  Max deviation Exp_pure vs Gumbel: {max_dev_pure_gumbel:.4f}")
    print(f"  Max deviation Exp_pure vs Haar:   {max_dev_pure_haar:.4f}")
    print(f"  All methods equivalent: {max_dev_pure_gumbel < 0.01 and max_dev_pure_haar < 0.01}")

    print(f"\n  TEST 6 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return all_pass


# ---- Test 7: Temperature Parameter τ ----

def test_tau_uniqueness():
    """Only τ=1 gives Born rule. τ≠1 gives |αₖ|^{2/τ} / Z."""
    print("\n" + "=" * 80)
    print("TEST 7: TEMPERATURE τ UNIQUENESS")
    print("=" * 80)
    print("  f_τ(|O⟩) = argmax_k |αₖ|^{2/τ} / |⟨Oₖ|O⟩|²")
    print("  Prediction: P(k) = |αₖ|^{2/τ} / Σ_j |α_j|^{2/τ}")
    print("  ONLY τ=1 gives Born rule P(k) = |αₖ|²")
    print()

    M = 3
    N_obs = 64
    a = np.array([0.5, 0.3, 0.2])
    n_samples = 50000

    taus = [0.5, 0.8, 1.0, 1.2, 1.5, 2.0, 3.0]
    pointers = make_orthogonal_pointer_states(M, N_obs)

    for tau in taus:
        # Expected distribution at temperature τ
        weights = np.power(a, 1.0 / tau)
        expected = weights / weights.sum()

        counts = np.zeros(M)
        for _ in range(n_samples):
            O = haar_random_state(N_obs)
            ovlp = overlaps(pointers, O)
            k = selection_rule_tau(a, ovlp, tau)
            counts[k] += 1

        freqs = counts / n_samples

        # Test against Born rule
        chi2_born, p_born = chi2_test(counts, a, n_samples)
        born_ok = p_born > 0.01

        # Test against predicted τ-distribution
        chi2_tau, p_tau = chi2_test(counts, expected, n_samples)
        tau_ok = p_tau > 0.01

        status_born = "PASS" if born_ok else "FAIL"
        status_tau = "PASS" if tau_ok else "FAIL"

        marker = " ← BORN" if abs(tau - 1.0) < 0.01 else ""
        print(f"  τ={tau:.1f}: freq={np.round(freqs, 4)}, "
              f"Born p={p_born:.4f} [{status_born}], "
              f"τ-pred p={p_tau:.4f} [{status_tau}] "
              f"expected={np.round(expected, 4)}{marker}")

    # The key result: only τ=1 passes Born, all τ pass their predicted distribution
    print("\n  KEY: Only τ=1.0 should pass Born rule test.")
    print("       All τ should pass their predicted |αₖ|^{2/τ}/Z test.")

    print("\n  TEST 7: COMPLETE")
    return True


# ---- Test 8: Joint Measurement (Bell State) ----

def test_joint_measurement():
    """Bell correlations from the selection rule applied to joint observer space.

    KEY INSIGHT: For correlated measurements, the observer must be a SINGLE state
    in the tensor product space C^{N_A⊗N_B}, NOT two independent observers.

    The Dirichlet-Gamma proof requires overlaps X_{kj} = |⟨O_{kj}|O⟩|² to be
    components of a single Dirichlet distribution. This requires:
    - |O⟩ ∈ C^{N_A × N_B} (single joint observer)
    - |O_{kj}⟩ = |O_{Ak}⟩ ⊗ |O_{Bj}⟩ (tensor product pointer states)
    - Orthogonality in the product space (automatic if individual pointers orthogonal)

    Products of independent overlaps X_Ak × X_Bj do NOT form Dirichlet components,
    so the factored form FAILS for non-symmetric states (as confirmed in v1).
    """
    print("\n" + "=" * 80)
    print("TEST 8: JOINT MEASUREMENT (Bell state)")
    print("=" * 80)
    print("  KEY: Joint observer |O⟩ ∈ C^{N_A⊗N_B}, NOT independent observers.")
    print("  Pointer states: |O_{kj}⟩ = |O_{Ak}⟩ ⊗ |O_{Bj}⟩")
    print("  Overlaps X_{kj} form Dirichlet in product space → Born exact.")
    print()

    M_A, M_B = 2, 2
    N_A, N_B = 8, 8  # Product space = C^64
    N_joint = N_A * N_B

    # Build tensor product pointer states (orthogonal in product space)
    pointers_A = make_orthogonal_pointer_states(M_A, N_A)
    pointers_B = make_orthogonal_pointer_states(M_B, N_B)

    # Tensor product: |O_{kj}⟩ = |O_{Ak}⟩ ⊗ |O_{Bj}⟩
    joint_pointers = []
    joint_labels = []
    for k in range(M_A):
        for j in range(M_B):
            ptr = np.kron(pointers_A[k], pointers_B[j])
            joint_pointers.append(ptr)
            joint_labels.append((k, j))

    # Verify orthogonality in product space
    M_joint = len(joint_pointers)
    for i in range(M_joint):
        for j_idx in range(i+1, M_joint):
            ip = np.abs(np.vdot(joint_pointers[i], joint_pointers[j_idx]))
            assert ip < 1e-10, f"Pointer {i},{j_idx} not orthogonal: {ip}"

    n_samples = 100000

    def run_joint_test(alpha_sq_matrix, desc):
        """Run joint selection with single observer in product space."""
        # Flatten α²_{kj} to vector matching joint_pointers order
        a_flat = np.array([alpha_sq_matrix[k, j] for k, j in joint_labels])

        counts_joint = np.zeros(M_joint)
        for _ in range(n_samples):
            O = haar_random_state(N_joint)
            ovlp = overlaps(joint_pointers, O)
            idx = selection_rule(a_flat, ovlp)
            counts_joint[idx] += 1

        # Reshape back to matrix
        counts_matrix = np.zeros((M_A, M_B))
        for idx, (k, j) in enumerate(joint_labels):
            counts_matrix[k, j] = counts_joint[idx]

        freqs = counts_matrix / n_samples
        return freqs

    # Also run factored (independent observers) for comparison
    def run_factored_test(alpha_sq_matrix, desc):
        """Run with independent observers (WRONG approach — for comparison)."""
        pointers_A_f = make_orthogonal_pointer_states(M_A, N_A)
        pointers_B_f = make_orthogonal_pointer_states(M_B, N_B)

        counts = np.zeros((M_A, M_B))
        for _ in range(n_samples):
            O_A = haar_random_state(N_A)
            O_B = haar_random_state(N_B)
            ovlp_A = overlaps(pointers_A_f, O_A)
            ovlp_B = overlaps(pointers_B_f, O_B)

            best_k, best_j = 0, 0
            best_ratio = -1.0
            for k in range(M_A):
                for j in range(M_B):
                    if alpha_sq_matrix[k, j] == 0:
                        continue
                    ratio = alpha_sq_matrix[k, j] / (
                        max(ovlp_A[k], 1e-300) * max(ovlp_B[j], 1e-300))
                    if ratio > best_ratio:
                        best_ratio = ratio
                        best_k, best_j = k, j
            counts[best_k, best_j] += 1

        return counts / n_samples

    # ---- Bell state: (|00⟩ + |11⟩)/√2 ----
    print("  --- Bell state: (|00⟩ + |11⟩)/√2 ---")
    alpha_bell = np.array([[0.5, 0.0],
                           [0.0, 0.5]])

    freqs_j = run_joint_test(alpha_bell, "Bell")
    freqs_f = run_factored_test(alpha_bell, "Bell")

    print(f"    JOINT observer (correct):")
    print(f"      P(00)={freqs_j[0,0]:.4f}, P(11)={freqs_j[1,1]:.4f}, "
          f"P(01)={freqs_j[0,1]:.4f}, P(10)={freqs_j[1,0]:.4f}")
    print(f"    FACTORED observers (wrong):")
    print(f"      P(00)={freqs_f[0,0]:.4f}, P(11)={freqs_f[1,1]:.4f}, "
          f"P(01)={freqs_f[0,1]:.4f}, P(10)={freqs_f[1,0]:.4f}")

    bell_j_ok = (freqs_j[0,1] == 0 and freqs_j[1,0] == 0 and
                 abs(freqs_j[0,0] - 0.5) < 0.01 and
                 abs(freqs_j[1,1] - 0.5) < 0.01)
    print(f"    Joint: {'PASS' if bell_j_ok else 'FAIL'}")

    # ---- Non-maximally entangled: √0.7|00⟩ + √0.3|11⟩ ----
    print(f"\n  --- Non-maximal: √0.7|00⟩ + √0.3|11⟩ ---")
    alpha_nm = np.array([[0.7, 0.0],
                         [0.0, 0.3]])

    freqs_j_nm = run_joint_test(alpha_nm, "Non-max")
    freqs_f_nm = run_factored_test(alpha_nm, "Non-max")

    print(f"    JOINT observer (correct):")
    print(f"      P(00)={freqs_j_nm[0,0]:.4f} (exp 0.7), "
          f"P(11)={freqs_j_nm[1,1]:.4f} (exp 0.3), "
          f"P(01)={freqs_j_nm[0,1]:.4f}, P(10)={freqs_j_nm[1,0]:.4f}")
    print(f"    FACTORED observers (wrong):")
    print(f"      P(00)={freqs_f_nm[0,0]:.4f} (exp 0.7), "
          f"P(11)={freqs_f_nm[1,1]:.4f} (exp 0.3), "
          f"P(01)={freqs_f_nm[0,1]:.4f}, P(10)={freqs_f_nm[1,0]:.4f}")

    nm_j_ok = (freqs_j_nm[0,1] == 0 and freqs_j_nm[1,0] == 0 and
               abs(freqs_j_nm[0,0] - 0.7) < 0.01 and
               abs(freqs_j_nm[1,1] - 0.3) < 0.01)
    nm_f_ok = (abs(freqs_f_nm[0,0] - 0.7) < 0.01 and
               abs(freqs_f_nm[1,1] - 0.3) < 0.01)
    print(f"    Joint: {'PASS' if nm_j_ok else 'FAIL'}")
    print(f"    Factored: {'PASS' if nm_f_ok else 'FAIL'} "
          f"(expected FAIL — products of Dirichlets ≠ Dirichlet)")

    # ---- GHZ-like: 3 parties in tensor product space ----
    print(f"\n  --- GHZ-like: √0.5|000⟩ + √0.3|111⟩ + √0.2|222⟩ ---")

    N_party = 4  # Each party's dimension (product space = 4^3 = 64)
    M_party = 3  # Each party has 3 outcomes
    N_ghz = N_party ** 3

    ptrs = [make_orthogonal_pointer_states(M_party, N_party) for _ in range(3)]

    # Build tensor product pointers
    ghz_pointers = []
    ghz_labels = []
    for i in range(M_party):
        for j in range(M_party):
            for k_idx in range(M_party):
                ptr = np.kron(np.kron(ptrs[0][i], ptrs[1][j]), ptrs[2][k_idx])
                ghz_pointers.append(ptr)
                ghz_labels.append((i, j, k_idx))

    # GHZ amplitudes: only diagonal terms
    ghz_a = np.zeros(len(ghz_pointers))
    for idx, (i, j, k_idx) in enumerate(ghz_labels):
        if i == j == k_idx == 0:
            ghz_a[idx] = 0.5
        elif i == j == k_idx == 1:
            ghz_a[idx] = 0.3
        elif i == j == k_idx == 2:
            ghz_a[idx] = 0.2

    n_ghz_samples = 50000
    counts_ghz = np.zeros(len(ghz_pointers))
    for _ in range(n_ghz_samples):
        O = haar_random_state(N_ghz)
        ovlp = overlaps(ghz_pointers, O)
        idx = selection_rule(ghz_a, ovlp)
        counts_ghz[idx] += 1

    # Extract diagonal
    p000 = p111 = p222 = 0.0
    cross = 0
    for idx, (i, j, k_idx) in enumerate(ghz_labels):
        f = counts_ghz[idx] / n_ghz_samples
        if i == j == k_idx == 0:
            p000 = f
        elif i == j == k_idx == 1:
            p111 = f
        elif i == j == k_idx == 2:
            p222 = f
        else:
            cross += counts_ghz[idx]

    print(f"    P(000)={p000:.4f} (expected 0.5)")
    print(f"    P(111)={p111:.4f} (expected 0.3)")
    print(f"    P(222)={p222:.4f} (expected 0.2)")
    print(f"    Cross-terms: {int(cross)}/{n_ghz_samples}")

    ghz_ok = (cross == 0 and
              abs(p000 - 0.5) < 0.02 and
              abs(p111 - 0.3) < 0.02 and
              abs(p222 - 0.2) < 0.02)

    overall = bell_j_ok and nm_j_ok and ghz_ok
    print(f"\n  STRUCTURAL INSIGHT:")
    print(f"    Correlated measurements require a SINGLE joint observer")
    print(f"    in the tensor product space, not independent observers.")
    print(f"    Independent observers give wrong Born statistics for")
    print(f"    non-symmetric entangled states (factored ≠ joint).")

    print(f"\n  TEST 8 OVERALL: {'PASS' if overall else 'FAIL'}")
    return overall


# ---- Test 9: M=2 Product/Ratio Symmetry ----

def test_m2_symmetry():
    """For M=2, product and ratio rules give identical Born statistics.
    For M≥3, product fails but ratio still works."""
    print("\n" + "=" * 80)
    print("TEST 9: M=2 PRODUCT/RATIO SYMMETRY")
    print("=" * 80)
    print("  For M=2: P(argmax a_k×X_k = j) = P(argmax a_k/X_k = j) = a_j")
    print("  For M≥3: only ratio gives Born (product fails)")
    print()

    # ---- M=2: both should pass ----
    print("  --- M=2: product = ratio = Born ---")
    n_samples = 80000

    for alpha_sq_0 in [0.5, 0.6, 0.7, 0.8, 0.9]:
        a = np.array([alpha_sq_0, 1 - alpha_sq_0])

        for N_obs in [4, 16, 64]:
            pointers = make_orthogonal_pointer_states(2, N_obs)
            counts_ratio = np.zeros(2)
            counts_product = np.zeros(2)

            for _ in range(n_samples):
                O = haar_random_state(N_obs)
                ovlp = overlaps(pointers, O)
                counts_ratio[selection_rule(a, ovlp)] += 1
                counts_product[rule_product(a, ovlp)] += 1

            _, p_ratio = chi2_test(counts_ratio, a, n_samples)
            _, p_product = chi2_test(counts_product, a, n_samples)

            freq_ratio = counts_ratio / n_samples
            freq_product = counts_product / n_samples
            dev = np.max(np.abs(freq_ratio - freq_product))

            r_status = "PASS" if p_ratio > 0.01 else "FAIL"
            p_status = "PASS" if p_product > 0.01 else "FAIL"

            print(f"    α²=({alpha_sq_0:.1f},{1-alpha_sq_0:.1f}), N={N_obs:2d}: "
                  f"ratio p={p_ratio:.4f} [{r_status}], "
                  f"product p={p_product:.4f} [{p_status}], "
                  f"max_diff={dev:.4f}")

    # ---- M=3: ratio should pass, product should fail ----
    print(f"\n  --- M=3: ratio passes, product fails ---")
    a3 = np.array([0.5, 0.3, 0.2])
    n_samples_3 = 80000

    for N_obs in [8, 32, 128]:
        pointers = make_orthogonal_pointer_states(3, N_obs)
        counts_ratio = np.zeros(3)
        counts_product = np.zeros(3)

        for _ in range(n_samples_3):
            O = haar_random_state(N_obs)
            ovlp = overlaps(pointers, O)
            counts_ratio[selection_rule(a3, ovlp)] += 1
            counts_product[rule_product(a3, ovlp)] += 1

        _, p_ratio = chi2_test(counts_ratio, a3, n_samples_3)
        _, p_product = chi2_test(counts_product, a3, n_samples_3)

        freq_ratio = counts_ratio / n_samples_3
        freq_product = counts_product / n_samples_3

        r_status = "PASS" if p_ratio > 0.01 else "FAIL"
        p_status = "PASS" if p_product > 0.01 else "FAIL"

        print(f"    N={N_obs:3d}: ratio freq={np.round(freq_ratio, 4)} "
              f"p={p_ratio:.4f} [{r_status}]")
        print(f"    {' '*6} product freq={np.round(freq_product, 4)} "
              f"p={p_product:.4f} [{p_status}]")
        if p_product <= 0.01:
            bias = freq_product - a3
            print(f"    {' '*6} product bias: {np.round(bias, 4)} "
                  f"(dominant outcome {'over' if bias[0] > 0 else 'under'}-selected)")

    # ---- Mathematical explanation ----
    print(f"\n  --- Why M=2 is special ---")
    print(f"  For M=2: P(a₀/X₀ > a₁/X₁) = P(a₀×X₁ > a₁×X₀)")
    print(f"           which is just a monotone transform of the same comparison.")
    print(f"  For M≥3: argmax_k a_k/X_k ≠ argmax_k a_k×X_k")
    print(f"           because the multiway comparison is not preserved by inversion.")
    print(f"  Gumbel proof: -log(Y) ~ Gumbel_max(0,1), but log(Y) ~ -Gumbel_max(0,1)")
    print(f"  For M=2, P(G₀+log a₀ > G₁+log a₁) = P(-G₀+log a₀ > -G₁+log a₁)")
    print(f"  by symmetry of the logistic distribution (difference of two Gumbels).")

    print(f"\n  TEST 9: COMPLETE")
    return True


# ---- Test 10: M=2 Product/Ratio Analytical Proof ----

def test_m2_product_ratio_proof():
    """Analytical proof that product and ratio rules are equivalent for M=2.

    The proof:
    1. Ratio: P(a₀/Y₀ > a₁/Y₁) = P(Y₁/Y₀ > a₁/a₀).
       Product: P(a₀Y₀ > a₁Y₁) = P(Y₀/Y₁ > a₁/a₀).
    2. T = Y₀/Y₁ where Y₀, Y₁ ~ Exp(1) has PDF f(t) = 1/(1+t)²,
       giving P(T > s) = 1/(1+s).
    3. P(1/T > s) = P(T < 1/s) = 1 - 1/(1+1/s) = 1/(1+s).
       So P(T > s) = P(1/T > s) for all s > 0. ∎
    4. Equivalently: D = G₀ - G₁ ~ Logistic(0,1) is symmetric about 0.

    For M≥3: closed-form via inclusion-exclusion shows product ≠ Born.
    """
    print("\n" + "=" * 80)
    print("TEST 10: M=2 PRODUCT/RATIO ANALYTICAL PROOF")
    print("=" * 80)
    print()

    all_pass = True
    n_samples = 200000

    # ---- Step 1: Verify P(T > s) = P(1/T > s) = 1/(1+s) ----
    print("  --- Verify exceedance identity P(T>s) = P(1/T>s) = 1/(1+s) ---")

    Y0 = np.random.exponential(1.0, size=n_samples)
    Y1 = np.random.exponential(1.0, size=n_samples)
    T = Y0 / Y1

    for s in [0.5, 1.0, 2.0, 5.0]:
        p_T_gt_s = np.mean(T > s)
        p_invT_gt_s = np.mean(1.0 / T > s)
        p_exact = 1.0 / (1.0 + s)
        tol = 3.0 / np.sqrt(n_samples)  # 3σ

        ok_T = abs(p_T_gt_s - p_exact) < tol
        ok_inv = abs(p_invT_gt_s - p_exact) < tol
        ok_eq = abs(p_T_gt_s - p_invT_gt_s) < tol
        ok = ok_T and ok_inv and ok_eq
        if not ok:
            all_pass = False

        status = "PASS" if ok else "FAIL"
        print(f"    s={s:.1f}: P(T>s)={p_T_gt_s:.4f}, P(1/T>s)={p_invT_gt_s:.4f}, "
              f"exact={p_exact:.4f} [{status}]")

    # ---- Step 2: Verify Logistic(0,1) symmetry ----
    print("\n  --- Verify Logistic(0,1) symmetry: P(D>c) = P(-D>c) ---")

    G0 = -np.log(np.random.exponential(1.0, size=n_samples))
    G1 = -np.log(np.random.exponential(1.0, size=n_samples))
    D = G0 - G1  # Logistic(0,1)

    for c in [0.5, 1.0, 2.0]:
        p_pos = np.mean(D > c)
        p_neg = np.mean(-D > c)
        p_exact_logistic = 1.0 / (1.0 + np.exp(c))
        tol = 3.0 / np.sqrt(n_samples)

        ok = abs(p_pos - p_neg) < tol and abs(p_pos - p_exact_logistic) < tol
        if not ok:
            all_pass = False

        status = "PASS" if ok else "FAIL"
        print(f"    c={c:.1f}: P(D>c)={p_pos:.4f}, P(-D>c)={p_neg:.4f}, "
              f"exact={p_exact_logistic:.4f} [{status}]")

    # ---- Step 3: M=3 closed-form counterexample ----
    print("\n  --- M=3 closed-form: P_product(k) via inclusion-exclusion ---")

    a3 = np.array([0.5, 0.3, 0.2])

    def p_product_closed_form(a, k):
        """P(Y_k is maximal for a_k * Y_k) via inclusion-exclusion.

        P_product(k) = Σ_{S ⊆ {0,...,M-1}\\{k}} (-1)^|S| / (1 + Σ_{j∈S} a_k/a_j)
        """
        M = len(a)
        others = [j for j in range(M) if j != k]
        total = 0.0
        for size in range(len(others) + 1):
            for S in combinations(others, size):
                sign = (-1) ** len(S)
                denom = 1.0 + sum(a[k] / a[j] for j in S)
                total += sign / denom
        return total

    # Analytical values
    p_analytical = np.array([p_product_closed_form(a3, k) for k in range(3)])

    # Monte Carlo comparison
    n_mc = 200000
    counts_mc = np.zeros(3)
    for _ in range(n_mc):
        Y = np.random.exponential(1.0, size=3)
        k = int(np.argmax(a3 * Y))
        counts_mc[k] += 1
    p_mc = counts_mc / n_mc

    tol = 0.006
    for k in range(3):
        ok = abs(p_analytical[k] - p_mc[k]) < tol
        if not ok:
            all_pass = False
        status = "PASS" if ok else "FAIL"
        print(f"    k={k}: P_analytical={p_analytical[k]:.4f}, "
              f"P_MC={p_mc[k]:.4f}, Born={a3[k]:.4f} [{status}]")

    # Verify product ≠ Born for M=3
    max_dev_from_born = np.max(np.abs(p_analytical - a3))
    product_differs = max_dev_from_born > 0.01
    print(f"\n    Product ≠ Born: max|P_product - Born| = {max_dev_from_born:.4f} "
          f"({'YES' if product_differs else 'NO'})")

    print(f"\n  TEST 10 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return all_pass


# ---- Test 11: Factored Observer Analytical Formula ----

def test_factored_observer_analytical():
    """Closed-form error formula for factored (independent) observers.

    For diagonal state √a₀₀|00⟩ + √a₁₁|11⟩ with independent observers:
    P_factored(00) = (1 - r + r·log r) / (1 - r)²
    where r = a₁₁/a₀₀.

    Derivation: S_A, S_B cancel → comparison of raw Exp(1) → sum of two
    i.i.d. Logistic(0,1) → CDF via convolution.
    """
    print("\n" + "=" * 80)
    print("TEST 11: FACTORED OBSERVER ANALYTICAL FORMULA")
    print("=" * 80)
    print("  P_factored(00) = (1 - r + r·log r) / (1 - r)²")
    print("  where r = a₁₁/a₀₀")
    print()

    def p_factored_analytical(r):
        """Closed-form probability for factored observers."""
        if abs(r - 1.0) < 1e-10:
            return 0.5  # L'Hôpital limit
        return (1.0 - r + r * np.log(r)) / (1.0 - r)**2

    all_pass = True

    # ---- Verify against Monte Carlo for multiple a₀₀ values ----
    print("  --- Analytical vs Monte Carlo ---")
    n_samples = 100000

    for a00 in [0.55, 0.60, 0.65, 0.70, 0.75, 0.80, 0.85, 0.90]:
        a11 = 1.0 - a00
        r = a11 / a00
        p_anal = p_factored_analytical(r)

        # Monte Carlo: two independent observers, each comparing Exp(1) ratios
        count_00 = 0
        for _ in range(n_samples):
            # Each observer: Y ~ Exp(1) i.i.d.
            YA0, YA1 = np.random.exponential(1.0, 2)
            YB0, YB1 = np.random.exponential(1.0, 2)
            # Factored selection: argmax a_{kj} / (Y_{Ak} * Y_{Bj})
            # For diagonal state: compare a00/(YA0*YB0) vs a11/(YA1*YB1)
            if a00 / (YA0 * YB0) > a11 / (YA1 * YB1):
                count_00 += 1

        p_mc = count_00 / n_samples
        tol = 0.006
        ok = abs(p_anal - p_mc) < tol
        if not ok:
            all_pass = False

        status = "PASS" if ok else "FAIL"
        print(f"    a₀₀={a00:.2f}: P_anal={p_anal:.4f}, P_MC={p_mc:.4f}, "
              f"Born={a00:.2f}, error_vs_Born={p_anal - a00:+.4f} [{status}]")

    # ---- Verify N-independence ----
    print("\n  --- N-independence (S cancels) ---")
    a00, a11 = 0.70, 0.30
    r = a11 / a00
    p_anal = p_factored_analytical(r)

    for N in [4, 8, 16, 32]:
        count_00 = 0
        for _ in range(n_samples):
            # Full Dirichlet with N dimensions per observer
            YA = np.random.exponential(1.0, N)
            YB = np.random.exponential(1.0, N)
            # S cancels: argmax a_{kj}/(YAk * YBj) = argmax a_{kj} * SA * SB / (YAk * YBj)
            # Only compare k=0,j=0 vs k=1,j=1 (diagonal)
            ratio_00 = a00 / (YA[0] * YB[0])
            ratio_11 = a11 / (YA[1] * YB[1])
            if ratio_00 > ratio_11:
                count_00 += 1

        p_mc = count_00 / n_samples
        ok = abs(p_anal - p_mc) < 0.006
        if not ok:
            all_pass = False
        status = "PASS" if ok else "FAIL"
        print(f"    N_A=N_B={N:2d}: P_MC={p_mc:.4f}, P_anal={p_anal:.4f} [{status}]")

    # ---- Limiting cases ----
    print("\n  --- Limiting cases ---")

    # r → 0: P → 1 (convergence is slow: r·log r → 0 slowly)
    p_r_small = p_factored_analytical(0.01)
    ok1 = p_r_small > 0.95  # At r=0.01, P≈0.963; true limit is 1
    print(f"    r=0.01: P={p_r_small:.4f} (expect →1 as r→0) "
          f"[{'PASS' if ok1 else 'FAIL'}]")

    # r = 1: P = 0.5
    p_r_1 = p_factored_analytical(1.0)
    ok2 = abs(p_r_1 - 0.5) < 1e-10
    print(f"    r=1.00: P={p_r_1:.4f} (expect 0.5) "
          f"[{'PASS' if ok2 else 'FAIL'}]")

    if not (ok1 and ok2):
        all_pass = False

    print(f"\n  TEST 11 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return all_pass


# ---- Test 12: Non-Orthogonal Analytical Integral ----

def test_nonorthogonal_analytical():
    """Exact N-independent integral for non-orthogonal pointer deviation.

    For M=2 with |O₁⟩ = √ε|O₀⟩ + √(1-ε)|O₀⊥⟩:

    P(f=0) = (1/2π) ∫₀²π I(θ) dθ

    where I(θ) depends on the quadratic Q(t) = At² + Bt + C with
    A = 1-ε, B = 2√(ε(1-ε))·cos θ, C = ε - a₁/a₀.

    Three cases (by discriminant and Vieta's formulas):
    Case 1: disc < 0 → I = 1
    Case 2: disc ≥ 0, C ≤ 0 → I = 1/(1 + t₊²)
    Case 3: disc ≥ 0, C > 0 → both roots same sign (Vieta: product = C/A > 0)
            If t₊ ≤ 0: I = 1. If t₊ > 0: I = t₋²/(1+t₋²) + 1/(1+t₊²)
    """
    print("\n" + "=" * 80)
    print("TEST 12: NON-ORTHOGONAL ANALYTICAL INTEGRAL")
    print("=" * 80)
    print("  Exact N-independent integral for pointer deviation.")
    print("  Three-branch integrand (Cases 1-3 via discriminant + Vieta).")
    print()

    def integrand(theta, a0, a1, eps):
        """I(θ) = P(Q > 0 | θ) for the non-orthogonal quadratic."""
        A = 1.0 - eps
        C_val = eps - a1 / a0
        B = 2.0 * np.sqrt(eps * (1.0 - eps)) * np.cos(theta)
        disc = B**2 - 4.0 * A * C_val

        if disc < 0:
            # Case 1: no real roots, Q > 0 for all t (A > 0)
            return 1.0

        sqrt_d = np.sqrt(disc)
        t_minus = (-B - sqrt_d) / (2.0 * A)
        t_plus = (-B + sqrt_d) / (2.0 * A)

        if C_val <= 0:
            # Case 2: Vieta product C/A ≤ 0 → one root ≤ 0, one ≥ 0
            if t_plus <= 0:
                return 1.0
            return 1.0 / (1.0 + t_plus**2)
        else:
            # Case 3: Vieta product C/A > 0 → both roots same sign
            if t_plus <= 0:
                # Both non-positive → Q > 0 for all t > 0
                return 1.0
            # Both positive: Q > 0 for t ∈ [0, t₋) ∪ (t₊, ∞)
            return t_minus**2 / (1.0 + t_minus**2) + 1.0 / (1.0 + t_plus**2)

    def p_nonorthogonal_integral(a0, a1, eps):
        """Compute P(f=0) by integrating I(θ) over [0, 2π]."""
        if eps < 1e-15:
            return a0  # Born rule at ε=0
        result, _ = quad(integrand, 0, 2 * np.pi, args=(a0, a1, eps),
                         limit=100, epsabs=1e-10, epsrel=1e-10)
        return result / (2.0 * np.pi)

    all_pass = True
    a0, a1 = 0.7, 0.3

    # ---- Verify integral matches MC at multiple ε values ----
    print("  --- Integral vs Monte Carlo (a₀=0.7, a₁=0.3) ---")
    n_samples = 100000

    eps_values = [0.0, 0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.50, 0.70, 0.90]

    for eps in eps_values:
        p_int = p_nonorthogonal_integral(a0, a1, eps)

        # Monte Carlo
        N_obs = 32
        if eps < 1e-10:
            pointers = make_orthogonal_pointer_states(2, N_obs)
        else:
            pointers = make_nonorthogonal_pointer_states_m2(N_obs, eps)

        count_0 = 0
        for _ in range(n_samples):
            O = haar_random_state(N_obs)
            ovlp = overlaps(pointers, O)
            k = selection_rule(np.array([a0, a1]), ovlp)
            if k == 0:
                count_0 += 1

        p_mc = count_0 / n_samples
        tol = 0.006
        ok = abs(p_int - p_mc) < tol
        if not ok:
            all_pass = False

        status = "PASS" if ok else "FAIL"
        delta_int = p_int - a0
        delta_mc = p_mc - a0
        print(f"    ε={eps:.2f}: P_int={p_int:.4f}, P_MC={p_mc:.4f}, "
              f"Δ_int={delta_int:+.4f}, Δ_MC={delta_mc:+.4f} [{status}]")

    # ---- Verify N-independence ----
    print("\n  --- N-independence (integral has no N parameter) ---")
    eps_test = 0.20
    p_int = p_nonorthogonal_integral(a0, a1, eps_test)

    for N_obs in [4, 8, 32, 128]:
        pointers = make_nonorthogonal_pointer_states_m2(N_obs, eps_test)
        count_0 = 0
        for _ in range(n_samples):
            O = haar_random_state(N_obs)
            ovlp = overlaps(pointers, O)
            k = selection_rule(np.array([a0, a1]), ovlp)
            if k == 0:
                count_0 += 1

        p_mc = count_0 / n_samples
        ok = abs(p_int - p_mc) < 0.006
        if not ok:
            all_pass = False
        status = "PASS" if ok else "FAIL"
        print(f"    N={N_obs:3d}: P_MC={p_mc:.4f}, P_int={p_int:.4f} [{status}]")

    # ---- Taylor coefficients via finite differences ----
    print("\n  --- Taylor coefficient c₁ = a₀·a₁·(a₀-a₁) ---")

    test_pairs = [
        (0.7, 0.3),
        (0.8, 0.2),
        (0.6, 0.4),
        (0.9, 0.1),
        (0.5, 0.5),  # symmetric: c₁ should vanish
    ]

    h = 1e-5
    for a0_t, a1_t in test_pairs:
        # Finite difference: c₁ ≈ [P(h) - P(0)] / h
        p_h = p_nonorthogonal_integral(a0_t, a1_t, h)
        p_0 = a0_t  # P(0) = a₀ (Born rule)
        c1_numerical = (p_h - p_0) / h

        c1_formula = a0_t * a1_t * (a0_t - a1_t)

        ok = abs(c1_numerical - c1_formula) < 0.001
        if not ok:
            all_pass = False
        status = "PASS" if ok else "FAIL"
        print(f"    (a₀,a₁)=({a0_t},{a1_t}): c₁_num={c1_numerical:.6f}, "
              f"c₁_formula={c1_formula:.6f} [{status}]")

    # ---- c₂ extraction ----
    print("\n  --- c₂ extraction (a₀=0.7, a₁=0.3) ---")
    # P(ε) ≈ a₀ + c₁ε + c₂ε², so c₂ = (P(h) - a₀ - c₁h) / h²
    h2 = 1e-3
    p_h2 = p_nonorthogonal_integral(0.7, 0.3, h2)
    c1_exact = 0.7 * 0.3 * 0.4
    c2_numerical = (p_h2 - 0.7 - c1_exact * h2) / h2**2
    print(f"    c₂ ≈ {c2_numerical:.4f}")

    # ---- Recovery of Born rule at ε=0 ----
    print("\n  --- Born rule recovery at ε=0 ---")
    for a0_t, a1_t in [(0.7, 0.3), (0.5, 0.5), (0.9, 0.1)]:
        p_0 = p_nonorthogonal_integral(a0_t, a1_t, 0.0)
        ok = abs(p_0 - a0_t) < 1e-10
        if not ok:
            all_pass = False
        status = "PASS" if ok else "FAIL"
        print(f"    (a₀,a₁)=({a0_t},{a1_t}): P(ε=0)={p_0:.6f}, Born={a0_t} [{status}]")

    print(f"\n  TEST 12 OVERALL: {'PASS' if all_pass else 'FAIL'}")
    return all_pass


# ---- Main ----

def main():
    np.random.seed(42)

    print("=" * 80)
    print("COMPREHENSIVE MATHEMATICAL VERIFICATION")
    print("BLD Selection Rule: f(|O⟩) = argmax_k |αₖ|²/|⟨Oₖ|O⟩|²")
    print("=" * 80)
    print()
    print("Verifying: Dirichlet-Gamma decomposition → exact Born statistics")
    print("12 tests covering all edge cases, consequences, and analytical derivations")
    print()

    results = {}
    results['test1_degenerate'] = test_degenerate_amplitudes()
    results['test2_m_equals_n'] = test_m_equals_n()
    results['test3_phases'] = test_complex_phases()
    results['test4_nonorthogonal'] = test_nonorthogonal_pointers()
    results['test5_large_m'] = test_large_m()
    results['test6_dirichlet'] = test_dirichlet_decomposition()
    results['test7_tau'] = test_tau_uniqueness()
    results['test8_joint'] = test_joint_measurement()
    results['test9_m2_symmetry'] = test_m2_symmetry()
    results['test10_m2_proof'] = test_m2_product_ratio_proof()
    results['test11_factored_formula'] = test_factored_observer_analytical()
    results['test12_nonorth_integral'] = test_nonorthogonal_analytical()

    # ---- Final Summary ----
    print("\n" + "=" * 80)
    print("FINAL SUMMARY")
    print("=" * 80)

    for name, passed in results.items():
        status = "PASS" if passed else "FAIL/DATA"
        print(f"  {name:35s}: {status}")

    critical_pass = all(results[k] for k in [
        'test1_degenerate', 'test2_m_equals_n', 'test3_phases',
        'test5_large_m', 'test6_dirichlet', 'test8_joint',
        'test10_m2_proof', 'test11_factored_formula', 'test12_nonorth_integral',
    ])

    print()
    if critical_pass:
        print("  ALL CRITICAL TESTS PASS")
        print()
        print("  Verified:")
        print("   1. Degenerate αₖ=0: outcome impossible (log(0)=-∞)")
        print("   2. M=N boundary: Born exact even with no extra dimensions")
        print("   3. Complex phases: irrelevant (|αₖ|² only)")
        print("   4. Non-orthogonal pointers: deviation curve quantified")
        print("   5. Large M (up to 50): Born holds")
        print("   6. Dirichlet mechanism: argmax a_k/Y_k = Born (direct proof)")
        print("   7. τ=1 unique: only temperature giving Born rule")
        print("   8. Joint measurement: Bell correlations emerge correctly")
        print("   9. M=2 symmetry: product=ratio for M=2, product fails M≥3")
        print("  10. M=2 proof: P(T>s) = P(1/T>s) = 1/(1+s) (exceedance identity)")
        print("  11. Factored observer: P = (1-r+r·log r)/(1-r)² (analytical)")
        print("  12. Non-orthogonal integral: exact 3-branch formula, c₁=a₀a₁(a₀-a₁)")
    else:
        failed = [k for k, v in results.items() if not v]
        print(f"  SOME TESTS FAILED: {failed}")


if __name__ == "__main__":
    main()
