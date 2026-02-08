"""Test BLD selection rule: does L→B predict k?

Tests whether the ratio rule f(|O⟩) = argmax_k |αₖ|²/|⟨Oₖ|O⟩|²
reproduces Born statistics via the Gumbel-max trick.

Mathematical basis:
- |⟨Oₖ|O⟩|² ≈ Exp(1)/(N-1) for Haar-random |O⟩, orthogonal pointers, large N
- -log(Exp(1)) ~ Gumbel_max(0,1)
- Gumbel-max trick: P(argmax_k [log aₖ + Gumbel_k] = j) = aⱼ
- Therefore: argmax_k [log aₖ - log|⟨Oₖ|O⟩|²] gives Born statistics for ALL M

BLD interpretation:
- L_k = |αₖ|² = system's structural weight (L-structure)
- B_k = |⟨Oₖ|O⟩|² = observer's proximity to pointer state (B-alignment)
- L→B compensation selects outcome with maximum L/B ratio (structural leverage)
"""

import numpy as np
from scipy.stats import chi2, unitary_group, kstest, gumbel_r


def haar_random_state(dim: int) -> np.ndarray:
    """Generate Haar-random pure state on S^{2dim-1}."""
    z = np.random.randn(dim) + 1j * np.random.randn(dim)
    return z / np.linalg.norm(z)


def make_pointer_states(M: int, N_obs: int) -> list[np.ndarray]:
    """Create M approximately orthogonal pointer states in dim N_obs.

    Uses Haar-random unitaries applied to a reference state.
    For N_obs >> M, pointer states are approximately orthogonal.
    """
    pointer_states = []
    for _ in range(M):
        U = unitary_group.rvs(N_obs)
        ref = np.zeros(N_obs, dtype=complex)
        ref[0] = 1.0
        pointer_states.append(U @ ref)
    return pointer_states


def overlaps(pointer_states: list[np.ndarray], O: np.ndarray) -> np.ndarray:
    """Compute |⟨Oₖ|O⟩|² for all k."""
    return np.array([np.abs(np.vdot(p, O))**2 for p in pointer_states])


# ---- Selection Rule Candidates ----

def rule_product(alphas_sq: np.ndarray, ovlps: np.ndarray) -> int:
    """Rule A: argmax aₖ × |⟨Oₖ|O⟩|² (PRODUCT — should fail M≥3)."""
    return int(np.argmax(alphas_sq * ovlps))


def rule_ratio(alphas_sq: np.ndarray, ovlps: np.ndarray) -> int:
    """Rule B: argmax aₖ / |⟨Oₖ|O⟩|² (RATIO — should pass all M).

    BLD interpretation: maximize L/B = structural leverage.
    Gumbel-max trick: -log|⟨Oₖ|O⟩|² ~ Gumbel_max → Born statistics.
    """
    safe_ovlps = np.maximum(ovlps, 1e-300)
    return int(np.argmax(alphas_sq / safe_ovlps))


def rule_max_overlap(ovlps: np.ndarray) -> int:
    """Rule C: argmax |⟨Oₖ|O⟩|² (control — ignores amplitudes)."""
    return int(np.argmax(ovlps))


def rule_cdf_partition(alphas_sq: np.ndarray, O: np.ndarray) -> int:
    """Rule D: CDF partition (trivially correct, no physics)."""
    u = (np.angle(O[0]) + np.pi) / (2 * np.pi)
    cumsum = np.cumsum(alphas_sq)
    for k, threshold in enumerate(cumsum):
        if u < threshold:
            return k
    return len(alphas_sq) - 1


def rule_born_sample(alphas_sq: np.ndarray) -> int:
    """Rule E: standard Born rule sampling."""
    return int(np.random.choice(len(alphas_sq), p=alphas_sq))


# ---- Statistical Tests ----

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


def test_gumbel_distribution(pointer_states: list[np.ndarray], N_obs: int,
                             n_samples: int = 20000) -> dict:
    """Test whether -log|⟨Oₖ|O⟩|² follows Gumbel_max distribution.

    Expected: Gumbel_max(log(N-1), 1) approximately.
    """
    M = len(pointer_states)
    results = {}

    for k in range(min(M, 3)):
        gumbel_samples = []
        for _ in range(n_samples):
            O = haar_random_state(N_obs)
            x = np.abs(np.vdot(pointer_states[k], O))**2
            gumbel_samples.append(-np.log(max(x, 1e-300)))

        g = np.array(gumbel_samples)
        loc_est = np.log(N_obs - 1) if N_obs > 1 else 0.0
        stat, p = kstest(g, 'gumbel_r', args=(loc_est, 1.0))
        results[f'pointer_{k}'] = {
            'ks_stat': stat, 'p_value': p,
            'mean': np.mean(g), 'expected_mean': loc_est + np.euler_gamma,
            'std': np.std(g), 'expected_std': np.pi / np.sqrt(6),
        }

    return results


def test_independence(pointer_states: list[np.ndarray], N_obs: int,
                      n_samples: int = 20000) -> np.ndarray:
    """Test independence of G_k = -log|⟨Oₖ|O⟩|² across k.

    Returns correlation matrix. Should be ~identity for large N/M.
    """
    M = len(pointer_states)
    G = np.zeros((n_samples, M))

    for i in range(n_samples):
        O = haar_random_state(N_obs)
        for k in range(M):
            x = np.abs(np.vdot(pointer_states[k], O))**2
            G[i, k] = -np.log(max(x, 1e-300))

    return np.corrcoef(G.T)


# ---- Main Test Runner ----

def run_test(M: int, N_obs: int, alphas_sq: list[float],
             n_samples: int = 50000) -> dict:
    """Run all selection rule candidates for given parameters."""
    a = np.array(alphas_sq)
    assert len(a) == M
    assert abs(np.sum(a) - 1.0) < 1e-10

    pointer_states = make_pointer_states(M, N_obs)

    rules = {
        'A_product': np.zeros(M),
        'B_ratio': np.zeros(M),
        'C_max_overlap': np.zeros(M),
        'D_cdf_partition': np.zeros(M),
        'E_born_sample': np.zeros(M),
    }

    for _ in range(n_samples):
        O = haar_random_state(N_obs)
        ovlp = overlaps(pointer_states, O)

        rules['A_product'][rule_product(a, ovlp)] += 1
        rules['B_ratio'][rule_ratio(a, ovlp)] += 1
        rules['C_max_overlap'][rule_max_overlap(ovlp)] += 1
        rules['D_cdf_partition'][rule_cdf_partition(a, O)] += 1
        rules['E_born_sample'][rule_born_sample(a)] += 1

    results = {}
    for name, counts in rules.items():
        chi2_stat, p_value = chi2_test(counts, a, n_samples)
        results[name] = {
            'frequencies': counts / n_samples,
            'expected': a.copy(),
            'chi2': chi2_stat,
            'p_value': p_value,
            'matches_born': p_value > 0.01,
        }

    return results


def main():
    """Run full test suite."""
    np.random.seed(42)

    print("=" * 80)
    print("BLD SELECTION RULE TEST: Does L/B = structural leverage predict k?")
    print("=" * 80)
    print()
    print("PREDICTION: Rule B (ratio = L/B) gives Born statistics for ALL M")
    print("            Rule A (product) works for M=2 only, fails M>=3")
    print("            Rule C (max overlap) gives ~1/M (ignores amplitudes)")
    print()

    configs = [
        (2, "equal", [0.5, 0.5]),
        (2, "80/20", [0.8, 0.2]),
        (2, "95/5", [0.95, 0.05]),
        (3, "equal", [1/3, 1/3, 1/3]),
        (3, "50/30/20", [0.5, 0.3, 0.2]),
        (3, "70/20/10", [0.7, 0.2, 0.1]),
        (4, "equal", [0.25, 0.25, 0.25, 0.25]),
        (4, "hierarchical", [0.5, 0.25, 0.15, 0.1]),
        (5, "equal", [0.2, 0.2, 0.2, 0.2, 0.2]),
        (5, "steep", [0.5, 0.2, 0.15, 0.1, 0.05]),
    ]

    observer_sizes = [4, 8, 16, 32]
    all_results = []

    for M, desc, alphas in configs:
        for N_obs in observer_sizes:
            if N_obs < M:
                continue

            n = min(50000, 20000 if N_obs >= 32 else 50000)
            print(f"\n--- M={M} ({desc}), N_obs={N_obs} ---")
            print(f"  Expected: {[round(a, 4) for a in alphas]}")

            results = run_test(M, N_obs, alphas, n_samples=n)

            for name, r in sorted(results.items()):
                status = "PASS" if r['matches_born'] else "FAIL"
                print(f"  {name:18s}: freq={np.round(r['frequencies'], 4)}, "
                      f"chi2={r['chi2']:8.2f}, p={r['p_value']:.4f} [{status}]")

            all_results.append({
                'M': M, 'desc': desc, 'N_obs': N_obs, 'results': results
            })

    # ---- Summary ----
    print("\n" + "=" * 80)
    print("SUMMARY: Pass rates by rule")
    print("=" * 80)

    for name in ['A_product', 'B_ratio', 'C_max_overlap',
                  'D_cdf_partition', 'E_born_sample']:
        passes = sum(1 for r in all_results
                     if r['results'][name]['matches_born'])
        total = len(all_results)

        m2_pass = sum(1 for r in all_results
                      if r['M'] == 2 and r['results'][name]['matches_born'])
        m2_total = sum(1 for r in all_results if r['M'] == 2)
        m3plus_pass = sum(1 for r in all_results
                         if r['M'] >= 3 and r['results'][name]['matches_born'])
        m3plus_total = sum(1 for r in all_results if r['M'] >= 3)

        print(f"  {name:18s}: {passes:2d}/{total} total, "
              f"{m2_pass}/{m2_total} M=2, {m3plus_pass}/{m3plus_total} M>=3")

    # ---- Key comparison: Product vs Ratio for M>=3 ----
    print("\n" + "=" * 80)
    print("KEY RESULT: Product (A) vs Ratio (B) for M >= 3")
    print("=" * 80)

    for r in all_results:
        if r['M'] < 3:
            continue
        ra = r['results']['A_product']
        rb = r['results']['B_ratio']
        print(f"  M={r['M']}, N={r['N_obs']:4d} ({r['desc']:12s}): "
              f"Product p={ra['p_value']:.4f}"
              f"[{'OK' if ra['matches_born'] else 'FAIL'}] "
              f"Ratio p={rb['p_value']:.4f}"
              f"[{'OK' if rb['matches_born'] else 'FAIL'}]")
        if not ra['matches_born']:
            print(f"    Product bias: expected={np.round(ra['expected'], 3)}, "
                  f"got={np.round(ra['frequencies'], 3)}")

    # ---- Gumbel distribution test ----
    print("\n" + "=" * 80)
    print("GUMBEL DISTRIBUTION TEST: Is -log|<O_k|O>|^2 ~ Gumbel_max?")
    print("=" * 80)

    for N_obs in [8, 16, 32, 64]:
        M_test = min(3, N_obs)
        ptrs = make_pointer_states(M_test, N_obs)
        gumbel_results = test_gumbel_distribution(ptrs, N_obs, n_samples=10000)
        for name, gr in gumbel_results.items():
            status = "PASS" if gr['p_value'] > 0.01 else "FAIL"
            print(f"  N={N_obs:3d}, {name}: KS={gr['ks_stat']:.4f}, "
                  f"p={gr['p_value']:.4f} [{status}] "
                  f"mean={gr['mean']:.2f} (exp={gr['expected_mean']:.2f})")

    # ---- Independence test ----
    print("\n" + "=" * 80)
    print("INDEPENDENCE TEST: Correlation of G_k across outcomes")
    print("=" * 80)

    for N_obs in [8, 16, 32, 64]:
        M_test = min(3, N_obs)
        ptrs = make_pointer_states(M_test, N_obs)
        corr = test_independence(ptrs, N_obs, n_samples=10000)
        off_diag = corr[np.triu_indices_from(corr, k=1)]
        print(f"  N={N_obs:3d}, M={M_test}: "
              f"max |off-diag corr| = {np.max(np.abs(off_diag)):.4f}, "
              f"mean = {np.mean(np.abs(off_diag)):.4f}")

    # ---- Final verdict ----
    print("\n" + "=" * 80)
    print("VERDICT")
    print("=" * 80)

    ratio_all_pass = all(
        r['results']['B_ratio']['matches_born'] for r in all_results
    )
    product_m3_any_fail = any(
        not r['results']['A_product']['matches_born']
        for r in all_results if r['M'] >= 3
    )

    if ratio_all_pass:
        print("  RATIO RULE (L/B) REPRODUCES BORN STATISTICS FOR ALL M")
        print("  f(|O>) = argmax_k |alpha_k|^2 / |<O_k|O>|^2")
        print("  BLD: L->B compensation maximizes structural leverage")
    else:
        ratio_fails = [r for r in all_results
                       if not r['results']['B_ratio']['matches_born']]
        print(f"  RATIO RULE FAILED {len(ratio_fails)} tests:")
        for r in ratio_fails:
            print(f"    M={r['M']}, N={r['N_obs']}: "
                  f"p={r['results']['B_ratio']['p_value']:.4f}")

    if product_m3_any_fail:
        print("  PRODUCT RULE FAILS FOR M>=3 (as predicted)")
    else:
        print("  WARNING: Product rule did not fail for M>=3 "
              "(check sample size)")


if __name__ == "__main__":
    main()
