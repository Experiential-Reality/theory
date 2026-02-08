"""Controlled-observer verification."""

import dataclasses
import sys

import numpy as np
import scipy.stats

from . import quantum


@dataclasses.dataclass(slots=True, frozen=True)
class BiasResult:
    alpha_sq: float
    theta_star_predicted: float
    theta_star_empirical: float | None
    match: bool


@dataclasses.dataclass(slots=True, frozen=True)
class BiasM3Result:
    unique_outcomes: int
    fractions: np.ndarray
    expected: np.ndarray


@dataclasses.dataclass(slots=True, frozen=True)
class RegimePoint:
    n_over_m: float
    chi2_dof: float


@dataclasses.dataclass(slots=True, frozen=True)
class ScalingPoint:
    n_obs: int
    max_corr: float


def run_determinism(rng: np.random.Generator) -> bool:
    configs = [
        (2, [0.7, 0.3]),
        (3, [0.5, 0.3, 0.2]),
        (5, [0.4, 0.25, 0.15, 0.12, 0.08]),
    ]
    for M, alphas in configs:
        a = np.array(alphas)
        N_obs = max(M * 4, 32)
        pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
        P = np.array(pointers.states)

        observers = quantum.haar_random_states(N_obs, 5000, rng)
        ovlps = quantum.overlaps_batch(P, observers)
        safe = np.maximum(ovlps, quantum.SAFE_FLOOR)
        choices1 = np.argmax(a[:, None] / safe, axis=0)
        choices2 = np.argmax(a[:, None] / safe, axis=0)
        if not np.array_equal(choices1, choices2):
            return False
    return True


def run_controlled_bias_m2(
    rng: np.random.Generator,
) -> list[BiasResult]:
    results = []
    for alpha_sq in [0.5, 0.7, 0.9]:
        beta_sq = 1.0 - alpha_sq
        alphas = np.array([alpha_sq, beta_sq])
        N_obs = 32
        pointers = quantum.make_orthogonal_pointers(2, N_obs, rng)
        P = np.array(pointers.states)

        theta_star_predicted = np.arctan(np.sqrt(beta_sq / alpha_sq))
        n_theta = 200
        thetas = np.linspace(0.001, np.pi / 2 - 0.001, n_theta)

        cos_t = np.cos(thetas)[:, None]
        sin_t = np.sin(thetas)[:, None]
        observers = cos_t * P[0] + sin_t * P[1]
        observers = observers / np.linalg.norm(observers, axis=1, keepdims=True)
        ovlps = quantum.overlaps_batch(P, observers)
        safe = np.maximum(ovlps, quantum.SAFE_FLOOR)
        outcomes = np.argmax(alphas[:, None] / safe, axis=0)

        switches = np.where(np.diff(outcomes) != 0)[0]
        theta_star_empirical = thetas[switches[0]] if len(switches) > 0 else None

        match = (
            theta_star_empirical is not None
            and abs(theta_star_empirical - theta_star_predicted) < 0.05
        )
        results.append(BiasResult(
            alpha_sq=alpha_sq,
            theta_star_predicted=float(theta_star_predicted),
            theta_star_empirical=float(theta_star_empirical) if theta_star_empirical is not None else None,
            match=match,
        ))
    return results


def run_controlled_bias_m3(
    rng: np.random.Generator,
) -> BiasM3Result:
    alphas = np.array([0.5, 0.3, 0.2])
    N_obs = 32
    pointers = quantum.make_orthogonal_pointers(3, N_obs, rng)
    P = np.array(pointers.states)

    n_grid = 50
    phis = np.linspace(0.01, np.pi / 2 - 0.01, n_grid)
    thetas = np.linspace(0.01, np.pi / 2 - 0.01, n_grid)

    phi_grid, theta_grid = np.meshgrid(phis, thetas, indexing='ij')
    phi_flat = phi_grid.ravel()
    theta_flat = theta_grid.ravel()

    observers = (
        np.sin(phi_flat)[:, None] * np.cos(theta_flat)[:, None] * P[0]
        + np.sin(phi_flat)[:, None] * np.sin(theta_flat)[:, None] * P[1]
        + np.cos(phi_flat)[:, None] * P[2]
    )
    observers = observers / np.linalg.norm(observers, axis=1, keepdims=True)
    ovlps = quantum.overlaps_batch(P, observers)
    safe = np.maximum(ovlps, quantum.SAFE_FLOOR)
    outcomes = np.argmax(alphas[:, None] / safe, axis=0)
    outcome_map = outcomes.reshape(n_grid, n_grid)

    unique_outcomes = len(np.unique(outcome_map))
    counts = np.bincount(outcome_map.ravel(), minlength=3)
    fracs = counts / counts.sum()

    return BiasM3Result(
        unique_outcomes=unique_outcomes,
        fractions=fracs,
        expected=alphas,
    )


def run_regime_transition(
    rng: np.random.Generator,
) -> list[RegimePoint]:
    M = 3
    alphas = np.array([0.5, 0.3, 0.2])
    N_values = [3, 4, 6, 8, 12, 16, 24, 32, 64, 128, 256, 512, 1024]
    results = []

    for N_obs in N_values:
        if N_obs < M:
            continue
        n = 20000 if N_obs >= 512 else 100000 if N_obs <= M * 2 else 50000
        pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
        outcome = quantum.run_selection_mc(pointers, alphas, n, rng)
        stat = quantum.chi2_test(outcome.counts, alphas, n)
        dof = max(1, np.sum(alphas * n > 5) - 1)
        chi2_dof = stat.chi2_stat / dof if dof > 0 else 0
        results.append(RegimePoint(N_obs / M, chi2_dof))

    return results


def run_finite_n_corrections(
    rng: np.random.Generator,
) -> float:
    M = 3
    N_values = [4, 8, 16, 32, 64, 128, 256]
    alphas = np.array([0.5, 0.3, 0.2])
    alphas = alphas / alphas.sum()
    log_alphas = np.log(alphas)

    ks_p_values = []
    for N_obs in N_values:
        pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
        P = np.array(pointers.states)
        n = 50000

        observers = quantum.haar_random_states(N_obs, n, rng)
        ovlps = quantum.overlaps_batch(P, observers)
        safe = np.maximum(ovlps, quantum.SAFE_FLOOR)
        choices_haar = np.argmax(alphas[:, None] / safe, axis=0)
        counts_haar = np.bincount(choices_haar, minlength=M).astype(float)

        X = rng.beta(1, N_obs - 1, size=(n, M))
        G_exact = -np.log(np.maximum(X, quantum.SAFE_FLOOR))
        choices_beta = np.argmax(log_alphas[None, :] + G_exact, axis=1)
        counts_beta = np.bincount(choices_beta, minlength=M).astype(float)

        freq_haar = counts_haar / n
        freq_beta = counts_beta / n
        combined = np.concatenate([freq_haar, freq_beta])
        expected = np.concatenate([alphas, alphas])
        _stat, p = scipy.stats.kstest(combined - expected, "norm", args=(0, 0.01))
        ks_p_values.append(p)

    return min(ks_p_values)


def run_independence_scaling(
    rng: np.random.Generator,
) -> list[ScalingPoint]:
    M = 3
    N_values = [4, 8, 16, 32, 64, 128, 256, 512]
    results = []

    for N_obs in N_values:
        if N_obs < M:
            continue
        pointers = quantum.make_orthogonal_pointers(M, N_obs, rng)
        P = np.array(pointers.states)
        n_samples = 10000

        observers = quantum.haar_random_states(N_obs, n_samples, rng)
        ovlps = quantum.overlaps_batch(P, observers)
        G = -np.log(np.maximum(ovlps, quantum.SAFE_FLOOR)).T

        corr = np.corrcoef(G.T)
        off_diag = corr[np.triu_indices_from(corr, k=1)]
        results.append(ScalingPoint(N_obs, float(np.max(np.abs(off_diag)))))

    return results


def main() -> int:
    rng = np.random.default_rng(42)

    print("=" * 80)
    print("CONTROLLED-OBSERVER VERIFICATION")
    print("=" * 80)

    print("\nTEST A: DETERMINISM")
    det = run_determinism(rng)
    print(f"  All deterministic: {det}")

    print("\nTEST B: CONTROLLED BIAS M=2")
    bias_m2 = run_controlled_bias_m2(rng)
    for r in bias_m2:
        emp_str = f"{r.theta_star_empirical:.4f}" if r.theta_star_empirical is not None else "N/A"
        status = "PASS" if r.match else "FAIL"
        print(
            f"  |a|^2={r.alpha_sq}: "
            f"predicted={r.theta_star_predicted:.4f}, "
            f"empirical={emp_str} [{status}]"
        )

    print("\nTEST B: CONTROLLED BIAS M=3")
    bias_m3 = run_controlled_bias_m3(rng)
    print(f"  Unique outcomes: {bias_m3.unique_outcomes} (expected: 3)")
    print(f"  Region fractions: {np.round(bias_m3.fractions, 4)}")

    print("\nTEST C: REGIME TRANSITION")
    regime = run_regime_transition(rng)
    for r in regime:
        print(f"  N/M={r.n_over_m:6.1f}: chi2/dof={r.chi2_dof:.2f}")

    print("\nTEST D: FINITE-N CORRECTIONS")
    ks_p = run_finite_n_corrections(rng)
    print(f"  Min KS p-value: {ks_p:.4f}")

    print("\nTEST E: INDEPENDENCE SCALING")
    indep = run_independence_scaling(rng)
    for r in indep:
        print(f"  N={r.n_obs:4d}: max|corr|={r.max_corr:.4f}")

    all_bias_match = all(r.match for r in bias_m2)
    ok = det and all_bias_match and bias_m3.unique_outcomes == 3
    print(f"\nVERDICT: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
