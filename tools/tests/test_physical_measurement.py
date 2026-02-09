"""Physical measurement simulation tests."""

import concurrent.futures
import dataclasses
import os

import numpy as np
import scipy.linalg

import tools.bld
import tools.quantum

from helpers import assert_all_pass


@dataclasses.dataclass(slots=True, frozen=True)
class SimPoint:
    g_tau: float
    epsilon: float
    p_integral: float
    p_mc: float
    passes: bool

def random_hermitian(dim: int, rng: np.random.Generator) -> np.ndarray:
    H = rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim))
    return (H + H.conj().T) / 2


def evolve_pointer_states(
    P: np.ndarray, A0: np.ndarray, g_tau: float,
) -> tuple[np.ndarray, np.ndarray, float]:
    U_minus = scipy.linalg.expm(-1j * g_tau * P)
    U_plus = scipy.linalg.expm(1j * g_tau * P)

    A0_prime = U_minus @ A0
    A1_prime = U_plus @ A0

    A0_prime = A0_prime / np.linalg.norm(A0_prime)
    A1_prime = A1_prime / np.linalg.norm(A1_prime)

    eps = np.abs(np.vdot(A0_prime, A1_prime)) ** 2
    return A0_prime, A1_prime, eps

def _process_job(
    alphas_sq: np.ndarray,
    P: np.ndarray,
    A0: np.ndarray,
    g_tau_values: list[float],
    n_samples: int,
    tol: float,
    child_rng: np.random.Generator,
) -> list[SimPoint]:
    a0, a1 = alphas_sq[0], alphas_sq[1]
    results = []
    for g_tau in g_tau_values:
        A0_prime, A1_prime, eps = evolve_pointer_states(P, A0, g_tau)

        if eps > 0.999:
            p_int = a0
        else:
            p_int = tools.quantum.p_nonorthogonal(a0, a1, eps)

        pointers = tools.quantum.PointerSet(
            (A0_prime, A1_prime),
            tools.quantum.PointerKind.NON_ORTHOGONAL,
            overlap_epsilon=eps,
        )
        outcome = tools.quantum.run_selection_mc(
            pointers, alphas_sq, n_samples, child_rng,
        )
        p_mc = outcome.counts[0] / n_samples

        results.append(SimPoint(
            g_tau=g_tau,
            epsilon=eps,
            p_integral=p_int,
            p_mc=p_mc,
            passes=abs(p_mc - p_int) < tol,
        ))
    return results


def test_physical_simulation(rng: np.random.Generator) -> None:
    n_samples = 100000
    tol = 0.006
    g_tau_values = [0.1, 0.3, 0.5, 0.8, 1.0, 1.5, 2.0, 3.0]
    N_A_values = [4, 8, 16, 32]
    n_hamiltonians = 3
    alpha_configs = [
        np.array([0.7, 0.3]),
        np.array([0.5, 0.5]),
    ]

    jobs = []
    for alphas_sq in alpha_configs:
        for N_A in N_A_values:
            for _ in range(n_hamiltonians):
                P = random_hermitian(N_A, rng)
                A0 = tools.bld.haar_random_state(N_A, rng)
                jobs.append((alphas_sq, P, A0))

    children = rng.bit_generator.seed_seq.spawn(len(jobs))
    child_rngs = [np.random.default_rng(s) for s in children]

    n_workers = min(len(jobs), os.cpu_count() or 1)
    with concurrent.futures.ThreadPoolExecutor(max_workers=n_workers) as pool:
        futures = [
            pool.submit(
                _process_job, alphas_sq, P, A0,
                g_tau_values, n_samples, tol, child_rng,
            )
            for (alphas_sq, P, A0), child_rng in zip(jobs, child_rngs)
        ]
        results = []
        for f in futures:
            results.extend(f.result())

    assert_all_pass(results)
