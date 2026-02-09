"""Quantum selection rule infrastructure."""
import dataclasses
import enum
import typing

import numpy as np
import scipy.integrate
import scipy.stats

from . import bld

SAFE_FLOOR = 1e-300


class PointerKind(enum.Enum):
    ORTHOGONAL = "orthogonal"
    NON_ORTHOGONAL = "non_orthogonal"

@dataclasses.dataclass(slots=True, frozen=True)
class PointerSet:
    states: tuple[np.ndarray, ...]
    kind: PointerKind
    overlap_epsilon: float = 0.0

@dataclasses.dataclass(slots=True)
class OutcomeResult:
    counts: np.ndarray
    n_samples: int
    @property
    def frequencies(self) -> np.ndarray:
        return self.counts / self.n_samples

@dataclasses.dataclass(slots=True, frozen=True)
class StatTest:
    chi2_stat: float
    p_value: float
    passes: bool

def overlaps_batch(
    pointer_matrix: np.ndarray, observers: np.ndarray,
) -> np.ndarray:
    return np.abs(pointer_matrix @ observers.conj().T) ** 2

def make_orthogonal_pointers(
    M: int, N_obs: int, rng: np.random.Generator,
) -> PointerSet:
    U = scipy.stats.unitary_group.rvs(N_obs, random_state=rng)
    states = tuple(U[:, k].copy() for k in range(M))
    return PointerSet(states, PointerKind.ORTHOGONAL, overlap_epsilon=0.0)

def make_nonorthogonal_pointers_m2(
    N_obs: int, epsilon: float, rng: np.random.Generator,
) -> PointerSet:
    U = scipy.stats.unitary_group.rvs(N_obs, random_state=rng)
    O0 = U[:, 0].copy()
    O0_perp = U[:, 1].copy()
    O1 = np.sqrt(epsilon) * O0 + np.sqrt(1 - epsilon) * O0_perp
    O1 = O1 / np.linalg.norm(O1)
    actual_overlap = np.abs(np.vdot(O0, O1)) ** 2
    assert abs(actual_overlap - epsilon) < 1e-10, (
        f"Overlap mismatch: {actual_overlap} vs {epsilon}"
    )
    return PointerSet(
        (O0, O1), PointerKind.NON_ORTHOGONAL, overlap_epsilon=epsilon,
    )

def make_nonorthogonal_pointers_m3(
    N_obs: int, epsilon: float, rng: np.random.Generator,
) -> PointerSet:
    U = scipy.stats.unitary_group.rvs(N_obs, random_state=rng)
    e0, e1, e2 = U[:, 0], U[:, 1], U[:, 2]
    O0 = e0.copy()
    c_10 = np.sqrt(epsilon)
    c_11 = np.sqrt(1 - epsilon)
    O1 = c_10 * e0 + c_11 * e1
    O1 = O1 / np.linalg.norm(O1)
    c_20 = np.sqrt(epsilon)
    c_21 = (np.sqrt(epsilon) - epsilon) / np.sqrt(1 - epsilon)
    c_22_sq = 1.0 - abs(c_20) ** 2 - abs(c_21) ** 2
    if c_22_sq < 0:
        c_22_sq = 0.0
    c_22 = np.sqrt(c_22_sq)
    O2 = c_20 * e0 + c_21 * e1 + c_22 * e2
    O2 = O2 / np.linalg.norm(O2)
    return PointerSet(
        (O0, O1, O2), PointerKind.NON_ORTHOGONAL, overlap_epsilon=epsilon,
    )

def overlaps(
    pointer_states: tuple[np.ndarray, ...] | list[np.ndarray],
    O: np.ndarray,
) -> np.ndarray:
    return np.array([np.abs(np.vdot(p, O)) ** 2 for p in pointer_states])

def selection_rule(alphas_sq: np.ndarray, ovlps: np.ndarray) -> int:
    safe_ovlps = np.maximum(ovlps, SAFE_FLOOR)
    return int(np.argmax(alphas_sq / safe_ovlps))

def selection_rule_tau(
    alphas_sq: np.ndarray, ovlps: np.ndarray, tau: float,
) -> int:
    safe_ovlps = np.maximum(ovlps, SAFE_FLOOR)
    weights = np.power(np.maximum(alphas_sq, SAFE_FLOOR), 1.0 / tau)
    return int(np.argmax(weights / safe_ovlps))

def rule_product(alphas_sq: np.ndarray, ovlps: np.ndarray) -> int:
    return int(np.argmax(alphas_sq * ovlps))

def rule_max_overlap(ovlps: np.ndarray) -> int:
    return int(np.argmax(ovlps))

def rule_cdf_partition(alphas_sq: np.ndarray, O: np.ndarray) -> int:
    u = (np.angle(O[0]) + np.pi) / (2 * np.pi)
    cumsum = np.cumsum(alphas_sq)
    for k, threshold in enumerate(cumsum):
        if u < threshold:
            return k
    return len(alphas_sq) - 1

def rule_born_sample(alphas_sq: np.ndarray, rng: np.random.Generator) -> int:
    return int(rng.choice(len(alphas_sq), p=alphas_sq))

def chi2_test(
    observed_counts: np.ndarray,
    expected_probs: np.ndarray,
    n_samples: int,
    threshold: float = 0.01,
) -> StatTest:
    expected_counts = expected_probs * n_samples
    mask = expected_counts > 5
    if np.sum(mask) <= 1:
        return StatTest(0.0, 1.0, True)
    chi2_stat = float(np.sum(
        (observed_counts[mask] - expected_counts[mask]) ** 2
        / expected_counts[mask]
    ))
    dof = np.sum(mask) - 1
    p_value = float(1.0 - scipy.stats.chi2.cdf(chi2_stat, dof))
    return StatTest(chi2_stat, p_value, p_value > threshold)

def nonorthogonal_integrand(
    theta: float, a0: float, a1: float, eps: float,
) -> float:
    A = 1.0 - eps
    C_val = eps - a1 / a0
    B = 2.0 * np.sqrt(eps * (1.0 - eps)) * np.cos(theta)
    disc = B ** 2 - 4.0 * A * C_val
    if disc < 0:
        return 1.0
    sqrt_d = np.sqrt(disc)
    t_minus = (-B - sqrt_d) / (2.0 * A)
    t_plus = (-B + sqrt_d) / (2.0 * A)
    if C_val <= 0:
        if t_plus <= 0:
            return 1.0
        return 1.0 / (1.0 + t_plus ** 2)
    else:
        if t_plus <= 0:
            return 1.0
        return t_minus ** 2 / (1.0 + t_minus ** 2) + 1.0 / (1.0 + t_plus ** 2)

def p_nonorthogonal(a0: float, a1: float, eps: float) -> float:
    if eps < 1e-15:
        return a0
    if eps > 1.0 - 1e-15:
        return 1.0 if a0 > a1 else 0.5
    result, _ = scipy.integrate.quad(
        nonorthogonal_integrand, 0, 2 * np.pi,
        args=(a0, a1, eps),
        limit=100, epsabs=1e-10, epsrel=1e-10,
    )
    return result / (2.0 * np.pi)

def _vec_ratio(a: np.ndarray, ovlps: np.ndarray) -> np.ndarray:
    safe = np.maximum(ovlps, SAFE_FLOOR)
    return np.argmax(a[:, None] / safe, axis=0)

def _vec_product(a: np.ndarray, ovlps: np.ndarray) -> np.ndarray:
    return np.argmax(a[:, None] * ovlps, axis=0)

_VECTORIZED_RULES: dict[typing.Callable, typing.Callable] = {
    selection_rule: _vec_ratio,
    rule_product: _vec_product,
}

def run_selection_mc(
    pointers: PointerSet,
    alphas_sq: np.ndarray,
    n_samples: int,
    rng: np.random.Generator,
    rule: typing.Callable = selection_rule,
) -> OutcomeResult:
    dim = len(pointers.states[0])
    M = len(pointers.states)
    P = np.array(pointers.states)
    observers = bld.haar_random_states(dim, n_samples, rng)
    ovlps = overlaps_batch(P, observers)

    vec = _VECTORIZED_RULES.get(rule)
    if vec is not None:
        choices = vec(alphas_sq, ovlps)
    else:
        choices = np.array([rule(alphas_sq, ovlps[:, i]) for i in range(n_samples)])

    counts = np.bincount(choices, minlength=M).astype(float)
    return OutcomeResult(counts, n_samples)

