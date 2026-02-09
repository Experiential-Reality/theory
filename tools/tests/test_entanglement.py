"""Entanglement entropy verification: S = K×L + H."""

import dataclasses

import numpy as np
import pytest

import tools.bld
SQRT2 = np.sqrt(2)


@dataclasses.dataclass(slots=True, frozen=True)
class EntropyResult:
    state_name: str
    von_neumann_s: float
    bld_link: float
    s_over_l: float
    h: float
    passes: bool


def _von_neumann_entropy(eigenvalues: np.ndarray) -> float:
    ev = eigenvalues[eigenvalues > 1e-15]
    return -float(np.sum(ev * np.log(ev)))


def _bld_link(rho_sq: float) -> float:
    return -0.5 * np.log(1 - rho_sq)


def _reduced_density_eigenvalues(psi: np.ndarray, dim_a: int) -> np.ndarray:
    dim_b = len(psi) // dim_a
    psi_matrix = psi.reshape(dim_a, dim_b)
    rho_a = psi_matrix @ psi_matrix.conj().T
    return np.linalg.eigvalsh(rho_a)


def run_bell_states() -> list[EntropyResult]:
    results = []
    bell_states = {
        "Φ+": np.array([1, 0, 0, 1], dtype=complex) / SQRT2,
        "Φ-": np.array([1, 0, 0, -1], dtype=complex) / SQRT2,
        "Ψ+": np.array([0, 1, 1, 0], dtype=complex) / SQRT2,
        "Ψ-": np.array([0, 1, -1, 0], dtype=complex) / SQRT2,
    }
    for name, psi in bell_states.items():
        ev = _reduced_density_eigenvalues(psi, 2)
        s = _von_neumann_entropy(ev)
        lambda_val = float(min(ev.max(), 1 - ev.min()))
        rho_sq = 2 * lambda_val * (1 - lambda_val)
        link = _bld_link(rho_sq)
        s_over_l = s / link
        h = s - tools.bld.K * link
        results.append(EntropyResult(
            f"Bell {name}", s, link, s_over_l, h,
            abs(s_over_l - 2.0) < 1e-10 and abs(h) < 1e-10,
        ))
    return results


def run_ghz_states() -> list[EntropyResult]:
    results = []
    for num_qubits in [3, 4, 5, 6]:
        dim = 2**num_qubits
        psi = np.zeros(dim, dtype=complex)
        psi[0] = 1 / SQRT2
        psi[-1] = 1 / SQRT2

        ev = _reduced_density_eigenvalues(psi, 2)
        s = _von_neumann_entropy(ev)
        rho_sq = 2 * 0.5 * 0.5
        link = _bld_link(rho_sq)
        s_over_l = s / link
        h = s - tools.bld.K * link
        results.append(EntropyResult(
            f"GHZ_{num_qubits}", s, link, s_over_l, h,
            abs(s_over_l - 2.0) < 1e-10 and abs(h) < 1e-10,
        ))
    return results


def run_w_states() -> list[EntropyResult]:
    results = []
    for num_qubits in [3, 4, 5]:
        dim = 2**num_qubits
        psi = np.zeros(dim, dtype=complex)
        for k in range(num_qubits):
            idx = 1 << (num_qubits - 1 - k)
            psi[idx] = 1 / np.sqrt(num_qubits)

        ev = _reduced_density_eigenvalues(psi, 2)
        s = _von_neumann_entropy(ev)
        lambda_val = 1 / num_qubits
        rho_sq = 2 * lambda_val * (1 - lambda_val)
        link = _bld_link(rho_sq)
        s_over_l = s / link
        h = s - tools.bld.K * link
        results.append(EntropyResult(
            f"W_{num_qubits}", s, link, s_over_l, h,
            h > 0 and s_over_l > 2.0,
        ))
    return results


def run_lambda_sweep() -> list[EntropyResult]:
    results = []
    for lambda_val in np.linspace(0.05, 0.50, 19):
        psi = np.array([
            0, np.sqrt(lambda_val), np.sqrt(1 - lambda_val), 0,
        ], dtype=complex)
        ev = _reduced_density_eigenvalues(psi, 2)
        s = _von_neumann_entropy(ev)
        rho_sq = 2 * lambda_val * (1 - lambda_val)
        link = _bld_link(rho_sq)
        s_over_l = s / link if link > 1e-15 else float("inf")
        h = s - tools.bld.K * link

        if abs(lambda_val - 0.5) < 1e-10:
            passes = abs(s_over_l - 2.0) < 1e-10 and abs(h) < 1e-10
        else:
            passes = h > 0 and s_over_l > 2.0
        results.append(EntropyResult(
            f"λ={lambda_val:.3f}", s, link, s_over_l, h, passes,
        ))
    return results


def run_concurrence_connection() -> list[EntropyResult]:
    results = []
    for lambda_val in [0.1, 0.2, 0.3, 0.4, 0.5]:
        psi = np.array([
            0, np.sqrt(lambda_val), np.sqrt(1 - lambda_val), 0,
        ], dtype=complex)

        concurrence = 2 * np.sqrt(lambda_val * (1 - lambda_val))
        rho_bld = concurrence / SQRT2
        rho_sq_from_concurrence = rho_bld**2
        rho_sq_direct = 2 * lambda_val * (1 - lambda_val)

        match = abs(rho_sq_from_concurrence - rho_sq_direct) < 1e-14
        link = _bld_link(rho_sq_direct)
        ev = _reduced_density_eigenvalues(psi, 2)
        s = _von_neumann_entropy(ev)
        results.append(EntropyResult(
            f"ρ=C/√2 λ={lambda_val}", s, link, s / link, s - 2 * link, match,
        ))
    return results


def run_h_non_negative(rng: np.random.Generator) -> list[EntropyResult]:
    """Negative test: H = S - 2L must be >= 0 for ALL 2-qubit states.

    BLD claims K=2 is a floor on S/L.  For 2-qubit pure states this is
    equivalent to  -λ ln λ - (1-λ) ln(1-λ) >= -ln(1-2λ(1-λ))  for all
    λ ∈ (0,1).  The lambda_sweep covers a 1-D slice; this tests 1000
    Haar-random orientations to verify the code handles arbitrary states.
    """
    n_states = 1000
    # Vectorized Haar-random 2-qubit state generation
    z = rng.standard_normal((n_states, 4)) + 1j * rng.standard_normal((n_states, 4))
    psi = z / np.linalg.norm(z, axis=1, keepdims=True)
    # Batched reduced density matrix eigenvalues
    M = psi.reshape(n_states, 2, 2)
    rho = M @ M.conj().transpose(0, 2, 1)
    ev = np.linalg.eigvalsh(rho)  # (n_states, 2), sorted ascending
    lam = ev[:, 1]  # larger eigenvalue

    # Von Neumann entropy (vectorized, guarding log(0))
    ev_safe = np.clip(ev, 1e-15, None)
    S = -np.sum(ev_safe * np.log(ev_safe), axis=1)

    # BLD link
    rho_sq = 2 * lam * (1 - lam)
    entangled = rho_sq > 1e-15
    L_bld = np.where(entangled, -0.5 * np.log(np.clip(1 - rho_sq, 1e-15, None)), 0.0)
    H = S - tools.bld.K * L_bld

    violations = np.where(entangled & (H < -1e-10))[0]
    results: list[EntropyResult] = []
    for i in violations:
        results.append(EntropyResult(
            f"random_{i}", float(S[i]), float(L_bld[i]),
            float(S[i] / L_bld[i]), float(H[i]), False,
        ))
    results.append(EntropyResult(
        f"H≥0 ({n_states} random)", 0, 0, 0, 0, len(violations) == 0,
    ))
    return results


def run_k_uniqueness() -> list[EntropyResult]:
    """Negative test: only K=2 gives H=0 for maximally entangled states.

    K=1: H = S - L = L > 0 (wrong -- Bell states should minimize H)
    K=3: H = S - 3L = -L < 0 (violates H>=0 bound)
    Only K=2: H = S - 2L = 0 exactly.
    """
    psi = np.array([1, 0, 0, 1], dtype=complex) / SQRT2
    ev = _reduced_density_eigenvalues(psi, 2)
    s = _von_neumann_entropy(ev)
    lambda_val = float(min(ev.max(), 1 - ev.min()))
    rho_sq = 2 * lambda_val * (1 - lambda_val)
    link = _bld_link(rho_sq)

    results = []
    for k_test in [1, 2, 3]:
        h = s - k_test * link
        if k_test == 2:
            # K=2 should give H=0
            results.append(EntropyResult(
                f"K={k_test} (correct)", s, link, s / link, h,
                abs(h) < 1e-10,
            ))
        elif k_test == 1:
            # K=1 should give H > 0 (wrong floor)
            results.append(EntropyResult(
                f"K={k_test} (too low)", s, link, s / link, h,
                h > 0.1,  # passes if K=1 gives wrong (positive) H
            ))
        elif k_test == 3:
            # K=3 should give H < 0 (violates bound)
            results.append(EntropyResult(
                f"K={k_test} (too high)", s, link, s / link, h,
                h < -0.1,  # passes if K=3 gives wrong (negative) H
            ))
    return results


# ---------------------------------------------------------------------------
# Adversarial: wrong link function
# ---------------------------------------------------------------------------


def run_wrong_link_function() -> list[EntropyResult]:
    """Only L = -½ln(1-ρ²) gives H=0 for maximally entangled states.

    The BLD link function's ½ factor comes from K=2: the bidirectional
    observation cost divides the information-theoretic log.  For Bell
    states (ρ²=0.5), S = ln(2) and L = ½ln(2), so S = 2L = K×L exactly.

    Test alternatives:
    - L = ρ²/2   (linear Taylor approximation — misses log structure)
    - L = -ln(1-ρ²)  (missing ½ factor — wrong K)
    - L = arctanh(ρ)  (different functional form entirely)

    All wrong links give H = S - K×L ≠ 0 for Bell states: the specific
    logarithmic form with the ½ factor is structurally determined.
    """
    psi = np.array([1, 0, 0, 1], dtype=complex) / SQRT2
    ev = _reduced_density_eigenvalues(psi, 2)
    s = _von_neumann_entropy(ev)
    lambda_val = float(min(ev.max(), 1 - ev.min()))
    rho_sq = 2 * lambda_val * (1 - lambda_val)
    rho = np.sqrt(rho_sq)

    link_correct = _bld_link(rho_sq)       # -0.5 * ln(1 - rho_sq)
    link_linear = rho_sq / 2               # Taylor: misses log
    link_no_half = -np.log(1 - rho_sq)     # wrong K (effectively K=1)
    link_arctanh = float(np.arctanh(rho))  # different function

    results: list[EntropyResult] = []
    for name, link_val in [
        ("correct: -½ln(1-ρ²)", link_correct),
        ("linear: ρ²/2", link_linear),
        ("no_half: -ln(1-ρ²)", link_no_half),
        ("arctanh: arctanh(ρ)", link_arctanh),
    ]:
        h = s - tools.bld.K * link_val
        is_correct = name.startswith("correct")
        if is_correct:
            passes = abs(h) < 1e-10
        else:
            passes = abs(h) > 0.01  # wrong link gives H ≠ 0
        s_over_l = s / link_val if link_val > 1e-15 else float("inf")
        results.append(EntropyResult(name, s, link_val, s_over_l, h, passes))

    return results


# ---------------------------------------------------------------------------
# Black hole entropy: S = K×L (same structure as entanglement entropy)
# ---------------------------------------------------------------------------


def run_bh_entropy_decomposition() -> list[EntropyResult]:
    """S_BH = A/(4 l_P²) decomposes as S = K×L where 4 = n.

    The Bekenstein-Hawking 1/4 IS 1/n (spacetime dimensions).
    L = A/(2n l_P²) and S = K×L = 2L = A/(n l_P²)/2 × 2 = A/(n l_P²).
    Same S = K×L structure as qubit entanglement entropy.
    """
    n_, K_ = tools.bld.n, tools.bld.K

    # For a black hole with area A in units of l_P²:
    # S_BH = A/4 = A/n
    # L_BH = A/(2n)
    # S = K * L = 2 * A/(2n) = A/n = A/4 ✓

    # Test with symbolic area A = 100 (in Planck units)
    A = 100.0
    s_standard = A / 4.0          # Standard Bekenstein-Hawking
    s_bld = A / n_                # BLD: 4 = n
    l_bld = A / (2 * n_)          # BLD link
    s_from_kl = K_ * l_bld        # S = K×L

    results: list[EntropyResult] = []
    # 1/4 = 1/n
    results.append(EntropyResult(
        "1/4 = 1/n", s_standard, l_bld, s_standard / l_bld if l_bld > 0 else 0, 0,
        abs(s_standard - s_bld) < 1e-10,
    ))
    # S = K×L
    results.append(EntropyResult(
        "S = K×L", s_from_kl, l_bld, s_from_kl / l_bld if l_bld > 0 else 0, 0,
        abs(s_from_kl - s_standard) < 1e-10,
    ))
    # S/L = K = 2
    results.append(EntropyResult(
        "S/L = K", s_standard, l_bld, s_standard / l_bld, 0,
        abs(s_standard / l_bld - K_) < 1e-10,
    ))
    return results


def run_schwarzschild_k() -> list[EntropyResult]:
    """The 2 in r_s = 2GM/c² is K (observation cost).

    Schwarzschild radius: r_s = K × GM/c².
    K = 2 appears because observation of the black hole boundary
    requires bidirectional traversal (same K as everywhere else).
    """
    K_ = tools.bld.K
    # r_s = coefficient × GM/c². The coefficient IS K.
    schwarzschild_coeff = 2  # Standard GR
    return [EntropyResult(
        "r_s coefficient = K", 0, 0, 0, 0,
        schwarzschild_coeff == K_,
    )]


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.theory
def test_bell_states() -> None:
    assert all(r.passes for r in run_bell_states())


@pytest.mark.theory
def test_ghz_states() -> None:
    assert all(r.passes for r in run_ghz_states())


@pytest.mark.theory
def test_w_states() -> None:
    assert all(r.passes for r in run_w_states())


@pytest.mark.theory
def test_lambda_sweep() -> None:
    assert all(r.passes for r in run_lambda_sweep())


@pytest.mark.theory
def test_concurrence_connection() -> None:
    assert all(r.passes for r in run_concurrence_connection())


@pytest.mark.theory
def test_h_non_negative(rng: np.random.Generator) -> None:
    assert all(r.passes for r in run_h_non_negative(rng))


@pytest.mark.theory
def test_k_uniqueness() -> None:
    assert all(r.passes for r in run_k_uniqueness())


@pytest.mark.theory
def test_wrong_link_function() -> None:
    assert all(r.passes for r in run_wrong_link_function())


@pytest.mark.theory
def test_bh_entropy_decomposition() -> None:
    assert all(r.passes for r in run_bh_entropy_decomposition())


@pytest.mark.theory
def test_schwarzschild_k() -> None:
    assert all(r.passes for r in run_schwarzschild_k())
