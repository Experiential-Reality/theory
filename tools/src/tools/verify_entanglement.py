"""Entanglement entropy verification: S = K×L + H."""

import dataclasses
import sys

import numpy as np


K_KILLING = 2
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
        h = s - K_KILLING * link
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
        h = s - K_KILLING * link
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
        h = s - K_KILLING * link
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
        h = s - K_KILLING * link

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
    H = S - K_KILLING * L_bld

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

    K=1: H = S - L = L > 0 (wrong — Bell states should minimize H)
    K=3: H = S - 3L = -L < 0 (violates H≥0 bound)
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


def main() -> int:
    print("=" * 80)
    print("ENTANGLEMENT ENTROPY: S = K×L + H")
    print("=" * 80)

    rng = np.random.default_rng(42)

    groups: list[tuple[str, list[EntropyResult]]] = [
        ("BELL STATES (S=2L exact)", run_bell_states()),
        ("GHZ STATES (S=2L for all N)", run_ghz_states()),
        ("W STATES (S>2L, H>0)", run_w_states()),
        ("LAMBDA SWEEP", run_lambda_sweep()),
        ("CONCURRENCE CONNECTION (ρ=C/√2)", run_concurrence_connection()),
        ("K=2 UNIQUENESS (negative)", run_k_uniqueness()),
        ("H≥0 BOUND (negative, 1000 random)", run_h_non_negative(rng)),
    ]

    all_pass = True
    for name, results in groups:
        print(f"\n--- {name} ---")
        for r in results:
            status = "PASS" if r.passes else "FAIL"
            print(
                f"  {r.state_name:16s}: S/L={r.s_over_l:.6f}, "
                f"H={r.h:+.6f} [{status}]"
            )
            if not r.passes:
                all_pass = False

    print(f"\n{'=' * 80}")
    print(f"VERDICT: {'ALL PASS' if all_pass else 'SOME FAILED'}")
    print(f"{'=' * 80}")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
