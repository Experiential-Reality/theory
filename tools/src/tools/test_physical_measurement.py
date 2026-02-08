"""End-to-end physical measurement simulation.

Tests whether the non-orthogonal pointer deviation formula holds when
pointer states emerge from a physical interaction Hamiltonian, not from
a mathematical test fixture.

The simulation:
1. System: 1 qubit |ψ⟩ = α|0⟩ + β|1⟩
2. Apparatus: dim N_A, initial state |A₀⟩
3. Interaction: H_int = σ_z ⊗ P (P = random Hermitian)
4. Evolution: |k⟩⊗|A₀⟩ → |k⟩⊗exp((-1)^k · igτP)|A₀⟩
5. Pointer states |A₀'⟩, |A₁'⟩ emerge with overlap ε(gτ)
6. Observer |O⟩ Haar-random, selection rule f(|O⟩) = argmax_k |αₖ|²/|⟨Aₖ'|O⟩|²
7. Compare outcome statistics to the exact integral formula at measured ε

What this tests beyond test_math_verification.py:
- Pointer states from physics (unitary evolution), not test fixtures
- Overlap ε is a physical output, not an input
- Pointer states related by exp(2igτP), not by √ε construction
- Multiple random Hamiltonians test universality
"""

import numpy as np
from scipy.integrate import quad
from scipy.linalg import expm


# ---- Infrastructure (self-contained) ----

def haar_random_state(dim: int) -> np.ndarray:
    """Haar-random pure state on S^{2dim-1}."""
    z = np.random.randn(dim) + 1j * np.random.randn(dim)
    return z / np.linalg.norm(z)


def random_hermitian(dim: int) -> np.ndarray:
    """Random Hermitian matrix on C^dim."""
    H = np.random.randn(dim, dim) + 1j * np.random.randn(dim, dim)
    return (H + H.conj().T) / 2


def overlaps(pointer_states: list[np.ndarray], O: np.ndarray) -> np.ndarray:
    """Compute |⟨Aₖ'|O⟩|² for all k."""
    return np.array([np.abs(np.vdot(p, O))**2 for p in pointer_states])


def selection_rule(alphas_sq: np.ndarray, ovlps: np.ndarray) -> int:
    """f(|O⟩) = argmax_k |αₖ|²/|⟨Aₖ'|O⟩|²."""
    safe_ovlps = np.maximum(ovlps, 1e-300)
    return int(np.argmax(alphas_sq / safe_ovlps))


def integrand(theta, a0, a1, eps):
    """I(θ) for the non-orthogonal pointer integral (three-branch)."""
    A = 1.0 - eps
    C_val = eps - a1 / a0
    B = 2.0 * np.sqrt(eps * (1.0 - eps)) * np.cos(theta)
    disc = B**2 - 4.0 * A * C_val

    if disc < 0:
        return 1.0

    sqrt_d = np.sqrt(disc)
    t_minus = (-B - sqrt_d) / (2.0 * A)
    t_plus = (-B + sqrt_d) / (2.0 * A)

    if C_val <= 0:
        if t_plus <= 0:
            return 1.0
        return 1.0 / (1.0 + t_plus**2)
    else:
        if t_plus <= 0:
            return 1.0
        return t_minus**2 / (1.0 + t_minus**2) + 1.0 / (1.0 + t_plus**2)


def p_nonorthogonal_integral(a0, a1, eps):
    """Exact probability P(f=0) from the integral formula."""
    if eps < 1e-15:
        return a0
    if eps > 1.0 - 1e-15:
        return 1.0 if a0 > a1 else 0.5  # fully overlapping pointers
    result, _ = quad(integrand, 0, 2 * np.pi, args=(a0, a1, eps),
                     limit=100, epsabs=1e-10, epsrel=1e-10)
    return result / (2.0 * np.pi)


# ---- Physical measurement simulation ----

def evolve_pointer_states(P: np.ndarray, A0: np.ndarray,
                          g_tau: float) -> tuple[np.ndarray, np.ndarray, float]:
    """Evolve apparatus state under H_int = σ_z ⊗ P.

    Returns (|A₀'⟩, |A₁'⟩, ε) where:
      |A₀'⟩ = exp(-igτP)|A₀⟩  (pointer for system outcome 0)
      |A₁'⟩ = exp(+igτP)|A₀⟩  (pointer for system outcome 1)
      ε = |⟨A₀'|A₁'⟩|²        (pointer overlap)
    """
    U_minus = expm(-1j * g_tau * P)
    U_plus = expm(1j * g_tau * P)

    A0_prime = U_minus @ A0
    A1_prime = U_plus @ A0

    # Normalize (should already be normalized since U is unitary, but be safe)
    A0_prime = A0_prime / np.linalg.norm(A0_prime)
    A1_prime = A1_prime / np.linalg.norm(A1_prime)

    eps = np.abs(np.vdot(A0_prime, A1_prime))**2
    return A0_prime, A1_prime, eps


def run_mc(pointer_states: list[np.ndarray], alphas_sq: np.ndarray,
           n_samples: int) -> float:
    """Monte Carlo: fraction of outcomes selecting k=0."""
    dim = len(pointer_states[0])
    count_0 = 0
    for _ in range(n_samples):
        O = haar_random_state(dim)
        ovlp = overlaps(pointer_states, O)
        k = selection_rule(alphas_sq, ovlp)
        if k == 0:
            count_0 += 1
    return count_0 / n_samples


def main():
    np.random.seed(42)

    print("=" * 80)
    print("PHYSICAL MEASUREMENT SIMULATION")
    print("End-to-end: H_int evolution → pointer states → selection rule → formula")
    print("=" * 80)
    print()
    print("H_int = σ_z ⊗ P (P = random Hermitian)")
    print("|k⟩⊗|A₀⟩ → |k⟩⊗ exp((-1)^k · igτP)|A₀⟩")
    print("Pointer overlap ε = |⟨A₀'|A₁'⟩|² emerges from physics")
    print("Prediction: P(f=0) matches exact integral formula at measured ε")
    print()

    n_samples = 100000
    tol = 0.006  # 3σ at n=100k
    g_tau_values = [0.1, 0.3, 0.5, 0.8, 1.0, 1.5, 2.0, 3.0]
    N_A_values = [4, 8, 16, 32]
    n_hamiltonians = 3
    alpha_configs = [
        ("0.7/0.3", np.array([0.7, 0.3])),
        ("0.5/0.5", np.array([0.5, 0.5])),
    ]

    total_tests = 0
    total_pass = 0
    max_diff_seen = 0.0

    for a_name, alphas_sq in alpha_configs:
        a0, a1 = alphas_sq[0], alphas_sq[1]
        print(f"\n{'=' * 80}")
        print(f"System: |ψ⟩ = √{a0}|0⟩ + √{a1}|1⟩   (α² = {a_name})")
        print(f"{'=' * 80}")

        for N_A in N_A_values:
            for p_idx in range(n_hamiltonians):
                P = random_hermitian(N_A)
                A0 = haar_random_state(N_A)

                print(f"\n  N_A={N_A:2d}, Hamiltonian #{p_idx+1}:")

                for g_tau in g_tau_values:
                    A0_prime, A1_prime, eps = evolve_pointer_states(P, A0, g_tau)

                    # Skip if ε is too close to 1 (pointers nearly identical,
                    # selection rule degenerates)
                    if eps > 0.999:
                        p_int = a0  # Born rule (effectively orthogonal)
                    else:
                        p_int = p_nonorthogonal_integral(a0, a1, eps)

                    p_mc = run_mc([A0_prime, A1_prime], alphas_sq, n_samples)

                    diff = abs(p_mc - p_int)
                    ok = diff < tol
                    total_tests += 1
                    if ok:
                        total_pass += 1
                    max_diff_seen = max(max_diff_seen, diff)

                    status = "PASS" if ok else "FAIL"
                    print(f"    gτ={g_tau:.1f}: ε={eps:.4f}  "
                          f"P_int={p_int:.4f}  P_MC={p_mc:.4f}  "
                          f"|diff|={diff:.4f}  [{status}]")

    # ---- Summary ----
    print(f"\n{'=' * 80}")
    print(f"SUMMARY")
    print(f"{'=' * 80}")
    print(f"  Total test points: {total_tests}")
    print(f"  Passed: {total_pass}/{total_tests}")
    print(f"  Max |P_MC - P_integral|: {max_diff_seen:.4f}")
    print(f"  Tolerance: {tol}")
    print()

    if total_pass == total_tests:
        print("  ALL TESTS PASS")
        print()
        print("  The non-orthogonal pointer deviation formula matches")
        print("  physically-generated pointer states (H_int = σ_z ⊗ P)")
        print("  across all apparatus dimensions, Hamiltonians, and")
        print("  coupling strengths tested.")
        print()
        print("  Key findings:")
        print("  - Formula depends only on ε, not on how pointer states were generated")
        print("  - N_A-independence confirmed (same ε → same P(f=0) at all N_A)")
        print("  - Universality: works for arbitrary apparatus Hamiltonians")
    else:
        n_fail = total_tests - total_pass
        print(f"  {n_fail} TESTS FAILED")
        print("  Investigate: does pointer state structure carry information beyond ε?")


if __name__ == "__main__":
    main()
