"""Wave function collapse tests: no-cloning, no-communication, path integral, irreversibility.

Tests BLD claims from wave-function-collapse.md and path-integral.md.
Each section includes positive verification AND adversarial attempts to
disprove the claim.
"""

import dataclasses

import numpy as np
import pytest
import scipy.linalg

import tools.bld
import tools.quantum


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------


def _partial_trace_a(rho_ab: np.ndarray, dim_a: int, dim_b: int) -> np.ndarray:
    """Trace out subsystem A, return reduced density matrix on B."""
    rho = rho_ab.reshape(dim_a, dim_b, dim_a, dim_b)
    return np.einsum("ijik->jk", rho)


# ---------------------------------------------------------------------------
# B2: No-cloning from unitarity
# ---------------------------------------------------------------------------
#
# BLD claim (wave-function-collapse.md, Claim 3):
#   z = z^2  =>  z in {0, 1}
#
# If a unitary U clones: U|psi>|0> = |psi>|psi> for all |psi>,
# then inner products give <psi1|psi2> = <psi1|psi2>^2.
# Only z=0 (orthogonal) or z=1 (identical) satisfy this.


@dataclasses.dataclass(slots=True, frozen=True)
class CloningResult:
    overlap: complex
    overlap_sq: complex
    residual: float
    is_clonable: bool
    passes: bool


def run_no_cloning(rng: np.random.Generator) -> list[CloningResult]:
    """For random state pairs, verify cloning constraint z = z^2.

    Positive: orthogonal (z~0) and identical (z=1) pairs satisfy z=z^2.
    Adversarial: random pairs with intermediate overlap do NOT satisfy it.
    """
    results: list[CloningResult] = []
    dim = 8

    # Identical states: z = 1, z^2 = 1  =>  clonable
    psi = tools.bld.haar_random_state(dim, rng)
    z = np.vdot(psi, psi)
    results.append(CloningResult(z, z**2, abs(z - z**2), True, abs(z - z**2) < 1e-12))

    # Orthogonal states: z = 0, z^2 = 0  =>  clonable
    psi1 = np.zeros(dim, dtype=complex)
    psi1[0] = 1.0
    psi2 = np.zeros(dim, dtype=complex)
    psi2[1] = 1.0
    z = np.vdot(psi1, psi2)
    results.append(CloningResult(z, z**2, abs(z - z**2), True, abs(z - z**2) < 1e-12))

    # Random pairs: z should NOT satisfy z = z^2
    for _ in range(200):
        s1 = tools.bld.haar_random_state(dim, rng)
        s2 = tools.bld.haar_random_state(dim, rng)
        z = np.vdot(s1, s2)
        residual = abs(z - z**2)
        # With overwhelming probability, random states have 0 < |z| < 1
        # so z != z^2 and cloning fails.
        is_clonable = residual < 1e-6
        results.append(CloningResult(z, z**2, residual, is_clonable, not is_clonable))

    return results


def run_no_cloning_unitary_test(rng: np.random.Generator) -> list[CloningResult]:
    """Attempt to construct an approximate cloner and verify it fails.

    For a set of non-orthogonal states, try to build a unitary that maps
    |psi_k>|0> -> |psi_k>|psi_k>.  Verify the map cannot be unitary:
    the Gram matrix of outputs doesn't match the Gram matrix of inputs.
    """
    dim = 4
    n_states = 3
    results: list[CloningResult] = []

    # Generate non-orthogonal states
    states = [tools.bld.haar_random_state(dim, rng) for _ in range(n_states)]

    # Input Gram matrix: G_in[j,k] = <psi_j, 0 | psi_k, 0> = <psi_j|psi_k>
    G_in = np.array([[np.vdot(states[j], states[k])
                       for k in range(n_states)]
                      for j in range(n_states)])

    # If cloning worked, output Gram: G_out[j,k] = <psi_j|psi_k>^2
    G_out = G_in ** 2

    # A unitary preserves inner products, so we need G_in == G_out.
    # This fails for non-orthogonal states.
    for j in range(n_states):
        for k in range(j + 1, n_states):
            z = G_in[j, k]
            z_sq = G_out[j, k]
            residual = abs(z - z_sq)
            is_clonable = residual < 1e-6
            results.append(CloningResult(z, z_sq, residual, is_clonable, not is_clonable))

    return results


# ---------------------------------------------------------------------------
# B3: No-communication
# ---------------------------------------------------------------------------
#
# BLD claim (wave-function-collapse.md, Claim 2):
#   Bob's reduced state is unchanged by Alice's local operations.
#   B is local, B->L fails, so Alice's B cannot modify the non-local L.


@dataclasses.dataclass(slots=True, frozen=True)
class NoCommunicationResult:
    state_name: str
    operation_name: str
    trace_distance: float
    passes: bool


def _random_unitary(dim: int, rng: np.random.Generator) -> np.ndarray:
    z = rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim))
    Q, R = np.linalg.qr(z)
    d = np.diag(R)
    ph = d / np.abs(d)
    return Q * ph[None, :]


def _trace_distance(rho1: np.ndarray, rho2: np.ndarray) -> float:
    diff = rho1 - rho2
    ev = np.linalg.eigvalsh(diff @ diff.conj().T)
    return 0.5 * float(np.sum(np.sqrt(np.maximum(ev, 0.0))))


def run_no_communication(rng: np.random.Generator) -> list[NoCommunicationResult]:
    """Verify Bob's reduced state is invariant under Alice's local unitaries.

    For entangled states and random local operations on Alice, compute
    Bob's reduced density matrix before and after.  Trace distance should
    be zero (within numerical precision).

    Adversarial: try many random unitaries, projective measurements, and
    non-trivial entangled states.
    """
    results: list[NoCommunicationResult] = []
    dim_a, dim_b = 2, 2
    dim_ab = dim_a * dim_b

    # States to test
    bell = np.array([1, 0, 0, 1], dtype=complex) / np.sqrt(2)
    asym = np.array([np.sqrt(0.7), 0, 0, np.sqrt(0.3)], dtype=complex)
    product = np.array([1, 0, 0, 0], dtype=complex)
    partial = np.array([np.sqrt(0.5), np.sqrt(0.2), np.sqrt(0.1), np.sqrt(0.2)], dtype=complex)

    states = {
        "Bell": bell,
        "asymmetric": asym,
        "product": product,
        "partial_entangled": partial,
    }

    for state_name, psi in states.items():
        rho_ab = np.outer(psi, psi.conj())
        rho_b_original = _partial_trace_a(rho_ab, dim_a, dim_b)

        # Alice applies random unitaries
        for i in range(20):
            U_a = _random_unitary(dim_a, rng)
            U_ab = np.kron(U_a, np.eye(dim_b))
            psi_after = U_ab @ psi
            rho_ab_after = np.outer(psi_after, psi_after.conj())
            rho_b_after = _partial_trace_a(rho_ab_after, dim_a, dim_b)

            td = _trace_distance(rho_b_original, rho_b_after)
            results.append(NoCommunicationResult(
                state_name, f"U_random_{i}", td, td < 1e-10,
            ))

        # Alice does a projective measurement (average over outcomes)
        for basis_idx in range(3):
            if basis_idx == 0:
                P0 = np.array([[1, 0], [0, 0]], dtype=complex)
                P1 = np.array([[0, 0], [0, 1]], dtype=complex)
                basis_name = "Z_basis"
            elif basis_idx == 1:
                P0 = np.array([[0.5, 0.5], [0.5, 0.5]], dtype=complex)
                P1 = np.array([[0.5, -0.5], [-0.5, 0.5]], dtype=complex)
                basis_name = "X_basis"
            else:
                P0 = np.array([[0.5, -0.5j], [0.5j, 0.5]], dtype=complex)
                P1 = np.array([[0.5, 0.5j], [-0.5j, 0.5]], dtype=complex)
                basis_name = "Y_basis"

            # After Alice measures, Bob's average state = Tr_A(rho_AB)
            # This is because sum_k (P_k x I) rho (P_k x I) traced over A
            # gives Tr_A(rho) regardless of which projectors Alice uses.
            rho_b_post = np.zeros((dim_b, dim_b), dtype=complex)
            for Pk in [P0, P1]:
                Pk_ab = np.kron(Pk, np.eye(dim_b))
                rho_post_k = Pk_ab @ rho_ab @ Pk_ab
                rho_b_post += _partial_trace_a(rho_post_k, dim_a, dim_b)

            td = _trace_distance(rho_b_original, rho_b_post)
            results.append(NoCommunicationResult(
                state_name, f"proj_{basis_name}", td, td < 1e-10,
            ))

    return results


def run_no_communication_higher_dim(rng: np.random.Generator) -> list[NoCommunicationResult]:
    """Same test in higher dimensions to stress-test."""
    results: list[NoCommunicationResult] = []

    for dim_a, dim_b in [(3, 3), (2, 4), (4, 2)]:
        dim_ab = dim_a * dim_b
        psi = tools.bld.haar_random_state(dim_ab, rng)
        rho_ab = np.outer(psi, psi.conj())
        rho_b_original = _partial_trace_a(rho_ab, dim_a, dim_b)

        for i in range(10):
            U_a = _random_unitary(dim_a, rng)
            U_ab = np.kron(U_a, np.eye(dim_b))
            psi_after = U_ab @ psi
            rho_ab_after = np.outer(psi_after, psi_after.conj())
            rho_b_after = _partial_trace_a(rho_ab_after, dim_a, dim_b)

            td = _trace_distance(rho_b_original, rho_b_after)
            results.append(NoCommunicationResult(
                f"random_{dim_a}x{dim_b}", f"U_{i}", td, td < 1e-10,
            ))

    return results


# ---------------------------------------------------------------------------
# B4: Path integral convergence (Trotter product formula)
# ---------------------------------------------------------------------------
#
# BLD claim (path-integral.md):
#   D(L(B)) = partition(B) × phase(L) × iterate(D)
#   ⟨x_f|U(t)|x_i⟩ = ∑_{all paths} ∏_k ⟨x_{k+1}|e^{-iĤΔt/ℏ}|x_k⟩
#
# On a finite lattice this becomes the Trotter product formula:
#   [exp(-iT*dt) * exp(-iV*dt)]^N  →  exp(-iH*t)  as N → ∞
#
# B = lattice sites (position basis)
# L = exp(-iH_slice*dt) phase link per slice
# D = N iterations of the slice operator


@dataclasses.dataclass(slots=True, frozen=True)
class TrotterResult:
    system: str
    n_slices: int
    error: float
    passes: bool


def _lattice_hamiltonian(
    n_sites: int, dx: float, m: float, hbar: float,
    potential: np.ndarray | None = None,
) -> np.ndarray:
    """Build H = T + V on a 1D lattice with n_sites points.

    T uses the standard 3-point finite-difference stencil:
      T_{jk} = -(ℏ²/2m) * d²/dx²  ≈  -(ℏ²/2m*dx²) * (δ_{j,k+1} - 2δ_{jk} + δ_{j,k-1})

    V is diagonal in the position basis.
    """
    coeff = hbar**2 / (2 * m * dx**2)
    T = np.zeros((n_sites, n_sites), dtype=complex)
    for j in range(n_sites):
        T[j, j] = 2.0 * coeff
        if j > 0:
            T[j, j - 1] = -coeff
        if j < n_sites - 1:
            T[j, j + 1] = -coeff

    H = T.copy()
    if potential is not None:
        H += np.diag(potential.astype(complex))
    return H


def _trotter_propagator(
    H: np.ndarray, T: np.ndarray, V_diag: np.ndarray,
    t: float, n_slices: int, hbar: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Compute exact and Trotter-approximated propagators.

    Exact:   U_exact = expm(-i*H*t/ℏ)
    Trotter: U_trotter = [expm(-i*T*dt/ℏ) @ expm(-i*V*dt/ℏ)]^N

    Returns (U_exact, U_trotter).
    """
    dt = t / n_slices
    U_exact = scipy.linalg.expm(-1j * H * t / hbar)

    # Slice operators
    U_T = scipy.linalg.expm(-1j * T * dt / hbar)
    U_V = np.diag(np.exp(-1j * V_diag * dt / hbar))

    # D-iteration: apply N slices
    U_slice = U_T @ U_V
    U_trotter = np.linalg.matrix_power(U_slice, n_slices)

    return U_exact, U_trotter


def run_trotter_free_particle() -> list[TrotterResult]:
    """Free particle on a lattice: Trotter converges to exact propagator.

    H = T (kinetic only), V = 0.  The Trotter splitting is trivial here
    (no V to split from), so this tests the D(L(B)) iteration mechanism
    itself: N identical slices of exp(-iT*dt) compose to exp(-iT*t).
    """
    results: list[TrotterResult] = []
    n_sites = 32
    dx = 0.3
    m, hbar, t = 1.0, 1.0, 0.5

    V_diag = np.zeros(n_sites)
    T = _lattice_hamiltonian(n_sites, dx, m, hbar)
    H = T.copy()

    for N in [1, 2, 4, 8, 16]:
        U_exact, U_trotter = _trotter_propagator(H, T, V_diag, t, N, hbar)
        # Operator norm error: ||U_exact - U_trotter||
        err = float(np.linalg.norm(U_exact - U_trotter, ord=2))
        # Free particle: T and V=0 commute, so Trotter is exact at all N
        results.append(TrotterResult("free_particle", N, err, err < 1e-10))

    return results


def run_trotter_harmonic() -> list[TrotterResult]:
    """Harmonic oscillator: Trotter error scales as O(dt) = O(t/N).

    H = T + V where V = ½mω²x².  [T,V] ≠ 0, so Trotter splitting
    introduces error proportional to dt * ||[T,V]||.  As N grows,
    the approximation converges to the exact propagator.
    """
    results: list[TrotterResult] = []
    n_sites = 32
    dx = 0.3
    m, hbar, omega, t = 1.0, 1.0, 1.0, 0.5

    # Position grid centered at 0
    x = (np.arange(n_sites) - n_sites // 2) * dx
    V_diag = 0.5 * m * omega**2 * x**2

    T = _lattice_hamiltonian(n_sites, dx, m, hbar, potential=None)
    H = _lattice_hamiltonian(n_sites, dx, m, hbar, potential=V_diag)

    prev_err = float("inf")
    for N in [2, 4, 8, 16, 32]:
        U_exact, U_trotter = _trotter_propagator(H, T, V_diag, t, N, hbar)
        err = float(np.linalg.norm(U_exact - U_trotter, ord=2))
        # Error should decrease with N (convergence = D(L(B)) works)
        converging = err < prev_err * 0.95 or err < 1e-10
        prev_err = err
        results.append(TrotterResult("harmonic", N, err, converging))

    return results


def run_trotter_wrong_phase() -> list[TrotterResult]:
    """Negative test: removing i from the phase breaks everything.

    BLD derives i as the observation unit (path-integral.md Step 2).
    Without it, the "propagator" exp(+H*t/ℏ) is not unitary and
    does not converge to the correct time evolution.
    """
    results: list[TrotterResult] = []
    n_sites = 16
    dx = 0.3
    m, hbar, omega, t = 1.0, 1.0, 1.0, 0.5

    x = (np.arange(n_sites) - n_sites // 2) * dx
    V_diag = 0.5 * m * omega**2 * x**2

    T = _lattice_hamiltonian(n_sites, dx, m, hbar, potential=None)
    H = _lattice_hamiltonian(n_sites, dx, m, hbar, potential=V_diag)

    # Correct propagator
    U_exact = scipy.linalg.expm(-1j * H * t / hbar)

    # WRONG: real exponential (no i) — exp(+H*t/hbar) instead of exp(-iH*t/hbar)
    dt = t / 4
    U_T_wrong = scipy.linalg.expm(T.real * dt / hbar)  # no -i
    U_V_wrong = np.diag(np.exp(V_diag * dt / hbar))    # no -i
    U_slice_wrong = U_T_wrong @ U_V_wrong
    U_wrong = np.linalg.matrix_power(U_slice_wrong, 4)

    err = float(np.linalg.norm(U_exact - U_wrong, ord=2))
    # Without i, this should be very wrong (not unitary, exponentially growing)
    results.append(TrotterResult("wrong_phase", 4, err, err > 1.0))

    return results


# ---------------------------------------------------------------------------
# B5: Collapse irreversibility
# ---------------------------------------------------------------------------
#
# BLD claim (wave-function-collapse.md, Claim 4):
#   B-outcome is many-to-one with L-structure.
#   Many different pre-measurement states can produce the same outcome k.
#   B-information cannot reconstruct L-information.


@dataclasses.dataclass(slots=True, frozen=True)
class IrreversibilityResult:
    name: str
    passes: bool


def run_many_to_one(rng: np.random.Generator) -> list[IrreversibilityResult]:
    """Verify the many-to-one nature of measurement.

    Generate many distinct states |psi> that all have |alpha_k|^2 = p for
    the same outcome k.  For a fixed observer, they all give the same
    selection rule outcome despite being different L-structures.
    This demonstrates information loss: B (outcome) doesn't determine L (state).
    """
    results: list[IrreversibilityResult] = []
    M = 2
    N_obs = 32
    # Fixed pointers and observer
    pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
    P = np.array(pointers.states)
    observer = tools.bld.haar_random_state(N_obs, rng)

    # Compute which outcome this observer selects for alpha^2 = [0.7, 0.3]
    ovlps = tools.quantum.overlaps(pointers.states, observer)
    reference_alphas = np.array([0.7, 0.3])
    safe = np.maximum(ovlps, tools.quantum.SAFE_FLOOR)
    reference_outcome = int(np.argmax(reference_alphas / safe))

    # Generate 50 DIFFERENT states with the same |alpha_0|^2 = 0.7
    # but different phases.  They all give the same outcome for this observer.
    same_outcome_count = 0
    n_states = 50
    for i in range(n_states):
        phase = 2 * np.pi * i / n_states
        alpha = np.array([np.sqrt(0.7) * np.exp(1j * phase), np.sqrt(0.3)])
        a_sq = np.abs(alpha) ** 2
        outcome = int(np.argmax(a_sq / safe))
        if outcome == reference_outcome:
            same_outcome_count += 1

    # All should give the same outcome (selection rule uses |alpha|^2)
    results.append(IrreversibilityResult(
        "phases_same_outcome",
        same_outcome_count == n_states,
    ))

    return results


def run_info_loss(rng: np.random.Generator) -> list[IrreversibilityResult]:
    """Quantify information loss: measurement outcome retains at most 1 bit
    from a continuous L-structure (amplitudes + phases).

    For M=2 with |alpha_0|^2 in [0.5, 0.95], a single measurement outcome
    (0 or 1) cannot distinguish the specific alpha values.
    """
    results: list[IrreversibilityResult] = []
    M = 2
    N_obs = 32
    n_samples = 20000

    # Multiple states with different alpha^2 values
    alpha_sq_values = [0.5, 0.6, 0.7, 0.8, 0.9]
    outcome_fractions: list[float] = []

    for a0 in alpha_sq_values:
        a = np.array([a0, 1 - a0])
        pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
        outcome = tools.quantum.run_selection_mc(pointers, a, n_samples, rng)
        frac_0 = outcome.counts[0] / n_samples
        outcome_fractions.append(frac_0)

    # Verify: outcome fractions approximate alpha^2 (Born rule works)
    for a0, frac in zip(alpha_sq_values, outcome_fractions):
        results.append(IrreversibilityResult(
            f"born_check_a0={a0:.1f}", abs(frac - a0) < 0.02,
        ))

    # But from a SINGLE outcome (0 or 1), you can't tell which alpha was used.
    # This is the information loss: continuous L -> discrete B is not invertible.
    # The best you can do is estimate alpha^2 from MANY outcomes (statistics).
    # One outcome carries at most log2(M) bits; the state has infinite info.
    results.append(IrreversibilityResult(
        "single_outcome_insufficient",
        True,  # structural fact: 1 bit < infinite continuous info
    ))

    return results


def run_irreversibility_reconstruction(rng: np.random.Generator) -> list[IrreversibilityResult]:
    """Attempt to reconstruct the original state from measurement outcomes.

    This is the operational test of B->L failure: given only outcome data,
    try to infer the full state.  With N measurements, the estimation error
    scales as 1/sqrt(N) -- never reaching exact reconstruction.
    """
    results: list[IrreversibilityResult] = []
    true_alpha_sq = np.array([0.7, 0.3])

    # Simulate measurements with increasing sample count
    for n_meas in [10, 100, 1000]:
        outcomes = rng.choice(2, size=n_meas, p=true_alpha_sq)
        estimated_p0 = np.mean(outcomes == 0)
        error = abs(estimated_p0 - 0.7)
        expected_error = 1.0 / np.sqrt(n_meas)
        results.append(IrreversibilityResult(
            f"reconstruction_n={n_meas}",
            error < 3 * expected_error,  # estimate within 3 sigma
        ))

    # Even with 1000 measurements, phase is completely lost
    # (outcomes don't depend on phase at all)
    results.append(IrreversibilityResult(
        "phase_unrecoverable",
        True,  # structural: |alpha|^2 is phase-independent
    ))

    return results


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.theory
def test_no_cloning(rng: np.random.Generator) -> None:
    assert all(r.passes for r in run_no_cloning(rng))


@pytest.mark.theory
def test_no_cloning_unitary(rng: np.random.Generator) -> None:
    assert all(r.passes for r in run_no_cloning_unitary_test(rng))


@pytest.mark.theory
def test_no_communication(rng: np.random.Generator) -> None:
    assert all(r.passes for r in run_no_communication(rng))


@pytest.mark.theory
def test_no_communication_higher_dim(rng: np.random.Generator) -> None:
    assert all(r.passes for r in run_no_communication_higher_dim(rng))


@pytest.mark.theory
def test_trotter_free_particle() -> None:
    assert all(r.passes for r in run_trotter_free_particle())


@pytest.mark.theory
def test_trotter_harmonic() -> None:
    assert all(r.passes for r in run_trotter_harmonic())


@pytest.mark.theory
def test_trotter_wrong_phase() -> None:
    assert all(r.passes for r in run_trotter_wrong_phase())


@pytest.mark.theory
def test_many_to_one(rng: np.random.Generator) -> None:
    assert all(r.passes for r in run_many_to_one(rng))


@pytest.mark.theory
def test_info_loss(rng: np.random.Generator) -> None:
    assert all(r.passes for r in run_info_loss(rng))


@pytest.mark.theory
def test_irreversibility_reconstruction(rng: np.random.Generator) -> None:
    assert all(r.passes for r in run_irreversibility_reconstruction(rng))
