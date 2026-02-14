"""Gauge subalgebra tests: su(3), su(2), u(1) in so(8).

Tests 25-28 from the equation of motion suite.
Generator construction, closure, independence, adjoint branching 28 = 12 + 16.
"""

import numpy as np
import numpy.linalg as la

import tools.bld

from helpers import assert_all_pass


TR = tools.bld.TestResult
SO8 = tools.bld.SO8


# ---------------------------------------------------------------------------
# Test 25: su(3) generators in so(8) — closure and dimension
# ---------------------------------------------------------------------------


def test_su3_generators_in_so8(so8: SO8) -> None:
    """Extract 8 su(3) generators from G₂ stabilizer, verify Lie closure.

    Prove: 8 generators from octonion derivation null space (D(e₁)=0).
    Verify: [T_a, T_b] lies in span({T_c}) for all a, b (Lie closure).
    Verify: dimension = 8 = dim(su(3)).
    Disprove: fixing e₂ instead of e₁ gives a DIFFERENT (rotated) su(3).
    """
    results: list[TR] = []

    gens = tools.bld.su3_generators()  # (8, 28)
    results.append(TR("su3_dim=8", gens.shape[0] == 8))

    # Compute so(8) structure constants for commutator in coefficient space
    basis_8, f_8 = so8.basis, so8.f

    # Verify closure: [T_a, T_b] should lie in span(gens)
    Q, _ = la.qr(gens.T, mode="reduced")  # Q is (28, 8), columns span su(3)
    proj = Q @ Q.T  # (28, 28) projection matrix

    max_residual = 0.0
    for a in range(8):
        for b in range(a + 1, 8):
            bracket = tools.bld.lie_bracket(gens[a], gens[b], f_8)
            residual = bracket - proj @ bracket
            res_norm = float(la.norm(residual))
            if res_norm > max_residual:
                max_residual = res_norm

    results.append(TR(
        f"su3_closure_max_residual={max_residual:.2e}",
        max_residual < 1e-12,
    ))

    # Verify: all generators have zero in row/col 0 and row/col 1
    # (derivations fix e₀ and e₁)
    max_fix_err = 0.0
    for g_idx in range(8):
        M = np.zeros((8, 8))
        k = 0
        for i in range(8):
            for j in range(i + 1, 8):
                M[i, j] = gens[g_idx, k]
                M[j, i] = -gens[g_idx, k]
                k += 1
        fix_err = max(float(la.norm(M[0, :])), float(la.norm(M[1, :])))
        if fix_err > max_fix_err:
            max_fix_err = fix_err

    results.append(TR(
        f"su3_fixes_e0_e1_err={max_fix_err:.2e}",
        max_fix_err < 1e-13,
    ))

    # Disprove: fixing e₂ instead of e₁ gives different su(3)
    struct = tools.bld.octonion_struct()
    base_rows = tools.bld.octonion_derivation_constraints(struct)
    fix_e2 = np.zeros((7, 49))
    for a in range(7):
        fix_e2[a, 7 + a] = 1.0
    A2 = np.vstack([base_rows, fix_e2])
    nullity2 = 49 - int(la.matrix_rank(A2, tol=1e-10))
    results.append(TR(f"fix_e2_also_dim_8={nullity2}", nullity2 == 8))

    # The two su(3)'s span different subspaces
    _, s2, Vt2 = la.svd(A2)
    n_null2 = 49 - int(np.sum(s2 > 1e-10))
    gens2 = np.zeros((8, 28))
    for g_idx in range(8):
        D7 = Vt2[-n_null2 + g_idx].reshape(7, 7)
        D8 = np.zeros((8, 8))
        D8[1:, 1:] = D7
        k = 0
        for i in range(8):
            for j in range(i + 1, 8):
                gens2[g_idx, k] = D8[i, j]
                k += 1

    combined = np.vstack([gens, gens2])  # (16, 28)
    combined_rank = int(la.matrix_rank(combined, tol=1e-10))
    results.append(TR(
        f"different_su3_combined_rank={combined_rank}>8",
        combined_rank > 8,
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 26: su(2) generators in so(8) — closure from quaternionic substructure
# ---------------------------------------------------------------------------


def test_su2_generators_in_so8(so8: SO8) -> None:
    """Build 3 su(2) generators from quaternionic left multiplication, verify closure.

    Prove: Left multiplication by {e₁,e₂,e₄} restricted to the quaternionic
      subspace {e₀,e₁,e₂,e₄} gives 3 generators closing to su(2).
    Verify: [T_a, T_b] = 2 T_c (cyclic) — the su(2) commutation relations.
    Verify: dim = 3.
    Disprove: unrestricted left multiplication does NOT close (non-associativity).
    """
    results: list[TR] = []

    gens = tools.bld.su2_generators()  # (3, 28)
    results.append(TR("su2_dim=3", gens.shape[0] == 3))

    # Verify closure using so(8) structure constants
    basis_8, f_8 = so8.basis, so8.f

    # [T₁, T₂] = 2T₄ (indices 0,1,2 in gens array)
    b01 = tools.bld.lie_bracket(gens[0], gens[1], f_8)
    err01 = float(la.norm(b01 - 2 * gens[2]))
    results.append(TR(f"[T1,T2]=2T4_err={err01:.2e}", err01 < 1e-14))

    # [T₂, T₄] = 2T₁
    b12 = tools.bld.lie_bracket(gens[1], gens[2], f_8)
    err12 = float(la.norm(b12 - 2 * gens[0]))
    results.append(TR(f"[T2,T4]=2T1_err={err12:.2e}", err12 < 1e-14))

    # [T₄, T₁] = 2T₂
    b20 = tools.bld.lie_bracket(gens[2], gens[0], f_8)
    err20 = float(la.norm(b20 - 2 * gens[1]))
    results.append(TR(f"[T4,T1]=2T2_err={err20:.2e}", err20 < 1e-14))

    # Disprove: UNRESTRICTED left multiplication doesn't close
    struct = tools.bld.octonion_struct()
    full_gens = np.zeros((3, 28))
    for g_idx, a in enumerate([1, 2, 4]):
        L = tools.bld.octonion_left_mult(struct, a)
        A = 0.5 * (L - L.T)
        k = 0
        for i in range(8):
            for j in range(i + 1, 8):
                full_gens[g_idx, k] = A[i, j]
                k += 1

    # [L₁_full, L₂_full] should NOT be 2*L₄_full
    b_full = tools.bld.lie_bracket(full_gens[0], full_gens[1], f_8)
    err_full = float(la.norm(b_full - 2 * full_gens[2]))
    results.append(TR(
        f"unrestricted_NOT_closed_err={err_full:.2f}",
        err_full > 0.1,  # large error — non-associativity breaks closure
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 27: gauge subalgebra linear independence in so(8)
# ---------------------------------------------------------------------------


def test_gauge_subalgebra_independence(so8: SO8, rng: np.random.Generator) -> None:
    """su(3), su(2), u(1) generators span 12 linearly independent directions.

    Prove: the 8+3+1=12 generators are linearly independent in R^28.
    Verify: rank of combined 12×28 matrix = 12.
    Verify: dimensions match bld.gauge_subalgebra_dims().
    Disprove: random 12 vectors in R^28 don't close to any Lie algebra.
    """
    results: list[TR] = []

    su3, su2, u1 = so8.su3, so8.su2, so8.u1

    all_gens = np.vstack([su3, su2, u1.reshape(1, -1)])  # (12, 28)
    rank = int(la.matrix_rank(all_gens, tol=1e-10))
    results.append(TR(f"gauge_rank={rank}=12", rank == 12))

    # Verify dimensions match bld
    dims = tools.bld.gauge_subalgebra_dims()
    results.append(TR(
        f"dims=({dims[0]},{dims[1]},{dims[2]})=(8,3,1)",
        dims == (8, 3, 1),
    ))

    # Verify individual ranks
    results.append(TR(
        f"su3_rank={int(la.matrix_rank(su3, tol=1e-10))}=8",
        int(la.matrix_rank(su3, tol=1e-10)) == 8,
    ))
    results.append(TR(
        f"su2_rank={int(la.matrix_rank(su2, tol=1e-10))}=3",
        int(la.matrix_rank(su2, tol=1e-10)) == 3,
    ))

    # Complementary dimension
    comp = tools.bld.adjoint_complementary_dim(tools.bld.so_dim(8))
    results.append(TR(f"complementary_dim={comp}=16", comp == 16))

    # Disprove: random generators don't close
    basis_8, f_8 = so8.basis, so8.f
    random_gens = rng.standard_normal((3, 28))

    Q_rand, _ = la.qr(random_gens.T, mode="reduced")
    proj_rand = Q_rand @ Q_rand.T
    max_res = 0.0
    for a in range(3):
        for b in range(a + 1, 3):
            br = tools.bld.lie_bracket(random_gens[a], random_gens[b], f_8)
            res = float(la.norm(br - proj_rand @ br))
            if res > max_res:
                max_res = res
    results.append(TR(
        f"random_3_NOT_closed_res={max_res:.2f}",
        max_res > 0.1,
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 28: adjoint branching 28 = 12 + 16
# ---------------------------------------------------------------------------


def test_adjoint_branching(so8: SO8) -> None:
    """The 28 so(8) generators split into 12 gauge + 16 complementary.

    Prove: 28 = 12 (gauge) + 16 (complementary).
    Verify: complementary 16 generators are orthogonal to gauge 12 in Killing metric.
    Verify: the 16 include generators involving indices {0,1} (gravity content)
      and generators in the su(3) orthogonal complement (matter content).
    """
    results: list[TR] = []
    dim = tools.bld.so_dim(8)  # 28

    gauge = so8.gauge  # (12, 28)

    # Build orthonormal basis for gauge subspace
    Q_gauge, _ = la.qr(gauge.T, mode="reduced")  # (28, 12)
    proj_gauge = Q_gauge @ Q_gauge.T

    # Complementary = orthogonal complement in Killing metric
    identity_28 = np.eye(dim)
    proj_comp = identity_28 - proj_gauge

    # Rank of complementary projection = 16
    comp_rank = int(np.round(np.trace(proj_comp)))
    results.append(TR(f"complementary_dim={comp_rank}=16", comp_rank == 16))

    # Dimension check: 12 + 16 = 28
    gauge_rank = int(la.matrix_rank(gauge, tol=1e-10))
    results.append(TR(
        f"28={gauge_rank}+{comp_rank}",
        gauge_rank + comp_rank == dim,
    ))

    # Verify: complementary generators include E_{0j} directions
    # (these are "gravity" directions — rotations involving the identity e₀)
    # E_{02} through E_{07} should have significant complementary projection
    # (E_{01} is u(1), so it's in the gauge subspace)
    n_gravity_in_comp = 0
    for j in range(2, 8):
        # Find index of E_{0j} in canonical basis
        e_0j = np.zeros(dim)
        k = 0
        for ii in range(8):
            for jj in range(ii + 1, 8):
                if ii == 0 and jj == j:
                    e_0j[k] = 1.0
                k += 1
        comp_proj = float(la.norm(proj_comp @ e_0j))
        if comp_proj > 0.1:
            n_gravity_in_comp += 1

    results.append(TR(
        f"gravity_directions_in_comp={n_gravity_in_comp}",
        n_gravity_in_comp >= 3,  # at least some E_{0j} in complementary
    ))

    # Verify: some E_{1j} directions also in complementary
    n_e1j_in_comp = 0
    for j in range(2, 8):
        e_1j = np.zeros(dim)
        k = 0
        for ii in range(8):
            for jj in range(ii + 1, 8):
                if ii == 1 and jj == j:
                    e_1j[k] = 1.0
                k += 1
        comp_proj = float(la.norm(proj_comp @ e_1j))
        if comp_proj > 0.1:
            n_e1j_in_comp += 1

    results.append(TR(
        f"E_1j_directions_in_comp={n_e1j_in_comp}",
        n_e1j_in_comp >= 3,
    ))

    assert_all_pass(results)
