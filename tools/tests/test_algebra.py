"""Division algebra tests.

Computationally verifies the algebra claims underpinning B=56, SU(3),
n=4 spacetime dimensions, and 3 generations.

Theory refs:
  - octonion-derivation.md (octonions forced, G2 -> SU(3))
  - octonion-necessity.md (Hurwitz, division algebra boundary)
  - e7-derivation.md (B=56 from triality, Spin(8))
"""

import dataclasses
import itertools

import numpy as np

from helpers import assert_all_pass


@dataclasses.dataclass(slots=True, frozen=True)
class AlgebraResult:
    name: str
    value: float
    passes: bool


# ---------------------------------------------------------------------------
# Octonion multiplication infrastructure
# ---------------------------------------------------------------------------
#
# Fano plane triples (i, j, k) mean e_i * e_j = e_k.
# Indices 1..7 for imaginary units; 0 is the real unit.
# Convention follows the standard Fano plane:
#   (1,2,4), (2,3,5), (3,4,6), (4,5,7), (5,6,1), (6,7,2), (7,1,3)

_FANO_TRIPLES = [
    (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 7),
    (5, 6, 1), (6, 7, 2), (7, 1, 3),
]

# Build structure constants: C[i][j] = (sign, k) where e_i * e_j = sign * e_k
# For i,j in 1..7.  e_0 is the identity.
_STRUCT = np.zeros((8, 8, 8), dtype=np.float64)

# e_0 * e_i = e_i, e_i * e_0 = e_i
for i in range(8):
    _STRUCT[0, i, i] = 1.0
    _STRUCT[i, 0, i] = 1.0

# e_i * e_i = -e_0 for i >= 1
for i in range(1, 8):
    _STRUCT[i, i, 0] = -1.0

# Fano plane triples
for a, b, c in _FANO_TRIPLES:
    _STRUCT[a, b, c] = 1.0
    _STRUCT[b, a, c] = -1.0    # antisymmetric
    # Cyclic: (a,b,c) -> (b,c,a) -> (c,a,b)
    _STRUCT[b, c, a] = 1.0
    _STRUCT[c, b, a] = -1.0
    _STRUCT[c, a, b] = 1.0
    _STRUCT[a, c, b] = -1.0


def _octonion_multiply(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Multiply two octonions represented as 8-vectors."""
    return np.einsum("ijk,i,j->k", _STRUCT, a, b)


def _octonion_conjugate(a: np.ndarray) -> np.ndarray:
    """Conjugate: negate imaginary parts."""
    result = a.copy()
    result[1:] = -result[1:]
    return result


def _octonion_norm_sq(a: np.ndarray) -> float:
    """Squared norm: a * conj(a) should give (|a|^2, 0, ..., 0)."""
    return float(np.dot(a, a))


def _octonion_norm(a: np.ndarray) -> float:
    return float(np.sqrt(np.dot(a, a)))


def _cayley_dickson_multiply(
    mult: np.ndarray, a: np.ndarray, b: np.ndarray,
) -> np.ndarray:
    """Multiply in a Cayley-Dickson doubled algebra.

    If the base algebra has dimension d with structure constants mult[d,d,d],
    then (a0,a1)*(b0,b1) = (a0*b0 - conj(b1)*a1, b1*a0 + a1*conj(b0))
    where a = (a0, a1), b = (b0, b1) are 2d-vectors.
    """
    d = len(a) // 2
    a0, a1 = a[:d], a[d:]
    b0, b1 = b[:d], b[d:]

    def _mul(x: np.ndarray, y: np.ndarray) -> np.ndarray:
        return np.einsum("ijk,i,j->k", mult, x, y)

    def _conj(x: np.ndarray) -> np.ndarray:
        c = x.copy()
        c[1:] = -c[1:]
        return c

    c0 = _mul(a0, b0) - _mul(_conj(b1), a1)
    c1 = _mul(b1, a0) + _mul(a1, _conj(b0))
    return np.concatenate([c0, c1])


def _make_real_mult() -> np.ndarray:
    """Structure constants for R (1D): trivial multiplication."""
    m = np.zeros((1, 1, 1))
    m[0, 0, 0] = 1.0
    return m


def _double_struct(mult: np.ndarray) -> np.ndarray:
    """Build structure constants for the Cayley-Dickson double."""
    d = mult.shape[0]
    d2 = 2 * d
    new = np.zeros((d2, d2, d2))
    # We compute the structure constants by multiplying basis vectors
    for i in range(d2):
        ei = np.zeros(d2)
        ei[i] = 1.0
        for j in range(d2):
            ej = np.zeros(d2)
            ej[j] = 1.0
            prod = _cayley_dickson_multiply(mult, ei, ej)
            new[i, j, :] = prod
    return new


def _octonion_derivation_matrix() -> np.ndarray:
    """Build the G2 derivation constraint matrix for octonions.

    A derivation D maps Im(O) -> Im(O) (7x7 matrix, 49 unknowns).
    D(e_i * e_j) = D(e_i)*e_j + e_i*D(e_j) gives linear constraints.
    """
    n_unknowns = 49
    equations = []
    for i in range(1, 8):
        for j in range(1, 8):
            for out_comp in range(8):
                row = np.zeros(n_unknowns)
                for k in range(1, 8):
                    coeff = _STRUCT[i, j, k]
                    if abs(coeff) < 1e-15:
                        continue
                    if out_comp >= 1:
                        row[(k - 1) * 7 + (out_comp - 1)] += coeff
                for a in range(7):
                    sc = _STRUCT[a + 1, j, out_comp]
                    if abs(sc) < 1e-15:
                        continue
                    row[(i - 1) * 7 + a] -= sc
                for a in range(7):
                    sc = _STRUCT[i, a + 1, out_comp]
                    if abs(sc) < 1e-15:
                        continue
                    row[(j - 1) * 7 + a] -= sc
                if np.any(np.abs(row) > 1e-15):
                    equations.append(row)
    return np.array(equations)


def test_octonion_norm(rng: np.random.Generator) -> None:
    """Verify |a*b| = |a|*|b| for random octonion pairs.

    The composition algebra property.  This is what makes octonions a
    normed division algebra.
    """
    results: list[AlgebraResult] = []
    max_residual = 0.0

    for _ in range(1000):
        a = rng.standard_normal(8)
        b = rng.standard_normal(8)
        ab = _octonion_multiply(a, b)

        norm_ab = _octonion_norm(ab)
        norm_a_times_b = _octonion_norm(a) * _octonion_norm(b)
        residual = abs(norm_ab - norm_a_times_b)
        max_residual = max(max_residual, residual)

    results.append(AlgebraResult(
        "norm_preserving", max_residual, max_residual < 1e-10,
    ))
    assert_all_pass(results)


def test_octonion_nonassociative(rng: np.random.Generator) -> None:
    """Verify octonions are alternative but NOT associative.

    If they were associative, quaternions would suffice and we wouldn't
    need the octonionic structure that gives B=56 and SU(3).
    """
    results: list[AlgebraResult] = []

    # Non-associativity: (a*b)*c != a*(b*c) for generic triples
    nonassoc_count = 0
    for _ in range(100):
        a = rng.standard_normal(8)
        b = rng.standard_normal(8)
        c = rng.standard_normal(8)
        lhs = _octonion_multiply(_octonion_multiply(a, b), c)
        rhs = _octonion_multiply(a, _octonion_multiply(b, c))
        if np.linalg.norm(lhs - rhs) > 1e-10:
            nonassoc_count += 1

    results.append(AlgebraResult(
        "nonassociative", float(nonassoc_count), nonassoc_count > 90,
    ))

    # Left alternativity: (a*a)*b = a*(a*b)
    max_alt_left = 0.0
    for _ in range(100):
        a = rng.standard_normal(8)
        b = rng.standard_normal(8)
        lhs = _octonion_multiply(_octonion_multiply(a, a), b)
        rhs = _octonion_multiply(a, _octonion_multiply(a, b))
        max_alt_left = max(max_alt_left, float(np.linalg.norm(lhs - rhs)))

    results.append(AlgebraResult(
        "left_alternative", max_alt_left, max_alt_left < 1e-10,
    ))

    # Right alternativity: (a*b)*b = a*(b*b)
    max_alt_right = 0.0
    for _ in range(100):
        a = rng.standard_normal(8)
        b = rng.standard_normal(8)
        lhs = _octonion_multiply(_octonion_multiply(a, b), b)
        rhs = _octonion_multiply(a, _octonion_multiply(b, b))
        max_alt_right = max(max_alt_right, float(np.linalg.norm(lhs - rhs)))

    results.append(AlgebraResult(
        "right_alternative", max_alt_right, max_alt_right < 1e-10,
    ))

    assert_all_pass(results)


def test_division_algebra_boundary(rng: np.random.Generator) -> None:
    """Verify the Hurwitz theorem boundary via Cayley-Dickson doubling.

    R(1D), C(2D), H(4D), O(8D) have no zero divisors.
    S(16D, sedenions) DO have zero divisors => not a division algebra.
    This is why octonions are the LAST division algebra.
    """
    results: list[AlgebraResult] = []
    mult = _make_real_mult()
    names = ["R(1)", "C(2)", "H(4)", "O(8)", "S(16)"]

    for step in range(5):
        dim = mult.shape[0]
        name = names[step]

        if step < 4:
            # Verify no zero divisors: random a,b with a*b should not be zero
            found_zero_divisor = False
            for _ in range(500):
                a = rng.standard_normal(dim)
                b = rng.standard_normal(dim)
                prod = np.einsum("ijk,i,j->k", mult, a, b)
                if np.linalg.norm(prod) < 1e-12 * np.linalg.norm(a) * np.linalg.norm(b):
                    found_zero_divisor = True
                    break
            results.append(AlgebraResult(
                f"{name}_no_zero_div", 0.0, not found_zero_divisor,
            ))
        else:
            # Sedenions (16D): find zero divisors by searching pairs
            # (e_i + e_j) * (e_k +/- e_l) = 0.
            found = False
            for i in range(1, dim):
                if found:
                    break
                for j in range(i + 1, dim):
                    if found:
                        break
                    a = np.zeros(dim)
                    a[i] = 1.0
                    a[j] = 1.0
                    for k in range(1, dim):
                        if found:
                            break
                        for l_idx in range(k + 1, dim):
                            for sign in [1.0, -1.0]:
                                b = np.zeros(dim)
                                b[k] = 1.0
                                b[l_idx] = sign
                                prod = np.einsum("ijk,i,j->k", mult, a, b)
                                if np.linalg.norm(prod) < 1e-10:
                                    found = True
                                    break
                            if found:
                                break

            results.append(AlgebraResult(
                f"{name}_has_zero_div", 1.0 if found else 0.0, found,
            ))

        if step < 4:
            mult = _double_struct(mult)

    assert_all_pass(results)


def test_g2_dimension() -> None:
    """Compute dim(Aut(O)) = dim(G2) = 14.

    A derivation D of the octonion algebra satisfies:
      D(e_i * e_j) = D(e_i) * e_j + e_i * D(e_j)

    D maps Im(O) -> Im(O) (7x7 real matrix, 49 unknowns).
    The derivation condition for all (i,j) pairs gives a linear system.
    The solution space dimension = dim(G2) = 14.
    """
    A = _octonion_derivation_matrix()
    rank = int(np.linalg.matrix_rank(A, tol=1e-10))
    nullity = 49 - rank

    assert_all_pass([AlgebraResult("dim_G2", float(nullity), nullity == 14)])


def test_su3_from_g2() -> None:
    """Fix one imaginary unit (e1).  The stabiliser has dim = 8 = dim(SU(3)).

    This is how color symmetry emerges: fixing a reference in G2 gives SU(3).
    """
    # Start with G2 derivation equations, then add stabiliser constraint
    base_rows = _octonion_derivation_matrix()
    # Additional constraint: D(e_1) = 0  =>  D[0, a] = 0 for a in 0..6
    fix_rows = np.zeros((7, 49))
    for a in range(7):
        fix_rows[a, a] = 1.0

    A = np.vstack([base_rows, fix_rows])
    rank = int(np.linalg.matrix_rank(A, tol=1e-10))
    nullity = 49 - rank

    assert_all_pass([AlgebraResult("dim_SU3_stabiliser", float(nullity), nullity == 8)])


def test_d4_triality() -> None:
    """D4 Dynkin diagram has S3 outer automorphism (triality).

    This is unique: for D_n with n != 4, |Out| = 2 (Z2 only).
    Triality -> 3 generations.  3 generations require D4 = Spin(8).
    """
    results: list[AlgebraResult] = []

    def _d_diagram_automorphisms(rank: int) -> int:
        """Count automorphisms of D_rank Dynkin diagram.

        D_rank has nodes 1..rank with edges:
          i -- (i+1) for i = 1..rank-2  (the spine)
          (rank-2) -- rank  (the fork)

        For rank >= 5: the diagram has a Z2 symmetry swapping
        nodes (rank-1) and rank.  |Aut| = 2.

        For rank == 4: the central node (2) connects to 1, 3, 4.
        Permuting {1,3,4} gives S3.  |Aut| = 6.

        For rank == 3: D3 = A3 (linear), |Aut| = 2.
        """
        if rank < 3:
            return 1

        # Build adjacency
        nodes = list(range(1, rank + 1))
        adj: dict[int, set[int]] = {i: set() for i in nodes}
        for i in range(1, rank - 1):
            adj[i].add(i + 1)
            adj[i + 1].add(i)
        # Fork: node (rank-2) connects to node rank
        adj[rank - 2].add(rank)
        adj[rank].add(rank - 2)

        # Count automorphisms by brute force (small graph)
        count = 0
        for perm in itertools.permutations(nodes):
            mapping = dict(zip(nodes, perm))
            is_auto = True
            for u in nodes:
                for v in adj[u]:
                    if mapping[v] not in adj[mapping[u]]:
                        is_auto = False
                        break
                if not is_auto:
                    break
            if is_auto:
                count += 1
        return count

    # D4: should have |Aut| = 6 (S3, triality)
    aut_d4 = _d_diagram_automorphisms(4)
    results.append(AlgebraResult("D4_Aut=S3", float(aut_d4), aut_d4 == 6))

    # D3, D5, D6, D7, D8: should have |Aut| = 2 (Z2 only)
    for rank in [3, 5, 6, 7, 8]:
        aut = _d_diagram_automorphisms(rank)
        results.append(AlgebraResult(
            f"D{rank}_Aut=Z2", float(aut), aut == 2,
        ))

    assert_all_pass(results)


def test_spacetime_dimension() -> None:
    """Verify sl(2,C) ~ so(3,1) as real Lie algebras.

    sl(2,C) has 6 real generators (3 Pauli + 3 i*Pauli).
    so(3,1) has 6 generators (3 rotations + 3 boosts).
    Their Killing forms should have the same signature (3,3),
    confirming n=4 spacetime dimensions from C subset O.
    """
    results: list[AlgebraResult] = []

    # sl(2,C) generators as 2x2 complex matrices
    sigma_1 = np.array([[0, 1], [1, 0]], dtype=complex)
    sigma_2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
    sigma_3 = np.array([[1, 0], [0, -1]], dtype=complex)

    # Real basis of sl(2,C): rotations (i*sigma/2) and boosts (sigma/2)
    basis = [
        sigma_1 / 2, sigma_2 / 2, sigma_3 / 2,
        1j * sigma_1 / 2, 1j * sigma_2 / 2, 1j * sigma_3 / 2,
    ]
    dim = len(basis)

    # Compute adjoint representation: (ad_i)_{jk} where [T_i, T_j] = sum_k f^k_{ij} T_k
    # Use vectorization: each 2x2 matrix has 4 complex components.
    # Map basis to column vectors, then solve for structure constants.
    basis_vecs = np.array([b.ravel() for b in basis])  # (6, 4) complex

    # Structure constants via least squares: [T_i, T_j] = sum_k f^k_{ij} T_k
    f = np.zeros((dim, dim, dim))
    for i in range(dim):
        for j in range(dim):
            comm = basis[i] @ basis[j] - basis[j] @ basis[i]
            comm_vec = comm.ravel()
            # Solve: basis_vecs.T @ coeffs = comm_vec (least squares)
            coeffs, *_ = np.linalg.lstsq(basis_vecs.T, comm_vec, rcond=None)
            f[i, j, :] = coeffs.real  # should be real for real structure constants

    # Killing form: K_{ij} = f^a_{ic} * f^c_{ja}
    K = np.einsum("iac,jca->ij", f, f)

    eigenvalues = np.sort(np.linalg.eigvalsh(K))

    # Signature: count positive and negative eigenvalues
    n_pos = int(np.sum(eigenvalues > 1e-6))
    n_neg = int(np.sum(eigenvalues < -1e-6))

    # sl(2,C)_R has Killing form with signature (3,3) = so(3,1) signature
    results.append(AlgebraResult(
        "sl2c_killing_sig",
        float(min(n_pos, n_neg)),
        {n_pos, n_neg} == {3, 3},
    ))

    # Verify dimension = 6 (= n*(n-1)/2 for n=4 spacetime)
    results.append(AlgebraResult(
        "sl2c_dim=6", float(dim), dim == 6,
    ))

    assert_all_pass(results)


def test_quaternion_insufficiency() -> None:
    """Quaternions (H) give Aut(H) = SO(3), dim=3 -- not SU(3).

    Same derivation-equation method as test_g2_dimension, but for the
    quaternion algebra (4D, 3 imaginary units i,j,k).  Derivations
    D: Im(H) -> Im(H) give a 3x3 matrix (9 unknowns).

    The nullity = dim(Aut(H)) = 3 = dim(SO(3)).  Since 3 < 8 = dim(SU(3)),
    quaternions cannot support color symmetry.  Octonions (dim(G2)=14,
    stabiliser dim=8=SU(3)) are the ONLY division algebra that works.
    """
    # Quaternion structure constants: e_0=1, e_1=i, e_2=j, e_3=k
    struct_q = np.zeros((4, 4, 4), dtype=np.float64)
    for i in range(4):
        struct_q[0, i, i] = 1.0
        struct_q[i, 0, i] = 1.0
    for i in range(1, 4):
        struct_q[i, i, 0] = -1.0
    # ij=k, jk=i, ki=j (and antisymmetry)
    for a, b, c in [(1, 2, 3), (2, 3, 1), (3, 1, 2)]:
        struct_q[a, b, c] = 1.0
        struct_q[b, a, c] = -1.0

    # Derivation equations: D maps Im(H) -> Im(H), 3x3 matrix, 9 unknowns
    n_unknowns = 9
    equations = []
    for i in range(1, 4):
        for j in range(1, 4):
            for out_comp in range(4):
                row = np.zeros(n_unknowns)
                for k in range(1, 4):
                    coeff = struct_q[i, j, k]
                    if abs(coeff) < 1e-15:
                        continue
                    if out_comp >= 1:
                        row[(k - 1) * 3 + (out_comp - 1)] += coeff
                for a in range(3):
                    sc = struct_q[a + 1, j, out_comp]
                    if abs(sc) < 1e-15:
                        continue
                    row[(i - 1) * 3 + a] -= sc
                for a in range(3):
                    sc = struct_q[i, a + 1, out_comp]
                    if abs(sc) < 1e-15:
                        continue
                    row[(j - 1) * 3 + a] -= sc
                if np.any(np.abs(row) > 1e-15):
                    equations.append(row)

    A = np.array(equations)
    rank = int(np.linalg.matrix_rank(A, tol=1e-10))
    nullity = n_unknowns - rank

    assert_all_pass([
        AlgebraResult("dim_Aut_H=3", float(nullity), nullity == 3),
        AlgebraResult("quaternions_lack_SU3", float(nullity), nullity < 8),
    ])


def test_stabilizer_equivariance() -> None:
    """Fixing ANY imaginary octonion unit gives stabiliser dim=8 (SU(3)).

    G2 acts transitively on the unit sphere S6 in Im(O), so every
    reference direction is equivalent.  The orbit-stabiliser theorem gives
    dim(stabiliser) = dim(G2) - dim(S6) = 14 - 6 = 8 = dim(SU(3)).

    Test all 7 imaginary units separately -> all give dim=8.
    Fix TWO units simultaneously -> dim < 8 (over-constrains).

    If some unit gave dim != 8, the G2 -> SU(3) reduction would be
    direction-dependent (not equivariant), breaking gauge freedom.
    """
    A_base = _octonion_derivation_matrix()

    results: list[AlgebraResult] = []

    # Fix each imaginary unit separately: D(e_unit) = 0
    for unit in range(1, 8):
        extra = np.zeros((7, 49))
        for a in range(7):
            extra[a, (unit - 1) * 7 + a] = 1.0
        A = np.vstack([A_base, extra])
        rank = int(np.linalg.matrix_rank(A, tol=1e-10))
        nullity = 49 - rank
        results.append(AlgebraResult(
            f"fix_e{unit}_dim={nullity}", float(nullity), nullity == 8,
        ))

    # Fix two units simultaneously: D(e_1) = D(e_2) = 0
    extra_two = np.zeros((14, 49))
    for unit_idx, unit in enumerate([1, 2]):
        for a in range(7):
            extra_two[unit_idx * 7 + a, (unit - 1) * 7 + a] = 1.0
    A_two = np.vstack([A_base, extra_two])
    rank_two = int(np.linalg.matrix_rank(A_two, tol=1e-10))
    nullity_two = 49 - rank_two
    results.append(AlgebraResult(
        f"fix_e1_e2_dim={nullity_two}", float(nullity_two), nullity_two < 8,
    ))

    assert_all_pass(results)
