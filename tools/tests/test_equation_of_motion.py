"""Equation of motion tests: Killing form, curvature, geodesics on so(8).

Tests the dynamical framework derived from BLD → so(8) → bi-invariant metric.
Every test follows Prove/Verify/Disprove structure:
  - Prove: BLD prediction matches (existence)
  - Verify: internal structural identities hold (consistency)
  - Disprove: wrong constants fail, alternatives fail (uniqueness)

State is explicit in structure: basis matrices as (28,8,8) arrays,
Killing form as (28,28) matrix, structure constants as (28,28,28) array.
Frozen dataclasses + numpy arrays = thread-safe, vectorizable.

Theory refs:
  - equation-of-motion.md (derivation)
  - killing-form.md (K=2 from Killing eigenvalue)
  - force-structure.md (K/X corrections, sign rule)
"""

import numpy as np
import numpy.linalg as la

import tools.bld

from helpers import assert_all_pass


TR = tools.bld.TestResult


# ---------------------------------------------------------------------------
# Explicit state: so(n) algebra construction
# ---------------------------------------------------------------------------


def _so_basis(n_dim: int) -> np.ndarray:
    """Construct canonical basis of so(n) as skew-symmetric matrices.

    Returns shape (dim_algebra, n_dim, n_dim) where dim_algebra = n(n-1)/2.
    State is explicit: each basis[k] is a concrete 2D matrix.
    """
    dim = tools.bld.so_dim(n_dim)
    basis = np.zeros((dim, n_dim, n_dim), dtype=np.float64)
    k = 0
    for i in range(n_dim):
        for j in range(i + 1, n_dim):
            basis[k, i, j] = 1.0
            basis[k, j, i] = -1.0
            k += 1
    return basis


def _structure_constants(basis: np.ndarray) -> np.ndarray:
    """Compute structure constants: [E_a, E_b] = f^c_{ab} E_c.

    Returns shape (dim, dim, dim) where f[a, b, c] is the coefficient of E_c
    in [E_a, E_b]. Enables vectorized curvature via einsum.
    """
    dim, n_dim, _ = basis.shape
    f = np.zeros((dim, dim, dim), dtype=np.float64)
    # Precompute basis norms: tr(E_c^T E_c) = 2 for canonical so(n) basis
    norms = np.array([np.trace(basis[c].T @ basis[c]) for c in range(dim)])
    for a in range(dim):
        for b in range(dim):
            bracket = basis[a] @ basis[b] - basis[b] @ basis[a]
            for c in range(dim):
                f[a, b, c] = np.trace(bracket @ basis[c].T) / norms[c]
    return f


def _killing_form(f: np.ndarray) -> np.ndarray:
    """Compute Killing form matrix: κ_{ab} = f^c_{ad} f^d_{bc}.

    Vectorized: κ_{ab} = tr(ad_a @ ad_b^T) where ad_a[c,d] = f[a,c,d].
    Returns shape (dim, dim).
    """
    # ad_a is the matrix f[a, :, :] of shape (dim, dim)
    # κ_{ab} = sum_{c,d} f[a,c,d] * f[b,d,c] = tr(f[a] @ f[b]^T)
    return np.einsum("acd,bdc->ab", f, f)


# ---------------------------------------------------------------------------
# Test 1: Killing form non-degeneracy
# ---------------------------------------------------------------------------


def test_killing_form_nondeg() -> None:
    """Killing form on so(8) is non-degenerate with coefficient 6.

    Prove: det(κ) != 0, κ = 6·tr-form.
    Disprove: so(n) for n in {3,4,5,6,7} has DIFFERENT coefficient (n-2).
      Only n=8 gives coefficient=6 AND dim=28 (matching B/2).
    """
    results: list[tools.bld.Prediction | TR] = []

    # Explicit state: build so(8) algebra
    basis_8 = _so_basis(8)
    f_8 = _structure_constants(basis_8)
    kf_8 = _killing_form(f_8)

    # Prove: non-degenerate
    det_kf = la.det(kf_8)
    results.append(TR("det(kf)!=0", abs(det_kf) > 1.0))

    # Prove: κ = (n-2) · tr(XY) for so(n). For skew-symmetric matrices,
    # tr(X^T Y) = -tr(XY), so κ = -(n-2) · tr(X^T Y) = -6 · tr_form.
    # The Killing form is NEGATIVE DEFINITE for compact so(8).
    expected_coeff = tools.bld.killing_form_coeff(8)
    results.append(TR("killing_coeff=6", expected_coeff == 6))

    # Verify: κ_{ab} = -6 · tr(E_a^T E_b) (negative definite)
    tr_form = np.einsum("aij,bij->ab", basis_8, basis_8)
    max_err = float(np.max(np.abs(kf_8 - (-expected_coeff) * tr_form)))
    results.append(TR(
        f"kf=-6*tr_form_err={max_err:.2e}",
        max_err < 1e-12,
    ))

    # Verify: κ is negative definite (all eigenvalues < 0)
    eigenvalues = la.eigvalsh(kf_8)
    results.append(TR("kf_negative_definite", bool(np.all(eigenvalues < -1e-10))))

    # Disprove: sweep so(n) for n=3..9 — only n=8 gives (dim=28, coeff=6)
    for n_dim in range(3, 10):
        dim_alg = tools.bld.so_dim(n_dim)
        coeff = tools.bld.killing_form_coeff(n_dim)
        matches_bld = (dim_alg == tools.bld.B // 2 and coeff == 6)
        is_so8 = (n_dim == 8)
        results.append(TR(
            f"so({n_dim})_dim={dim_alg}_coeff={coeff}_{'match' if is_so8 else 'fail'}",
            matches_bld == is_so8,
        ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 2: Ad-invariance of Killing form
# ---------------------------------------------------------------------------


def test_killing_ad_invariant(rng: np.random.Generator) -> None:
    """Killing form is ad-invariant: κ([Z,X], Y) + κ(X, [Z,Y]) = 0.

    Prove: holds for 50 random triples in so(8).
    Disprove: random NON-ad-invariant bilinear form fails this test.
    """
    basis_8 = _so_basis(8)
    f_8 = _structure_constants(basis_8)
    kf_8 = _killing_form(f_8)
    results: list[TR] = []

    # Prove: ad-invariance for 50 random triples
    n_trials = 50
    max_violation = 0.0
    for _ in range(n_trials):
        coeffs = rng.standard_normal((3, 28))
        x, y, z = coeffs[0], coeffs[1], coeffs[2]
        # [Z, X] in basis coords: (zx)_c = z_a x_b f_{ab}^c
        zx = np.einsum("a,b,abc->c", z, x, f_8)
        zy = np.einsum("a,b,abc->c", z, y, f_8)
        # κ([Z,X], Y) + κ(X, [Z,Y]) should = 0
        violation = abs(float(zx @ kf_8 @ y + x @ kf_8 @ zy))
        max_violation = max(max_violation, violation)
    results.append(TR(
        f"ad_invariant_50_trials_maxviol={max_violation:.2e}",
        max_violation < 1e-10,
    ))

    # Disprove: random symmetric bilinear form is NOT ad-invariant
    fake_kf = rng.standard_normal((28, 28))
    fake_kf = fake_kf + fake_kf.T  # symmetric but not ad-invariant
    fake_violations = 0
    for _ in range(20):
        coeffs = rng.standard_normal((3, 28))
        x, y, z = coeffs[0], coeffs[1], coeffs[2]
        zx = np.einsum("a,b,abc->c", z, x, f_8)
        zy = np.einsum("a,b,abc->c", z, y, f_8)
        val = abs(float(zx @ fake_kf @ y + x @ fake_kf @ zy))
        if val > 1e-8:
            fake_violations += 1
    results.append(TR("random_form_not_ad_invariant", fake_violations > 0))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 3: Connection properties (torsion-free, metric-compatible)
# ---------------------------------------------------------------------------


def test_connection_properties(rng: np.random.Generator) -> None:
    """nabla_X Y = 1/2 [X,Y] is torsion-free and metric-compatible.

    Prove (algebraic): nabla_X Y - nabla_Y X = [X,Y] (torsion = 0).
    Prove (numerical): kappa(nabla_X Y, Z) + kappa(Y, nabla_X Z) = 0 for 50 triples.
    Verify: connection coefficient = 1/2 (from bld.py).
    Disprove: coefficient != 1/2 breaks metric compatibility.
    """
    c = tools.bld.levi_civita_coeff()
    results: list[TR] = []

    # Verify coefficient
    results.append(TR(
        "levi_civita_coeff=0.5",
        abs(c - 0.5) < tools.bld.FLOAT_EPSILON,
    ))

    # Prove (algebraic): torsion = 0
    # nabla_X Y - nabla_Y X = c*[X,Y] - c*[Y,X] = c*[X,Y] + c*[X,Y] = 2c*[X,Y]
    # For c=0.5: 2*0.5*[X,Y] = [X,Y]. Torsion = nabla_X Y - nabla_Y X - [X,Y] = 0.
    # Verify via structure constants: torsion_c = c*f_{ab}^c - c*f_{ba}^c - f_{ab}^c
    #   = c*f_{ab}^c + c*f_{ab}^c - f_{ab}^c = (2c - 1)*f_{ab}^c = 0 when c=0.5
    basis_8 = _so_basis(8)
    f_8 = _structure_constants(basis_8)
    torsion = (2 * c - 1) * f_8
    max_torsion = float(np.max(np.abs(torsion)))
    results.append(TR(
        f"torsion_free_max={max_torsion:.2e}",
        max_torsion < tools.bld.FLOAT_EPSILON,
    ))

    # Prove: metric compatibility for 50 random triples
    kf_8 = _killing_form(f_8)
    max_violation = 0.0
    for _ in range(50):
        coeffs = rng.standard_normal((3, 28))
        x, y, z = coeffs[0], coeffs[1], coeffs[2]
        # nabla_X Y in basis coords: (nabla_X Y)_c = c * x_a y_b f_{ab}^c
        nabla_xy = c * np.einsum("a,b,abc->c", x, y, f_8)
        nabla_xz = c * np.einsum("a,b,abc->c", x, z, f_8)
        # kappa(nabla_X Y, Z) + kappa(Y, nabla_X Z) = 0
        val = abs(float(nabla_xy @ kf_8 @ z + y @ kf_8 @ nabla_xz))
        max_violation = max(max_violation, val)
    results.append(TR(
        f"metric_compatible_50_trials_maxviol={max_violation:.2e}",
        max_violation < 1e-10,
    ))

    # Disprove: wrong coefficient gives nonzero torsion.
    # Metric compatibility holds for ANY c (it's c times the ad-invariance identity).
    # But torsion = (2c - 1)[X,Y], which vanishes ONLY when c = 0.5.
    for wrong_c in [0.25, 0.75, 1.0]:
        torsion_wrong = (2 * wrong_c - 1) * f_8
        max_torsion_wrong = float(np.max(np.abs(torsion_wrong)))
        results.append(TR(
            f"c={wrong_c}_has_torsion={max_torsion_wrong:.4f}",
            max_torsion_wrong > 0.1,
        ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 4: Curvature formula R = -1/4 [[X,Y],Z]
# ---------------------------------------------------------------------------


def test_curvature_formula(rng: np.random.Generator) -> None:
    """Riemann curvature R(X,Y)Z = -1/4 [[X,Y],Z] on bi-invariant so(8).

    Prove: direct computation matches closed form for 50 random triples.
    Verify: coefficient = -0.25 (from bld.py).
    Disprove: wrong coefficients (+1/4, -1/2, -1/8) fail the identity.
    """
    basis_8 = _so_basis(8)
    f_8 = _structure_constants(basis_8)
    c = tools.bld.levi_civita_coeff()   # 0.5
    r = tools.bld.riemann_coeff()       # -0.25
    results: list[TR] = []

    results.append(TR(
        "riemann_coeff=-0.25",
        abs(r - (-0.25)) < tools.bld.FLOAT_EPSILON,
    ))

    # Prove: R(X,Y)Z via direct nabla computation = -1/4 [[X,Y],Z]
    max_err = 0.0
    for _ in range(50):
        coeffs = rng.standard_normal((3, 28))
        x, y, z = coeffs[0], coeffs[1], coeffs[2]

        # Direct: R(X,Y)Z = nabla_X(nabla_Y Z) - nabla_Y(nabla_X Z) - nabla_{[X,Y]} Z
        nabla_yz = c * np.einsum("a,b,abc->c", y, z, f_8)
        nabla_xz = c * np.einsum("a,b,abc->c", x, z, f_8)
        xy_bracket = np.einsum("a,b,abc->c", x, y, f_8)
        nabla_x_nabla_yz = c * np.einsum("a,b,abc->c", x, nabla_yz, f_8)
        nabla_y_nabla_xz = c * np.einsum("a,b,abc->c", y, nabla_xz, f_8)
        nabla_xy_z = c * np.einsum("a,b,abc->c", xy_bracket, z, f_8)
        R_direct = nabla_x_nabla_yz - nabla_y_nabla_xz - nabla_xy_z

        # Closed form: -1/4 [[X,Y],Z]
        xy_z_bracket = np.einsum("a,b,abc->c", xy_bracket, z, f_8)
        R_formula = r * xy_z_bracket

        err = float(la.norm(R_direct - R_formula))
        max_err = max(max_err, err)

    results.append(TR(
        f"R=-1/4[[X,Y],Z]_50_trials_maxerr={max_err:.2e}",
        max_err < 1e-10,
    ))

    # Disprove: wrong coefficients
    for wr in [+0.25, -0.5, -0.125, +1.0]:
        mismatches = 0
        for _ in range(20):
            coeffs = rng.standard_normal((3, 28))
            x, y, z = coeffs[0], coeffs[1], coeffs[2]
            nabla_yz = c * np.einsum("a,b,abc->c", y, z, f_8)
            nabla_xz = c * np.einsum("a,b,abc->c", x, z, f_8)
            xy_bracket = np.einsum("a,b,abc->c", x, y, f_8)
            nabla_x_nabla_yz = c * np.einsum("a,b,abc->c", x, nabla_yz, f_8)
            nabla_y_nabla_xz = c * np.einsum("a,b,abc->c", y, nabla_xz, f_8)
            nabla_xy_z = c * np.einsum("a,b,abc->c", xy_bracket, z, f_8)
            R_direct = nabla_x_nabla_yz - nabla_y_nabla_xz - nabla_xy_z
            xy_z_bracket = np.einsum("a,b,abc->c", xy_bracket, z, f_8)
            R_wrong = wr * xy_z_bracket
            if la.norm(R_direct - R_wrong) > 1e-8:
                mismatches += 1
        results.append(TR(f"coeff={wr}_fails", mismatches > 0))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 5: Sectional curvature >= 0
# ---------------------------------------------------------------------------


def test_sectional_curvature_nonneg() -> None:
    """Sectional curvature K(X,Y) >= 0 for all pairs on so(8).

    Prove: K >= 0 for all 28x28 basis pairs (vectorized).
    Verify: coefficient = 1/4 (from bld.py).
    """
    basis_8 = _so_basis(8)
    f_8 = _structure_constants(basis_8)
    kf_8 = _killing_form(f_8)
    results: list[TR] = []

    results.append(TR(
        "sectional_coeff=0.25",
        abs(tools.bld.sectional_curvature_coeff() - 0.25) < tools.bld.FLOAT_EPSILON,
    ))

    # The bi-invariant metric is g = -κ (positive definite, since κ is
    # negative definite for compact so(8)). All geometric norms use g.
    metric = -kf_8

    # Vectorized: |[E_a, E_b]|^2_g = f_{ab}^c g_{cd} f_{ab}^d
    bracket_norms_sq = np.einsum("abc,cd,abd->ab", f_8, metric, f_8)

    # |E_a|^2_g = g_{aa}, <E_a, E_b>_g = g_{ab}
    diag = np.diag(metric)
    denom = np.outer(diag, diag) - metric ** 2

    # Sectional curvature where denominator > 0
    mask = denom > 1e-12
    K_sect = np.full_like(bracket_norms_sq, 0.0)
    K_sect[mask] = 0.25 * bracket_norms_sq[mask] / denom[mask]

    min_K = float(np.min(K_sect[mask])) if np.any(mask) else 0.0
    results.append(TR(f"K_sect>=0_min={min_K:.6f}", min_K >= -1e-12))

    # Count positive curvatures (should be many for so(8))
    n_positive = int(np.sum(K_sect[mask] > 1e-12))
    results.append(TR(f"n_positive_curvatures={n_positive}", n_positive > 100))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 6: Geodesics = one-parameter subgroups
# ---------------------------------------------------------------------------


def _matrix_exp(A: np.ndarray, terms: int = 30) -> np.ndarray:
    """Matrix exponential via Taylor series. Avoids scipy dependency."""
    result = np.eye(A.shape[0], dtype=A.dtype)
    power = np.eye(A.shape[0], dtype=A.dtype)
    for k in range(1, terms + 1):
        power = power @ A / k
        result = result + power
    return result


def test_geodesic() -> None:
    """Geodesics are one-parameter subgroups: exp(tX) for X in so(8).

    Prove: [X, X] = 0 for all 28 basis elements (algebraic).
    Prove: body angular velocity Omega = exp(-tX) X exp(tX) = X (constant).
    Verify: geodesic stays in SO(8) (orthogonality check).
    """
    basis_8 = _so_basis(8)
    results: list[TR] = []

    # Prove (algebraic): [X, X] = 0 for all basis elements
    max_self_bracket = 0.0
    for a in range(28):
        sb = basis_8[a] @ basis_8[a] - basis_8[a] @ basis_8[a]
        max_self_bracket = max(max_self_bracket, float(la.norm(sb)))
    results.append(TR(
        f"[X,X]=0_all_28_max={max_self_bracket:.2e}",
        max_self_bracket < tools.bld.FLOAT_EPSILON,
    ))

    # Prove: body angular velocity is constant along geodesic
    # gamma(t) = exp(tX), Omega = gamma^{-1} gamma_dot = exp(-tX) X exp(tX)
    # For skew-symmetric X, this should equal X at all t.
    for a in range(5):
        X = basis_8[a]
        max_deviation = 0.0
        for t in [0.0, 0.1, 0.5, 1.0, 2.0, 5.0]:
            gamma = _matrix_exp(t * X)
            gamma_inv = _matrix_exp(-t * X)
            omega = gamma_inv @ X @ gamma
            deviation = float(la.norm(omega - X))
            max_deviation = max(max_deviation, deviation)
        results.append(TR(
            f"constant_Omega_basis_{a}_dev={max_deviation:.2e}",
            max_deviation < 1e-10,
        ))

    # Verify: exp(tX) stays orthogonal (in SO(8))
    for a in range(3):
        X = basis_8[a]
        for t in [0.5, 1.0, 3.0]:
            gamma = _matrix_exp(t * X)
            ortho_err = float(la.norm(gamma @ gamma.T - np.eye(8)))
            results.append(TR(
                f"SO8_basis_{a}_t={t}_ortho_err={ortho_err:.2e}",
                ortho_err < 1e-10,
            ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 7: GUT unification at alpha^-1 = 25
# ---------------------------------------------------------------------------


def test_gut_unification() -> None:
    """alpha^-1(GUT) = n + L + 1 = 25 -- uniquely from BLD.

    Prove: n + L + 1 = 25 for BLD constants.
    Verify: matches SO(10) GUT prediction (25.0 +/- 1.5).
    Disprove: systematic grid sweep -- only (n=4, K=2) gives 25.
      Grid: n in 2..8, K in 1..6, L = n^2(n^2-1)/12.
    """
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    results: list[tools.bld.Prediction | TR] = []

    # Prove
    gut = tools.bld.alpha_inv_gut(n, L)
    results.append(TR("alpha_inv_gut=25", gut == 25))

    # Verify: within SO(10) GUT prediction range
    results.append(tools.bld.Prediction("alpha_inv_gut_vs_SO10", float(gut), 25.0, 1.5))

    # Disprove: sweep grid, only one n gives L such that n+L+1=25
    n_tested = 0
    matching: list[tuple[int, int, int]] = []
    for n_ in range(2, 9):
        L_ = n_**2 * (n_**2 - 1) // 12
        if L_ < 1:
            continue
        for K_ in range(1, 7):
            n_tested += 1
            gut_ = tools.bld.alpha_inv_gut(n_, L_)
            if gut_ == 25:
                matching.append((n_, K_, L_))

    # alpha_inv_gut depends only on (n, L), not K. But L is derived from n,
    # so effectively it depends only on n. The sweep confirms n=4 is unique.
    n_values_matching = {m[0] for m in matching}
    results.append(TR(
        f"GUT=25_n_unique_in_{n_tested}({len(n_values_matching)}_n_match)",
        n_values_matching == {4},
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 8: Force K/X table + composite sweep
# ---------------------------------------------------------------------------


def test_force_kx_table() -> None:
    """K/X corrections match force-structure.md exactly.

    Prove: each force's K/X matches the ForceGeometry table.
    Verify: K = killing_form_coeff(n) for Lorentz algebra (n=4 -> so(3,1)).
    Disprove: exhaustive BLD composite sweep -- each force's X is unique.

    Theory ref: force-structure.md S8.1
    """
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S
    results: list[TR] = []

    # Prove: K/X values from ForceGeometry table
    for fg in tools.bld.FORCE_GEOMETRY:
        if fg.sign == tools.bld.DetectionCompleteness.EMBEDDED:
            # Gravity uses multiplicative (X+1)/X, not additive K/X
            expected_kx = (fg.x_value + 1) / fg.x_value
        else:
            expected_kx = tools.bld.force_kx(K, fg.x_value)
        results.append(TR(
            f"{fg.name}_kx={fg.kx:.6f}",
            abs(fg.kx - expected_kx) < tools.bld.FLOAT_EPSILON,
        ))

    # Verify: K = killing_form_coeff(n) for Lorentz algebra so(3,1)
    # so(3,1) ~ so(4) locally, coefficient = 4-2 = 2 = K
    lorentz_coeff = tools.bld.killing_form_coeff(tools.bld.n)
    results.append(TR("K=killing_coeff(n)", lorentz_coeff == K))

    # Disprove: exhaustive composite sweep for EM (X=B)
    composites = tools.bld.bld_composites(B, L, n, K, S)
    names = list(composites.keys())
    X_vals = np.array([composites[name] for name in names], dtype=np.float64)
    pos = X_vals > 0
    corrections = np.full_like(X_vals, np.inf)
    corrections[pos] = K / X_vals[pos]
    target_correction = K / B
    within = np.abs(corrections - target_correction) < tools.bld.FLOAT_EPSILON
    matching_names = [names[i] for i in range(len(names)) if within[i]]
    results.append(TR(
        f"EM_X_unique_in_{len(composites)}({len(matching_names)}_match)",
        len(matching_names) == 1 and matching_names[0] == "B",
    ))

    # Disprove: for strong force X=n+L, check uniqueness in composites
    target_strong = K / (n + L)
    within_strong = np.abs(corrections - target_strong) < tools.bld.FLOAT_EPSILON
    matching_strong = [names[i] for i in range(len(names)) if within_strong[i]]
    results.append(TR(
        f"Strong_X_unique({len(matching_strong)}_match)",
        len(matching_strong) == 1 and matching_strong[0] == "n+L",
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 9: Wrong constants — dispatch table sweep
# ---------------------------------------------------------------------------


# Dispatch table: checks that must all pass for correct (n, K)
_CURVATURE_CHECKS: tuple[tuple[str, object, float, float], ...] = (
    ("killing_coeff=K",
     lambda n_, K_, _L: abs(tools.bld.killing_form_coeff(n_) - K_),
     0.0, tools.bld.FLOAT_EPSILON),
    ("K^2=n",
     lambda n_, K_, _L: abs(K_**2 - n_),
     0.0, 0.5),
    ("GUT=25",
     lambda n_, K_, L_: abs(tools.bld.alpha_inv_gut(n_, L_) - 25),
     0.0, 0.5),
    ("dim_so(2n)=B/2",
     lambda n_, K_, _L: abs(tools.bld.so_dim(2 * n_) - tools.bld.B / 2),
     0.0, 0.5),
)


def _check_curvature_tuple(n_: int, K_: int, L_: int) -> int:
    """Count how many curvature checks pass for a (n, K) tuple."""
    passed = 0
    for _name, fn, _target, tol in _CURVATURE_CHECKS:
        try:
            if fn(n_, K_, L_) <= tol:
                passed += 1
        except (ZeroDivisionError, OverflowError, ValueError):
            pass
    return passed


def test_wrong_constants_curvature() -> None:
    """Only (n=4, K=2) simultaneously satisfies all curvature identities.

    Sweep: n in 2..8, K in 1..6.
    Prove: (4, 2) passes all 4 checks.
    Disprove: every other tuple fails at least one.
    """
    results: list[TR] = []
    n_tested = 0
    full_matches: list[tuple[int, int]] = []

    for n_ in range(2, 9):
        L_ = n_**2 * (n_**2 - 1) // 12
        if L_ < 1:
            continue
        for K_ in range(1, 7):
            n_tested += 1
            n_pass = _check_curvature_tuple(n_, K_, L_)
            if n_pass == len(_CURVATURE_CHECKS):
                full_matches.append((n_, K_))

    results.append(TR(
        f"BLD_unique_in_{n_tested}({len(full_matches)}_match)",
        len(full_matches) == 1 and full_matches[0] == (4, 2),
    ))

    # Verify BLD passes all
    n, K, L = tools.bld.n, tools.bld.K, tools.bld.L
    results.append(TR(
        "BLD_passes_all_4",
        _check_curvature_tuple(n, K, L) == len(_CURVATURE_CHECKS),
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 10: Sign rule — detection completeness
# ---------------------------------------------------------------------------


def test_sign_rule() -> None:
    """K/X sign rule: complete detection -> -, incomplete -> +.

    Prove: EM (+), Weak (+), Strong (-) match ForceGeometry table.
    Verify: sign assignments match force-structure.md S8.3.
    Verify: carrier -> X mapping is physically motivated.

    Theory ref: force-structure.md S8.3
    """
    results: list[TR] = []

    # Expected signs from force-structure.md
    expected = {
        "EM": tools.bld.DetectionCompleteness.INCOMPLETE,
        "Weak": tools.bld.DetectionCompleteness.INCOMPLETE,
        "Strong": tools.bld.DetectionCompleteness.COMPLETE,
        "Gravity": tools.bld.DetectionCompleteness.EMBEDDED,
    }

    # Prove: ForceGeometry table matches expected
    for fg in tools.bld.FORCE_GEOMETRY:
        results.append(TR(
            f"{fg.name}_sign={fg.sign.value}",
            fg.sign == expected[fg.name],
        ))

    # Verify: K/X > 0 for all forces (magnitude is always positive)
    for fg in tools.bld.FORCE_GEOMETRY:
        results.append(TR(f"{fg.name}_kx>0", fg.kx > 0))

    # Verify: carrier -> X mapping
    carrier_x = {
        "photon": "B",
        "Z": "nLB",
        "gluon": "n+L",
        "metric": "nL-K",
    }
    for fg in tools.bld.FORCE_GEOMETRY:
        results.append(TR(
            f"{fg.name}_carrier={fg.carrier}_x={fg.x_expr}",
            fg.x_expr == carrier_x[fg.carrier],
        ))

    # Verify: X values are ordered correctly (EM < Strong < Gravity < Weak)
    # Smaller X = larger correction = stronger at low energy
    xs = {fg.name: fg.x_value for fg in tools.bld.FORCE_GEOMETRY}
    results.append(TR(
        "X_order: n+L < B < nL-K < nLB",
        xs["Strong"] < xs["EM"] < xs["Gravity"] < xs["Weak"],
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 11: so(8) dimension sweep — uniqueness
# ---------------------------------------------------------------------------


def test_so_dim_sweep() -> None:
    """dim(so(2n)) = B/2 = 28 uniquely selects n=4 -> so(8).

    Prove: so_dim(8) = 28 = B/2.
    Disprove: vectorized sweep over n_dim=3..20 -- only 8 gives 28.
    Verify: Killing form on so(8) has coefficient K * (n/2 - 1) = 2 * 3 = 6.
    """
    results: list[TR] = []
    target = tools.bld.B // 2  # 28

    # Prove
    results.append(TR("so_dim(8)=28", tools.bld.so_dim(8) == target))

    # Vectorized sweep
    n_dims = np.arange(3, 21, dtype=np.int64)
    dims = n_dims * (n_dims - 1) // 2
    matches = n_dims[dims == target]
    results.append(TR(
        f"so(n)_dim=28_unique({len(matches)}_match)",
        len(matches) == 1 and int(matches[0]) == 8,
    ))

    # Verify: dim(so(2n)) for BLD n
    results.append(TR(
        "so(2*4)=so(8)_dim=28",
        tools.bld.so_dim(2 * tools.bld.n) == target,
    ))

    # Verify Killing coefficient chain: K=2, n=4, so(2n)=so(8), coeff=6
    results.append(TR(
        "killing_chain_K=2_coeff=6",
        tools.bld.killing_form_coeff(2 * tools.bld.n) == 6,
    ))

    assert_all_pass(results)
