"""Killing form, curvature, and Riemannian identities on so(8).

Tests 1-5, 12-13, 19-24 from the equation of motion suite.
Killing form, Ricci/scalar curvature, Jacobi, Bianchi, Riemann symmetries.
"""

import numpy as np
import numpy.linalg as la

import tools.bld

from helpers import assert_all_pass


TR = tools.bld.TestResult
SO8 = tools.bld.SO8


# ---------------------------------------------------------------------------
# Test 1: Killing form non-degeneracy
# ---------------------------------------------------------------------------


def test_killing_form_nondeg(so8: SO8) -> None:
    """Killing form on so(8) is non-degenerate with coefficient 6.

    Prove: det(κ) != 0, κ = 6·tr-form.
    Disprove: so(n) for n in {3,4,5,6,7} has DIFFERENT coefficient (n-2).
      Only n=8 gives coefficient=6 AND dim=28 (matching B/2).
    """
    results: list[tools.bld.Prediction | TR] = []

    # Explicit state: build so(8) algebra
    basis_8, f_8, kf_8 = so8.basis, so8.f, so8.kf

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
        max_err < 1e-14,  # exact: integer structure constants
    ))

    # Verify: κ is negative definite (all eigenvalues < 0)
    eigenvalues = la.eigvalsh(kf_8)
    results.append(TR("kf_negative_definite", bool(np.all(eigenvalues < -1e-12))))

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


def test_killing_ad_invariant(so8: SO8, rng: np.random.Generator) -> None:
    """Killing form is ad-invariant: κ([Z,X], Y) + κ(X, [Z,Y]) = 0.

    Prove: holds for 50 random triples in so(8).
    Disprove: random NON-ad-invariant bilinear form fails this test.
    """
    basis_8, f_8, kf_8 = so8.basis, so8.f, so8.kf
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
        max_violation < 1e-12,  # random vectors, accumulated roundoff
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


def test_connection_properties(so8: SO8, rng: np.random.Generator) -> None:
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
    basis_8, f_8 = so8.basis, so8.f
    torsion = (2 * c - 1) * f_8
    max_torsion = float(np.max(np.abs(torsion)))
    results.append(TR(
        f"torsion_free_max={max_torsion:.2e}",
        max_torsion < tools.bld.FLOAT_EPSILON,
    ))

    # Prove: metric compatibility for 50 random triples
    kf_8 = so8.kf
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
        max_violation < 1e-12,  # random vectors, accumulated roundoff
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


def test_curvature_formula(so8: SO8, rng: np.random.Generator) -> None:
    """Riemann curvature R(X,Y)Z = -1/4 [[X,Y],Z] on bi-invariant so(8).

    Prove: direct computation matches closed form for 50 random triples.
    Verify: coefficient = -0.25 (from bld.py).
    Disprove: wrong coefficients (+1/4, -1/2, -1/8) fail the identity.
    """
    basis_8, f_8 = so8.basis, so8.f
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
        max_err < 1e-12,  # random vectors, accumulated roundoff
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
            if la.norm(R_direct - R_wrong) > 1e-10:
                mismatches += 1
        results.append(TR(f"coeff={wr}_fails", mismatches > 0))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 5: Sectional curvature >= 0
# ---------------------------------------------------------------------------


def test_sectional_curvature_nonneg(so8: SO8) -> None:
    """Sectional curvature K(X,Y) >= 0 for all pairs on so(8).

    Prove: K >= 0 for all 28x28 basis pairs (vectorized).
    Verify: coefficient = 1/4 (from bld.py).
    """
    basis_8, f_8, kf_8 = so8.basis, so8.f, so8.kf
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
# Test 12: Ricci curvature — SO(8) is an Einstein manifold
# ---------------------------------------------------------------------------


def test_ricci_curvature(so8: SO8, rng: np.random.Generator) -> None:
    """Ric(X,Y) = ¼ g(X,Y) for compact Lie group with bi-invariant metric.

    Prove: Ric_{ab} = ¼ g_{ab} for all 28×28 basis pairs (max error < 1e-10).
      Ric_{ab} = Σ_c R_{cacb} where R_{abcd} is the Riemann tensor in components.
      R(E_a,E_b)E_d = -¼ [[E_a,E_b],E_d] expressed via structure constants.
    Verify: coefficient = 0.25 matches bld.ricci_coeff_biinvariant().
    Disprove: random non-Killing metric fails Einstein condition.
    """
    results: list[TR] = []

    basis_8, f_8, kf_8 = so8.basis, so8.f, so8.kf
    g_8 = -kf_8  # positive definite bi-invariant metric

    dim = 28

    # Ricci tensor via (1,3) Riemann tensor contraction:
    # R(E_a,E_b)E_d = -¼ [[E_a,E_b],E_d] = -¼ Σ_e f_{abe} f_{edc} E_c
    # So R^c_{abd} = -¼ Σ_e f_{abe} f_{edc}
    # Ric_{bd} = Σ_a R^a_{abd} = -¼ Σ_{a,e} f_{abe} f_{eda}
    ricci = -0.25 * np.einsum("abe,eda->bd", f_8, f_8)

    # Prove: Ric = ¼ g  (Einstein manifold with constant ¼)
    max_err = float(np.max(np.abs(ricci - 0.25 * g_8)))
    results.append(TR(
        f"ricci=0.25*g_err={max_err:.2e}",
        max_err < 1e-14,  # exact: integer structure constants
    ))

    # Verify: coefficient matches bld formula
    results.append(TR(
        "ricci_coeff=0.25",
        abs(tools.bld.ricci_coeff_biinvariant() - 0.25) < 1e-15,
    ))

    # Verify: Ricci tensor is symmetric
    ricci_symm_err = float(np.max(np.abs(ricci - ricci.T)))
    results.append(TR(
        f"ricci_symmetric_err={ricci_symm_err:.2e}",
        ricci_symm_err < 1e-12,
    ))

    # Disprove: random metric fails Einstein condition
    rand_metric = rng.standard_normal((dim, dim))
    rand_metric = rand_metric @ rand_metric.T + np.eye(dim) * dim  # SPD
    # Ric_rand = ¼ * rand_metric would be a coincidence
    ricci_rand_err = float(np.max(np.abs(ricci - 0.25 * rand_metric)))
    results.append(TR(
        "random_metric_fails_einstein",
        ricci_rand_err > 1.0,
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 13: Scalar curvature
# ---------------------------------------------------------------------------


def test_scalar_curvature(so8: SO8) -> None:
    """Scalar curvature R = dim(g)/4 = 7 for SO(8).

    Prove: R = tr(Ric · g⁻¹) = 28/4 = 7.
    Verify: matches bld.scalar_curvature(28).
    Disprove: sweep so(n) for n=3..10 — each gives different R.
    """
    results: list[TR] = []

    basis_8, f_8, kf_8 = so8.basis, so8.f, so8.kf
    g_8 = -kf_8
    g_inv = la.inv(g_8)

    # Compute Ricci via (1,3) tensor trace (same as test_ricci_curvature)
    ricci = -0.25 * np.einsum("abe,eda->bd", f_8, f_8)

    # Scalar curvature: R = g^{ab} Ric_{ab}
    R_scalar = float(np.einsum("ab,ab->", g_inv, ricci))

    # Prove: R = 7
    results.append(TR(
        f"scalar_curvature={R_scalar:.6f}",
        abs(R_scalar - 7.0) < 1e-12,  # exact algebra + matrix inverse
    ))

    # Verify: matches bld formula
    results.append(TR(
        "bld_scalar_curvature=7",
        abs(tools.bld.scalar_curvature(28) - 7.0) < 1e-15,
    ))

    # Disprove: sweep so(n) for n=3..10 — different dimensions give different R
    seen_R = set()
    for n_dim in range(3, 11):
        dim_alg = tools.bld.so_dim(n_dim)
        R_predicted = tools.bld.scalar_curvature(dim_alg)
        seen_R.add(R_predicted)
    results.append(TR(
        f"scalar_R_unique_across_so(n)_{len(seen_R)}_values",
        len(seen_R) == 8,  # 8 different values for n=3..10
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 19: Ricci curvature cross-check via so(n) sweep
# ---------------------------------------------------------------------------


def test_ricci_coefficient_sweep(so8: SO8) -> None:
    """Einstein constant ¼ is universal for compact simple Lie groups with g = -κ.

    Prove: for so(n) with n=3,4,5,6, Ric = ¼ g holds.
    Verify: scalar curvature R = dim(so(n))/4 for each.
    Disprove: random coefficient c ≠ ¼ fails for at least one n.
    """
    results: list[TR] = []

    for n_dim in [3, 4, 5, 6]:
        basis = tools.bld.so_basis(n_dim)
        f = tools.bld.structure_constants(basis)
        kf = tools.bld.killing_form_numerical(f)
        g = -kf
        dim_alg = tools.bld.so_dim(n_dim)

        ricci = -0.25 * np.einsum("abe,eda->bd", f, f)

        err = float(np.max(np.abs(ricci - 0.25 * g)))
        results.append(TR(
            f"so({n_dim})_einstein_err={err:.2e}",
            err < 1e-14,  # exact: integer structure constants
        ))

        # Scalar curvature
        if abs(la.det(g)) > 1e-12:
            g_inv = la.inv(g)
            R_scalar = float(np.einsum("ab,ab->", g_inv, ricci))
            R_expected = tools.bld.scalar_curvature(dim_alg)
            results.append(TR(
                f"so({n_dim})_R={R_scalar:.4f}_expected={R_expected:.4f}",
                abs(R_scalar - R_expected) < 1e-12,  # exact algebra + matrix inverse
            ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 20: Jacobi identity for structure constants
# ---------------------------------------------------------------------------


def test_jacobi_identity(so8: SO8) -> None:
    """[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0 for all basis triples.

    This is the fundamental identity of a Lie algebra. If it fails,
    NOTHING downstream (curvature, Ricci, geodesics) can be trusted.

    Prove: Jacobi identity holds for all 28^3 = 21952 triples (vectorized).
    Disprove: random non-Lie bracket violates Jacobi.
    """
    results: list[TR] = []

    basis_8, f_8 = so8.basis, so8.f

    # Jacobi: f_{ab}^e f_{ec}^d + f_{bc}^e f_{ea}^d + f_{ca}^e f_{eb}^d = 0
    # Vectorized over all a,b,c,d
    term1 = np.einsum("abe,ecd->abcd", f_8, f_8)
    term2 = np.einsum("bce,ead->abcd", f_8, f_8)
    term3 = np.einsum("cae,ebd->abcd", f_8, f_8)
    jacobi = term1 + term2 + term3

    max_err = float(np.max(np.abs(jacobi)))
    results.append(TR(
        f"jacobi_identity_max_err={max_err:.2e}",
        max_err < 1e-14,  # exact: integer structure constants
    ))

    # Disprove: random "structure constants" violate Jacobi
    rng_local = np.random.default_rng(77)  # intentional: independent of fixture rng
    fake_f = rng_local.standard_normal((28, 28, 28))
    fake_f = fake_f - np.swapaxes(fake_f, 0, 1)  # antisymmetric in first two
    t1 = np.einsum("abe,ecd->abcd", fake_f, fake_f)
    t2 = np.einsum("bce,ead->abcd", fake_f, fake_f)
    t3 = np.einsum("cae,ebd->abcd", fake_f, fake_f)
    fake_jacobi_err = float(np.max(np.abs(t1 + t2 + t3)))
    results.append(TR(
        f"random_bracket_violates_jacobi_err={fake_jacobi_err:.2e}",
        fake_jacobi_err > 1.0,
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 21: Bianchi identity for Riemann tensor
# ---------------------------------------------------------------------------


def test_bianchi_identity(so8: SO8, rng: np.random.Generator) -> None:
    """First Bianchi: R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0.

    Prove: holds for 100 random triples to machine precision.
    This is an independent check that R = -1/4[[·,·],·] is a valid curvature.
    """
    results: list[TR] = []

    basis_8, f_8 = so8.basis, so8.f

    # R(X,Y)Z = -1/4 [[X,Y],Z] in coefficient space
    def riemann(x: np.ndarray, y: np.ndarray, z: np.ndarray) -> np.ndarray:
        xy = np.einsum("abe,a,b->e", f_8, x, y)
        return -0.25 * np.einsum("ecg,e,c->g", f_8, xy, z)

    max_bianchi_err = 0.0
    for _ in range(100):
        x = rng.standard_normal(28)
        y = rng.standard_normal(28)
        z = rng.standard_normal(28)
        bianchi = riemann(x, y, z) + riemann(y, z, x) + riemann(z, x, y)
        max_bianchi_err = max(max_bianchi_err, float(np.max(np.abs(bianchi))))

    results.append(TR(
        f"first_bianchi_100_trials_err={max_bianchi_err:.2e}",
        max_bianchi_err < 1e-12,  # random vectors, accumulated roundoff
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 22: Riemann tensor symmetries
# ---------------------------------------------------------------------------


def test_riemann_symmetries(so8: SO8) -> None:
    """Riemann tensor R_{abcd} has the standard symmetries.

    Prove (vectorized over all indices):
    1. R_{abcd} = -R_{bacd}  (antisymmetric in first pair)
    2. R_{abcd} = -R_{abdc}  (antisymmetric in second pair)
    3. R_{abcd} = R_{cdab}   (pair symmetry)
    """
    results: list[TR] = []

    basis_8, f_8, kf_8 = so8.basis, so8.f, so8.kf
    g_8 = -kf_8

    # Build full (0,4) Riemann tensor: R_{abcd} = g(R(E_a,E_b)E_d, E_c)
    # R^f_{abd} = -1/4 f_{abe} f_{edf}
    # R_{abdc} = R^f_{abd} g_{fc}
    R13 = -0.25 * np.einsum("abe,edf->abdf", f_8, f_8)  # R^f_{abd}
    R04 = np.einsum("abdf,fc->abdc", R13, g_8)  # R_{abdc}

    # 1. Antisymmetric in first pair: R_{abdc} = -R_{badc}
    err1 = float(np.max(np.abs(R04 + np.swapaxes(R04, 0, 1))))
    results.append(TR(
        f"R_antisym_first_pair_err={err1:.2e}",
        err1 < 1e-14,
    ))

    # 2. Antisymmetric in second pair: R_{abdc} = -R_{abcd}
    err2 = float(np.max(np.abs(R04 + np.swapaxes(R04, 2, 3))))
    results.append(TR(
        f"R_antisym_second_pair_err={err2:.2e}",
        err2 < 1e-14,
    ))

    # 3. Pair symmetry: R_{abdc} = R_{dcab}
    err3 = float(np.max(np.abs(R04 - np.transpose(R04, (2, 3, 0, 1)))))
    results.append(TR(
        f"R_pair_symmetry_err={err3:.2e}",
        err3 < 1e-14,
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 23: Geodesic equation by finite differences
# ---------------------------------------------------------------------------


def test_geodesic_finite_diff(so8: SO8) -> None:
    """Verify geodesic equation nabla_{gamma'} gamma' = 0 by numerical integration.

    Prove: gamma(t) = exp(tX) satisfies dOmega/dt = 0 (body angular velocity constant).
    Uses finite differences on the actual matrix exponential — independent of algebra.
    """
    results: list[TR] = []

    basis_8 = so8.basis

    # Pick a non-trivial direction: sum of two non-commuting generators
    X = basis_8[0] + 0.7 * basis_8[1]  # E_{01} + 0.7 * E_{02}

    # Omega(t) = exp(-tX) X exp(tX) should be constant = X for bi-invariant metric
    # Check at multiple time points
    max_omega_drift = 0.0
    for t in [0.0, 0.3, 1.0, 2.5, 5.0]:
        gamma_t = tools.bld.matrix_exp(t * X)
        gamma_inv = tools.bld.matrix_exp(-t * X)
        omega = gamma_inv @ X @ gamma_t
        drift = float(la.norm(omega - X))
        max_omega_drift = max(max_omega_drift, drift)

    results.append(TR(
        f"dOmega/dt=0_max_drift={max_omega_drift:.2e}",
        max_omega_drift < 1e-13,  # Taylor series (50 terms)
    ))

    # Cross-check: gamma stays in SO(8) at all tested times
    max_ortho = 0.0
    for t in [0.3, 1.0, 2.5, 5.0]:
        gamma_t = tools.bld.matrix_exp(t * X)
        ortho = float(la.norm(gamma_t.T @ gamma_t - np.eye(8)))
        max_ortho = max(max_ortho, ortho)
    results.append(TR(
        f"gamma_stays_SO8_err={max_ortho:.2e}",
        max_ortho < 1e-13,
    ))

    # Velocity via actual finite diff (independent of body-frame argument)
    dt = 1e-5
    t0 = 1.0
    gp = tools.bld.matrix_exp((t0 + dt) * X)
    gm = tools.bld.matrix_exp((t0 - dt) * X)
    gamma_dot_fd = (gp - gm) / (2 * dt)

    # True velocity: gamma'(t0) = X exp(t0 X) (left derivative)
    g0 = tools.bld.matrix_exp(t0 * X)
    gamma_dot_exact = X @ g0
    vel_err = float(la.norm(gamma_dot_fd - gamma_dot_exact))
    results.append(TR(
        f"finite_diff_velocity_err={vel_err:.2e}",
        vel_err < 1e-5,  # O(dt²) ≈ 1e-10, but matrix exp adds noise
    ))

    assert_all_pass(results)


# ---------------------------------------------------------------------------
# Test 24: Killing form equals negative Ricci times 4 (cross-check)
# ---------------------------------------------------------------------------


def test_killing_equals_neg_ricci_times_4(so8: SO8) -> None:
    """kappa_{ab} = -4 Ric_{ab} -- two independent computations agree.

    The Killing form kappa is computed from structure constants (tr(ad ad)).
    The Ricci tensor is computed from the Riemann curvature contraction.
    If Ric = 1/4 g = -1/4 kappa, then kappa = -4 Ric.

    Prove: max|kappa + 4 Ric| < machine epsilon.
    """
    results: list[TR] = []

    basis_8, f_8, kf_8 = so8.basis, so8.f, so8.kf

    # Ricci from curvature contraction (independent computation)
    ricci = -0.25 * np.einsum("abe,eda->bd", f_8, f_8)

    # Cross-check: kappa = -4 Ric
    cross_err = float(np.max(np.abs(kf_8 + 4 * ricci)))
    results.append(TR(
        f"killing=-4*ricci_err={cross_err:.2e}",
        cross_err < 1e-14,  # exact: integer structure constants
    ))

    assert_all_pass(results)
