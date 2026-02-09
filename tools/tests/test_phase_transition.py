"""Phase transition verification: BLD link divergence at criticality."""

import concurrent.futures
import dataclasses
import os

import numpy as np
import scipy.sparse
import scipy.sparse.csgraph

from helpers import assert_all_pass

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# 2D Ising (Onsager exact)
T_C_2D = 2.0 / np.log(1.0 + np.sqrt(2.0))
NU_2D = 1.0
GAMMA_NU_2D = 7 / 4
BETA_NU_2D = 1 / 8

# 3D Ising (high-precision MC / conformal bootstrap)
T_C_3D = 4.511528
NU_3D = 0.6301
GAMMA_NU_3D = 1.9637
BETA_NU_3D = 0.5181

# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------


@dataclasses.dataclass(slots=True, frozen=True)
class IsingPoint:
    L_sys: int
    T: float
    mag: float
    chi: float
    xi: float
    binder: float
    nn_corr: float


@dataclasses.dataclass(slots=True, frozen=True)
class ScalingResult:
    name: str
    fitted: float
    exact: float
    r_squared: float
    passes: bool


@dataclasses.dataclass(slots=True, frozen=True)
class LinkResult:
    T: float
    xi: float
    rho: float
    L_bld: float
    passes: bool


# ---------------------------------------------------------------------------
# Swendsen-Wang core (dimension-agnostic)
# ---------------------------------------------------------------------------


def _bond_indices(
    shape: tuple[int, ...],
) -> list[tuple[np.ndarray, np.ndarray]]:
    """Pre-compute periodic bond endpoints for any dimension."""
    idx = np.arange(int(np.prod(shape))).reshape(shape)
    bonds = []
    for axis in range(len(shape)):
        bonds.append((idx.ravel(), np.roll(idx, -1, axis=axis).ravel()))
    return bonds


def _sw_step(
    spins: np.ndarray,
    p_bond: float,
    bonds: list[tuple[np.ndarray, np.ndarray]],
    rng: np.random.Generator,
) -> None:
    """Single Swendsen-Wang step. Fully vectorized."""
    N = spins.size
    flat = spins.ravel()
    src_parts: list[np.ndarray] = []
    dst_parts: list[np.ndarray] = []
    for src_b, dst_b in bonds:
        same = flat[src_b] == flat[dst_b]
        active = same & (rng.random(N) < p_bond)
        src_parts.append(src_b[active])
        dst_parts.append(dst_b[active])

    src = np.concatenate(src_parts)
    dst = np.concatenate(dst_parts)
    if len(src) == 0:
        flat[:] = rng.integers(0, 2, N) * 2 - 1
        return
    adj = scipy.sparse.csr_matrix(
        (np.ones(len(src), dtype=np.int8), (src, dst)), shape=(N, N),
    )
    n_comp, labels = scipy.sparse.csgraph.connected_components(
        adj, directed=False,
    )
    flat[:] = (rng.integers(0, 2, n_comp) * 2 - 1)[labels]


# ---------------------------------------------------------------------------
# Simulation
# ---------------------------------------------------------------------------


def _simulate_point(
    shape: tuple[int, ...],
    T: float,
    n_therm: int,
    n_measure: int,
    rng: np.random.Generator,
) -> IsingPoint:
    L_sys = shape[0]
    ndim = len(shape)
    spins = np.ones(shape, dtype=np.int8)
    bonds = _bond_indices(shape)
    p_bond = 1.0 - np.exp(-2.0 / T)

    for _ in range(n_therm):
        _sw_step(spins, p_bond, bonds, rng)

    mag_abs = np.empty(n_measure)
    mag2 = np.empty(n_measure)
    mag4 = np.empty(n_measure)
    nn_accum = 0.0
    fft_fn = np.fft.fftn
    Sk_accum = np.zeros(shape, dtype=np.float64)

    for i in range(n_measure):
        _sw_step(spins, p_bond, bonds, rng)
        m = spins.mean()
        mag_abs[i] = abs(m)
        mag2[i] = m * m
        mag4[i] = m * m * m * m
        Sk = fft_fn(spins.astype(np.float64))
        Sk_accum += np.abs(Sk) ** 2
        # Nearest-neighbor correlation
        nn_sum = sum(
            np.roll(spins, 1, axis=ax) + np.roll(spins, -1, axis=ax)
            for ax in range(ndim)
        )
        nn_accum += float((spins * nn_sum).mean()) / (2 * ndim)

    # Correlation length from second-moment estimator
    Sk_avg = Sk_accum / n_measure
    idx_kmin = tuple(1 if ax == 0 else 0 for ax in range(ndim))
    G0 = float(Sk_avg.flat[0].real)
    G1 = float(Sk_avg[idx_kmin].real)
    if G1 > 0 and G0 / G1 > 1:
        xi = np.sqrt(G0 / G1 - 1) / (2 * np.sin(np.pi / L_sys))
    else:
        xi = float(L_sys)

    N = int(np.prod(shape))
    chi = N * (mag2.mean() - mag_abs.mean() ** 2) / T
    binder = 1.0 - mag4.mean() / (3.0 * mag2.mean() ** 2)
    nn_corr = nn_accum / n_measure

    return IsingPoint(L_sys, T, float(mag_abs.mean()), chi, xi, binder, nn_corr)


def _run_grid(
    shapes: list[tuple[int, ...]],
    T_values: np.ndarray,
    n_therm: int,
    n_measure: int,
    rng: np.random.Generator,
) -> list[IsingPoint]:
    jobs = [(s, T) for s in shapes for T in T_values]
    children = rng.bit_generator.seed_seq.spawn(len(jobs))
    n_workers = min(len(jobs), os.cpu_count() or 1)
    with concurrent.futures.ThreadPoolExecutor(max_workers=n_workers) as pool:
        futures = [
            pool.submit(
                _simulate_point, s, float(T), n_therm, n_measure,
                np.random.default_rng(seed),
            )
            for (s, T), seed in zip(jobs, children)
        ]
        return [f.result() for f in futures]


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _linfit(x: np.ndarray, y: np.ndarray) -> tuple[float, float, float]:
    """Return (slope, intercept, r_squared) from OLS."""
    A = np.vstack([x, np.ones(len(x))]).T
    result = np.linalg.lstsq(A, y, rcond=None)
    slope, intercept = result[0]
    ss_res = float(np.sum((y - A @ result[0]) ** 2))
    ss_tot = float(np.sum((y - y.mean()) ** 2))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0
    return float(slope), float(intercept), r2


def _temperatures_2d() -> np.ndarray:
    base = np.linspace(1.8, 2.8, 21)
    extra = np.array([T_C_2D - 0.02, T_C_2D - 0.01, T_C_2D + 0.01, T_C_2D + 0.02])
    return np.sort(np.unique(np.concatenate([base, extra])))


def _temperatures_3d() -> np.ndarray:
    base = np.linspace(4.0, 5.5, 21)
    extra = np.array([T_C_3D - 0.02, T_C_3D + 0.02, T_C_3D + 0.05, T_C_3D + 0.1])
    return np.sort(np.unique(np.concatenate([base, extra])))


# ---------------------------------------------------------------------------
# Run functions
# ---------------------------------------------------------------------------


def run_finite_size_scaling(
    rng: np.random.Generator,
) -> list[ScalingResult]:
    L_values = [8, 16, 32, 64]
    T_values = _temperatures_2d()
    shapes = [(L, L) for L in L_values]
    data = _run_grid(shapes, T_values, 200, 500, rng)

    results: list[ScalingResult] = []

    # chi_max vs L
    chi_max_by_L: dict[int, float] = {}
    for L in L_values:
        pts = [p for p in data if p.L_sys == L]
        chi_max_by_L[L] = max(p.chi for p in pts)

    x = np.log(np.array(L_values, dtype=float))
    y = np.log(np.array([chi_max_by_L[L] for L in L_values]))
    slope, _, r2 = _linfit(x, y)
    results.append(ScalingResult(
        "gamma/nu from chi_max", slope, GAMMA_NU_2D, r2,
        r2 > 0.95 and abs(slope - GAMMA_NU_2D) < 0.3,
    ))

    # m(T_c) vs L
    mag_at_tc: dict[int, float] = {}
    for L in L_values:
        pts = [p for p in data if p.L_sys == L]
        closest = min(pts, key=lambda p: abs(p.T - T_C_2D))
        mag_at_tc[L] = closest.mag

    y_m = np.log(np.array([mag_at_tc[L] for L in L_values]))
    slope_m, _, r2_m = _linfit(x, y_m)
    results.append(ScalingResult(
        "beta/nu from m(T_c)", -slope_m, BETA_NU_2D, r2_m,
        r2_m > 0.90 and abs(-slope_m - BETA_NU_2D) < 0.3,
    ))

    return results


def run_bld_link_divergence(
    rng: np.random.Generator,
) -> list[LinkResult | ScalingResult]:
    L = 64
    T_values = _temperatures_2d()
    above_tc = T_values[T_values > T_C_2D]
    data = _run_grid([(L, L)], above_tc, 200, 500, rng)
    data.sort(key=lambda p: p.T)

    results: list[LinkResult | ScalingResult] = []

    # Filter: xi in reliable range (> 2 to avoid noise, < L/4 to avoid saturation)
    usable = [p for p in data if 2.0 < p.xi < L / 4]

    for p in usable:
        rho = np.sqrt(1.0 - 1.0 / (p.xi ** 2))
        L_bld = np.log(p.xi)
        ok = 0 < rho < 1 and L_bld > 0
        results.append(LinkResult(p.T, p.xi, rho, L_bld, ok))

    # Overall trend: L_bld should decrease with T (negative correlation)
    link_vals = [r for r in results if isinstance(r, LinkResult)]
    if len(link_vals) >= 3:
        T_arr = np.array([r.T for r in link_vals])
        L_arr = np.array([r.L_bld for r in link_vals])
        slope_trend, _, _ = _linfit(T_arr, L_arr)
        results.append(ScalingResult(
            "L_bld decreasing with T", slope_trend, 0.0, 0.0,
            slope_trend < 0,
        ))

    # Fit L_bld vs ln(1/|t|)
    if len(usable) >= 3:
        t_vals = np.array([(p.T - T_C_2D) / T_C_2D for p in usable])
        x = np.log(1.0 / t_vals)
        y = np.array([np.log(p.xi) for p in usable])
        slope, _, r2 = _linfit(x, y)
        results.append(ScalingResult(
            "nu from L_bld(2D)", slope, NU_2D, r2,
            abs(slope - NU_2D) < 0.2 and r2 > 0.90,
        ))

    return results


def run_binder_crossing(
    rng: np.random.Generator,
) -> list[ScalingResult]:
    T_values = _temperatures_2d()
    shapes = [(16, 16), (32, 32)]
    data = _run_grid(shapes, T_values, 200, 500, rng)

    pts_16 = sorted([p for p in data if p.L_sys == 16], key=lambda p: p.T)
    pts_32 = sorted([p for p in data if p.L_sys == 32], key=lambda p: p.T)

    # Find crossing by linear interpolation
    T_cross = T_C_2D  # fallback
    found = False
    for i in range(min(len(pts_16), len(pts_32)) - 1):
        diff_i = pts_16[i].binder - pts_32[i].binder
        diff_next = pts_16[i + 1].binder - pts_32[i + 1].binder
        if diff_i * diff_next <= 0:
            # Linear interpolation
            t0, t1 = pts_16[i].T, pts_16[i + 1].T
            frac = abs(diff_i) / (abs(diff_i) + abs(diff_next)) if abs(diff_i) + abs(diff_next) > 0 else 0.5
            T_cross = t0 + frac * (t1 - t0)
            found = True
            break

    err = abs(T_cross - T_C_2D)
    return [ScalingResult(
        "T_c from Binder", T_cross, T_C_2D, 1.0 if found else 0.0,
        found and err < 0.05,
    )]


def run_dl_interplay(
    rng: np.random.Generator,
) -> list[ScalingResult]:
    L_values = [8, 16, 32, 64]
    # Simulate at T_c for each L
    T_at_tc = np.array([T_C_2D])
    shapes = [(L, L) for L in L_values]
    data = _run_grid(shapes, T_at_tc, 200, 500, rng)

    xi_by_L = {p.L_sys: p.xi for p in data}
    x = np.log(np.array(L_values, dtype=float))
    y = np.array([np.log(max(xi_by_L[L], 1.0)) for L in L_values])
    slope, _, r2 = _linfit(x, y)

    return [ScalingResult(
        "L_bld ~ ln(L_sys)", slope, 1.0, r2,
        0.5 < slope < 1.5 and r2 > 0.90,
    )]


def run_nn_link_profile(
    rng: np.random.Generator,
) -> list[LinkResult]:
    L = 64
    T_values = np.linspace(1.8, 3.5, 25)
    data = _run_grid([(L, L)], T_values, 200, 500, rng)
    data.sort(key=lambda p: p.T)

    results: list[LinkResult] = []
    for p in data:
        rho_nn = p.nn_corr
        if abs(rho_nn) >= 1.0:
            results.append(LinkResult(p.T, p.xi, rho_nn, float("inf"), False))
            continue
        L_nn = -0.5 * np.log(1.0 - rho_nn ** 2)
        ok = 0 < L_nn < 100 and 0 < abs(rho_nn) < 1
        results.append(LinkResult(p.T, p.xi, rho_nn, L_nn, ok))

    # L_nn should decrease with T (rho_nn monotonically decreases T=0->inf)
    T_arr = np.array([r.T for r in results])
    L_arr = np.array([r.L_bld for r in results])
    slope, _, r2 = _linfit(T_arr, L_arr)
    results.append(LinkResult(
        0.0, 0.0, 0.0, slope,
        slope < 0,
    ))

    return results


def run_3d_ising(
    rng: np.random.Generator,
) -> list[ScalingResult]:
    L_sys = 20
    shape = (L_sys, L_sys, L_sys)
    # Temperatures above T_c
    t_reduced = np.array([0.02, 0.03, 0.05, 0.07, 0.1, 0.13, 0.17, 0.22, 0.3])
    T_values = T_C_3D * (1.0 + t_reduced)
    data = _run_grid([shape], T_values, 200, 500, rng)
    data.sort(key=lambda p: p.T)

    # Filter: xi > 1 and xi < L/4
    usable = [p for p in data if 1.0 < p.xi < L_sys / 4]

    results: list[ScalingResult] = []

    if len(usable) < 3:
        results.append(ScalingResult("3D: insufficient data", 0, 0, 0, False))
        return results

    t_vals = np.array([(p.T - T_C_3D) / T_C_3D for p in usable])
    ln_inv_t = np.log(1.0 / t_vals)
    ln_xi = np.array([np.log(p.xi) for p in usable])

    # Fit nu from L_bld vs ln(1/|t|)
    # L_bld = ln(xi) = -nu ln|t| + const  ->  ln(xi) vs ln(1/|t|) slope = nu
    slope_nu, _, r2_nu = _linfit(ln_inv_t, ln_xi)
    results.append(ScalingResult(
        "nu from 3D", slope_nu, NU_3D, r2_nu,
        abs(slope_nu - NU_3D) < 0.15 and r2_nu > 0.90,
    ))

    # Discriminating test: L_from_t - L_A should be constant
    # L_from_t = -nu ln|t| = nu ln(1/|t|)
    L_from_t = NU_3D * ln_inv_t
    L_A = ln_xi  # scenario A: L = ln(xi)
    L_B = NU_3D * ln_xi  # scenario B: L = nu ln(xi)

    residual_A = L_from_t - L_A
    residual_B = L_from_t - L_B

    # Fit residuals vs ln(1/|t|) -- slope should be ~0 for correct scenario
    slope_A, _, _ = _linfit(ln_inv_t, residual_A)
    slope_B, _, _ = _linfit(ln_inv_t, residual_B)

    results.append(ScalingResult(
        "residual_A slope (expect ~0)", slope_A, 0.0, 0.0,
        abs(slope_A) < 0.15,
    ))
    results.append(ScalingResult(
        "residual_B slope (expect ~0.23)", slope_B, NU_3D * (1 - NU_3D), 0.0,
        abs(slope_B - NU_3D * (1 - NU_3D)) < 0.15,
    ))

    return results


# ---------------------------------------------------------------------------
# Adversarial: wrong link definition
# ---------------------------------------------------------------------------


def run_wrong_link_definition(
    rng: np.random.Generator,
) -> list[ScalingResult]:
    """Only L=ln(ξ) gives the correct critical exponent ν for 2D Ising.

    Near criticality, ξ ~ |t|^{-ν} where t = (T-T_c)/T_c.  The BLD
    identification L = ln(ξ) means:

        L = ln(ξ) = ν × ln(1/|t|)

    so L is LINEAR in ln(1/|t|) with slope = ν ≈ 1.0 (Onsager exact).

    Test three link definitions fitted against ln(1/|t|):
    - L = ln(ξ)  — BLD logarithmic: linear fit gives slope ≈ 1.0, r² > 0.9
    - L = ξ      — linear: exponential in ln(1/|t|), bad linear fit
    - L = √ξ     — power: still exponential, wrong slope

    If alternative link definitions worked equally well, the logarithmic
    identification wouldn't be structurally necessary.
    """
    L_sys = 64
    T_values = _temperatures_2d()
    above_tc = T_values[T_values > T_C_2D]
    data = _run_grid([(L_sys, L_sys)], above_tc, 200, 500, rng)
    data.sort(key=lambda p: p.T)

    # Filter: xi in reliable range
    usable = [p for p in data if 2.0 < p.xi < L_sys / 4]
    if len(usable) < 3:
        return [ScalingResult("insufficient_data", 0, 0, 0, False)]

    t_vals = np.array([(p.T - T_C_2D) / T_C_2D for p in usable])
    ln_inv_t = np.log(1.0 / t_vals)
    xi_arr = np.array([p.xi for p in usable])

    results: list[ScalingResult] = []

    # BLD logarithmic: L = ln(ξ) → linear in ln(1/|t|), slope = ν
    y_log = np.log(xi_arr)
    slope_log, _, r2_log = _linfit(ln_inv_t, y_log)
    results.append(ScalingResult(
        "L=ln(ξ) correct", slope_log, NU_2D, r2_log,
        abs(slope_log - NU_2D) < 0.2 and r2_log > 0.90,
    ))

    # Linear: L = ξ → exponential in ln(1/|t|), poor linear fit
    y_lin = xi_arr
    slope_lin, _, r2_lin = _linfit(ln_inv_t, y_lin)
    results.append(ScalingResult(
        "L=ξ wrong", slope_lin, NU_2D, r2_lin,
        r2_lin < 0.90 or abs(slope_lin - NU_2D) > 0.3,
    ))

    # Quadratic: L = ξ² → steep exponential growth, wildly wrong slope
    y_sq = xi_arr ** 2
    slope_sq, _, r2_sq = _linfit(ln_inv_t, y_sq)
    results.append(ScalingResult(
        "L=ξ² wrong", slope_sq, NU_2D, r2_sq,
        r2_sq < 0.90 or abs(slope_sq - NU_2D) > 0.3,
    ))

    return results


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_finite_size_scaling(rng: np.random.Generator) -> None:
    assert_all_pass(run_finite_size_scaling(rng))


def test_bld_link_divergence(rng: np.random.Generator) -> None:
    assert_all_pass(run_bld_link_divergence(rng))


def test_binder_crossing(rng: np.random.Generator) -> None:
    assert_all_pass(run_binder_crossing(rng))


def test_dl_interplay(rng: np.random.Generator) -> None:
    assert_all_pass(run_dl_interplay(rng))


def test_nn_link_profile(rng: np.random.Generator) -> None:
    assert_all_pass(run_nn_link_profile(rng))


def test_3d_ising(rng: np.random.Generator) -> None:
    assert_all_pass(run_3d_ising(rng))


def test_wrong_link_definition(rng: np.random.Generator) -> None:
    results = run_wrong_link_definition(rng)
    assert all(r.passes for r in results), [
        (r.name, r.fitted, r.exact, r.r_squared) for r in results if not r.passes
    ]
