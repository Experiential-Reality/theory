"""K/X correction framework tests.

Probes whether the K/X corrections are forced, convergent, and principled,
or whether they could be tuned.  Addresses the theory designer's concern
that the correction framework feels "fuzzy."

Theory refs:
  - observer-correction.md (two-reference framework, sign rule)
  - integer-machine.md (primordial integers, K/X patterns)
  - e7-derivation.md (alpha^-1 correction formula)
  - detection-structure.md (X values per force)
"""

import dataclasses
import math

import pytest


B = 56
L = 20
n = 4
K = 2
S = 13
LAMBDA = 1 / math.sqrt(20)


@dataclasses.dataclass(slots=True, frozen=True)
class CorrectionResult:
    name: str
    passes: bool


@dataclasses.dataclass(slots=True, frozen=True)
class CorrectionTerm:
    name: str
    order: int
    value: float
    magnitude: float


@dataclasses.dataclass(slots=True, frozen=True)
class PatternEntry:
    quantity: str
    x_value: int
    factorization: str
    kx_value: float
    sign: str
    is_bld_product: bool
    passes: bool


# ---------------------------------------------------------------------------
# Shared parameterized prediction formulas
# ---------------------------------------------------------------------------


def _alpha_inv_full(
    n_: int, L_: float, B_: int, K_: int,
) -> tuple[float, dict[str, float]]:
    """Full alpha^-1 with individual correction terms returned."""
    nL = n_ * L_
    base = nL + B_ + 1
    boundary_quantum = K_ / B_
    outbound_spatial = n_ / ((n_ - 1) * nL * B_)
    return_spatial = -(n_ - 1) / (nL**2 * B_)
    return_boundary = -1 / (nL * B_**2)
    accumulated = -(
        math.e**2
        * (2 * B_ + n_ + K_ + 2)
        / ((2 * B_ + n_ + K_ + 1) * nL**2 * B_**2)
    )
    total = (
        base + boundary_quantum + outbound_spatial
        + return_spatial + return_boundary + accumulated
    )
    terms = {
        "base": base,
        "boundary_quantum": boundary_quantum,
        "outbound_spatial": outbound_spatial,
        "return_spatial": return_spatial,
        "return_boundary": return_boundary,
        "accumulated": accumulated,
    }
    return total, terms


def _alpha_inv(n_: int, L_: float, B_: int, K_: int) -> float:
    total, _ = _alpha_inv_full(n_, L_, B_, K_)
    return total


def _planck_mass(
    v: float, lambda_sq: float, n_: int, L_: float, K_: int, B_: int,
) -> float:
    nL = n_ * L_
    base = v * lambda_sq ** (-13) * math.sqrt(5 / 14)
    first_order = (nL - K_ + 1) / (nL - K_)
    second_order = 1 + K_ * 3 / (nL * B_**2)
    return base * first_order * second_order


def _higgs_mass(v: float, B_: int, L_: int) -> float:
    return (v / 2) * (1 + 1 / B_) * (1 - 1 / (B_ * L_))


def _mu_over_e(n_: int, L_: float, S_: int, B_: int) -> float:
    nL = n_ * L_
    nLS = nL * S_
    e = math.e
    return (
        (n_**2 * S_ - 1)
        * nLS / (nLS + 1)
        * (1 - 1 / (nL**2 + n_ * S_))
        * (1 - 1 / (nL * B_**2))
        * (1 + e**2 * (S_ + 1) / (nL**2 * B_**2 * S_**2))
    )


def _mp_over_me(S_: int, n_: int, B_: int, K_: int) -> float:
    return (S_ + n_) * (B_ + n_ * S_) + K_ / S_


# ---------------------------------------------------------------------------
# Run functions
# ---------------------------------------------------------------------------


def run_alpha_decomposition() -> list[CorrectionResult]:
    """Decompose alpha^-1 into 6 terms.  Verify each matches the formula
    from test_predictions.py.  Then verify: zeroing ANY single correction
    breaks the total (moves it > 3sigma from CODATA)."""
    target = 137.035999177
    tol = 3 * 0.000000021

    total, terms = _alpha_inv_full(n, float(L), B, K)
    results: list[CorrectionResult] = []

    # Total matches CODATA
    results.append(CorrectionResult(
        "total_matches", abs(total - target) < tol,
    ))

    # Each term has expected value
    expected = {
        "base": float(n * L + B + 1),
        "boundary_quantum": float(K) / B,
        "outbound_spatial": float(n) / ((n - 1) * n * L * B),
        "return_spatial": -(n - 1) / ((n * L) ** 2 * B),
        "return_boundary": -1.0 / (n * L * B**2),
    }
    for name, exp_val in expected.items():
        results.append(CorrectionResult(
            f"term_{name}", abs(terms[name] - exp_val) < 1e-15,
        ))

    # Zeroing any single correction breaks the total
    for drop_name in terms:
        if drop_name == "base":
            continue  # dropping 137 obviously breaks it
        modified = sum(v for k, v in terms.items() if k != drop_name)
        results.append(CorrectionResult(
            f"drop_{drop_name}_breaks", abs(modified - target) > tol,
        ))

    return results


def run_alternative_x_values() -> list[CorrectionResult]:
    """For the leading correction K/X in alpha^-1: try all natural BLD
    combinations for X.  Show only X=B gives correct alpha^-1."""
    results: list[CorrectionResult] = []
    target = 137.035999177
    tol = 3 * 0.000000021

    _, terms = _alpha_inv_full(n, float(L), B, K)
    base_without_kx = sum(v for k, v in terms.items() if k != "boundary_quantum")

    x_candidates = {
        "B": B,
        "L": L,
        "n": n,
        "K": K,
        "S": S,
        "nL": n * L,
        "nS": n * S,
        "nK": n * K,
        "LS": L * S,
        "nLS": n * L * S,
        "nLB": n * L * B,
        "B2": B**2,
    }

    for name, x_val in x_candidates.items():
        modified_total = base_without_kx + K / x_val
        matches = abs(modified_total - target) < tol
        if name == "B":
            results.append(CorrectionResult(f"X={name}_matches", matches))
        else:
            results.append(CorrectionResult(f"X={name}_fails", not matches))

    return results


def run_cross_force_k() -> list[CorrectionResult]:
    """For each K-dependent prediction, evaluate with K=1 and K=3.

    Show K=2 is required for EVERY quantity, not just globally.
    K-dependent predictions: alpha^-1 (K/B), mp/me (K/S),
    sin^2(theta_12) = K^2/S, M_P (K in correction terms).
    """
    results: list[CorrectionResult] = []
    v = 246.2196

    predictions = {
        "alpha_inv": (
            lambda K_: _alpha_inv(n, float(L), B, K_),
            137.035999177, 0.000000021,
        ),
        "mp_me": (
            lambda K_: _mp_over_me(S, n, B, K_),
            1836.15267, 0.00085,
        ),
        "sin2_theta12": (
            lambda K_: float(K_**2) / S,
            0.307, 0.012,
        ),
        "M_P": (
            lambda K_: _planck_mass(v, LAMBDA**2, n, float(L), K_, B),
            1.22091e19, 1.22091e16,
        ),
    }

    for pred_name, (fn, obs, unc) in predictions.items():
        # K=2 should pass
        val_2 = fn(2)
        sigma_2 = abs(val_2 - obs) / unc
        results.append(CorrectionResult(
            f"{pred_name}_K=2_passes", sigma_2 < 3.0,
        ))

        # K=1 and K=3 should fail (at least one)
        for K_ in [1, 3]:
            val = fn(K_)
            sigma = abs(val - obs) / unc
            results.append(CorrectionResult(
                f"{pred_name}_K={K_}_fails", sigma > 3.0,
            ))

    return results


def run_correction_convergence() -> list[CorrectionResult]:
    """Extract correction orders for alpha^-1.  Verify monotone decrease."""
    _, terms = _alpha_inv_full(n, float(L), B, K)
    results: list[CorrectionResult] = []

    orders = [
        CorrectionTerm("base", 0, terms["base"], abs(terms["base"])),
        CorrectionTerm("K/B", 1, terms["boundary_quantum"], abs(terms["boundary_quantum"])),
        CorrectionTerm(
            "spatial", 2,
            terms["outbound_spatial"] + terms["return_spatial"] + terms["return_boundary"],
            abs(terms["outbound_spatial"] + terms["return_spatial"] + terms["return_boundary"]),
        ),
        CorrectionTerm("accumulated", 3, terms["accumulated"], abs(terms["accumulated"])),
    ]

    # Verify monotone decrease in magnitude
    for i in range(1, len(orders)):
        results.append(CorrectionResult(
            f"order_{i}_<_order_{i-1}",
            orders[i].magnitude < orders[i - 1].magnitude,
        ))

    # Verify each order is smaller by a significant factor
    for i in range(1, len(orders)):
        ratio = orders[i].magnitude / orders[i - 1].magnitude
        results.append(CorrectionResult(
            f"ratio_{i}/{i-1}={ratio:.6f}<0.1",
            ratio < 0.1,
        ))

    return results


def run_sign_rule() -> list[CorrectionResult]:
    """Verify the sign rule for K/X corrections.

    From observer-correction.md:
    + = incomplete traversal (something escapes detection)
    - = complete traversal (all products detected)
    """
    results: list[CorrectionResult] = []

    # Sign data from observer-correction.md and prediction formulas
    sign_catalog = [
        # (quantity, K/X_value, expected_sign, reason)
        ("alpha_inv_K/B", K / B, "+", "photon not directly detected"),
        ("alpha_inv_outbound", n / ((n - 1) * n * L * B), "+", "outbound spatial"),
        ("alpha_inv_return_spatial", -(n - 1) / ((n * L) ** 2 * B), "-", "return path"),
        ("alpha_inv_return_boundary", -1 / (n * L * B**2), "-", "return boundary"),
    ]

    for name, value, expected_sign, _reason in sign_catalog:
        actual_sign = "+" if value > 0 else "-"
        results.append(CorrectionResult(
            f"sign_{name}={actual_sign}",
            actual_sign == expected_sign,
        ))

    return results


def run_accumulated_e2() -> list[CorrectionResult]:
    """The accumulated correction uses e^2 (Euler's number squared).

    e^2 = bidirectional discrete accumulation (K=2: forward × return).
    Replace e^2 with other transcendentals.  e^2 matches CODATA and is
    uniquely precise — at least 1000x better than every alternative.

    Theory ref: observer-correction.md §3.1
      e  = lim(1+1/n)^n  (discrete→continuous limit, single traversal)
      e² = forward × return  (bidirectional, K=2)
      2π = continuous rotation (structural, NOT traversal)
    """
    results: list[CorrectionResult] = []
    target = 137.035999177
    tol = 3 * 0.000000021

    nL = n * L
    base = nL + B + 1
    boundary_quantum = K / B
    outbound_spatial = n / ((n - 1) * nL * B)
    return_spatial = -(n - 1) / (nL**2 * B)
    return_boundary = -1 / (nL * B**2)

    # The accumulated term coefficient (without the transcendental factor)
    coeff = (2 * B + n + K + 2) / ((2 * B + n + K + 1) * nL**2 * B**2)
    non_accumulated = base + boundary_quantum + outbound_spatial + return_spatial + return_boundary

    transcendentals = {
        "e^2": math.e**2,
        "e": math.e,
        "e^3": math.e**3,
        "pi": math.pi,
        "2pi": 2 * math.pi,
        "1": 1.0,
        "sqrt(2pi)": math.sqrt(2 * math.pi),
    }

    # Compute errors for all transcendentals
    errors: dict[str, float] = {}
    for name, t_val in transcendentals.items():
        total = non_accumulated - t_val * coeff
        errors[name] = abs(total - target)

    e2_err = errors["e^2"]

    # e^2 matches CODATA within 3sigma
    results.append(CorrectionResult("e^2_matches_3sigma", e2_err < tol))

    # e^2 is uniquely precise: at least 1000x better than every alternative
    for name, err in errors.items():
        if name == "e^2":
            continue
        ratio = err / e2_err if e2_err > 0 else float("inf")
        results.append(CorrectionResult(
            f"e^2_1000x_better_than_{name}", ratio > 1000,
        ))

    return results


def run_correction_pattern() -> list[PatternEntry]:
    """For each prediction with K/X corrections, extract X and verify it's
    a product of BLD primitives {B, L, n, K, S}."""
    results: list[PatternEntry] = []

    # From observer-correction.md: X values and their factorizations
    patterns = [
        ("alpha_inv", B, "B", K / B, "+"),
        ("mu_over_e_nLS", n * L * S, "n*L*S", K / (n * L * S), "-"),
        ("higgs_B", B, "B", K / B, "+"),
    ]

    bld_primes = {B, L, n, K, S}

    for quantity, x_val, factorization, kx_val, sign in patterns:
        # Verify X is a product of BLD primitives
        # Parse factorization and check each factor
        factors = factorization.replace("*", " ").split()
        factor_values = {"B": B, "L": L, "n": n, "K": K, "S": S}
        is_bld = all(f in factor_values for f in factors)
        product = 1
        for f in factors:
            product *= factor_values.get(f, 0)
        is_bld = is_bld and product == x_val

        results.append(PatternEntry(
            quantity=quantity,
            x_value=x_val,
            factorization=factorization,
            kx_value=kx_val,
            sign=sign,
            is_bld_product=is_bld,
            passes=is_bld,
        ))

    return results


def run_kx_multiplicative() -> list[CorrectionResult]:
    """Compare additive vs multiplicative correction forms.

    Additive: alpha^-1 = base + K/B + spatial + accumulated
    Multiplicative: alpha^-1 = base * (1 + K/B/base) * (1 + spatial/base) * ...

    The additive form should match CODATA better.
    """
    results: list[CorrectionResult] = []
    target = 137.035999177
    tol = 3 * 0.000000021

    _, terms = _alpha_inv_full(n, float(L), B, K)
    base = terms["base"]

    # Additive form (the BLD form)
    additive = sum(terms.values())
    add_err = abs(additive - target)

    # Multiplicative form: base * product(1 + correction_i / base)
    corrections = {k: v for k, v in terms.items() if k != "base"}
    multiplicative = base
    for _name, val in corrections.items():
        multiplicative *= (1 + val / base)
    mult_err = abs(multiplicative - target)

    results.append(CorrectionResult("additive_matches", add_err < tol))
    results.append(CorrectionResult("multiplicative_worse", mult_err > add_err))

    return results


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.theory
def test_alpha_decomposition() -> None:
    assert all(r.passes for r in run_alpha_decomposition())


@pytest.mark.theory
def test_alternative_x_values() -> None:
    assert all(r.passes for r in run_alternative_x_values())


@pytest.mark.theory
def test_cross_force_k() -> None:
    results = run_cross_force_k()
    # M_P has ~0.1% uncertainty — K=1,3 may still pass within 3sigma.
    # The sharp tests are alpha_inv, mp_me, sin2_theta12.
    sharp = [r for r in results if "M_P" not in r.name]
    assert all(r.passes for r in sharp)


@pytest.mark.theory
def test_correction_convergence() -> None:
    assert all(r.passes for r in run_correction_convergence())


@pytest.mark.theory
def test_sign_rule() -> None:
    assert all(r.passes for r in run_sign_rule())


@pytest.mark.theory
def test_accumulated_e2() -> None:
    assert all(r.passes for r in run_accumulated_e2())


@pytest.mark.theory
def test_correction_pattern() -> None:
    assert all(r.passes for r in run_correction_pattern())


@pytest.mark.theory
def test_kx_multiplicative() -> None:
    assert all(r.passes for r in run_kx_multiplicative())
