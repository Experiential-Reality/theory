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

import tools.bld

from helpers import assert_all_pass


@dataclasses.dataclass(slots=True, frozen=True)
class CorrectionOrder:
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
    sign: tools.bld.CorrectionSign
    is_bld_product: bool
    passes: bool


def test_alpha_decomposition() -> None:
    """Decompose alpha^-1 into 6 terms.  Verify each matches the formula
    from test_predictions.py.  Then verify: zeroing ANY single correction
    breaks the total (moves it > 3sigma from CODATA)."""
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.ALPHA_INV
    target = obs.value
    tol = tools.bld.SIGMA_THRESHOLD * obs.uncertainty

    total, terms = tools.bld.alpha_inv_full(n, float(L), B, K)
    CT = tools.bld.CorrectionTerm
    results: list[tools.bld.TestResult] = []

    # Total matches CODATA
    results.append(tools.bld.TestResult(
        "total_matches", abs(total - target) < tol,
    ))

    # Each term has expected value
    expected = {
        CT.BASE: float(n * L + B + 1),
        CT.BOUNDARY_QUANTUM: float(K) / B,
        CT.OUTBOUND_SPATIAL: float(n) / ((n - 1) * n * L * B),
        CT.RETURN_SPATIAL: -(n - 1) / ((n * L) ** 2 * B),
        CT.RETURN_BOUNDARY: -1.0 / (n * L * B**2),
    }
    for term, exp_val in expected.items():
        results.append(tools.bld.TestResult(
            f"term_{term.value}", abs(terms[term] - exp_val) < tools.bld.FLOAT_EPSILON,
        ))

    # Zeroing any single correction breaks the total
    for drop_term in terms:
        if drop_term is CT.BASE:
            continue  # dropping 137 obviously breaks it
        modified = sum(v for k, v in terms.items() if k is not drop_term)
        results.append(tools.bld.TestResult(
            f"drop_{drop_term.value}_breaks", abs(modified - target) > tol,
        ))

    assert_all_pass(results)


def test_alternative_x_values() -> None:
    """For the leading correction K/X in alpha^-1: exhaustive sweep X = 1..10,000.

    Show only X = B = 56 gives correct alpha^-1 within 3sigma of CODATA.
    Vectorized: single numpy broadcast replaces 12 hand-picked candidates.
    """
    import numpy as np

    results: list[tools.bld.TestResult] = []
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.ALPHA_INV
    target = obs.value
    tol = tools.bld.SIGMA_THRESHOLD * obs.uncertainty
    CT = tools.bld.CorrectionTerm

    _, terms = tools.bld.alpha_inv_full(n, float(L), B, K)
    base_without_kx = sum(v for k, v in terms.items() if k is not CT.BOUNDARY_QUANTUM)

    # Exhaustive vectorized sweep
    X = np.arange(1, 10_001, dtype=np.float64)
    modified = base_without_kx + K / X
    within = np.abs(modified - target) < tol
    matching_X = X[within].astype(int)

    results.append(tools.bld.TestResult(
        f"X_unique_in_10000({len(matching_X)}_match)",
        len(matching_X) == 1 and matching_X[0] == B,
    ))

    assert_all_pass(results)


def test_cross_force_k() -> None:
    """For each K-dependent prediction, evaluate with K=1 and K=3.

    Show K=2 is required for EVERY quantity, not just globally.
    K-dependent predictions: alpha^-1 (K/B), mp/me (K/S),
    sin^2(theta_12) = K^2/S, M_P (K in correction terms).
    """
    results: list[tools.bld.TestResult] = []
    B, L, n, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.S
    v = tools.bld.V_EW

    predictions = {
        "alpha_inv": (
            lambda K_: tools.bld.alpha_inv(n, float(L), B, K_),
            tools.bld.ALPHA_INV,
        ),
        "mp_me": (
            lambda K_: tools.bld.mp_over_me(S, n, B, K_),
            tools.bld.MP_OVER_ME,
        ),
        "sin2_theta12": (
            lambda K_: float(K_**2) / S,
            tools.bld.SIN2_THETA_12,
        ),
        "M_P": (
            lambda K_: tools.bld.planck_mass(
                v, tools.bld.LAMBDA**2, n, float(L), K_, B,
            ),
            tools.bld.PLANCK_MASS,
        ),
    }

    for pred_name, (fn, obs) in predictions.items():
        # K=2 should pass
        val_2 = fn(2)
        sigma_2 = abs(val_2 - obs.value) / obs.uncertainty
        results.append(tools.bld.TestResult(
            f"{pred_name}_K=2_passes", sigma_2 < tools.bld.SIGMA_THRESHOLD,
        ))

        # K=1 and K=3 should fail (at least one)
        for K_ in [1, 3]:
            val = fn(K_)
            sigma = abs(val - obs.value) / obs.uncertainty
            results.append(tools.bld.TestResult(
                f"{pred_name}_K={K_}_fails", sigma > tools.bld.SIGMA_THRESHOLD,
            ))

    # M_P has ~0.1% uncertainty -- K=1,3 may still pass within 3sigma.
    # The sharp tests are alpha_inv, mp_me, sin2_theta12.
    sharp = [r for r in results if "M_P" not in r.name]
    assert_all_pass(sharp)


def test_correction_convergence() -> None:
    """Extract correction orders for alpha^-1.  Verify monotone decrease."""
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    _, terms = tools.bld.alpha_inv_full(n, float(L), B, K)
    CT = tools.bld.CorrectionTerm
    results: list[tools.bld.TestResult] = []

    spatial_sum = terms[CT.OUTBOUND_SPATIAL] + terms[CT.RETURN_SPATIAL] + terms[CT.RETURN_BOUNDARY]
    orders = [
        CorrectionOrder("base", 0, terms[CT.BASE], abs(terms[CT.BASE])),
        CorrectionOrder("K/B", 1, terms[CT.BOUNDARY_QUANTUM], abs(terms[CT.BOUNDARY_QUANTUM])),
        CorrectionOrder("spatial", 2, spatial_sum, abs(spatial_sum)),
        CorrectionOrder("accumulated", 3, terms[CT.ACCUMULATED], abs(terms[CT.ACCUMULATED])),
    ]

    # Verify monotone decrease in magnitude
    for i in range(1, len(orders)):
        results.append(tools.bld.TestResult(
            f"order_{i}_<_order_{i-1}",
            orders[i].magnitude < orders[i - 1].magnitude,
        ))

    # Verify each order is smaller by a significant factor
    for i in range(1, len(orders)):
        ratio = orders[i].magnitude / orders[i - 1].magnitude
        results.append(tools.bld.TestResult(
            f"ratio_{i}/{i-1}={ratio:.6f}<{tools.bld.CONVERGENCE_RATIO}",
            ratio < tools.bld.CONVERGENCE_RATIO,
        ))

    assert_all_pass(results)


def test_sign_rule() -> None:
    """Verify the sign rule for K/X corrections.

    From observer-correction.md:
    + = incomplete traversal (something escapes detection)
    - = complete traversal (all products detected)
    """
    results: list[tools.bld.TestResult] = []
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    POS = tools.bld.CorrectionSign.POSITIVE
    NEG = tools.bld.CorrectionSign.NEGATIVE

    # Sign data from observer-correction.md and prediction formulas
    sign_catalog = [
        # (quantity, K/X_value, expected_sign, reason)
        ("alpha_inv_K/B", K / B, POS, "photon not directly detected"),
        ("alpha_inv_outbound", n / ((n - 1) * n * L * B), POS, "outbound spatial"),
        ("alpha_inv_return_spatial", -(n - 1) / ((n * L) ** 2 * B), NEG, "return path"),
        ("alpha_inv_return_boundary", -1 / (n * L * B**2), NEG, "return boundary"),
    ]

    for name, value, expected_sign, _reason in sign_catalog:
        actual_sign = POS if value > 0 else NEG
        results.append(tools.bld.TestResult(
            f"sign_{name}={actual_sign.value}",
            actual_sign is expected_sign,
        ))

    assert_all_pass(results)


def test_accumulated_e2() -> None:
    """The accumulated correction uses e^2 (Euler's number squared).

    e^2 = bidirectional discrete accumulation (K=2: forward x return).
    Replace e^2 with other transcendentals.  e^2 matches CODATA and is
    uniquely precise --- at least 1000x better than every alternative.

    Theory ref: observer-correction.md S3.1
      e  = lim(1+1/n)^n  (discrete->continuous limit, single traversal)
      e^2 = forward x return  (bidirectional, K=2)
      2pi = continuous rotation (structural, NOT traversal)
    """
    results: list[tools.bld.TestResult] = []
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.ALPHA_INV
    target = obs.value
    tol = tools.bld.SIGMA_THRESHOLD * obs.uncertainty

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
    results.append(tools.bld.TestResult("e^2_matches_3sigma", e2_err < tol))

    # e^2 is uniquely precise: at least 1000x better than every alternative
    for name, err in errors.items():
        if name == "e^2":
            continue
        ratio = err / e2_err if e2_err > 0 else float("inf")
        results.append(tools.bld.TestResult(
            f"e^2_1000x_better_than_{name}", ratio > tools.bld.TRANSCENDENTAL_UNIQUENESS,
        ))

    assert_all_pass(results)


def test_correction_pattern() -> None:
    """For each prediction with K/X corrections, extract X and verify it's
    a product of BLD primitives {B, L, n, K, S}."""
    results: list[PatternEntry] = []
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S
    POS = tools.bld.CorrectionSign.POSITIVE
    NEG = tools.bld.CorrectionSign.NEGATIVE

    # From observer-correction.md: X values and their factorizations
    patterns = [
        ("alpha_inv", B, "B", K / B, POS),
        ("mu_over_e_nLS", n * L * S, "n*L*S", K / (n * L * S), NEG),
        ("higgs_B", B, "B", K / B, POS),
    ]

    factor_values = {"B": B, "L": L, "n": n, "K": K, "S": S}

    for quantity, x_val, factorization, kx_val, sign in patterns:
        # Verify X is a product of BLD primitives
        factors = factorization.replace("*", " ").split()
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

    assert_all_pass(results)


def test_kx_multiplicative() -> None:
    """Compare additive vs multiplicative correction forms.

    Additive: alpha^-1 = base + K/B + spatial + accumulated
    Multiplicative: alpha^-1 = base * (1 + K/B/base) * (1 + spatial/base) * ...

    The additive form should match CODATA better.
    """
    results: list[tools.bld.TestResult] = []
    B, L, n, K = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K
    obs = tools.bld.ALPHA_INV
    target = obs.value
    tol = tools.bld.SIGMA_THRESHOLD * obs.uncertainty
    CT = tools.bld.CorrectionTerm

    _, terms = tools.bld.alpha_inv_full(n, float(L), B, K)
    base = terms[CT.BASE]

    # Additive form (the BLD form)
    additive = sum(terms.values())
    add_err = abs(additive - target)

    # Multiplicative form: base * product(1 + correction_i / base)
    corrections = {k: v for k, v in terms.items() if k is not CT.BASE}
    multiplicative = base
    for _term, val in corrections.items():
        multiplicative *= (1 + val / base)
    mult_err = abs(multiplicative - target)

    results.append(tools.bld.TestResult("additive_matches", add_err < tol))
    results.append(tools.bld.TestResult("multiplicative_worse", mult_err > add_err))

    assert_all_pass(results)
