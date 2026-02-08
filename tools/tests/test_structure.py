"""BLD structural constant tests.

Tests that the constants (B=56, L=20, n=4, K=2, S=13) are forced, unique,
and over-determined.  Each test either verifies a structural claim from the
theory or attempts to disprove it by showing alternatives fail.

Theory refs:
  - bld-calculus.md Proposition 8.5 (mode count)
  - bld-calculus.md Lemma 7.3 (LD cardinality collapse)
  - test_predictions.py (five constant identities)
  - e7-derivation.md (correction formulas)
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
class Prediction:
    name: str
    predicted: float
    observed: float
    uncertainty: float

    @property
    def sigma(self) -> float:
        if self.uncertainty <= 0:
            return 0.0 if abs(self.predicted - self.observed) < 1e-15 else float("inf")
        return abs(self.predicted - self.observed) / self.uncertainty

    @property
    def passes(self) -> bool:
        return self.sigma < 3.0


@dataclasses.dataclass(slots=True, frozen=True)
class StructureResult:
    name: str
    value: float
    passes: bool


# ---------------------------------------------------------------------------
# Shared prediction formulas (parameterized for constant variation)
# ---------------------------------------------------------------------------


def _alpha_inv(n_: int, L_: float, B_: int, K_: int) -> float:
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
    return (
        base + boundary_quantum + outbound_spatial
        + return_spatial + return_boundary + accumulated
    )


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


def run_mode_count() -> list[StructureResult]:
    """Verify mode count: mu(Pi_4(Pi_20(1))) + mu(Sigma_56(1)) + mu(1) = 137.

    bld-calculus.md Definition 8.3:
      mu(1) = 1
      mu(Pi_n(tau)) = n * mu(tau)
      mu(tau1 + tau2) = mu(tau1) + mu(tau2)

    bld-calculus.md Proposition 8.5:
      alpha^-1 = mu(tau_geom) + mu(tau_bound) + mu(tau_trav) = 137
    """
    mu_unit = 1
    mu_geom = n * (L * mu_unit)     # Pi_4(Pi_20(1)) = 4 * 20 * 1 = 80
    mu_bound = B * mu_unit           # Sigma_56(1) = 56 * 1 = 56
    mu_trav = mu_unit                # 1 (traverser type)
    total = mu_geom + mu_bound + mu_trav
    return [StructureResult("mode_count", total, total == 137)]


def run_ld_cardinality_collapse() -> list[StructureResult]:
    """Enumerate LD-calculus types and verify cardinality = 1.

    bld-calculus.md Lemma 7.3: In the LD-calculus (no Sum type), every
    closed inhabited type has cardinality exactly 1.

    LD types are built from:  1, (->), Pi_n  (no Sum/+)
    Cardinality rules:
      |1| = 1
      |Pi_n(tau)| = |tau|^n
      |tau1 -> tau2| = |tau2|^|tau1|

    Since |1| = 1, and 1^anything = 1, all LD types have cardinality 1.
    This is WHY B (Sum) is irreducible: you need it to get cardinality > 1.

    We generate types at each depth from the PREVIOUS depth only (not all
    previous) to keep the count manageable: ~200 types at depth 3.
    """
    results: list[StructureResult] = []

    # Types at each depth: (name, cardinality)
    depth_0: list[tuple[str, int]] = [("1", 1)]
    all_types = list(depth_0)

    prev = depth_0
    for _depth in range(1, 4):
        current: list[tuple[str, int]] = []
        for name_a, card_a in prev:
            for name_b, card_b in prev:
                fn_card = card_b ** card_a if card_a < 100 else card_b
                current.append((f"({name_a}->{name_b})", fn_card))
            for pi_n in [2, 3, 4]:
                pi_card = card_a ** pi_n if card_a < 100 else card_a
                current.append((f"Pi_{pi_n}({name_a})", pi_card))
        all_types.extend(current)
        prev = current

    for type_name, card in all_types:
        results.append(StructureResult(
            f"LD|{type_name}|={card}",
            float(card),
            card == 1,
        ))

    return results


def run_constant_rigidity() -> list[StructureResult]:
    """The five identities form a 1D family parameterised by K.

    Identity 3 (lambda^2 * nL = K^2 with lambda^2 = 1/L) gives n = K^2.
    Identity 5: L = n^2(n^2-1)/12.
    Identity 2: S = K^2 + (n-1)^2.
    Identity 4: B = n(S+1).

    For K in 1..10, compute the unique (n,L,S,B) and evaluate all physics
    predictions.  Show K=2 is the ONLY value matching experiment.
    """
    results: list[StructureResult] = []

    for K_ in range(1, 11):
        n_ = K_**2
        L_ = n_**2 * (n_**2 - 1) / 12
        if L_ < 1:
            continue
        S_ = K_**2 + (n_ - 1) ** 2
        B_ = n_ * (S_ + 1)

        # Alpha inverse
        try:
            alpha = _alpha_inv(n_, L_, B_, K_)
        except (ZeroDivisionError, OverflowError):
            alpha = float("inf")
        alpha_ok = abs(alpha - 137.035999177) < 3 * 0.000000021

        # Mu/e
        try:
            mu_e = _mu_over_e(n_, L_, S_, B_)
        except (ZeroDivisionError, OverflowError):
            mu_e = float("inf")
        mu_e_ok = abs(mu_e - 206.7682827) < 3 * 0.0000005

        # mp/me
        try:
            mp_me = _mp_over_me(S_, n_, B_, K_)
        except (ZeroDivisionError, OverflowError):
            mp_me = float("inf")
        mp_me_ok = abs(mp_me - 1836.15267) < 3 * 0.00085

        all_match = alpha_ok and mu_e_ok and mp_me_ok
        if K_ == 2:
            results.append(StructureResult(f"K={K_}_matches", 1.0, all_match))
        else:
            results.append(StructureResult(f"K={K_}_fails", 0.0, not all_match))

    return results


def run_alternative_137() -> list[StructureResult]:
    """Try all (a,b,c) with a*b + c + 1 = 137, a,b,c > 0.

    Plug into the full alpha^-1 correction formula with n=a, L=b, B=c.
    Show only (4,20,56) gives alpha^-1 matching CODATA.
    """
    results: list[StructureResult] = []
    target = 137.035999177
    tol = 3 * 0.000000021

    for a in range(1, 137):
        for b in range(1, 137):
            c = 136 - a * b
            if c < 1:
                break
            try:
                alpha = _alpha_inv(a, float(b), c, K)
            except (ZeroDivisionError, OverflowError, ValueError):
                alpha = float("inf")
            matches = abs(alpha - target) < tol
            if a == n and b == L and c == B:
                results.append(StructureResult(
                    f"({a},{b},{c})=BLD", alpha, matches,
                ))
            elif matches:
                # Another decomposition also works — would disprove uniqueness
                results.append(StructureResult(
                    f"({a},{b},{c})_unexpected", alpha, False,
                ))

    # Ensure BLD was found
    bld_found = any("BLD" in r.name and r.passes for r in results)
    if not bld_found:
        results.append(StructureResult("BLD_missing", 0.0, False))

    return results


def run_broken_k() -> list[Prediction]:
    """Compute K-dependent predictions with K=1 and K=3.

    Keep all other constants at BLD values (including S=13).
    K appears in: alpha^-1 (K/B term), mp/me (K/S term),
    sin^2(theta_12) = K^2/S.  mu/e and m_H do not depend on K.
    """
    results: list[Prediction] = []

    for K_ in [1, 3]:
        results.append(Prediction(
            f"alpha_inv_K={K_}",
            _alpha_inv(n, float(L), B, K_),
            137.035999177, 0.000000021,
        ))
        results.append(Prediction(
            f"mp_me_K={K_}",
            _mp_over_me(S, n, B, K_),
            1836.15267, 0.00085,
        ))
        results.append(Prediction(
            f"sin2_theta12_K={K_}",
            float(K_**2) / S,
            0.307, 0.012,
        ))

    return results


def run_broken_n() -> list[Prediction]:
    """For n in {2,3,5,6}: compute L, then alpha^-1.  All should fail."""
    results: list[Prediction] = []

    for n_ in [2, 3, 5, 6]:
        L_ = n_**2 * (n_**2 - 1) / 12
        if L_ < 1:
            continue
        try:
            alpha = _alpha_inv(n_, L_, B, K)
        except (ZeroDivisionError, OverflowError):
            alpha = float("inf")
        results.append(Prediction(
            f"alpha_inv_n={n_}", alpha, 137.035999177, 0.000000021,
        ))

    return results


def run_lambda_uniqueness() -> list[Prediction]:
    """Perturb lambda^2.  Only 1/20 should match M_P and m_H."""
    results: list[Prediction] = []
    v = 246.2196

    for denom in [18, 19, 20, 21, 22]:
        lam_sq = 1.0 / denom
        M_P = _planck_mass(v, lam_sq, n, float(L), K, B)
        results.append(Prediction(
            f"M_P_lambda2=1/{denom}", M_P, 1.22091e19, 1.22091e16,
        ))

    return results


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


@pytest.mark.theory
def test_mode_count() -> None:
    assert all(r.passes for r in run_mode_count())


@pytest.mark.theory
def test_ld_cardinality_collapse() -> None:
    results = run_ld_cardinality_collapse()
    assert len(results) > 100  # enough types enumerated
    assert all(r.passes for r in results)


@pytest.mark.theory
def test_constant_rigidity() -> None:
    assert all(r.passes for r in run_constant_rigidity())


@pytest.mark.theory
def test_alternative_137() -> None:
    assert all(r.passes for r in run_alternative_137())


@pytest.mark.theory
def test_broken_k() -> None:
    results = run_broken_k()
    assert all(not p.passes for p in results)


@pytest.mark.theory
def test_broken_n() -> None:
    assert all(not p.passes for p in run_broken_n())


@pytest.mark.theory
def test_lambda_uniqueness() -> None:
    results = run_lambda_uniqueness()
    for r in results:
        if "1/20" in r.name:
            assert r.passes
        else:
            assert not r.passes
