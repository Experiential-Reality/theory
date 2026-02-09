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

import math

import tools.bld

from helpers import assert_all_pass, assert_none_pass


TR = tools.bld.TestResult


def test_mode_count() -> None:
    """Verify mode count: mu(Pi_4(Pi_20(1))) + mu(Sigma_56(1)) + mu(1) = 137.

    bld-calculus.md Definition 8.3:
      mu(1) = 1
      mu(Pi_n(tau)) = n * mu(tau)
      mu(tau1 + tau2) = mu(tau1) + mu(tau2)

    bld-calculus.md Proposition 8.5:
      alpha^-1 = mu(tau_geom) + mu(tau_bound) + mu(tau_trav) = 137
    """
    B, L, n = tools.bld.B, tools.bld.L, tools.bld.n
    mu_unit = 1
    mu_geom = n * (L * mu_unit)     # Pi_4(Pi_20(1)) = 4 * 20 * 1 = 80
    mu_bound = B * mu_unit           # Sigma_56(1) = 56 * 1 = 56
    mu_trav = mu_unit                # 1 (traverser type)
    total = mu_geom + mu_bound + mu_trav
    results = [TR("mode_count", total == 137, float(total))]
    assert_all_pass(results)


def test_ld_cardinality_collapse() -> None:
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
    results: list[TR] = []

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
        results.append(TR(
            f"LD|{type_name}|={card}",
            card == 1,
            float(card),
        ))

    assert len(results) > 100
    assert_all_pass(results)


def test_constant_rigidity() -> None:
    """The five identities form a 1D family parameterised by K.

    Identity 3 (lambda^2 * nL = K^2 with lambda^2 = 1/L) gives n = K^2.
    Identity 5: L = n^2(n^2-1)/12.
    Identity 2: S = K^2 + (n-1)^2.
    Identity 4: B = n(S+1).

    For K in 1..10, compute the unique (n,L,S,B) and evaluate all physics
    predictions.  Show K=2 is the ONLY value matching experiment.
    """
    results: list[TR] = []

    for K_ in range(1, 11):
        n_ = K_**2
        L_ = n_**2 * (n_**2 - 1) / 12
        if L_ < 1:
            continue
        S_ = K_**2 + (n_ - 1) ** 2
        B_ = n_ * (S_ + 1)

        # Alpha inverse
        try:
            alpha = tools.bld.alpha_inv(n_, L_, B_, K_)
        except (ZeroDivisionError, OverflowError):
            alpha = float("inf")
        obs = tools.bld.ALPHA_INV
        alpha_ok = abs(alpha - obs.value) < tools.bld.SIGMA_THRESHOLD * obs.uncertainty

        # Mu/e
        try:
            mu_e = tools.bld.mu_over_e(n_, L_, S_, B_)
        except (ZeroDivisionError, OverflowError):
            mu_e = float("inf")
        obs_mu = tools.bld.MU_OVER_E
        mu_e_ok = abs(mu_e - obs_mu.value) < tools.bld.SIGMA_THRESHOLD * obs_mu.uncertainty

        # mp/me
        try:
            mp_me = tools.bld.mp_over_me(S_, n_, B_, K_)
        except (ZeroDivisionError, OverflowError):
            mp_me = float("inf")
        obs_mp = tools.bld.MP_OVER_ME
        mp_me_ok = abs(mp_me - obs_mp.value) < tools.bld.SIGMA_THRESHOLD * obs_mp.uncertainty

        all_match = alpha_ok and mu_e_ok and mp_me_ok
        if K_ == 2:
            results.append(TR(f"K={K_}_matches", all_match, 1.0))
        else:
            results.append(TR(f"K={K_}_fails", not all_match, 0.0))

    assert_all_pass(results)


def test_alternative_137() -> None:
    """Try all (a,b,c) with a*b + c + 1 = 137, a,b,c > 0.

    Vectorized: meshgrid over (a, b), compute c = 136 - a*b, then evaluate
    alpha^-1 for all valid triples in a single numpy broadcast.
    Show only (4,20,56) gives alpha^-1 matching CODATA.
    """
    import numpy as np

    results: list[TR] = []
    obs = tools.bld.ALPHA_INV
    target = obs.value
    tol = tools.bld.SIGMA_THRESHOLD * obs.uncertainty
    K_ = tools.bld.K
    e2 = math.e ** 2

    # Build all valid (a, b, c) triples via meshgrid
    a_range = np.arange(2, 137, dtype=np.float64)  # a >= 2 (a=1 gives n-1=0 → div by 0)
    b_range = np.arange(1, 137, dtype=np.float64)
    A, B_grid = np.meshgrid(a_range, b_range, indexing="ij")
    C = 136.0 - A * B_grid
    valid = C >= 1

    # Extract valid triples
    n_ = A[valid]
    L_ = B_grid[valid]
    B_ = C[valid]

    # Vectorized alpha_inv: same formula as bld.alpha_inv but numpy-broadcasted
    nL = n_ * L_
    base = nL + B_ + 1
    boundary_quantum = K_ / B_
    outbound_spatial = n_ / ((n_ - 1) * nL * B_)
    return_spatial = -(n_ - 1) / (nL**2 * B_)
    return_boundary = -1 / (nL * B_**2)
    accumulated = -(e2 * (2 * B_ + n_ + K_ + 2) / ((2 * B_ + n_ + K_ + 1) * nL**2 * B_**2))
    alpha = base + boundary_quantum + outbound_spatial + return_spatial + return_boundary + accumulated

    within = np.abs(alpha - target) < tol
    n_tested = int(valid.sum())
    n_matches = int(within.sum())

    # Check which triples matched
    match_n = n_[within]
    match_L = L_[within]
    match_B = B_[within]

    bld_found = False
    for i in range(n_matches):
        a_i, b_i, c_i = int(match_n[i]), int(match_L[i]), int(match_B[i])
        if a_i == tools.bld.n and b_i == tools.bld.L and c_i == tools.bld.B:
            bld_found = True
        else:
            results.append(TR(
                f"({a_i},{b_i},{c_i})_unexpected", False, float(alpha[within][i]),
            ))

    results.append(TR(
        f"BLD_unique_in_{n_tested}_triples({n_matches}_match)",
        bld_found and n_matches == 1,
        float(alpha[within][0]) if n_matches else 0.0,
    ))

    assert_all_pass(results)


def test_broken_k() -> None:
    """Compute K-dependent predictions with K=1 and K=3.

    Keep all other constants at BLD values (including S=13).
    K appears in: alpha^-1 (K/B term), mp/me (K/S term),
    sin^2(theta_12) = K^2/S.  mu/e and m_H do not depend on K.
    """
    results: list[tools.bld.Prediction] = []
    B, L, n, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.S

    obs_alpha = tools.bld.ALPHA_INV
    obs_mp = tools.bld.MP_OVER_ME
    obs_s12 = tools.bld.SIN2_THETA_12

    for K_ in [1, 3]:
        results.append(tools.bld.Prediction(
            f"alpha_inv_K={K_}",
            tools.bld.alpha_inv(n, float(L), B, K_),
            obs_alpha.value, obs_alpha.uncertainty,
        ))
        results.append(tools.bld.Prediction(
            f"mp_me_K={K_}",
            tools.bld.mp_over_me(S, n, B, K_),
            obs_mp.value, obs_mp.uncertainty,
        ))
        results.append(tools.bld.Prediction(
            f"sin2_theta12_K={K_}",
            float(K_**2) / S,
            obs_s12.value, obs_s12.uncertainty,
        ))

    assert_none_pass(results)


def test_broken_n() -> None:
    """For n in {2,3,5,6}: compute L, then alpha^-1.  All should fail."""
    results: list[tools.bld.Prediction] = []
    obs = tools.bld.ALPHA_INV

    for n_ in [2, 3, 5, 6]:
        L_ = n_**2 * (n_**2 - 1) / 12
        if L_ < 1:
            continue
        try:
            alpha = tools.bld.alpha_inv(n_, L_, tools.bld.B, tools.bld.K)
        except (ZeroDivisionError, OverflowError):
            alpha = float("inf")
        results.append(tools.bld.Prediction(
            f"alpha_inv_n={n_}", alpha, obs.value, obs.uncertainty,
        ))

    assert_none_pass(results)


def test_lambda_uniqueness() -> None:
    """Perturb lambda^2.  Only 1/20 should match M_P and m_H."""
    results: list[tools.bld.Prediction] = []
    v = tools.bld.V_EW
    obs = tools.bld.PLANCK_MASS

    for denom in [18, 19, 20, 21, 22]:
        lam_sq = 1.0 / denom
        M_P = tools.bld.planck_mass(
            v, lam_sq, tools.bld.n, float(tools.bld.L), tools.bld.K, tools.bld.B,
        )
        results.append(tools.bld.Prediction(
            f"M_P_lambda2=1/{denom}", M_P, obs.value, obs.uncertainty,
        ))

    for r in results:
        if "1/20" in r.name:
            assert r.passes
        else:
            assert not r.passes


def test_spin8_boundary() -> None:
    """B = 2×dim(so(8)) and B-K = K(n-1)³.

    Theory ref: constants.md, e7-derivation.md
    dim(so(8)) = 8×7/2 = 28.
    B = 2×28 = 56 (bidirectional Spin(8) boundary).
    B - K = K(n-1)³ = 2×27 = 54 (usable boundary capacity).
    """
    B, n, K = tools.bld.B, tools.bld.n, tools.bld.K
    dim_so8 = 8 * 7 // 2  # 28

    assert_all_pass([
        TR("dim(so(8))=28", dim_so8 == 28, float(dim_so8)),
        TR("B=2×dim(so(8))", B == 2 * dim_so8, float(B)),
        TR("B-K=K(n-1)³=54", B - K == K * (n - 1) ** 3, float(B - K)),
    ])


def test_spin8_boundary_uniqueness() -> None:
    """Only (n=4, K=2, B=56) satisfies B-K=K(n-1)³ AND B/2=28.

    B-K = K(n-1)³ alone is NOT unique: for n=4 it reduces to
    K²-7K+10=0 giving K∈{2,5}.  But K=5→B=140, B/2=70≠28.

    Adding B/2=28=dim(so(8)) forces exactly one solution.
    """
    B, n, K, S = tools.bld.B, tools.bld.n, tools.bld.K, tools.bld.S

    # Phase 1: B-K = K(n-1)³ has multiple solutions
    bk_solutions = []
    for n_ in range(2, 21):
        for K_ in range(1, 11):
            B_ = n_ * (K_**2 + (n_ - 1) ** 2 + 1)
            if B_ - K_ == K_ * (n_ - 1) ** 3:
                bk_solutions.append((n_, K_, B_))

    results: list[TR] = [
        TR("B-K=K(n-1)³_multiple", len(bk_solutions) > 1, float(len(bk_solutions))),
    ]

    # Phase 2: adding B/2=28 forces unique solution
    spin8_solutions = [(n_, K_, B_) for n_, K_, B_ in bk_solutions if B_ // 2 == 28]
    results.append(TR(
        "with_so(8)_unique", len(spin8_solutions) == 1, float(len(spin8_solutions)),
    ))
    if spin8_solutions:
        n_, K_, B_ = spin8_solutions[0]
        results.append(TR(
            f"solution=({n_},{K_},{B_})", n_ == n and K_ == K and B_ == B,
            float(n_),
        ))

    assert_all_pass(results)


def test_planck_structure() -> None:
    """Planck mass formula constants are BLD expressions, not magic numbers.

    Theory ref: planck-derivation.md
    bld.py planck_mass() uses: lambda_sq**(-13), sqrt(5/14), (79/78).
    These are:
      -13 = -S               (exponent = negative structure constant)
      5/14 = L/B = 20/56     (geometric factor)
      79/78 = (nL-K+1)/(nL-K) (first-order correction)
      B/2-K = 2S = 26        (cascade exponent n_c)
    """
    B, L, n, K, S = tools.bld.B, tools.bld.L, tools.bld.n, tools.bld.K, tools.bld.S

    assert_all_pass([
        TR("exponent_-13=-S", S == 13, float(S)),
        TR("5/14=L/B", abs(5 / 14 - L / B) < 1e-15, L / B),
        TR("79=nL-K+1", n * L - K + 1 == 79, float(n * L - K + 1)),
        TR("78=nL-K", n * L - K == 78, float(n * L - K)),
        TR("cascade_B/2-K=2S=26", B // 2 - K == 2 * S, float(B // 2 - K)),
    ])
