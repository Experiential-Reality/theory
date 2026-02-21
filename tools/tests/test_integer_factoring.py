"""Adversarial tests for integer-factorization.md empirical claims.

Pure math (BLD constants, Fano combinatorics, Hamming identity) is proven
in Lean and excluded here. These tests cover ONLY the empirical/statistical/
computational claims that require generating actual semiprimes and running
actual algorithms.

Refactored from bld-prime experiment scripts:
  - bld_theory_tests.py (experiments 1-6)
  - fano_exploit.py (experiments 1-5)
  - seven_dimensions.py (experiments 1-4)

Theory ref: integer-factorization.md
"""

import math
import random

import numpy as np
import pytest

import tools.bld
import tools.factoring


# ---------------------------------------------------------------------------
# Module-level precomputation (shared across xdist workers via import)
# ---------------------------------------------------------------------------

_PRIMES_200 = [m for m in tools.factoring.small_primes(200) if m > 2]
_FANO_MATRIX = tools.factoring.build_fano_matrix()
_FANO_SORTED = tools.factoring.FANO_SORTED

# 0-indexed Fano set for carry analysis
_FANO_0 = frozenset(
    tuple(sorted([a - 1, b - 1, c - 1])) for a, b, c in tools.bld.FANO_TRIPLES
)
_NON_FANO_0 = frozenset(
    (i, j, k)
    for i in range(7)
    for j in range(i + 1, 7)
    for k in range(j + 1, 7)
    if (i, j, k) not in _FANO_0
)


# =========================================================================
# 1. Probe equation — K/X = 1 bit per coprime probe
# =========================================================================


class TestProbeEquation:
    """K/X = 1 bit per coprime probe (Claims 1, 2, 3, 8).

    Uses the correct Fermat sieve (QR check): S is valid iff S²-4n
    is a quadratic residue mod m. True S always passes because
    S²-4n = (p-q)². Approximately half of candidates survive each
    probe, giving ~1 bit of information per probe.
    """

    @pytest.mark.parametrize("k", [20, 28, 36])
    def test_kx_equals_one(self, k: int) -> None:
        """Each coprime probe eliminates approximately half the candidates.

        Theory: K/X = K/2 = 1 bit per probe. The Fermat sieve partitions
        candidates into those where S²-4n is a QR mod m (survive) and
        those where it is a QNR (eliminated). ~50% survive → 1 bit.
        """
        _, _, n = tools.factoring.gen_semiprime(k)

        survival_rates = []
        for m in _PRIMES_200[:20]:
            if math.gcd(m, n) != 1:
                continue
            survivors = tools.factoring.fermat_sieve_survivors(n, m)
            rate = len(survivors) / m
            survival_rates.append(rate)

        avg_rate = float(np.mean(survival_rates))
        # K/X = 1 bit → ~50% elimination per probe
        assert 0.4 < avg_rate < 0.65, (
            f"avg survival rate = {avg_rate:.3f}, expected ~0.5 (1 bit/probe)"
        )

    @pytest.mark.parametrize("k", [20, 28, 36])
    def test_true_factor_passes_all_probes(self, k: int) -> None:
        """True S = p+q passes every Fermat sieve probe.

        Theory: S²-4n = (p-q)² is always a perfect square, hence always
        a QR mod m. The true factor is never eliminated.
        """
        p, q, n = tools.factoring.gen_semiprime(k)
        S_true = p + q

        for m in _PRIMES_200:
            if math.gcd(m, n) != 1:
                continue
            survivors = tools.factoring.fermat_sieve_survivors(n, m)
            assert S_true % m in survivors, (
                f"True S={S_true} eliminated by probe m={m}: "
                f"S%m={S_true % m} not in survivors (|surv|={len(survivors)})"
            )

    @pytest.mark.parametrize("k", [20, 28, 36])
    def test_wrong_candidate_fails_probes(self, k: int) -> None:
        """Wrong S fails approximately half of Fermat sieve probes.

        With K/X = 1 bit per probe, a random wrong candidate passes
        each probe with probability ~0.5 and fails with ~0.5.
        """
        p, q, n = tools.factoring.gen_semiprime(k)
        S_wrong = p + q + 2

        failures = 0
        total = 0
        for m in _PRIMES_200[:30]:
            if math.gcd(m, n) != 1:
                continue
            survivors = tools.factoring.fermat_sieve_survivors(n, m)
            total += 1
            if S_wrong % m not in survivors:
                failures += 1

        fail_rate = failures / total if total > 0 else 0
        # Each probe eliminates ~50% of wrong candidates
        assert fail_rate > 0.2, (
            f"wrong S fail rate = {fail_rate:.2f} ({failures}/{total}), "
            f"expected > 0.2"
        )

    @pytest.mark.parametrize("k", [20, 28, 36])
    def test_k_half_probes_suffice(self, k: int) -> None:
        """k/2 coprime probes produce approximately k/2 bits of elimination.

        Theory: each probe provides ~1 bit (K/X = 1). After k/2 probes,
        cumulative elimination narrows the search space by ~2^(k/2).
        """
        _, _, n = tools.factoring.gen_semiprime(k)
        half = k // 2

        log2_elimination = 0.0
        probes_used = 0

        for m in _PRIMES_200:
            if math.gcd(m, n) != 1:
                continue
            survivors = tools.factoring.fermat_sieve_survivors(n, m)
            rate = len(survivors) / m
            if 0 < rate < 1:
                log2_elimination += -math.log2(rate)
            probes_used += 1
            if probes_used >= half:
                break

        # After k/2 probes at ~1 bit each, expect ~k/2 bits total
        assert log2_elimination > half * 0.6, (
            f"After {probes_used} probes: {log2_elimination:.1f} bits, "
            f"expected > {half * 0.6:.1f} (60% of k/2={half})"
        )

    @pytest.mark.parametrize("k", [20, 28, 36])
    def test_coprime_probes_independent(self, k: int) -> None:
        """Coprime probes are independent: joint elimination = sum of parts.

        Theory: coprime probes provide orthogonal information. By CRT,
        the joint survivor count for coprime moduli m1,m2 equals
        |surv1| × |surv2|. Verify information is additive (no redundancy).
        """
        _, _, n = tools.factoring.gen_semiprime(k)
        primes = [m for m in _PRIMES_200[:15] if math.gcd(m, n) == 1]

        # Test CRT independence: joint count = product of individual counts
        for i in range(min(3, len(primes))):
            for j in range(i + 1, min(6, len(primes))):
                m1, m2 = primes[i], primes[j]
                s1 = tools.factoring.fermat_sieve_survivors(n, m1)
                s2 = tools.factoring.fermat_sieve_survivors(n, m2)

                # Count joint survivors over Z/(m1*m2)
                joint_count = sum(
                    1 for s in range(m1 * m2)
                    if s % m1 in s1 and s % m2 in s2
                )

                # CRT guarantees independence: joint = |s1| × |s2|
                expected = len(s1) * len(s2)
                assert joint_count == expected, (
                    f"m1={m1}, m2={m2}: joint={joint_count}, "
                    f"expected |s1|×|s2|={expected} — probes not independent"
                )


# =========================================================================
# 2. Master formula — Work = N^{1/(2D)}
# =========================================================================


class TestMasterFormula:
    """Work = N^{1/(2D)} hierarchy (Claim 5)."""

    @pytest.mark.parametrize("k", [20, 24, 28, 32])
    def test_trial_division_d1(self, k: int) -> None:
        """Trial division ops ~ N^{1/2} (D=1)."""
        p, q, n = tools.factoring.gen_semiprime(k)
        trial_ops = 0
        for c in range(3, math.isqrt(n) + 1, 2):
            trial_ops += 1
            if n % c == 0:
                break

        expected = n**0.5
        ratio = trial_ops / expected
        assert 0.01 < ratio < 4.0, (
            f"trial_ops={trial_ops}, N^(1/2)={expected:.0f}, ratio={ratio:.2f}"
        )

    @pytest.mark.parametrize("k", [20, 24, 28, 32])
    def test_pollard_rho_d2(self, k: int) -> None:
        """Pollard rho steps ~ N^{1/4} (D=2)."""
        p, q, n = tools.factoring.gen_semiprime(k)
        _, rho_steps = tools.factoring.pollard_rho(n)

        expected = n**0.25
        ratio = rho_steps / expected
        assert 0.01 < ratio < 8.0, (
            f"rho_steps={rho_steps}, N^(1/4)={expected:.0f}, ratio={ratio:.2f}"
        )

    @pytest.mark.parametrize("k", [20, 24, 28, 32])
    def test_d_hierarchy_ordering(self, k: int) -> None:
        """Trial division (D=1) takes more steps than Pollard rho (D=2)."""
        p, q, n = tools.factoring.gen_semiprime(k)

        trial_ops = 0
        for c in range(3, math.isqrt(n) + 1, 2):
            trial_ops += 1
            if n % c == 0:
                break

        _, rho_steps = tools.factoring.pollard_rho(n)
        assert trial_ops > rho_steps, (
            f"trial_ops={trial_ops} <= rho_steps={rho_steps}"
        )

    @pytest.mark.parametrize("k", [20, 24, 28, 32])
    def test_rho_birthday_bound(self, k: int) -> None:
        """Pollard rho steps < 4 * N^{1/4} (birthday bound)."""
        p, q, n = tools.factoring.gen_semiprime(k)
        _, rho_steps = tools.factoring.pollard_rho(n)

        bound = 4 * n**0.25
        assert rho_steps < bound, f"rho_steps={rho_steps} >= 4*N^(1/4)={bound:.0f}"


# =========================================================================
# 3. Same L-type — Legendre universality
# =========================================================================


class TestSameLType:
    """Fermat sieve uses Legendre symbol structure (Claim 6)."""

    @pytest.mark.parametrize("k", [24, 32, 40])
    def test_valid_residue_count_matches_legendre(self, k: int) -> None:
        """valid_residues count = 1 + Legendre(4n, m) for coprime primes.

        The Legendre symbol determines the sieve elimination power:
        - |vr| = 0 when 4n is a QNR mod m (probe eliminates ~all candidates)
        - |vr| = 2 when 4n is a QR mod m (probe eliminates ~half)
        - |vr| = 1 when m | 4n (degenerate)
        """
        _, _, n = tools.factoring.gen_semiprime(k)

        for m in _PRIMES_200:
            if math.gcd(m, n) != 1:
                continue
            vr = tools.factoring.valid_residues(n, m)
            target = (4 * n) % m
            # Legendre symbol via Euler's criterion: a^((m-1)/2) mod m
            legendre = pow(target, (m - 1) // 2, m)
            if legendre == m - 1:
                legendre = -1
            expected_count = 1 + legendre  # 0 if QNR, 2 if QR
            assert len(vr) == expected_count, (
                f"m={m}: |vr|={len(vr)}, expected {expected_count} "
                f"(Legendre(4n,m)={legendre})"
            )

    @pytest.mark.parametrize("k", [24, 32, 40])
    def test_true_s_passes_when_m_divides_pq_diff(self, k: int) -> None:
        """True S passes sieve mod m exactly when m | (p-q).

        S_true^2 - 4n = (p-q)^2, so S_true^2 ≡ 4n (mod m) iff m | (p-q).
        This is the structural connection: the sieve tests divisibility
        of the factor difference.
        """
        p, q, n = tools.factoring.gen_semiprime(k)
        S_true = p + q
        diff = abs(p - q)

        for m in _PRIMES_200:
            if math.gcd(m, n) != 1:
                continue
            vr = tools.factoring.valid_residues(n, m)
            s_in_vr = S_true % m in vr
            m_divides_diff = diff % m == 0
            assert s_in_vr == m_divides_diff, (
                f"m={m}: S in vr = {s_in_vr}, m|(p-q) = {m_divides_diff}"
            )


# =========================================================================
# 4. Cost conservation — C_total = k/2
# =========================================================================


class TestCostConservation:
    """C_total = k/2 bits, algorithm-independent (Claims 1, 8, 9).

    The unique claim here (distinct from TestMasterFormula) is INVARIANCE:
    different algorithms partition C_total differently between visible
    and hidden cost, but the total is always k/2 bits.
    """

    @pytest.mark.parametrize("k", [20, 24, 28, 32])
    def test_cost_invariance_trial_vs_rho(self, k: int) -> None:
        """D × log₂(Work) ≈ k/2 for both trial division and Pollard rho.

        Theory: C_total = k/2 is algorithm-independent.
        Trial (D=1): C_total = 1 × log₂(N^{1/2}) = k/2.
        Rho (D=2): C_total = 2 × log₂(N^{1/4}) = k/2.
        Both give the same total cost despite different visible work.
        """
        p, q, n = tools.factoring.gen_semiprime(k)
        half = k // 2

        # Trial division work
        trial_ops = 0
        for c in range(3, math.isqrt(n) + 1, 2):
            trial_ops += 1
            if n % c == 0:
                break

        # Pollard rho work
        _, rho_steps = tools.factoring.pollard_rho(n)

        # D × log₂(Work) = C_total ≈ k/2
        trial_cost = 1 * math.log2(max(trial_ops, 1))  # D=1
        rho_cost = 2 * math.log2(max(rho_steps, 1))    # D=2

        # Both should be close to k/2
        assert abs(trial_cost - half) < half * 0.5, (
            f"trial C_total = {trial_cost:.1f}, expected ≈ {half}"
        )
        assert abs(rho_cost - half) < half * 0.5, (
            f"rho C_total = {rho_cost:.1f}, expected ≈ {half}"
        )
        # And close to each other (invariance)
        assert abs(trial_cost - rho_cost) < half * 0.6, (
            f"trial C_total={trial_cost:.1f} vs rho C_total={rho_cost:.1f}, "
            f"diff too large for invariance"
        )

    @pytest.mark.parametrize("k", [20, 24, 28, 32])
    def test_sieve_information_budget(self, k: int) -> None:
        """Fermat sieve converges in approximately k/2 probes.

        Theory: C_total = k/2 bits, each probe provides ~1 bit.
        Therefore ~k/2 probes should suffice to narrow the search.
        The cumulative elimination from k/2 probes should yield
        approximately k/2 bits of information.
        """
        _, _, n = tools.factoring.gen_semiprime(k)
        half = k // 2

        log2_elim = 0.0
        probes_used = 0

        for m in _PRIMES_200:
            if math.gcd(m, n) != 1:
                continue
            survivors = tools.factoring.fermat_sieve_survivors(n, m)
            rate = len(survivors) / m
            if 0 < rate < 1:
                log2_elim += -math.log2(rate)
            probes_used += 1
            if probes_used >= half:
                break

        # k/2 probes should provide close to k/2 bits of elimination
        assert log2_elim > half * 0.5, (
            f"After {probes_used} probes: {log2_elim:.1f} bits, "
            f"expected > {half * 0.5:.1f} (half of k/2={half})"
        )

    @pytest.mark.parametrize("k", [24, 28, 32])
    def test_rho_hides_cost_in_group(self, k: int) -> None:
        """Rho's visible work is exponentially less than trial's.

        Theory: C_total = k/2 is invariant, but rho hides k/4 bits
        in the Z/pZ group structure. Visible: trial=k/2, rho=k/4.
        The ratio trial_ops/rho_steps should grow as 2^{k/4}.
        """
        p, q, n = tools.factoring.gen_semiprime(k)

        trial_ops = 0
        for c in range(3, math.isqrt(n) + 1, 2):
            trial_ops += 1
            if n % c == 0:
                break

        _, rho_steps = tools.factoring.pollard_rho(n)

        # Ratio should grow exponentially with k
        log_ratio = math.log2(trial_ops / max(rho_steps, 1))
        expected_log_ratio = k / 4  # trial=2^{k/2}, rho=2^{k/4}
        assert log_ratio > expected_log_ratio * 0.3, (
            f"log₂(trial/rho) = {log_ratio:.1f}, expected ≈ {expected_log_ratio:.1f}"
        )


# =========================================================================
# 5. Fano carry correlation — r~0.4 Fano, r~0 non-Fano
# =========================================================================


class TestFanoCarryCorrelation:
    """Fano-aligned position pairs have correlated carries (Claims 10, 21)."""

    @pytest.mark.parametrize("k", [14, 21, 28])
    def test_fano_correlation_positive(self, k: int) -> None:
        """Fano triple carry correlation r > 0.15."""
        fano_r, _ = tools.factoring.fano_carry_correlation(k, 2000, seed=42)
        assert fano_r > 0.15, f"Fano r = {fano_r:.4f}, expected > 0.15"

    @pytest.mark.parametrize("k", [14, 21, 28])
    def test_non_fano_correlation_near_zero(self, k: int) -> None:
        """Non-Fano triple carry correlation |r| < 0.1."""
        _, non_fano_r = tools.factoring.fano_carry_correlation(k, 2000, seed=42)
        assert non_fano_r < 0.1, f"Non-Fano |r| = {non_fano_r:.4f}, expected < 0.1"

    @pytest.mark.parametrize("k", [14, 21, 28])
    def test_fano_exceeds_non_fano(self, k: int) -> None:
        """Fano r significantly exceeds non-Fano |r|."""
        fano_r, non_fano_r = tools.factoring.fano_carry_correlation(k, 2000, seed=42)
        assert fano_r > 3 * non_fano_r, (
            f"Fano r={fano_r:.4f} not > 3× non-Fano |r|={non_fano_r:.4f}"
        )

    def test_fano_carry_percent_grows(self) -> None:
        """Fano carry correlation increases with k.

        Theory data: r goes from 0.36 (k=14) to 0.46 (k=35).
        """
        r_small, _ = tools.factoring.fano_carry_correlation(14, 2000, seed=42)
        r_large, _ = tools.factoring.fano_carry_correlation(35, 2000, seed=42)
        assert r_large > r_small, (
            f"r(k=35)={r_large:.4f} not > r(k=14)={r_small:.4f}"
        )

    @pytest.mark.parametrize("k", [14, 21, 28])
    def test_correlation_range(self, k: int) -> None:
        """Fano r in expected range [0.15, 0.6]."""
        fano_r, _ = tools.factoring.fano_carry_correlation(k, 2000, seed=42)
        assert 0.15 < fano_r < 0.6, f"Fano r = {fano_r:.4f}, expected in (0.15, 0.6)"


# =========================================================================
# 6. Honest negatives — confirm failures
# =========================================================================


class TestHonestNegatives:
    """Adversarial: things that SHOULDN'T work, DON'T (Claims 13, 16, 18)."""

    def test_fano_no_factor_discrimination(self) -> None:
        """Fano carry syndromes can't distinguish real from fake factors.

        Refactored from fano_exploit.py experiment 3.
        """
        M = _FANO_MATRIX
        n_samples = 200
        rng_local = random.Random(42)

        real_zero_frac = 0.0
        fake_zero_frac = 0.0
        real_count = 0
        fake_count = 0

        for _ in range(n_samples):
            k = 28
            p, q, n = tools.factoring.gen_semiprime(k, seed=rng_local.randint(0, 10**6))

            # Real carries
            carries = tools.factoring.get_carries(p, q, k)
            v = tools.factoring.carry_class_vector(carries, k)
            syndrome = (M @ v) % 2
            if np.all(syndrome == 0):
                real_zero_frac += 1
            real_count += 1

            # Fake carries
            p_fake = rng_local.randrange(3, math.isqrt(n) + 100, 2)
            if p_fake == p or p_fake == q or n % p_fake == 0:
                continue
            q_fake = n // p_fake
            if q_fake < 2:
                continue
            carries_fake = tools.factoring.get_carries(p_fake, q_fake, k)
            v_fake = tools.factoring.carry_class_vector(carries_fake, k)
            syndrome_fake = (M @ v_fake) % 2
            if np.all(syndrome_fake == 0):
                fake_zero_frac += 1
            fake_count += 1

        if real_count > 0 and fake_count > 0:
            real_rate = real_zero_frac / real_count
            fake_rate = fake_zero_frac / fake_count
            diff = abs(real_rate - fake_rate)
            assert diff < 0.1, (
                f"Syndrome discrimination = {diff:.3f}, expected < 0.1 "
                f"(real={real_rate:.3f}, fake={fake_rate:.3f})"
            )

    def test_carry_prediction_no_advantage(self) -> None:
        """XOR carry prediction ~50% for both real and fake factors.

        Refactored from fano_exploit.py experiment 4.
        """
        n_samples = 200
        rng_local = random.Random(42)
        real_errors: list[float] = []
        fake_errors: list[float] = []

        for _ in range(n_samples):
            k = 28
            p, q, n = tools.factoring.gen_semiprime(k, seed=rng_local.randint(0, 10**6))
            carries_real = tools.factoring.get_carries(p, q, k)

            # Group by mod 7
            classes: dict[int, np.ndarray] = {}
            for c in range(7):
                pos = np.arange(c, len(carries_real), 7)
                classes[c] = (carries_real[pos] > 0).astype(np.float64)

            # XOR prediction error for real
            total_err = 0.0
            total_pos = 0
            for a, b, c in tools.bld.FANO_TRIPLES:
                ca = classes[(a - 1) % 7]
                cb = classes[(b - 1) % 7]
                cc = classes[(c - 1) % 7]
                min_len = min(len(ca), len(cb), len(cc))
                if min_len == 0:
                    continue
                pred = (ca[:min_len] + cb[:min_len]) % 2
                total_err += float(np.sum(np.abs(pred - cc[:min_len])))
                total_pos += min_len
            if total_pos > 0:
                real_errors.append(total_err / total_pos)

            # Fake carries
            p_fake = rng_local.randrange(3, math.isqrt(n) + 100, 2)
            if p_fake == p or p_fake == q or n % p_fake == 0:
                continue
            q_fake = n // p_fake
            if q_fake < 2:
                continue
            carries_fake = tools.factoring.get_carries(p_fake, q_fake, k)
            classes_fake: dict[int, np.ndarray] = {}
            for c_idx in range(7):
                pos = np.arange(c_idx, len(carries_fake), 7)
                classes_fake[c_idx] = (carries_fake[pos] > 0).astype(np.float64)

            total_err = 0.0
            total_pos = 0
            for a, b, c in tools.bld.FANO_TRIPLES:
                ca = classes_fake[(a - 1) % 7]
                cb = classes_fake[(b - 1) % 7]
                cc = classes_fake[(c - 1) % 7]
                min_len = min(len(ca), len(cb), len(cc))
                if min_len == 0:
                    continue
                pred = (ca[:min_len] + cb[:min_len]) % 2
                total_err += float(np.sum(np.abs(pred - cc[:min_len])))
                total_pos += min_len
            if total_pos > 0:
                fake_errors.append(total_err / total_pos)

        avg_real = float(np.mean(real_errors))
        avg_fake = float(np.mean(fake_errors))
        gap = avg_fake - avg_real

        # The gap should be near zero or negative — no advantage for real factors
        assert gap < 0.05, (
            f"Carry prediction gap = {gap:+.4f} "
            f"(real={avg_real:.4f}, fake={avg_fake:.4f}), expected < 0.05"
        )

    def test_born_ordering_no_speedup(self) -> None:
        """Born-ordered Fermat sieve has no meaningful speedup vs random.

        Test with small k for speed.
        """
        k = 24
        p, q, n = tools.factoring.gen_semiprime(k)
        S_true = p + q
        sieve_table = tools.factoring.build_sieve_table(n, _PRIMES_200)

        # Random ordering
        rng_local = random.Random(42)
        random_order = list(sieve_table)
        rng_local.shuffle(random_order)

        def count_sieve_steps(
            table: list[tuple[int, frozenset[int]]],
        ) -> int:
            s_start = math.isqrt(4 * n)
            if s_start % 2 != S_true % 2:
                s_start += 1
            steps = 0
            for s_cand in range(s_start, s_start + math.isqrt(n), 2):
                steps += 1
                passed = True
                for m, vr in table:
                    if s_cand % m not in vr:
                        passed = False
                        break
                if passed:
                    disc = s_cand * s_cand - 4 * n
                    if disc >= 0:
                        isq = math.isqrt(disc)
                        if isq * isq == disc:
                            return steps
            return steps

        steps_sorted = count_sieve_steps(sieve_table)
        steps_random = count_sieve_steps(random_order)

        # Born ordering should give at most marginal improvement
        if steps_random > 0:
            ratio = steps_sorted / steps_random
            # Theory: no meaningful speedup. Ratio should be near 1.0.
            assert 0.5 < ratio < 1.5, (
                f"Sorted/random ratio = {ratio:.2f}, expected ≈ 1.0 (no speedup)"
            )


# =========================================================================
# 7. Fano universality — predictions at larger k
# =========================================================================


class TestFanoUniversality:
    """Fano carry structure persists at larger k (Prediction 6.5)."""

    @pytest.mark.parametrize("k", [42, 56])
    def test_fano_carries_large_k(self, k: int) -> None:
        """Fano r > 0.1 at large k (extends beyond tested range)."""
        fano_r, _ = tools.factoring.fano_carry_correlation(k, 1000, seed=42)
        assert fano_r > 0.1, f"Fano r = {fano_r:.4f} at k={k}, expected > 0.1"

    @pytest.mark.parametrize("k", [42, 56])
    def test_non_fano_stays_zero_large_k(self, k: int) -> None:
        """Non-Fano |r| < 0.1 at large k."""
        _, non_fano_r = tools.factoring.fano_carry_correlation(k, 1000, seed=42)
        assert non_fano_r < 0.1, f"Non-Fano |r| = {non_fano_r:.4f} at k={k}, expected < 0.1"

    def test_non_multiple_of_7(self) -> None:
        """Fano structure persists at k=30 (not a multiple of 7)."""
        fano_r, non_fano_r = tools.factoring.fano_carry_correlation(30, 2000, seed=42)
        assert fano_r > 0.1, f"Fano r = {fano_r:.4f} at k=30, expected > 0.1"
        assert fano_r > 2 * non_fano_r, (
            f"Fano r={fano_r:.4f} not > 2× non-Fano |r|={non_fano_r:.4f} at k=30"
        )
