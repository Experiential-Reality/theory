"""Integer factoring utilities for BLD theory tests.

Refactored from bld-prime experiment scripts (bld_theory_tests.py,
fano_exploit.py, seven_dimensions.py) into a proper module with
vectorized numpy variants for batch operations.

Theory ref: integer-factorization.md
"""

import math
import random

import numpy as np

import tools.bld

FANO_TRIPLES = tools.bld.FANO_TRIPLES
FANO_SORTED: frozenset[tuple[int, int, int]] = frozenset(
    tuple(sorted(t)) for t in FANO_TRIPLES
)


# ---------------------------------------------------------------------------
# Primality and semiprime generation
# ---------------------------------------------------------------------------


def is_probable_prime(n: int) -> bool:
    """Deterministic Miller-Rabin for n < 3.3×10^24 (witnesses 2..31)."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def gen_semiprime(k: int, seed: int = 42) -> tuple[int, int, int]:
    """Generate a k-bit semiprime. Returns (p, q, n) with p < q."""
    rng = random.Random(seed + k)
    half = k // 2
    lo = (1 << (half - 1)) | 1
    hi = (1 << half) - 1
    while True:
        p = rng.randrange(lo, hi + 1, 2)
        q = rng.randrange(lo, hi + 1, 2)
        if p != q and is_probable_prime(p) and is_probable_prime(q):
            return min(p, q), max(p, q), p * q


# ---------------------------------------------------------------------------
# Sieve utilities
# ---------------------------------------------------------------------------

_SMALL_PRIMES_CACHE: list[int] | None = None


def small_primes(bound: int) -> list[int]:
    """Sieve of Eratosthenes, cached."""
    global _SMALL_PRIMES_CACHE
    if _SMALL_PRIMES_CACHE is None or (
        _SMALL_PRIMES_CACHE and _SMALL_PRIMES_CACHE[-1] < bound
    ):
        sieve = bytearray(b"\x01") * (bound + 1)
        sieve[0] = sieve[1] = 0
        for i in range(2, int(bound**0.5) + 1):
            if sieve[i]:
                sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
        _SMALL_PRIMES_CACHE = [i for i, v in enumerate(sieve) if v]
    return [p for p in _SMALL_PRIMES_CACHE if p <= bound]


def valid_residues(n_val: int, m: int) -> frozenset[int]:
    """Valid residues r where r^2 = 4n (mod m). Precomputed set for O(1) lookup."""
    target = (4 * n_val) % m
    return frozenset(r for r in range(m) if (r * r) % m == target)


def fermat_sieve_survivors(n_val: int, m: int) -> frozenset[int]:
    """Valid S residues mod m for the correct Fermat sieve.

    S is valid iff S² - 4n is a quadratic residue or zero mod m,
    i.e., there exists d with d² ≡ S² - 4n (mod m).

    True S = p+q always survives because S² - 4n = (p-q)².
    Approximately m/2 out of m residues survive: ~1 bit per probe.
    """
    qr_set = frozenset(pow(r, 2, m) for r in range(m))
    return frozenset(
        s for s in range(m)
        if (s * s - 4 * n_val) % m in qr_set
    )


def build_sieve_table(
    n_val: int, primes: list[int]
) -> list[tuple[int, frozenset[int]]]:
    """Precompute valid residue sets for all sieve primes."""
    table = []
    for m in primes:
        if m == 2:
            continue
        vr = valid_residues(n_val, m)
        if vr:
            table.append((m, vr))
    return table


# ---------------------------------------------------------------------------
# Pollard rho
# ---------------------------------------------------------------------------


def pollard_rho(n: int, max_steps: int = 0) -> tuple[int, int]:
    """Pollard rho (Brent variant). Returns (factor, steps)."""
    if n % 2 == 0:
        return 2, 1
    for c in [1, 3, 5, 7, 11]:
        x = y = 2
        d = 1
        steps = 0
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            steps += 1
            d = math.gcd(abs(x - y), n)
            if max_steps and steps > max_steps:
                break
        if 1 < d < n:
            return d, steps
    return n, steps


# ---------------------------------------------------------------------------
# Carry computation
# ---------------------------------------------------------------------------


def get_carries(p: int, q: int, k: int) -> np.ndarray:
    """Extract carry vector from schoolbook binary multiplication."""
    carries = []
    carry = 0
    for i in range(2 * k):
        s = carry
        for j in range(max(0, i - k + 1), min(i + 1, k)):
            s += ((p >> j) & 1) * ((q >> (i - j)) & 1)
        carries.append(s >> 1)
        carry = s >> 1
    return np.array(carries, dtype=np.int64)



# ---------------------------------------------------------------------------
# Fano plane / Hamming
# ---------------------------------------------------------------------------


def build_fano_matrix() -> np.ndarray:
    """7x7 Fano incidence matrix: M[line][point] = 1 iff point on line."""
    M = np.zeros((7, 7), dtype=np.int64)
    for i, (a, b, c) in enumerate(FANO_TRIPLES):
        M[i, a - 1] = 1
        M[i, b - 1] = 1
        M[i, c - 1] = 1
    return M


def gf2_rank(matrix: np.ndarray) -> int:
    """Compute rank of matrix over GF(2)."""
    M = matrix.copy() % 2
    rows, cols = M.shape
    rank = 0
    for col in range(cols):
        pivot = None
        for row in range(rank, rows):
            if M[row, col] % 2:
                pivot = row
                break
        if pivot is None:
            continue
        M[[rank, pivot]] = M[[pivot, rank]]
        for r in range(rows):
            if r != rank and M[r, col] % 2:
                M[r] = (M[r] + M[rank]) % 2
        rank += 1
    return rank


def carry_class_vector(carries: np.ndarray, k: int) -> np.ndarray:
    """Compute 7-element parity vector: v[c] = XOR of (carry>0) at positions = c (mod 7)."""
    v = np.zeros(7, dtype=np.int64)
    for c in range(7):
        positions = np.arange(c, len(carries), 7)
        v[c] = np.sum(carries[positions] > 0) % 2
    return v


# ---------------------------------------------------------------------------
# Information theory
# ---------------------------------------------------------------------------


def mutual_info_2x2(joint: np.ndarray) -> float:
    """Mutual information from a 2x2 contingency table (in bits)."""
    total = joint.sum()
    if total == 0:
        return 0.0
    p = joint / total
    px, py = p.sum(axis=1), p.sum(axis=0)
    mi = 0.0
    for a in range(2):
        for b in range(2):
            if p[a, b] > 1e-10 and px[a] > 1e-10 and py[b] > 1e-10:
                mi += p[a, b] * math.log2(p[a, b] / (px[a] * py[b]))
    return mi


