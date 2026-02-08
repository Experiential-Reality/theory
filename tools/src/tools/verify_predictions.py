"""BLD theory quantitative predictions vs observation."""

import dataclasses
import math
import sys

import numpy as np


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


def run_constant_identities() -> list[Prediction]:
    return [
        Prediction("S=(B-n)/n", (B - n) / n, S, 0),
        Prediction("K²+(n-1)²=S", K**2 + (n - 1) ** 2, S, 0),
        Prediction("λ²×nL=K²", LAMBDA**2 * n * L, K**2, 0),
        Prediction("S+1=B/n", S + 1, B / n, 0),
        Prediction("Riemann=L", n**2 * (n**2 - 1) / 12, L, 0),
    ]


def run_fine_structure() -> list[Prediction]:
    nL = n * L
    base = nL + B + 1
    boundary_quantum = K / B
    outbound_spatial = n / ((n - 1) * nL * B)
    return_spatial = -(n - 1) / (nL**2 * B)
    return_boundary = -1 / (nL * B**2)
    accumulated = -(
        math.e**2
        * (2 * B + n + K + 2)
        / ((2 * B + n + K + 1) * nL**2 * B**2)
    )
    alpha_inv = (
        base + boundary_quantum + outbound_spatial
        + return_spatial + return_boundary + accumulated
    )
    return [Prediction("α⁻¹", alpha_inv, 137.035999177, 0.000000021)]


def run_lepton_ratios() -> list[Prediction]:
    nL = n * L
    nLS = nL * S
    e = math.e

    mu_over_e = (
        (n**2 * S - 1)
        * nLS / (nLS + 1)
        * (1 - 1 / (nL**2 + n * S))
        * (1 - 1 / (nL * B**2))
        * (1 + e**2 * (S + 1) / (nL**2 * B**2 * S**2))
    )

    tau_over_mu = (
        2 * math.pi * e
        * (n**2 * S - 1) / (n**2 * S)
        * (nL - 1) / nL
        * (1 + 2 / nLS)
    )

    return [
        Prediction("μ/e", mu_over_e, 206.7682827, 0.0000005),
        Prediction("τ/μ", tau_over_mu, 16.8172, 0.0011),
    ]


def run_nucleon_ratio() -> list[Prediction]:
    mp_over_me = (S + n) * (B + n * S) + K / S
    return [Prediction("m_p/m_e", mp_over_me, 1836.15267, 0.00085)]


def run_neutrino_mixing() -> list[Prediction]:
    return [
        Prediction("sin²θ₁₂", K**2 / S, 0.307, 0.012),
        Prediction("sin²θ₁₃", n**2 / (n - 1) ** 6, 0.02195, 0.00058),
        Prediction("sin²θ₂₃", (S + 1) / (L + n + 1), 0.561, 0.015),
    ]


def run_muon_g2() -> list[Prediction]:
    alpha = 1 / 137.036
    nL = n * L
    base = alpha**2 * K**2 / (nL**2 * S)
    detection = (B + L) / (B + L + K)
    delta_a_mu = base * detection * 1e11
    return [Prediction("Δaμ(×10⁻¹¹)", delta_a_mu, 249, 17)]


def run_neutron_lifetime() -> list[Prediction]:
    tau_bottle = 877.8
    tau_beam = tau_bottle * (1 + K / S**2)
    return [Prediction("τ_beam(s)", tau_beam, 888.1, 2.0)]


def run_planck_mass() -> list[Prediction]:
    v = 246.2196
    nL = n * L
    base = v * LAMBDA ** (-26) * math.sqrt(5 / 14)
    first_order = (nL - K + 1) / (nL - K)
    second_order = 1 + K * 3 / (nL * B**2)
    M_P = base * first_order * second_order
    return [Prediction("M_P(GeV)", M_P, 1.22091e19, 1.22091e16)]


def run_higgs_mass() -> list[Prediction]:
    v = 246.2196
    m_H = (v / 2) * (1 + 1 / B) * (1 - 1 / (B * L))
    return [Prediction("m_H(GeV)", m_H, 125.20, 0.11)]


def run_constant_uniqueness() -> tuple[Prediction, list[Prediction]]:
    """Negative test: BLD constants (B=56, L=20, n=4, K=2, S=13) are unique.

    Five simultaneous identities over-determine the system.  Perturbing any
    single constant by ±1 breaks at least one identity, proving the solution
    is isolated — not one of many nearby integer tuples.

    Returns (true_result, perturbations) so the test can assert true passes
    and all perturbations fail.
    """
    def _count_satisfied(B_: int, L_: int, n_: int, K_: int, S_: int) -> int:
        checks = [
            abs((B_ - n_) / n_ - S_) < 0.01,
            abs(K_**2 + (n_ - 1) ** 2 - S_) < 0.01,
            abs((1.0 / L_) * n_ * L_ - K_**2) < 0.01,
            abs(S_ + 1 - B_ / n_) < 0.01,
            abs(n_**2 * (n_**2 - 1) / 12 - L_) < 0.01,
        ]
        return sum(checks)

    base = (56, 20, 4, 2, 13)
    names = ["B", "L", "n", "K", "S"]

    true_result = Prediction("true constants", float(_count_satisfied(*base)), 5.0, 0)

    perturbations: list[Prediction] = []
    for idx, name in enumerate(names):
        for delta in [-1, +1]:
            perturbed = list(base)
            perturbed[idx] += delta
            sat = _count_satisfied(*perturbed)
            # Perturbed should satisfy fewer than 5 → sigma=inf → passes=False
            perturbations.append(Prediction(
                f"{name}{'+' if delta > 0 else '−'}1",
                float(sat), 5.0, 0,
            ))
    return true_result, perturbations


def run_wrong_integers() -> tuple[list[Prediction], list[Prediction]]:
    """Negative test: nearby integers don't match observed mass ratios.

    BLD derives μ/e primordial integer as n²S−1 = 207.  Using 206 or 208
    shifts the prediction by ~1 unit — thousands of σ from observation.
    Same for m_p/m_e base (S+n)(B+nS) = 17×108 = 1836.

    Returns (correct, wrong) so the test can assert correct pass and wrong fail.
    """
    nL = n * L
    nLS = nL * S
    e = math.e

    def _mu_over_e(base_int: int) -> float:
        return (
            base_int
            * nLS / (nLS + 1)
            * (1 - 1 / (nL**2 + n * S))
            * (1 - 1 / (nL * B**2))
            * (1 + e**2 * (S + 1) / (nL**2 * B**2 * S**2))
        )

    def _mp_over_me(base_int: int) -> float:
        return base_int + K / S

    correct: list[Prediction] = [
        Prediction("μ/e n²S−1=207", _mu_over_e(207), 206.7682827, 0.0000005),
        Prediction("m_p/m_e base=1836", _mp_over_me((S + n) * (B + n * S)), 1836.15267, 0.00085),
    ]
    wrong: list[Prediction] = [
        Prediction(f"μ/e base={w}", _mu_over_e(w), 206.7682827, 0.0000005)
        for w in [206, 208]
    ] + [
        Prediction(f"m_p/m_e base={w}", _mp_over_me(w), 1836.15267, 0.00085)
        for w in [1835, 1837]
    ]
    return correct, wrong


def main() -> int:
    print("=" * 80)
    print("BLD THEORY PREDICTIONS VS OBSERVATION")
    print("=" * 80)

    groups = [
        ("CONSTANT IDENTITIES", run_constant_identities),
        ("FINE STRUCTURE CONSTANT", run_fine_structure),
        ("LEPTON MASS RATIOS", run_lepton_ratios),
        ("NUCLEON MASS RATIO", run_nucleon_ratio),
        ("NEUTRINO MIXING ANGLES", run_neutrino_mixing),
        ("MUON g-2 ANOMALY", run_muon_g2),
        ("NEUTRON LIFETIME", run_neutron_lifetime),
        ("PLANCK MASS", run_planck_mass),
        ("HIGGS MASS", run_higgs_mass),
    ]

    all_pass = True
    total = 0
    passed = 0

    def _print_result(r: Prediction) -> None:
        nonlocal all_pass, total, passed
        status = "PASS" if r.passes else "FAIL"
        sigma_str = f"{r.sigma:.2f}σ" if r.uncertainty > 0 else "exact"
        print(
            f"  {r.name:16s}: predicted={r.predicted:.10g}, "
            f"observed={r.observed:.10g} [{sigma_str}] [{status}]"
        )
        total += 1
        if r.passes:
            passed += 1
        else:
            all_pass = False

    for name, fn in groups:
        print(f"\n--- {name} ---")
        for r in fn():
            _print_result(r)

    # Negative tests: correct values should pass, wrong values should fail
    print("\n--- CONSTANT UNIQUENESS (negative) ---")
    true_result, perturbations = run_constant_uniqueness()
    _print_result(true_result)
    for p in perturbations:
        status = "PASS" if not p.passes else "FAIL"
        print(f"  {p.name:16s}: {int(p.predicted)}/5 identities hold [{status}]")
        total += 1
        if not p.passes:
            passed += 1
        else:
            all_pass = False

    print("\n--- WRONG INTEGERS (negative) ---")
    correct, wrong = run_wrong_integers()
    for r in correct:
        _print_result(r)
    for w in wrong:
        status = "PASS" if not w.passes else "FAIL"
        print(
            f"  {w.name:16s}: predicted={w.predicted:.10g}, "
            f"off by {w.sigma:.0f}σ [{status}]"
        )
        total += 1
        if not w.passes:
            passed += 1
        else:
            all_pass = False

    print(f"\n{'=' * 80}")
    print(f"VERDICT: {passed}/{total} checks pass")
    print(f"{'=' * 80}")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
