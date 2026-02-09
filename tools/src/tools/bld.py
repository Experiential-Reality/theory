"""BLD theory: constants, observed values, and prediction formulas.

The BLD theory derives physical constants from three irreducible primitives:
B (Boundary), L (Link), D (Dimension, here n).  This module encodes the
mathematical content: fundamental constants, experimentally observed values,
and the parameterized prediction formulas that connect them.

All formulas are parameterized (take BLD constants as arguments) so tests
can evaluate them with wrong constants for adversarial falsification.
"""

import dataclasses
import enum
import math

import numpy as np


# ---------------------------------------------------------------------------
# BLD fundamental constants
# ---------------------------------------------------------------------------

B = 56                      # Boundary (E7 rank)
L = 20                      # Link (Killing form dimension)
n = 4                       # Spacetime dimensions
K = 2                       # Observation cost (bidirectional)
S = 13                      # Structure: (B - n) / n
LAMBDA = 1 / math.sqrt(L)   # Coupling scale
V_EW = 246.2196             # Electroweak VEV (GeV)
TAU_BOTTLE = 877.8          # Neutron bottle lifetime (s)


# ---------------------------------------------------------------------------
# Measurement type + observed values
# ---------------------------------------------------------------------------


@dataclasses.dataclass(slots=True, frozen=True)
class Measurement:
    """An experimentally observed value with uncertainty."""
    value: float
    uncertainty: float


# Electromagnetic
ALPHA_INV = Measurement(137.035999177, 0.000000021)         # CODATA 2018

# Lepton ratios
MU_OVER_E = Measurement(206.7682827, 0.0000005)             # CODATA 2018
TAU_OVER_MU = Measurement(16.8172, 0.0011)                  # PDG 2024

# Nucleon ratio
MP_OVER_ME = Measurement(1836.15267, 0.00085)               # CODATA 2018

# Neutrino mixing
SIN2_THETA_12 = Measurement(0.307, 0.012)                   # NuFIT 5.2
SIN2_THETA_13 = Measurement(0.02195, 0.00058)               # NuFIT 5.2
SIN2_THETA_23 = Measurement(0.561, 0.015)                   # NuFIT 5.2

# Anomalous magnetic moment (x10^-11)
MUON_G2 = Measurement(249, 17)                              # Fermilab

# Neutron lifetime
TAU_BEAM = Measurement(888.1, 2.0)                          # PDG 2024

# Mass scales
PLANCK_MASS = Measurement(1.22091e19, 1.22091e16)           # GeV, CODATA
HIGGS_MASS = Measurement(125.20, 0.11)                      # GeV, ATLAS+CMS

# Electroweak bosons
Z_MASS = Measurement(91.1876, 0.0021)                       # GeV, PDG 2024
W_MASS = Measurement(80.377, 0.012)                         # GeV, PDG 2024
SIN2_THETA_W = Measurement(0.23121, 0.00004)                # PDG 2024
ALPHA_S = Measurement(0.1179, 0.0010)                       # PDG 2024 (at M_Z)

# Higgs couplings (ATLAS Run 2)
KAPPA_GAMMA = Measurement(1.05, 0.09)
KAPPA_Z = Measurement(1.01, 0.08)
KAPPA_W = Measurement(1.04, 0.08)
KAPPA_B = Measurement(0.98, 0.13)

# Feigenbaum constants
FEIGENBAUM_DELTA = Measurement(4.6692016091, 0.0000000001)  # Molteni 2016
FEIGENBAUM_ALPHA = Measurement(2.5029078750, 0.0000000001)  # Molteni 2016

# Classical turbulence (empirical)
RE_PIPE_OBSERVED = Measurement(2300.0, 1.0)
RE_FLAT_PLATE = Measurement(5e5, 1.5e4)
RE_SPHERE = Measurement(2e5, 1e3)
RE_JET = Measurement(2000.0, 1000.0)

# She-Leveque DNS data: zeta_p for p = 1..8
SL_DNS_ZETA = (0.37, 0.70, 1.000, 1.28, 1.54, 1.78, 2.00, 2.21)
SL_DNS_UNC = (0.01, 0.01, 0.001, 0.02, 0.03, 0.04, 0.05, 0.07)

# Higgs self-coupling bounds (ATLAS Run 2)
KAPPA_LAMBDA_LOWER = -1.6
KAPPA_LAMBDA_UPPER = 6.6

# Cosmological parameters (Planck 2018)
OMEGA_BARYON = Measurement(0.049, 0.001)
OMEGA_DARK_MATTER = Measurement(0.27, 0.01)
OMEGA_DARK_ENERGY = Measurement(0.68, 0.01)
H0_CMB = Measurement(67.4, 0.5)              # km/s/Mpc, Planck 2018
H0_LOCAL = Measurement(73.0, 1.0)            # km/s/Mpc, SH0ES 2022
SIGMA8_CMB = Measurement(0.811, 0.006)        # Planck 2018
SIGMA8_LOCAL = Measurement(0.77, 0.02)        # weak lensing (DES, KiDS)


# ---------------------------------------------------------------------------
# Tolerance constants
# ---------------------------------------------------------------------------

SIGMA_THRESHOLD = 3.0           # Standard sigma threshold for pass/fail
FLOAT_EPSILON = 1e-15           # Floating-point zero threshold
IDENTITY_TOLERANCE = 0.01       # Tolerance for integer identity checks
CONVERGENCE_RATIO = 0.1         # Maximum ratio for convergence tests
TRANSCENDENTAL_UNIQUENESS = 1000  # Minimum superiority ratio for e^2 test
IMPROVEMENT_THRESHOLD = 50      # Minimum improvement factor for e-correction

# Feigenbaum prediction tolerances (fraction of measured value)
FEIGENBAUM_DELTA_TOL = 0.0001   # 0.0003% of ~4.669
FEIGENBAUM_ALPHA_TOL = 0.000001  # 0.00001% of ~2.503


# ---------------------------------------------------------------------------
# Enumerations
# ---------------------------------------------------------------------------


class CorrectionTerm(enum.Enum):
    """Alpha^-1 decomposition term names."""
    BASE = "base"
    BOUNDARY_QUANTUM = "boundary_quantum"
    OUTBOUND_SPATIAL = "outbound_spatial"
    RETURN_SPATIAL = "return_spatial"
    RETURN_BOUNDARY = "return_boundary"
    ACCUMULATED = "accumulated"


class CorrectionSign(enum.Enum):
    """K/X correction sign convention (observer-correction.md)."""
    POSITIVE = "+"   # incomplete traversal (escapes detection)
    NEGATIVE = "-"   # complete traversal (all products detected)


# ---------------------------------------------------------------------------
# Prediction type
# ---------------------------------------------------------------------------


@dataclasses.dataclass(slots=True, frozen=True)
class Prediction:
    """A theoretical prediction compared to observation."""
    name: str
    predicted: float
    observed: float
    uncertainty: float

    @property
    def sigma(self) -> float:
        if self.uncertainty <= 0:
            return 0.0 if abs(self.predicted - self.observed) < FLOAT_EPSILON else float("inf")
        return abs(self.predicted - self.observed) / self.uncertainty

    @property
    def passes(self) -> bool:
        return self.sigma < SIGMA_THRESHOLD


@dataclasses.dataclass(slots=True, frozen=True)
class TestResult:
    """A boolean test result with optional diagnostic value."""
    name: str
    passes: bool
    value: float = 0.0


# ---------------------------------------------------------------------------
# Existing prediction formulas (e7-derivation.md, boson-masses.md)
# ---------------------------------------------------------------------------


def alpha_inv_full(
    n_: int, L_: float, B_: int, K_: int,
) -> tuple[float, dict[CorrectionTerm, float]]:
    """Fine structure constant inverse with decomposed correction terms.

    Theory ref: e7-derivation.md, observer-correction.md
    """
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
        CorrectionTerm.BASE: base,
        CorrectionTerm.BOUNDARY_QUANTUM: boundary_quantum,
        CorrectionTerm.OUTBOUND_SPATIAL: outbound_spatial,
        CorrectionTerm.RETURN_SPATIAL: return_spatial,
        CorrectionTerm.RETURN_BOUNDARY: return_boundary,
        CorrectionTerm.ACCUMULATED: accumulated,
    }
    return total, terms


def alpha_inv(n_: int, L_: float, B_: int, K_: int) -> float:
    """Fine structure constant inverse.

    Theory ref: e7-derivation.md
    """
    total, _ = alpha_inv_full(n_, L_, B_, K_)
    return total


def higgs_mass(v: float, B_: int, L_: int) -> float:
    """Higgs boson mass (GeV).

    Theory ref: boson-masses.md
    """
    return (v / 2) * (1 + 1 / B_) * (1 - 1 / (B_ * L_))


def planck_mass(
    v: float, lambda_sq: float, n_: int, L_: float, K_: int, B_: int,
) -> float:
    """Planck mass (GeV).

    Theory ref: e7-derivation.md
    """
    nL = n_ * L_
    base = v * lambda_sq ** (-13) * math.sqrt(5 / 14)
    first_order = (nL - K_ + 1) / (nL - K_)
    second_order = 1 + K_ * 3 / (nL * B_**2)
    return base * first_order * second_order


def mu_over_e(n_: int, L_: float, S_: int, B_: int) -> float:
    """Muon to electron mass ratio.

    Theory ref: e7-derivation.md
    """
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


def mp_over_me(S_: int, n_: int, B_: int, K_: int) -> float:
    """Proton to electron mass ratio.

    Theory ref: e7-derivation.md
    """
    return (S_ + n_) * (B_ + n_ * S_) + K_ / S_


def tau_over_mu(n_: int, L_: float, S_: int) -> float:
    """Tau to muon mass ratio.

    Theory ref: e7-derivation.md
    """
    nL = n_ * L_
    nLS = nL * S_
    return (
        2 * math.pi * math.e
        * (n_**2 * S_ - 1) / (n_**2 * S_)
        * (nL - 1) / nL
        * (1 + 2 / nLS)
    )


def sin2_theta_12(K_: int, S_: int) -> float:
    """Neutrino mixing angle sin^2(theta_12).

    Theory ref: e7-derivation.md
    """
    return K_**2 / S_


def sin2_theta_13(n_: int) -> float:
    """Neutrino mixing angle sin^2(theta_13).

    Theory ref: e7-derivation.md
    """
    return n_**2 / (n_ - 1) ** 6


def sin2_theta_23(S_: int, L_: int, n_: int) -> float:
    """Neutrino mixing angle sin^2(theta_23).

    Theory ref: e7-derivation.md
    """
    return (S_ + 1) / (L_ + n_ + 1)


def muon_g2(n_: int, L_: float, K_: int, S_: int, B_: int) -> float:
    """Muon anomalous magnetic moment delta_a_mu (x10^-11).

    Self-consistent: uses BLD alpha^-1 rather than empirical value.
    Theory ref: e7-derivation.md
    """
    alpha = 1.0 / alpha_inv(n_, L_, B_, K_)
    nL = n_ * L_
    base = alpha**2 * K_**2 / (nL**2 * S_)
    detection = (B_ + L_) / (B_ + L_ + K_)
    return base * detection * 1e11


def tau_beam(tau_bottle: float, K_: int, S_: int) -> float:
    """Neutron beam lifetime (s).

    Theory ref: e7-derivation.md
    """
    return tau_bottle * (1 + K_ / S_**2)


# ---------------------------------------------------------------------------
# Electroweak formulas (boson-masses.md, strong-coupling.md)
# ---------------------------------------------------------------------------


def sin2_theta_w(S_: int, K_: int, n_: int, L_: int, B_: int) -> float:
    """Weak mixing angle sin^2(theta_W).

    Theory ref: boson-masses.md
    """
    return 3.0 / S_ + K_ / (n_ * L_ * B_)


def z_mass(v_: float, n_: int, L_: int, B_: int, K_: int) -> float:
    """Z boson mass (GeV).

    Theory ref: boson-masses.md
    """
    alpha_inv_base = n_ * L_ + B_ + 1
    return (v_ / math.e) * (alpha_inv_base / (alpha_inv_base - 1)) * (1 - K_ / B_**2)


def w_mass(m_z: float, n_: int, L_: int, S_: int) -> float:
    """W boson mass (GeV).

    Theory ref: boson-masses.md
    """
    cos_w = math.sqrt((S_ - 3) / S_)
    n2s = n_**2 * S_
    return m_z * cos_w * ((n2s + 1) / n2s) * (1 + 1 / ((n_ * L_)**2 + n_ * S_))


def alpha_s_inv(alpha_inv_val: float, n_: int, L_: int, K_: int) -> float:
    """Strong coupling constant inverse.

    Theory ref: strong-coupling.md
    """
    return alpha_inv_val / n_**2 - K_ / (n_ + L_)


def kappa_em(K_: int, B_: int) -> float:
    """Higgs coupling modifier for EM channels (kappa_gamma, kappa_Z).

    Detection structure: X = B (boundary).
    Theory ref: higgs-couplings.md
    """
    return 1 + K_ / B_


def kappa_hadronic(K_: int, n_: int, L_: int) -> float:
    """Higgs coupling modifier for hadronic channels (kappa_b, kappa_c).

    Detection structure: X = n+L (geometry).
    Theory ref: higgs-couplings.md
    """
    return 1 + K_ / (n_ + L_)


def kappa_w_coupling(K_: int, B_: int, L_: int) -> float:
    """Higgs coupling modifier for W channel.

    Detection structure: X = B+L (EM + neutrino escape).
    Theory ref: higgs-couplings.md
    """
    return 1 + K_ / (B_ + L_)


def kappa_lambda_coupling(K_: int, n_: int, L_: int) -> float:
    """Higgs self-coupling modifier.

    Detection structure: X = nL (full observer geometry).
    Theory ref: higgs-self-coupling.md
    """
    return 1 + K_ / (n_ * L_)


def bld_composites(
    B_: int, L_: int, n_: int, K_: int, S_: int,
) -> dict[str, int]:
    """All structurally meaningful BLD composites from theory documents.

    Products, sums, differences, powers, and compound expressions
    that appear in any BLD prediction formula.
    """
    nL = n_ * L_
    return {
        # Singles
        "B": B_, "L": L_, "n": n_, "K": K_, "S": S_,
        # Products
        "nL": nL, "nS": n_ * S_, "nK": n_ * K_, "nB": n_ * B_,
        "LS": L_ * S_, "KS": K_ * S_, "BL": B_ * L_,
        "nLS": nL * S_, "nLK": nL * K_, "nLB": nL * B_,
        "nBS": n_ * B_ * S_, "nBK": n_ * B_ * K_,
        "nLBS": nL * B_ * S_, "nLBK": nL * B_ * K_,
        # Sums
        "n+L": n_ + L_, "n+K": n_ + K_, "B+L": B_ + L_, "B+K": B_ + K_,
        "B+n+L": B_ + (n_ + L_), "nL+B": nL + B_, "nL+B+1": nL + B_ + 1,
        "S+1": S_ + 1, "S+n": S_ + n_,
        # Differences
        "B-L": B_ - L_, "B-L+1": B_ - L_ + 1,
        # Powers
        "B2": B_**2, "L2": L_**2, "n2": n_**2, "K2": K_**2, "S2": S_**2,
        "(nL)2": nL**2, "n2S": n_**2 * S_,
        # Compound
        "(nL)2+nS": nL**2 + n_ * S_,
    }


# ---------------------------------------------------------------------------
# Classical / turbulence formulas
# (reynolds-derivation.md, feigenbaum-derivation.md, she-leveque-derivation.md)
# ---------------------------------------------------------------------------


def reynolds_pipe(n_: int, L_: int, B_: int, K_: int) -> float:
    """Critical Reynolds number for pipe flow.

    Theory ref: reynolds-derivation.md
    """
    X = B_ - L_ + 1
    return (n_ * L_ * B_ / K_) * (X + 1) / X


def feigenbaum_delta(n_: int, L_: int, K_: int) -> float:
    """Feigenbaum bifurcation ratio delta.

    Theory ref: feigenbaum-derivation.md
    """
    X = n_ + K_ + K_ / n_ + 1.0 / L_
    return math.sqrt(L_ + K_ - K_**2 / L_ + 1 / math.exp(X))


def feigenbaum_alpha(n_: int, L_: int, B_: int, K_: int) -> float:
    """Feigenbaum spatial scaling factor alpha.

    Theory ref: feigenbaum-derivation.md
    """
    X = n_ + K_ + K_ / n_ + 1.0 / L_
    D = L_ + 1 - 1.0 / n_**2
    return K_ + 1.0 / K_ + 1.0 / ((n_ + K_) * B_) - 1.0 / (D * math.exp(X))


def she_leveque_zeta(p: float, n_: int, K_: int) -> float:
    """She-Leveque structure function exponent zeta_p.

    Theory ref: she-leveque-derivation.md
    """
    return p / (n_ - 1)**2 + K_ * (1 - (K_ / (n_ - 1))**(p / (n_ - 1)))


def reynolds_flat_plate(re_pipe: float, n_: int, B_: int) -> float:
    """Critical Reynolds number for flat plate flow.

    B-escape: boundary escapes detection.
    Theory ref: reynolds-derivation.md
    """
    return re_pipe * n_ * B_


def reynolds_sphere(re_pipe: float, n_: int, L_: int, K_: int) -> float:
    """Critical Reynolds number for sphere flow.

    L-escape: link/geometry partially escapes.
    Theory ref: reynolds-derivation.md
    """
    return re_pipe * (n_ * (L_ + K_) - 1)


def reynolds_jet(re_pipe: float, K_: int) -> float:
    """Critical Reynolds number for jet flow.

    Destabilizing: K reduces stability.
    Theory ref: reynolds-derivation.md
    """
    return re_pipe / K_


# ---------------------------------------------------------------------------
# Cosmological formulas (dark-matter-mapping.md, hubble-tension.md,
# sigma8-tension.md)
# ---------------------------------------------------------------------------


def dark_matter_fraction(x: float, n_: int, L_: int, K_: int) -> float:
    """Dark matter fraction: (L/n)*x + K*n*x².

    Primordial: L/n geometric DOF per dimensional DOF.
    Observer correction: K*n*x² (cost of observing geometry).
    Theory ref: dark-matter-mapping.md
    """
    return (L_ / n_) * x + K_ * n_ * x ** 2


def dark_energy_fraction(x: float, n_: int, L_: int, K_: int) -> float:
    """Dark energy fraction: 1 - (1 + L/n)*x - K*n*x².

    Remainder after ordinary matter + dark matter.
    Theory ref: dark-matter-mapping.md
    """
    return 1.0 - (1.0 + L_ / n_) * x - K_ * n_ * x ** 2


def hubble_local(h0_cmb: float, K_: int, n_: int, L_: int) -> float:
    """Local Hubble constant: H₀(CMB) × (1 + K/(n+L)).

    Observer embedded in structure pays K/(n+L) traversal cost.
    X = n+L = 24 (spacetime + Riemann curvature).
    Theory ref: hubble-tension.md
    """
    return h0_cmb * (1.0 + K_ / (n_ + L_))


def sigma8_primordial(L_: int, n_: int) -> float:
    """Primordial clustering amplitude: L/(n+L).

    Fraction of structure that is connections (clustering).
    Theory ref: sigma8-tension.md
    """
    return L_ / (n_ + L_)


def sigma8_cmb(L_: int, n_: int, K_: int) -> float:
    """CMB clustering amplitude: σ₈(primordial) × (1 - K/(n×L)).

    First observer correction: geometric smoothing.
    Theory ref: sigma8-tension.md
    """
    return sigma8_primordial(L_, n_) * (1.0 - K_ / (n_ * L_))


def sigma8_local(L_: int, n_: int, K_: int) -> float:
    """Local clustering amplitude: σ₈(CMB) × (1 - K/(2L)).

    Second observer correction: additional structure smoothing.
    Theory ref: sigma8-tension.md
    """
    return sigma8_cmb(L_, n_, K_) * (1.0 - K_ / (2 * L_))


# ---------------------------------------------------------------------------
# Quantum utilities
# ---------------------------------------------------------------------------


def haar_random_state(dim: int, rng: np.random.Generator) -> np.ndarray:
    """Generate a single Haar-random quantum state."""
    z = rng.standard_normal(dim) + 1j * rng.standard_normal(dim)
    return z / np.linalg.norm(z)


def haar_random_states(dim: int, n: int, rng: np.random.Generator) -> np.ndarray:
    """Generate n Haar-random quantum states as rows of a matrix."""
    z = rng.standard_normal((n, dim)) + 1j * rng.standard_normal((n, dim))
    return z / np.linalg.norm(z, axis=1, keepdims=True)
