"""BLD theory: constants, observed values, and prediction formulas.

The BLD theory derives physical constants from three irreducible primitives:
B (Boundary), L (Link), D (Dimension, here n).  This module encodes the
mathematical content: fundamental constants, experimentally observed values,
and the parameterized prediction formulas that connect them.

All formulas are parameterized (take BLD constants as arguments) so tests
can evaluate them with wrong constants for adversarial falsification.
"""

import dataclasses
import math


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
            return 0.0 if abs(self.predicted - self.observed) < 1e-15 else float("inf")
        return abs(self.predicted - self.observed) / self.uncertainty

    @property
    def passes(self) -> bool:
        return self.sigma < 3.0


# ---------------------------------------------------------------------------
# Existing prediction formulas (e7-derivation.md, boson-masses.md)
# ---------------------------------------------------------------------------


def alpha_inv_full(
    n_: int, L_: float, B_: int, K_: int,
) -> tuple[float, dict[str, float]]:
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
        "base": base,
        "boundary_quantum": boundary_quantum,
        "outbound_spatial": outbound_spatial,
        "return_spatial": return_spatial,
        "return_boundary": return_boundary,
        "accumulated": accumulated,
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
