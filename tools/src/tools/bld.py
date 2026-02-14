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
import numpy.linalg as la


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
N_COLORS = 3                # SU(3) color charges (octonion -> G2 -> SU(3))
M_ELECTRON = 0.511          # Electron mass (MeV)


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
ETA_BARYON = Measurement(6.104e-10, 0.058e-10)  # Planck 2018

# Unit conversion constants
HBAR_GEV_S = 6.582119569e-25    # ℏ in GeV·s (CODATA 2022)
MPC_KM = 3.0857e19              # 1 Mpc in km

# Quark masses (MS-bar, PDG 2024)
M_UP = Measurement(2.16, 0.49)              # MeV
M_DOWN = Measurement(4.67, 0.48)            # MeV
M_STRANGE = Measurement(93.4, 8.6)          # MeV
M_CHARM = Measurement(1270.0, 20.0)         # MeV (at m_c)
M_BOTTOM = Measurement(4180.0, 30.0)        # MeV (at m_b)
M_TOP = Measurement(172.69, 0.30)           # GeV (direct)

# CKM matrix elements (PDG 2024)
V_US = Measurement(0.2243, 0.0005)

# Neutrino mass-squared differences (NuFIT 6.0, normal ordering)
DM2_21 = Measurement(7.53e-5, 0.18e-5)      # eV^2
DM2_32 = Measurement(2.453e-3, 0.033e-3)    # eV^2 (normal ordering)


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


class DetectionCompleteness(enum.Enum):
    """K/X sign rule: detection completeness determines correction sign.

    Theory ref: force-structure.md §8.3
    """
    COMPLETE = "-"      # all products detected → negative K/X
    INCOMPLETE = "+"    # something escapes → positive K/X
    EMBEDDED = "x"      # observer in geometry → multiplicative


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


@dataclasses.dataclass(slots=True, frozen=True)
class ForceGeometry:
    """Explicit state for one force's K/X geometry.

    Each force is determined by: what gauge group, what the carrier
    traverses (X), and whether detection is complete.
    Thread-safe (frozen). Vectorizable (plain fields).

    Theory ref: force-structure.md §8.1
    """
    name: str
    carrier: str
    x_expr: str          # human-readable: "B", "n+L", "nLB", "nL-K"
    x_value: int         # evaluated at BLD constants
    sign: DetectionCompleteness
    kx: float            # K / x_value (or (x+1)/x for embedded)


FORCE_GEOMETRY: tuple[ForceGeometry, ...] = (
    ForceGeometry("EM", "photon", "B", B, DetectionCompleteness.INCOMPLETE,
                  K / B),
    ForceGeometry("Weak", "Z", "nLB", n * L * B, DetectionCompleteness.INCOMPLETE,
                  K / (n * L * B)),
    ForceGeometry("Strong", "gluon", "n+L", n + L, DetectionCompleteness.COMPLETE,
                  K / (n + L)),
    ForceGeometry("Gravity", "metric", "nL-K", n * L - K, DetectionCompleteness.EMBEDDED,
                  (n * L - K + 1) / (n * L - K)),
)


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
# Equation of motion formulas (equation-of-motion.md, killing-form.md)
# ---------------------------------------------------------------------------


def so_dim(n_dim: int) -> int:
    """Dimension of so(n): n(n-1)/2.

    Theory ref: equation-of-motion.md
    """
    return n_dim * (n_dim - 1) // 2


def killing_form_coeff(n_dim: int) -> int:
    """Killing form coefficient for so(n): κ(X,Y) = (n-2)·tr(XY).

    Theory ref: killing-form.md, equation-of-motion.md
    """
    return n_dim - 2


def levi_civita_coeff() -> float:
    """Levi-Civita connection on bi-invariant Lie group: ∇_X Y = c·[X,Y].

    Returns c = 0.5.
    Theory ref: equation-of-motion.md (Koszul formula)
    """
    return 0.5


def riemann_coeff() -> float:
    """Riemann curvature of bi-invariant metric: R(X,Y)Z = c·[[X,Y],Z].

    Returns c = -0.25.
    Theory ref: equation-of-motion.md (Step 7)
    """
    return -0.25


def sectional_curvature_coeff() -> float:
    """Sectional curvature: K(X,Y) = c·|[X,Y]|²/(|X|²|Y|²−⟨X,Y⟩²).

    Returns c = 0.25.
    Theory ref: equation-of-motion.md (Step 7)
    """
    return 0.25


def alpha_inv_gut(n_: int, L_: int) -> int:
    """α⁻¹ at GUT scale: B drops out, leaving n + L + 1.

    Theory ref: equation-of-motion.md (Part IV), force-structure.md §9
    """
    return n_ + L_ + 1


def force_kx(K_: int, x: int) -> float:
    """K/X correction for a force with detection structure X.

    Theory ref: force-structure.md §8
    """
    return K_ / x


def ricci_coeff_biinvariant() -> float:
    """Ricci tensor on compact Lie group with bi-invariant metric: Ric(X,Y) = c·g(X,Y).

    Returns c = 0.25.
    Theory ref: equation-of-motion.md (Ricci curvature), Milnor 1976
    """
    return 0.25


def scalar_curvature(dim_algebra: int) -> float:
    """Scalar curvature R = dim(g)/4 for compact Lie group with bi-invariant metric.

    For SO(8): R = 28/4 = 7.
    Theory ref: equation-of-motion.md (Ricci curvature)
    """
    return dim_algebra / 4.0


def einstein_coupling(K_: int, n_: int) -> float:
    """Einstein coupling 8πG = K·n·π. For BLD: 2·4·π = 8π.

    Theory ref: general-relativity.md, equation-of-motion.md
    """
    return K_ * n_ * math.pi


def sign_from_x_expr(x_expr: str) -> DetectionCompleteness:
    """Derive detection completeness from X expression structure.

    The sign of K/X corrections is determined by what structure X
    traverses, which maps to subalgebra projections in so(8):

    - B in expression → INCOMPLETE (boundary crossing → info escapes)
    - Pure geometry (n,L) → COMPLETE (confined → all detected)
    - Subtract K → EMBEDDED (self-reference, observer in geometry)

    Theory ref: force-structure.md §8.3, detection-structure.md §5
    """
    if "-K" in x_expr or "−K" in x_expr:
        return DetectionCompleteness.EMBEDDED
    if "B" in x_expr:
        return DetectionCompleteness.INCOMPLETE
    return DetectionCompleteness.COMPLETE


def gauge_subalgebra_dims() -> tuple[int, int, int]:
    """Dimensions of gauge subalgebras in so(8): (su3=8, su2=3, u1=1).

    From division algebra tower:
      𝕆 → G₂ → fix e₁ → SU(3) (8 generators)
      ℍ → SU(2) (3 generators)
      ℂ → U(1) (1 generator)

    Theory ref: octonion-derivation.md, particle-classification.md
    """
    return (8, 3, 1)


def adjoint_complementary_dim(so_dim_: int) -> int:
    """Complementary generators in so(8) beyond gauge subalgebras.

    28 - 8 - 3 - 1 = 16 (matter + gravity content).
    Theory ref: equation-of-motion.md (Open Problem #1)
    """
    return so_dim_ - sum(gauge_subalgebra_dims())


def dual_coxeter_number(n_dim: int) -> int:
    """Dual Coxeter number h_v for so(n): h_v = n - 2.

    For so(8): h_v = 6.
    Theory ref: Helgason, Differential Geometry Ch. X
    """
    return n_dim - 2


def casimir_adjoint(n_dim: int) -> int:
    """Quadratic Casimir of adjoint rep of so(n): C₂(adj) = 2(n-2).

    For so(8): C₂ = 12.
    Theory ref: Humphreys, Introduction to Lie Algebras Ch. 8
    """
    return 2 * (n_dim - 2)


def casimir_vector_so(n_dim: int) -> int:
    """Quadratic Casimir of vector rep of so(n): C₂(vector) = n-1.

    For so(8): C₂ = 7 = scalar curvature R = dim(so(8))/4.
    This equality C₂ = R is unique to so(8) among all so(n).
    Theory ref: Humphreys, Introduction to Lie Algebras Ch. 8
    """
    return n_dim - 1


def vol_sphere(k: int) -> float:
    """Volume of the unit k-sphere S^k = 2π^{(k+1)/2} / Γ((k+1)/2).

    Theory ref: do Carmo, Riemannian Geometry Ch. 3
    """
    return 2.0 * math.pi ** ((k + 1) / 2.0) / math.gamma((k + 1) / 2.0)


def vol_so(n_dim: int) -> float:
    """Volume of SO(n) with bi-invariant metric g = -κ.

    Vol(SO(n)) = 2^{⌊n/2⌋} × ∏_{k=1}^{n-1} Vol(S^k).
    Theory ref: Helgason, Differential Geometry Ch. X
    """
    result = 2.0 ** (n_dim // 2)
    for k in range(1, n_dim):
        result *= vol_sphere(k)
    return result


def _d4_hw_orthogonal(
    a1: int, a2: int, a3: int, a4: int,
) -> tuple[float, float, float, float]:
    """Convert D4 Dynkin labels [a1,a2,a3,a4] to orthogonal basis.

    Fundamental weights in orthogonal basis:
      ω₁ = (1,0,0,0)
      ω₂ = (1,1,0,0)
      ω₃ = (½,½,½,-½)
      ω₄ = (½,½,½,½)

    Highest weight λ = a1·ω₁ + a2·ω₂ + a3·ω₃ + a4·ω₄.
    Theory ref: Humphreys, Introduction to Lie Algebras Ch. 13
    """
    return (
        a1 + a2 + 0.5 * a3 + 0.5 * a4,
        a2 + 0.5 * a3 + 0.5 * a4,
        0.5 * a3 + 0.5 * a4,
        -0.5 * a3 + 0.5 * a4,
    )


def weyl_dimension_d4(a1: int, a2: int, a3: int, a4: int) -> int:
    """Dimension of SO(8) irrep with Dynkin labels [a1,a2,a3,a4].

    Weyl dimension formula: d = ∏_{α>0} (λ+ρ, α) / (ρ, α)
    where ρ = (3,2,1,0) and positive roots are e_i ± e_j (i<j).

    Known values:
      (0,0,0,0) → 1    (trivial)
      (1,0,0,0) → 8    (vector 8_v)
      (0,1,0,0) → 28   (adjoint)
      (0,0,1,0) → 8    (spinor 8_c)
      (0,0,0,1) → 8    (spinor 8_s)

    Theory ref: Humphreys Ch. 24
    """
    hw = _d4_hw_orthogonal(a1, a2, a3, a4)
    rho = (3.0, 2.0, 1.0, 0.0)
    lam_rho = tuple(hw[i] + rho[i] for i in range(4))

    num = 1.0
    den = 1.0
    # Positive roots of D4: e_i - e_j and e_i + e_j for 0 <= i < j <= 3
    for i in range(4):
        for j in range(i + 1, 4):
            # e_i - e_j
            num *= lam_rho[i] - lam_rho[j]
            den *= rho[i] - rho[j]
            # e_i + e_j
            num *= lam_rho[i] + lam_rho[j]
            den *= rho[i] + rho[j]

    result = num / den
    return int(round(result))


def casimir_d4(a1: int, a2: int, a3: int, a4: int) -> float:
    """Quadratic Casimir C₂(R) = (λ, λ + 2ρ) for SO(8) irrep.

    Convention: mathematical (longest root² = 2).

    Cross-checks:
      (0,0,0,0) → 0   (trivial)
      (1,0,0,0) → 7   (vector)
      (0,1,0,0) → 12  (adjoint)
      (0,0,1,0) → 7   (spinor 8_c)
      (0,0,0,1) → 7   (spinor 8_s)

    Theory ref: Humphreys Ch. 23
    """
    hw = _d4_hw_orthogonal(a1, a2, a3, a4)
    rho = (3.0, 2.0, 1.0, 0.0)
    lam_plus_2rho = tuple(hw[i] + 2.0 * rho[i] for i in range(4))
    return sum(hw[i] * lam_plus_2rho[i] for i in range(4))


def spectral_zeta_so8(s: float, max_label_sum: int = 6) -> float:
    """Spectral zeta function ζ(s) = Σ_{R≠trivial} d_R² × C₂(R)^{-s}.

    Sums over SO(8) irreps with Dynkin labels a1+a2+a3+a4 ≤ max_label_sum,
    excluding the trivial representation (C₂=0).

    Used for one-loop determinant: det(Δ) = exp(-ζ'(0)).
    Theory ref: Camporesi 1990, Spectral zeta functions on compact Lie groups
    """
    total = 0.0
    for a1 in range(max_label_sum + 1):
        for a2 in range(max_label_sum + 1 - a1):
            for a3 in range(max_label_sum + 1 - a1 - a2):
                for a4 in range(max_label_sum + 1 - a1 - a2 - a3):
                    if a1 == a2 == a3 == a4 == 0:
                        continue
                    d = weyl_dimension_d4(a1, a2, a3, a4)
                    c2 = casimir_d4(a1, a2, a3, a4)
                    if c2 > 0:
                        total += d * d * c2 ** (-s)
    return total


def heat_kernel_trace(t: float, max_label_sum: int = 6) -> float:
    """Heat kernel trace Z(t) = Σ_R d_R² exp(-t C₂(R)) on SO(8).

    Sums over all D₄ irreps with Dynkin labels a1+a2+a3+a4 ≤ max_label_sum.
    Includes trivial representation (d=1, C₂=0), so Z(0) = Σ d_R² and Z(∞) → 1.

    Theory ref: Camporesi 1990, equation-of-motion.md (heat kernel on Lie groups)
    """
    total = 1.0  # trivial rep: d=1, C₂=0, exp(0)=1
    for a1 in range(max_label_sum + 1):
        for a2 in range(max_label_sum + 1 - a1):
            for a3 in range(max_label_sum + 1 - a1 - a2):
                for a4 in range(max_label_sum + 1 - a1 - a2 - a3):
                    if a1 == a2 == a3 == a4 == 0:
                        continue
                    d = weyl_dimension_d4(a1, a2, a3, a4)
                    c2 = casimir_d4(a1, a2, a3, a4)
                    if c2 > 0:
                        total += d * d * math.exp(-t * c2)
    return total


def cascade_energy(k: int, v: float = V_EW) -> float:
    """Energy at cascade step k: μ(k) = v × λ^{-k}.

    Each cascade step multiplies energy by λ⁻¹ ≈ 4.47.
    k=0 → electroweak scale, k=n_c → GUT scale.

    Theory ref: scale-derivation.md, equation-of-motion.md
    """
    return v * LAMBDA ** (-k)


def sm_alpha_inv_em_1loop(
    mu: float,
    m_z: float = 91.1876,
    alpha_inv_mz: float = 127.9,
) -> float:
    """SM 1-loop electromagnetic running (NOT BLD prediction, for comparison).

    α⁻¹(μ) = α⁻¹(M_Z) - (b_EM / 2π) × ln(μ / M_Z)
    b_EM = -80/9 (SM 1-loop coefficient for U(1)_Y + SU(2)_L combined EM).

    This is standard SM, not derived from BLD. Used only for comparison.
    """
    b_em = -80.0 / 9.0
    return alpha_inv_mz - (b_em / (2.0 * math.pi)) * math.log(mu / m_z)


# ---------------------------------------------------------------------------
# Numerical Lie algebra infrastructure
# (reusable computation for equation-of-motion tests and future theory work)
# ---------------------------------------------------------------------------


def so_basis(n_dim: int) -> np.ndarray:
    """Construct canonical basis of so(n) as skew-symmetric matrices.

    Returns shape (dim_algebra, n_dim, n_dim) where dim_algebra = n(n-1)/2.
    """
    dim = so_dim(n_dim)
    basis = np.zeros((dim, n_dim, n_dim), dtype=np.float64)
    k = 0
    for i in range(n_dim):
        for j in range(i + 1, n_dim):
            basis[k, i, j] = 1.0
            basis[k, j, i] = -1.0
            k += 1
    return basis


def structure_constants(basis: np.ndarray) -> np.ndarray:
    """Compute structure constants: [E_a, E_b] = f^c_{ab} E_c.

    Returns shape (dim, dim, dim) where f[a, b, c] is the coefficient of E_c
    in [E_a, E_b].
    """
    dim, n_dim, _ = basis.shape
    f = np.zeros((dim, dim, dim), dtype=np.float64)
    norms = np.array([np.trace(basis[c].T @ basis[c]) for c in range(dim)])
    for a in range(dim):
        for b in range(dim):
            bracket = basis[a] @ basis[b] - basis[b] @ basis[a]
            for c in range(dim):
                f[a, b, c] = np.trace(bracket @ basis[c].T) / norms[c]
    return f


def killing_form_numerical(f: np.ndarray) -> np.ndarray:
    """Compute Killing form matrix: κ_{ab} = tr(ad_a @ ad_b^T).

    Returns shape (dim, dim).
    """
    return np.einsum("acd,bdc->ab", f, f)


def lie_bracket(
    v1: np.ndarray, v2: np.ndarray, f: np.ndarray,
) -> np.ndarray:
    """Lie bracket in coefficient space: [v1, v2]^c = v1^d v2^e f[d,e,c]."""
    return np.einsum("d,e,dec->c", v1, v2, f)


def coeff_to_matrix(v: np.ndarray, rep: np.ndarray) -> np.ndarray:
    """Convert coefficient vector to representation matrix: sum v[k] rep[k]."""
    return np.einsum("k,kij->ij", v, rep)


def matrix_exp(A: np.ndarray, terms: int = 50) -> np.ndarray:
    """Matrix exponential via Taylor series. Avoids scipy dependency."""
    result = np.eye(A.shape[0], dtype=A.dtype)
    power = np.eye(A.shape[0], dtype=A.dtype)
    for k in range(1, terms + 1):
        power = power @ A / k
        result = result + power
    return result


def ricci_tensor(f: np.ndarray) -> np.ndarray:
    """Ricci tensor on compact Lie group with bi-invariant metric.

    Ric_{ab} = -1/4 f^{cd}_a f_{cdb} = 1/4 g_{ab}.
    Returns shape (dim, dim).
    """
    return -0.25 * np.einsum("abe,eda->bd", f, f)


# ---------------------------------------------------------------------------
# Octonion algebra
# ---------------------------------------------------------------------------

FANO_TRIPLES: list[tuple[int, int, int]] = [
    (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 7),
    (5, 6, 1), (6, 7, 2), (7, 1, 3),
]


def octonion_struct() -> np.ndarray:
    """Octonion multiplication table: C[a,b,c] = component of e_a*e_b along e_c."""
    C = np.zeros((8, 8, 8))
    for i in range(8):
        C[0, i, i] = 1.0
        C[i, 0, i] = 1.0
    for i in range(1, 8):
        C[i, i, 0] = -1.0
    for a, b, c in FANO_TRIPLES:
        C[a, b, c] = 1.0
        C[b, a, c] = -1.0
        C[b, c, a] = 1.0
        C[c, b, a] = -1.0
        C[c, a, b] = 1.0
        C[a, c, b] = -1.0
    return C


def octonion_multiply(a: np.ndarray, b: np.ndarray,
                      struct: np.ndarray) -> np.ndarray:
    """Multiply two octonions represented as 8-vectors."""
    return np.einsum("ijk,i,j->k", struct, a, b)


def octonion_conjugate(a: np.ndarray) -> np.ndarray:
    """Conjugate: negate imaginary parts."""
    result = a.copy()
    result[1:] = -result[1:]
    return result


def octonion_derivation_constraints(struct: np.ndarray) -> np.ndarray:
    """Derivation constraint matrix for octonions. Null space = G2 Lie algebra.

    Theory ref: octonion-derivation.md
    """
    n_unknowns = 49
    equations = []
    for i in range(1, 8):
        for j in range(1, 8):
            for out_comp in range(8):
                row = np.zeros(n_unknowns)
                for k in range(1, 8):
                    coeff = struct[i, j, k]
                    if abs(coeff) < 1e-15:
                        continue
                    if out_comp >= 1:
                        row[(k - 1) * 7 + (out_comp - 1)] += coeff
                for a in range(7):
                    sc = struct[a + 1, j, out_comp]
                    if abs(sc) < 1e-15:
                        continue
                    row[(i - 1) * 7 + a] -= sc
                for a in range(7):
                    sc = struct[i, a + 1, out_comp]
                    if abs(sc) < 1e-15:
                        continue
                    row[(j - 1) * 7 + a] -= sc
                if np.any(np.abs(row) > 1e-15):
                    equations.append(row)
    return np.array(equations)


def octonion_left_mult(struct: np.ndarray, a: int) -> np.ndarray:
    """8x8 matrix for left multiplication by e_a in octonions.

    (L_a)_{c,b} = struct[a,b,c].
    """
    L = np.zeros((8, 8))
    for b in range(8):
        for c in range(8):
            L[c, b] = struct[a, b, c]
    return L


# ---------------------------------------------------------------------------
# Quaternion algebra
# ---------------------------------------------------------------------------


QUATERNION_TRIPLE: tuple[int, int, int] = (1, 2, 3)
"""Cyclic triple for quaternion multiplication: e₁e₂ = e₃ (ij = k)."""


def quaternion_struct() -> np.ndarray:
    """Quaternion multiplication table: C[a,b,c] = component of e_a*e_b along e_c.

    Basis: e₀=1, e₁=i, e₂=j, e₃=k.
    One cyclic triple (1,2,3) vs seven Fano triples for octonions.
    Theory ref: exceptional-algebras.md (der(H) = so(3))
    """
    C = np.zeros((4, 4, 4))
    for i in range(4):
        C[0, i, i] = 1.0
        C[i, 0, i] = 1.0
    for i in range(1, 4):
        C[i, i, 0] = -1.0
    a, b, c = QUATERNION_TRIPLE
    C[a, b, c] = 1.0
    C[b, a, c] = -1.0
    C[b, c, a] = 1.0
    C[c, b, a] = -1.0
    C[c, a, b] = 1.0
    C[a, c, b] = -1.0
    return C


def quaternion_derivation_constraints(struct: np.ndarray) -> np.ndarray:
    """Derivation constraint matrix for quaternions. Null space = so(3).

    D: Im(H) → Im(H) satisfying D(xy) = D(x)y + xD(y).
    D(1)=0 is automatic, so unknowns are a 3×3 matrix (9 unknowns).
    Theory ref: exceptional-algebras.md (der(H) = so(3))
    """
    n_unknowns = 9
    equations = []
    for i in range(1, 4):
        for j in range(1, 4):
            for out_comp in range(4):
                row = np.zeros(n_unknowns)
                for k in range(1, 4):
                    coeff = struct[i, j, k]
                    if abs(coeff) < 1e-15:
                        continue
                    if out_comp >= 1:
                        row[(k - 1) * 3 + (out_comp - 1)] += coeff
                for a in range(3):
                    sc = struct[a + 1, j, out_comp]
                    if abs(sc) < 1e-15:
                        continue
                    row[(i - 1) * 3 + a] -= sc
                for a in range(3):
                    sc = struct[i, a + 1, out_comp]
                    if abs(sc) < 1e-15:
                        continue
                    row[(j - 1) * 3 + a] -= sc
                if np.any(np.abs(row) > 1e-15):
                    equations.append(row)
    return np.array(equations)


def division_algebra_derivation_dims() -> dict[str, int]:
    """Derivation algebra dimensions for each division algebra.

    Returns {"R": 0, "C": 0, "H": 3, "O": 14}.
    der(R) = 0 (reals have no nontrivial automorphisms)
    der(C) = 0 (complex conjugation is discrete, not continuous)
    der(H) = so(3) = 3 (quaternion derivations = weak gauge)
    der(O) = G₂ = 14 (octonion derivations = color source)
    Theory ref: force-structure.md §2, exceptional-algebras.md
    """
    # H: compute via constraint matrix null space
    h_struct = quaternion_struct()
    h_mat = quaternion_derivation_constraints(h_struct)
    h_rank = la.matrix_rank(h_mat, tol=1e-10)
    h_der = 9 - h_rank

    # O: compute via constraint matrix null space
    o_struct = octonion_struct()
    o_mat = octonion_derivation_constraints(o_struct)
    o_rank = la.matrix_rank(o_mat, tol=1e-10)
    o_der = 49 - o_rank

    return {"R": 0, "C": 0, "H": h_der, "O": o_der}


# ---------------------------------------------------------------------------
# Gauge subalgebra construction
# ---------------------------------------------------------------------------


def su3_generators() -> np.ndarray:
    """Extract 8 su(3) generators as vectors in so(8) basis (length 28).

    Method: G2 derivation equations + D(e1)=0 -> 8-dim null space.
    Returns shape (8, 28).

    Theory ref: octonion-derivation.md
    """
    struct = octonion_struct()
    base_rows = octonion_derivation_constraints(struct)

    fix_rows = np.zeros((7, 49))
    for a in range(7):
        fix_rows[a, a] = 1.0
    A = np.vstack([base_rows, fix_rows])

    _, s, Vt = la.svd(A)
    n_null = 49 - int(np.sum(s > 1e-10))
    null_vecs = Vt[-n_null:]

    assert null_vecs.shape[0] == 8, (
        f"Expected 8 su(3) generators, got {null_vecs.shape[0]}"
    )

    dim = so_dim(8)
    generators = np.zeros((8, dim))
    for g_idx in range(8):
        D7 = null_vecs[g_idx].reshape(7, 7)
        D8 = np.zeros((8, 8))
        D8[1:, 1:] = D7
        k = 0
        for i in range(8):
            for j in range(i + 1, 8):
                generators[g_idx, k] = D8[i, j]
                k += 1

    return generators


def su2_generators() -> np.ndarray:
    """Extract 3 su(2) generators from quaternionic left multiplication.

    Uses the first Fano triple (1,2,4).
    Returns shape (3, 28).

    Theory ref: octonion-derivation.md
    """
    struct = octonion_struct()
    quat_units = [1, 2, 4]
    quat_indices = [0, 1, 2, 4]
    dim = so_dim(8)
    generators = np.zeros((3, dim))

    for g_idx, a in enumerate(quat_units):
        L_full = octonion_left_mult(struct, a)
        L_restr = np.zeros((8, 8))
        for r in quat_indices:
            for c in quat_indices:
                L_restr[r, c] = L_full[r, c]
        A = 0.5 * (L_restr - L_restr.T)
        k = 0
        for i in range(8):
            for j in range(i + 1, 8):
                generators[g_idx, k] = A[i, j]
                k += 1

    return generators


# ---------------------------------------------------------------------------
# Gauge algebra structure: u(4) and hypercharge
# ---------------------------------------------------------------------------


def _ij_to_idx(i: int, j: int) -> int:
    """Map (i, j) pair with i < j to canonical basis index in so(8)."""
    idx = 0
    for ii in range(8):
        for jj in range(ii + 1, 8):
            if ii == i and jj == j:
                return idx
            idx += 1
    raise ValueError(f"Invalid pair ({i}, {j})")


def complex_structure_j() -> np.ndarray:
    """Complex structure J in centralizer of su(3) ⊂ so(8).

    J = -(1/√3)(E₂₄ + E₃₇ + E₅₆)

    The (2,4), (3,7), (5,6) pairs are the Fano triple complements of e₁:
    removing 1 from triples (1,2,4), (1,3,7), (1,5,6).

    J² = -(1/3)I₆ on {e₂,...,e₇}, J² = 0 on {e₀,e₁}.
    J commutes with su(3) (derivations fixing e₁).

    Returns shape (28,) coefficient vector.
    """
    J = np.zeros(so_dim(8))
    c = -1.0 / math.sqrt(3)
    J[_ij_to_idx(2, 4)] = c
    J[_ij_to_idx(3, 7)] = c
    J[_ij_to_idx(5, 6)] = c
    return J


def hypercharge_bl() -> np.ndarray:
    """Baryon-minus-lepton charge Y_{B-L} in so(8).

    Y_{B-L} = (√3/2) E₀₁ + (1/2) J

    Eigenvalue magnitudes (from Y_{B-L}²):
      - Leptons {e₀,e₁}: |q| = √3/2
      - Quarks {e₂,...,e₇}: |q| = 1/(2√3)
      - Ratio: 3 (exact, from algebra)

    Commutes with su(3). Does NOT commute with su(2).

    Returns shape (28,) coefficient vector (unit norm).
    """
    E01 = np.zeros(so_dim(8))
    E01[0] = 1.0
    J = complex_structure_j()
    return (math.sqrt(3) / 2) * E01 + 0.5 * J


def hypercharge_sm() -> np.ndarray:
    """SM-normalized hypercharge Y_SM in so(8).

    Y_SM = (1/2) E₀₁ - (1/6)(E₂₄ + E₃₇ + E₅₆)

    Eigenvalue magnitudes (from Y_SM²):
      8_v: |Y| = 1/2 (leptons) and 1/6 (quarks)
      8_s: |Y| = 1/2 (leptons) and 1/6 (quarks)
      8_c: |Y| = 1/3 and 0  (right-handed pattern)

    This is Y_{B-L} / √3, normalized so |Y_lepton| = 1/2.

    Returns shape (28,) coefficient vector.
    """
    return hypercharge_bl() / math.sqrt(3)


def u4_center() -> np.ndarray:
    """Center of the u(4) gauge algebra in so(8).

    Y_c = -(1/2) E₀₁ + (1/2)(E₂₄ + E₃₇ + E₅₆)

    This is the UNIQUE element (up to scale) commuting with all 12 gauge
    generators (su(3) ∪ su(2) ∪ u(1)).  It generates the u(1) center
    of u(4) = su(4) ⊕ u(1).

    Eigenvalue magnitudes on all three 8-dim reps:
      8_v: |Y_c| = 1/2 (all 8 states equal)

    Returns shape (28,) coefficient vector (unit norm).
    """
    E01 = np.zeros(so_dim(8))
    E01[0] = 1.0
    J = complex_structure_j()
    # Y_c = E01/2 + (√3/2) J = -(1/2) E₀₁ + (1/2)(E₂₄ + E₃₇ + E₅₆)
    # in terms of the two orthogonal centralizer generators.
    # From SVD: Y_c has components [-0.5, 0.5, 0.5, 0.5] at [E01, E24, E37, E56].
    Yc = np.zeros(so_dim(8))
    Yc[0] = -0.5
    Yc[_ij_to_idx(2, 4)] = 0.5
    Yc[_ij_to_idx(3, 7)] = 0.5
    Yc[_ij_to_idx(5, 6)] = 0.5
    return Yc


def gauge_generated_dim() -> int:
    """Dimension of the Lie algebra generated by su(3) ∪ su(2) ∪ u(1).

    Returns 16 (= dim u(4) = dim su(4) + 1).

    The 12 nominal gauge generators do NOT close: [su(3), su(2)] ≠ 0.
    The brackets generate 4 additional directions, giving u(4) ⊂ so(8).
    """
    return 16


def centralizer_su3_dim() -> int:
    """Dimension of the centralizer of su(3) in so(8).

    Returns 2.  The centralizer is span{E₀₁, J} and is ABELIAN:
    [E₀₁, J] = 0.  This means NO su(2) inside so(8) commutes with su(3),
    so the SM gauge group SU(3)×SU(2)×U(1) cannot embed as a direct product.
    """
    return 2


def sym2_rep(rep: np.ndarray) -> np.ndarray:
    """Build S²(V) representation matrices from a representation V.

    Given rep of shape (n_gens, d, d), returns shape (n_gens, d*(d+1)/2, d*(d+1)/2).
    Basis: {e_i⊗e_j + e_j⊗e_i}/√2 for i<j, and e_i⊗e_i for i=j.
    """
    n_gens, d, _ = rep.shape
    pairs: list[tuple[int, int]] = []
    for i in range(d):
        for j in range(i, d):
            pairs.append((i, j))
    dim_s2 = len(pairs)
    pair_idx = {p: k for k, p in enumerate(pairs)}

    out = np.zeros((n_gens, dim_s2, dim_s2))
    for g in range(n_gens):
        M = rep[g]
        for idx1, (i, j) in enumerate(pairs):
            for k in range(d):
                # M_{ki} contribution: acts on first index
                ii, jj = min(k, j), max(k, j)
                out[g, pair_idx[(ii, jj)], idx1] += M[k, i]
                # M_{kj} contribution: acts on second index
                ii, jj = min(i, k), max(i, k)
                out[g, pair_idx[(ii, jj)], idx1] += M[k, j]
    return out


# ---------------------------------------------------------------------------
# Representation theory (Clifford, spinor, decomposition)
# ---------------------------------------------------------------------------


def clifford_gammas(dim: int = 8) -> tuple[np.ndarray, np.ndarray]:
    """Gamma matrices (16x16) for Clifford algebra Cl(dim).

    Returns (gammas, chirality) where gammas has shape (dim, 16, 16).
    """
    s1 = np.array([[0, 1], [1, 0]], dtype=complex)
    s2 = np.array([[0, -1j], [1j, 0]], dtype=complex)
    s3 = np.array([[1, 0], [0, -1]], dtype=complex)
    I2 = np.eye(2, dtype=complex)

    gammas = np.zeros((dim, 16, 16), dtype=complex)
    for k in range(4):
        factors_even = [I2] * k + [s1] + [s3] * (3 - k)
        factors_odd = [I2] * k + [s2] + [s3] * (3 - k)
        mat_e = factors_even[0]
        for f in factors_even[1:]:
            mat_e = np.kron(mat_e, f)
        mat_o = factors_odd[0]
        for f in factors_odd[1:]:
            mat_o = np.kron(mat_o, f)
        gammas[2 * k] = mat_e
        gammas[2 * k + 1] = mat_o

    chirality = np.eye(16, dtype=complex)
    for i in range(dim):
        chirality = chirality @ gammas[i]

    return gammas, chirality


def spinor_reps_d4(
    gammas: np.ndarray, chirality: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    """Build 8x8 REAL representation matrices for 8_s and 8_c.

    Returns (spinor_s, spinor_c) each shape (28, 8, 8) real.
    """
    diag_c = np.diag(chirality).real
    plus_idx = np.where(diag_c > 0)[0]
    minus_idx = np.where(diag_c < 0)[0]

    P_plus = np.zeros((16, 8), dtype=complex)
    for col, idx in enumerate(plus_idx):
        P_plus[idx, col] = 1.0
    P_minus = np.zeros((16, 8), dtype=complex)
    for col, idx in enumerate(minus_idx):
        P_minus[idx, col] = 1.0

    spinor_s_raw = []
    spinor_c_raw = []
    for i in range(8):
        for j in range(i + 1, 8):
            sigma = (gammas[i] @ gammas[j] - gammas[j] @ gammas[i]) / 4
            spinor_s_raw.append(P_plus.conj().T @ sigma @ P_plus)
            spinor_c_raw.append(P_minus.conj().T @ sigma @ P_minus)
    spinor_s_raw = np.array(spinor_s_raw)
    spinor_c_raw = np.array(spinor_c_raw)

    C_mat = gammas[1] @ gammas[3] @ gammas[5] @ gammas[7]

    out = []
    for P, sp_raw in [(P_plus, spinor_s_raw), (P_minus, spinor_c_raw)]:
        C_p = (P.conj().T @ C_mat @ P).real
        eigvals, eigvecs = la.eigh(C_p)
        V_plus = eigvecs[:, eigvals > 0]
        V_minus = eigvecs[:, eigvals < 0]
        U = np.zeros((8, 8), dtype=complex)
        U[:, :V_plus.shape[1]] = V_plus
        U[:, V_plus.shape[1]:] = 1j * V_minus
        sp_real = np.array([(U.conj().T @ m @ U).real for m in sp_raw])
        out.append(sp_real)

    return out[0], out[1]


def decompose_rep_gauge(
    rep: np.ndarray,
    su3_gens: np.ndarray,
    su2_gens: np.ndarray,
    u1_gen: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Decompose a representation under su(3)xsu(2)xu(1).

    Returns (eigvecs, c2_su3, c2_su2, y_sq).
    """
    su3_mats = np.array([coeff_to_matrix(g, rep) for g in su3_gens])
    su2_mats = np.array([coeff_to_matrix(g, rep) for g in su2_gens])
    u1_mat = coeff_to_matrix(u1_gen, rep)

    C2_su3 = sum(m @ m for m in su3_mats)
    C2_su2 = sum(m @ m for m in su2_mats)
    Y_sq = u1_mat @ u1_mat

    A = 1.0 * C2_su3 + math.sqrt(2) * C2_su2 + math.sqrt(3) * Y_sq
    _, V = la.eigh(A)

    c2_su3 = np.diag(V.T @ C2_su3 @ V)
    c2_su2 = np.diag(V.T @ C2_su2 @ V)
    y_sq = np.diag(V.T @ Y_sq @ V)

    return V, c2_su3, c2_su2, y_sq


def adjoint_on_complement(
    gen_vec: np.ndarray,
    Q_comp: np.ndarray,
    f: np.ndarray,
) -> np.ndarray:
    """Adjoint action of generator on complement subspace.

    M[i,j] = Q_comp[:,i]^T @ [gen_vec, Q_comp[:,j]].
    """
    n_comp = Q_comp.shape[1]
    M = np.zeros((n_comp, n_comp))
    for j in range(n_comp):
        bracket = lie_bracket(gen_vec, Q_comp[:, j], f)
        for i in range(n_comp):
            M[i, j] = Q_comp[:, i] @ bracket
    return M


# ---------------------------------------------------------------------------
# Eigenvalue / multiplet clustering utilities
# ---------------------------------------------------------------------------


def cluster_eigenvalues(
    eigs: np.ndarray, tol: float = 1e-8,
) -> list[tuple[float, int]]:
    """Group sorted eigenvalues into (value, multiplicity) clusters."""
    clusters: list[tuple[float, int]] = []
    i = 0
    while i < len(eigs):
        val = eigs[i]
        count = 1
        while i + count < len(eigs) and abs(eigs[i + count] - val) < tol:
            count += 1
        clusters.append((float(val), count))
        i += count
    return clusters


def cluster_multiplets(
    quantum_nums: np.ndarray, tol: float = 1e-4,
) -> dict[tuple[float, ...], list[int]]:
    """Cluster states by quantum number tuples.

    Args:
        quantum_nums: shape (n_states, n_operators)
        tol: tolerance for matching

    Returns dict mapping rounded quantum number tuple to list of state indices.
    """
    n_states, n_ops = quantum_nums.shape
    multiplets: dict[tuple[float, ...], list[int]] = {}
    for k in range(n_states):
        key = tuple(round(float(quantum_nums[k, d]), 4) for d in range(n_ops))
        found = False
        for existing_key in multiplets:
            if all(abs(key[d] - existing_key[d]) < tol for d in range(n_ops)):
                multiplets[existing_key].append(k)
                found = True
                break
        if not found:
            multiplets[key] = [k]
    return multiplets


# ---------------------------------------------------------------------------
# SO8 algebra state (frozen dataclass + builder)
# ---------------------------------------------------------------------------


@dataclasses.dataclass(slots=True, frozen=True)
class SO8:
    """The so(8) algebra with octonion-derived gauge structure.

    All fields are numpy arrays. Frozen to prevent mutation across tests.
    """
    basis: np.ndarray   # (28, 8, 8) canonical E_{ij} basis
    f: np.ndarray       # (28, 28, 28) structure constants
    kf: np.ndarray      # (28, 28) Killing form (negative definite)
    g: np.ndarray       # (28, 28) bi-invariant metric = -kf (positive definite)
    su3: np.ndarray     # (8, 28) su(3) generators from G2 stabilizer
    su2: np.ndarray     # (3, 28) su(2) generators from quaternionic left mult
    u1: np.ndarray      # (28,) u(1) generator E_{01}
    gauge: np.ndarray   # (12, 28) full gauge subalgebra
    Q_comp: np.ndarray  # (28, 16) orthonormal basis of 16-dim complement


def build_so8() -> SO8:
    """Construct the full SO8 algebra state."""
    basis = so_basis(8)
    f = structure_constants(basis)
    kf = killing_form_numerical(f)
    g = -kf

    su3 = su3_generators()
    su2 = su2_generators()
    u1 = np.zeros(28)
    u1[0] = 1.0  # E_{01}
    gauge = np.vstack([su3, su2, u1.reshape(1, -1)])

    Q_gauge, _ = la.qr(gauge.T, mode="reduced")
    proj_comp = np.eye(28) - Q_gauge @ Q_gauge.T
    eigvals, eigvecs = la.eigh(proj_comp)
    Q_comp = eigvecs[:, eigvals > 0.5]

    return SO8(
        basis=basis, f=f, kf=kf, g=g,
        su3=su3, su2=su2, u1=u1, gauge=gauge,
        Q_comp=Q_comp,
    )


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


def baryon_asymmetry(K_: int, B_: int, L_: int, n_: int, S_: int) -> float:
    """Baryon-to-photon ratio eta.

    Formula: (K/B) × (1/L)^d × S/(S-1)
    where d = n(n-1)/2 = dim(SO(3,1)) = 6 (Lorentz group dimension).

    Theory ref: baryon-asymmetry.md
    """
    lorentz_dim = n_ * (n_ - 1) // 2
    return (K_ / B_) * (1 / L_) ** lorentz_dim * S_ / (S_ - 1)


def hubble_absolute(v: float, lambda_: float, B_: int, L_: int,
                    n_: int, K_: int) -> float:
    """Hubble constant absolute value in GeV.

    Formula: H₀ = v × λ^(B+L-Kn)
    where λ = 1/√L and the exponent 68 = B+L-Kn counts net cosmological
    cascade modes (total structure minus dimensional observation cost).

    Theory ref: hubble-absolute.md
    """
    cascade = B_ + L_ - K_ * n_
    return v * lambda_ ** cascade


def hubble_absolute_km_s_mpc(v: float, lambda_: float, B_: int, L_: int,
                              n_: int, K_: int) -> float:
    """Hubble constant in km/s/Mpc.

    Converts from GeV: H₀[1/s] = H₀[GeV] / ℏ[GeV·s],
    then H₀[km/s/Mpc] = H₀[1/s] × (1 Mpc in km).

    Theory ref: hubble-absolute.md
    """
    h0_gev = hubble_absolute(v, lambda_, B_, L_, n_, K_)
    h0_inv_s = h0_gev / HBAR_GEV_S
    return h0_inv_s * MPC_KM


# ---------------------------------------------------------------------------
# Quark mass formulas (quark-masses.md)
# ---------------------------------------------------------------------------


def ms_over_me(n_: int, S_: int, L_: int) -> float:
    """Strange-to-electron mass ratio.

    Structure: n²S (generational) - L (link cost) - L/n (confinement).
    Theory ref: quark-masses.md
    """
    return n_**2 * S_ - L_ - L_ / n_


def ms_over_md(L_: int, K_: int) -> float:
    """Strange-to-down mass ratio.

    Theory ref: quark-masses.md
    """
    return L_ + K_ / L_


def md_over_mu_quark(K_: int, S_: int) -> float:
    """Down-to-up quark mass ratio.

    Theory ref: quark-masses.md
    """
    return K_ * S_ / (S_ - 1)


def mc_over_ms(S_: int, K_: int, n_colors: int = N_COLORS) -> float:
    """Charm-to-strange mass ratio.

    Theory ref: quark-masses.md
    """
    return S_ + K_ / n_colors


def mb_over_mc(K_: int, n_: int, n_colors: int = N_COLORS) -> float:
    """Bottom-to-charm mass ratio.

    Theory ref: quark-masses.md
    """
    return n_colors + K_ / (n_ + n_colors)


def top_mass(v: float, K_: int, n_: int, S_: int) -> float:
    """Top quark mass (GeV).

    Theory ref: quark-masses.md
    """
    return v / math.sqrt(K_) * (1 - K_ / (n_**2 * S_))


# ---------------------------------------------------------------------------
# Neutrino mass formulas (neutrino-masses.md)
# ---------------------------------------------------------------------------


def neutrino_mass_e(
    m_e: float, K_: int, B_: int, n_: int, L_: int, S_: int,
) -> float:
    """Electron neutrino mass (same units as m_e input).

    Formula: m_e * (K/B)^2 * K/((nL)^2 * S) * (1 + K/(nLB))

    Second-order generational coupling: the neutrino (T∩S = ∅) gets mass
    only through 1/(nLS) leakage — the inverse of the muon's nLS/(nLS+1).
    The (nL)^2 * S denominator matches the muon g-2 base factor.

    Theory ref: neutrino-masses.md
    """
    nL = n_ * L_
    return m_e * (K_ / B_) ** 2 * K_ / (nL ** 2 * S_) * (1 + K_ / (nL * B_))


def dm2_ratio(L_: int, S_: int) -> float:
    """Ratio of neutrino mass-squared differences |Dm2_32|/|Dm2_21|.

    Theory ref: neutrino-masses.md
    """
    return float(L_ + S_)


# ---------------------------------------------------------------------------
# CKM Cabibbo angle (neutrino-mixing.md)
# ---------------------------------------------------------------------------


def cabibbo_sin(n_: int, S_: int) -> float:
    """|V_us| = sin(arctan((n-1)/S)).

    Theory ref: neutrino-mixing.md
    """
    return math.sin(math.atan((n_ - 1) / S_))


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
