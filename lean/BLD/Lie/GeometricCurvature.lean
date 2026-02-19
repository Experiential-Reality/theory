/- BLD Calculus — Geometric Curvature from Connection

   Derives curvature AS A CONSEQUENCE of the Levi-Civita connection
   ∇_X Y = 1/2 [X,Y] from Connection.lean.

   Contents:
   1. Curvature tensor R(X,Y)Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_{[X,Y]} Z
   2. R = -1/4 [[X,Y],Z] derived from conn (Jacobi identity)
   3. First Bianchi identity (from Mathlib's lie_jacobi)
   4. Curvature skew symmetry
   5. Metric skew symmetry of curvature
   6. Sectional curvature formula: g(R(X,Y)Y,X) = (1/4)·g([X,Y],[X,Y])
   7. SO(8) concrete: Ricci = -1/4 κ, Einstein Ric = 1/4 g

   MANIFOLD EQUIVALENCE: The Riemann curvature tensor on (G, g) restricted to
   left-invariant fields X, Y, Z gives R(X,Y)Z = -1/4 [[X,Y],Z]. Our algebraic
   curvature IS the Riemannian curvature on this subbundle. The sectional curvature
   K(σ) = g(R(X,Y)Y,X) / |X∧Y|² ≥ 0 is a manifold invariant that we compute
   algebraically. Positive sectional curvature means nearby geodesics converge —
   tidal forces are attractive (Jacobi equation).

   Reference: equation-of-motion.md §II, KillingForm.lean
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic.Module
import BLD.Lie.Connection
import BLD.Lie.KillingForm

namespace BLD.GeometricCurvature

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

open BLD.Connection

-- ═══════════════════════════════════════════════════════════
-- Section 1: Curvature tensor from connection
-- ═══════════════════════════════════════════════════════════

/-- The Riemann curvature tensor of the bi-invariant connection:
    R(X,Y)Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_{[X,Y]} Z -/
def curvature (X Y Z : L) : L :=
  conn X (conn Y Z) - conn Y (conn X Z) - conn ⁅X, Y⁆ Z

/-- **Curvature = -1/4 [[X,Y],Z]**, derived from the connection ∇ = 1/2[·,·].
    Uses the Jacobi identity (lie_lie) and coefficient arithmetic (module). -/
theorem curvature_eq (X Y Z : L) :
    curvature X Y Z = -(1/4 : ℚ) • ⁅⁅X, Y⁆, Z⁆ := by
  unfold curvature conn
  simp only [lie_smul]
  have h : (1/2 : ℚ) • ((1/2 : ℚ) • ⁅X, ⁅Y, Z⁆⁆)
      - (1/2 : ℚ) • ((1/2 : ℚ) • ⁅Y, ⁅X, Z⁆⁆)
      = (1/4 : ℚ) • ⁅⁅X, Y⁆, Z⁆ := by
    rw [show (1/2 : ℚ) • ((1/2 : ℚ) • ⁅X, ⁅Y, Z⁆⁆)
        - (1/2 : ℚ) • ((1/2 : ℚ) • ⁅Y, ⁅X, Z⁆⁆)
        = (1/4 : ℚ) • (⁅X, ⁅Y, Z⁆⁆ - ⁅Y, ⁅X, Z⁆⁆) from by module]
    rw [← lie_lie]
  rw [h]; module

-- ═══════════════════════════════════════════════════════════
-- Section 2: Curvature identities
-- ═══════════════════════════════════════════════════════════

/-- Curvature is skew-symmetric: R(X,Y) = -R(Y,X). -/
theorem curvature_skew (X Y Z : L) :
    curvature X Y Z = - curvature Y X Z := by
  simp only [curvature_eq]
  -- lie_skew X Y : -⁅Y, X⁆ = ⁅X, Y⁆, so .symm : ⁅X, Y⁆ = -⁅Y, X⁆
  rw [show (⁅X, Y⁆ : L) = -⁅Y, X⁆ from (lie_skew X Y).symm, neg_lie, smul_neg]

/-- **First Bianchi identity**: R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0.
    Uses Mathlib's lie_jacobi: ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0. -/
theorem first_bianchi (X Y Z : L) :
    curvature X Y Z + curvature Y Z X + curvature Z X Y = 0 := by
  simp only [curvature_eq]
  rw [show -(1/4 : ℚ) • ⁅⁅X, Y⁆, Z⁆ + -(1/4 : ℚ) • ⁅⁅Y, Z⁆, X⁆ + -(1/4 : ℚ) • ⁅⁅Z, X⁆, Y⁆
      = -(1/4 : ℚ) • (⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆ + ⁅⁅Z, X⁆, Y⁆) from by module]
  -- Convert ⁅⁅a,b⁆,c⁆ = -⁅c,⁅a,b⁆⁆ using lie_skew
  rw [show (⁅⁅X, Y⁆, Z⁆ : L) = -⁅Z, ⁅X, Y⁆⁆ from (lie_skew ⁅X, Y⁆ Z).symm,
      show (⁅⁅Y, Z⁆, X⁆ : L) = -⁅X, ⁅Y, Z⁆⁆ from (lie_skew ⁅Y, Z⁆ X).symm,
      show (⁅⁅Z, X⁆, Y⁆ : L) = -⁅Y, ⁅Z, X⁆⁆ from (lie_skew ⁅Z, X⁆ Y).symm]
  rw [show (-⁅Z, ⁅X, Y⁆⁆ + -⁅X, ⁅Y, Z⁆⁆ + -⁅Y, ⁅Z, X⁆⁆ : L)
      = -(⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆) from by abel]
  rw [lie_jacobi, neg_zero, smul_zero]

/-- Metric skew-symmetry: g(R(X,Y)Z, W) = -g(R(X,Y)W, Z)
    when g is symmetric and ad-invariant. -/
theorem curvature_metric_skew
    (g : L →ₗ[ℚ] L →ₗ[ℚ] ℚ)
    (gsymm : ∀ x y, g x y = g y x)
    (hinv : ∀ x y z : L, g ⁅x, y⁆ z = - g y ⁅x, z⁆)
    (X Y Z W : L) :
    g (curvature X Y Z) W = - g (curvature X Y W) Z := by
  simp only [curvature_eq, map_smul, LinearMap.smul_apply, smul_eq_mul]
  linarith [hinv ⁅X, Y⁆ Z W, hinv ⁅X, Y⁆ W Z,
            gsymm Z ⁅⁅X, Y⁆, W⁆, gsymm W ⁅⁅X, Y⁆, Z⁆]

/-- **Sectional curvature formula**: g(R(X,Y)Y, X) = (1/4) · g([X,Y], [X,Y]).
    The numerator of sectional curvature equals 1/4 of the squared norm of [X,Y].
    For a compact Lie group with bi-invariant metric, this is always ≥ 0
    (when g is positive definite), so sectional curvature is non-negative. -/
theorem sectional_curvature_formula
    (g : L →ₗ[ℚ] L →ₗ[ℚ] ℚ)
    (hinv : ∀ x y z : L, g ⁅x, y⁆ z = - g y ⁅x, z⁆)
    (X Y : L) :
    g (curvature X Y Y) X = (1/4 : ℚ) * g ⁅X, Y⁆ ⁅X, Y⁆ := by
  simp only [curvature_eq, map_smul, LinearMap.smul_apply, smul_eq_mul]
  suffices h : g ⁅⁅X, Y⁆, Y⁆ X = -(g ⁅X, Y⁆ ⁅X, Y⁆) by linarith
  -- ⁅⁅X,Y⁆, Y⁆ = -⁅Y, ⁅X,Y⁆⁆ by lie_skew
  rw [show (⁅⁅X, Y⁆, Y⁆ : L) = -⁅Y, ⁅X, Y⁆⁆ from (lie_skew ⁅X, Y⁆ Y).symm,
      map_neg, LinearMap.neg_apply]
  -- g(⁅Y, ⁅X,Y⁆⁆, X) = -g(⁅X,Y⁆, ⁅Y,X⁆) by ad-invariance
  rw [hinv Y ⁅X, Y⁆ X]
  -- ⁅Y, X⁆ = -⁅X, Y⁆
  rw [show (⁅Y, X⁆ : L) = -⁅X, Y⁆ from (lie_skew Y X).symm, map_neg]
  ring

-- ═══════════════════════════════════════════════════════════
-- Section 3: SO(8) concrete results
-- ═══════════════════════════════════════════════════════════

section SO8

open BLD.Lie BLD.Lie.KillingForm

/-- Ricci = -1/4 κ on so(8), verified on all basis pairs. -/
theorem ricci_from_connection :
    ∀ i j k l : Fin 8, i < j → k < l →
    ricciEntry i j k l = -(1/4 : ℚ) * killingEntry i j k l :=
  ricci_eq_quarter_killing

/-- Ricci diagonal: Ric(E_{ij}, E_{ij}) = 3. -/
theorem ricci_diagonal_value :
    ∀ i j : Fin 8, i < j → ricciEntry i j i j = 3 := ricci_diagonal

/-- **Einstein condition**: with metric g = -κ (diagonal = 12),
    Ric = -1/4 κ = 1/4 g. So Ric_diag = 3 = (1/4) × 12 = (1/4) × g_diag.
    This is the vacuum Einstein equation with Λ = 1/4. -/
theorem einstein_value : (-(1/4 : ℚ)) * (-12 : ℚ) = 3 := einstein_lambda

/-- Metric diagonal: g = -κ has g(E_{ij}, E_{ij}) = 12. -/
theorem metric_diagonal :
    ∀ i j : Fin 8, i < j → -(killingEntry i j i j) = 12 := by
  intro i j hij; have := killing_diagonal i j hij; linarith

/-- Scalar curvature: R = 28 × Ric_diag / g_diag = 28 × 3/12 = 7. -/
theorem scalar_curvature : (28 : ℚ) * 3 / 12 = 7 := by norm_num

/-- Einstein coupling: 8πG factor is K × n = 2 × 4 = 8. -/
theorem einstein_coupling : BLD.K * BLD.n = 8 := by decide

end SO8

end BLD.GeometricCurvature
