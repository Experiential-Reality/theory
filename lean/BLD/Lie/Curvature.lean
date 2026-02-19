/- BLD Calculus — Algebraic Curvature from Lie Bracket

   On a compact semisimple Lie group with bi-invariant metric g = -κ,
   the Levi-Civita connection is ∇_X Y = 1/2 [X,Y].

   This file proves the ALGEBRAIC consequence:
     R(X,Y)Z = -1/4 [[X,Y],Z]    (curvature from bracket)

   This is a pure Lie algebra identity — no Riemannian geometry needed.
   The proof uses Mathlib's `lie_lie` (Jacobi identity consequence)
   and the `module` tactic for coefficient arithmetic.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic.Module

namespace BLD.Curvature

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- The curvature of the bi-invariant connection ∇_X Y = (1/2)⁅X,Y⁆ equals -1/4 ⁅⁅X,Y⁆,Z⁆.

    Expanding:
      R(X,Y)Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_{[X,Y]} Z
             = (1/4)⁅X,⁅Y,Z⁆⁆ - (1/4)⁅Y,⁅X,Z⁆⁆ - (1/2)⁅⁅X,Y⁆,Z⁆

    Using lie_lie: ⁅⁅X,Y⁆,Z⁆ = ⁅X,⁅Y,Z⁆⁆ - ⁅Y,⁅X,Z⁆⁆, so the first two terms
    collapse to (1/4)⁅⁅X,Y⁆,Z⁆, giving (1/4 - 1/2)⁅⁅X,Y⁆,Z⁆ = -1/4 ⁅⁅X,Y⁆,Z⁆. -/
theorem curvature_bracket (X Y Z : L) :
    (1/2 : ℚ) • ⁅X, (1/2 : ℚ) • ⁅Y, Z⁆⁆
    - (1/2 : ℚ) • ⁅Y, (1/2 : ℚ) • ⁅X, Z⁆⁆
    - (1/2 : ℚ) • ⁅⁅X, Y⁆, Z⁆
    = -(1/4 : ℚ) • ⁅⁅X, Y⁆, Z⁆ := by
  -- Push 1/2 through inner brackets
  simp only [lie_smul]
  -- Combine first two terms via ← lie_lie
  have h : (1/2 : ℚ) • ((1/2 : ℚ) • ⁅X, ⁅Y, Z⁆⁆)
      - (1/2 : ℚ) • ((1/2 : ℚ) • ⁅Y, ⁅X, Z⁆⁆)
      = (1/4 : ℚ) • ⁅⁅X, Y⁆, Z⁆ := by
    rw [show (1/2 : ℚ) • ((1/2 : ℚ) • ⁅X, ⁅Y, Z⁆⁆)
        - (1/2 : ℚ) • ((1/2 : ℚ) • ⁅Y, ⁅X, Z⁆⁆)
        = (1/4 : ℚ) • (⁅X, ⁅Y, Z⁆⁆ - ⁅Y, ⁅X, Z⁆⁆) from by module]
    rw [← lie_lie]
  rw [h]
  -- 1/4 - 1/2 = -1/4
  module

end BLD.Curvature
