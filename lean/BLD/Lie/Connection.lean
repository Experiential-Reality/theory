/- BLD Calculus — Algebraic Levi-Civita Connection

   On a Lie group with bi-invariant metric g = -κ (Killing form),
   the Levi-Civita connection restricted to left-invariant vector fields is:

     ∇_X Y = 1/2 [X, Y]

   This file defines the algebraic connection on a Lie algebra and proves:
   1. Torsion-free: ∇_X Y - ∇_Y X = [X,Y]
   2. Metric-compatible: κ(∇_X Y, Z) + κ(Y, ∇_X Z) = 0  (from ad-invariance)
   3. Koszul formula: 2g(∇_X Y, Z) = g([X,Y],Z) - g([X,Z],Y) - g([Y,Z],X)
   4. Uniqueness: any torsion-free metric-compatible connection = 1/2[·,·]
   5. Geodesic equation: ∇_X X = 0  (since [X,X] = 0)

   These are valid for any Lie algebra with non-degenerate ad-invariant bilinear form.
   Specialized to so(8,ℚ) using the IsKilling instance from KillingForm.lean.

   MANIFOLD EQUIVALENCE: For a compact Lie group G with bi-invariant metric g,
   left-invariant vector fields form a Lie algebra 𝔤 ≅ T_e G. The Levi-Civita
   connection ∇ on (G, g) restricts to left-invariant fields as ∇_X Y = 1/2 [X,Y]
   (Milnor 1976, Thm 21.4; Helgason 1978, Ch. II §3). Since any vector field on G
   decomposes into left-invariant fields pointwise, and ∇ is determined by its values
   on left-invariant fields, our algebraic conn captures the full Riemannian connection.
   The proofs here at the Lie algebra level ARE the manifold-level proofs restricted
   to the left-invariant subbundle — no generality is lost.

   Reference: equation-of-motion.md §I, Milnor 1976, Helgason 1978
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.TraceForm
import Mathlib.Tactic.Module
import BLD.Lie.KillingForm

namespace BLD.Connection

-- ═══════════════════════════════════════════════════════════
-- Section 1: Abstract algebraic connection
-- ═══════════════════════════════════════════════════════════

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- The bi-invariant connection on a Lie algebra: ∇_X Y = 1/2 [X, Y].
    For a Lie group with bi-invariant metric, this IS the Levi-Civita connection
    restricted to left-invariant vector fields. -/
def conn (X Y : L) : L := (1/2 : ℚ) • ⁅X, Y⁆

/-- The torsion of a bilinear operator: T(X,Y) = ∇_X Y - ∇_Y X - [X,Y]. -/
def torsion (nabla : L → L → L) (X Y : L) : L :=
  nabla X Y - nabla Y X - ⁅X, Y⁆

/-- The bi-invariant connection is torsion-free: ∇_X Y - ∇_Y X = [X,Y]. -/
theorem conn_torsion_free (X Y : L) : torsion conn X Y = 0 := by
  simp only [torsion, conn, ← lie_skew Y X]
  module

/-- Metric compatibility: g(∇_X Y, Z) + g(Y, ∇_X Z) = 0
    when g is an ad-invariant bilinear form.

    For left-invariant fields, the directional derivative X·g(Y,Z) = 0
    (the metric is constant along the group), so this is the full
    metric compatibility condition. -/
theorem conn_metric_compatible
    (g : L →ₗ[ℚ] L →ₗ[ℚ] ℚ) (hinv : ∀ x y z : L, g ⁅x, y⁆ z = - g y ⁅x, z⁆)
    (X Y Z : L) :
    g (conn X Y) Z + g Y (conn X Z) = 0 := by
  simp only [conn, map_smul, LinearMap.smul_apply, smul_eq_mul]
  linarith [hinv X Y Z]

-- ═══════════════════════════════════════════════════════════
-- Section 2: Koszul formula and uniqueness
-- ═══════════════════════════════════════════════════════════

/-- Koszul formula for left-invariant fields.

    For left-invariant vector fields on a Lie group with bi-invariant metric,
    the directional derivative terms X·g(Y,Z) vanish (g is constant).
    The Koszul formula reduces to:
      2·g(∇_X Y, Z) = g([X,Y],Z) - g([X,Z],Y) - g([Y,Z],X)

    This is derived from torsion-free + metric-compatible. -/
theorem koszul_formula
    (nabla : L → L → L)
    (g : L →ₗ[ℚ] L →ₗ[ℚ] ℚ)
    (gsymm : ∀ x y, g x y = g y x)
    (htf : ∀ X Y, nabla X Y - nabla Y X = ⁅X, Y⁆)
    (hmc : ∀ X Y Z, g (nabla X Y) Z + g Y (nabla X Z) = 0)
    (X Y Z : L) :
    2 • g (nabla X Y) Z = g ⁅X, Y⁆ Z - g ⁅X, Z⁆ Y - g ⁅Y, Z⁆ X := by
  -- From metric compatibility with (X,Y,Z), (X,Z,Y), (Y,Z,X):
  --   g(∇_X Y, Z) = -g(Y, ∇_X Z)
  --   g(∇_X Z, Y) = -g(Z, ∇_X Y)   ... not quite, need to be more careful.
  -- Standard derivation: use mc and tf to express g(∇_X Y, Z) in terms of brackets.
  --
  -- mc(X,Y,Z): g(∇_X Y, Z) + g(Y, ∇_X Z) = 0      ...(1)
  -- mc(X,Z,Y): g(∇_X Z, Y) + g(Z, ∇_X Y) = 0      ...(2)
  -- From (1): g(∇_X Y, Z) = -g(Y, ∇_X Z)
  -- From (2): g(∇_X Z, Y) = -g(Z, ∇_X Y) = -g(∇_X Y, Z) [by symm of g]
  -- So g(Y, ∇_X Z) = g(∇_X Z, Y) [by symm] = -g(∇_X Y, Z)
  -- Consistent but doesn't give us brackets yet.
  --
  -- Use torsion-free: ∇_X Y = ∇_Y X + [X,Y]
  -- mc(Y,X,Z): g(∇_Y X, Z) + g(X, ∇_Y Z) = 0
  -- So g(∇_Y X, Z) = -g(X, ∇_Y Z)
  -- And ∇_X Y = ∇_Y X + [X,Y], so:
  -- g(∇_X Y, Z) = g(∇_Y X, Z) + g([X,Y], Z) = -g(X, ∇_Y Z) + g([X,Y], Z)
  --
  -- mc(Y,Z,X): g(∇_Y Z, X) + g(Z, ∇_Y X) = 0
  -- So g(∇_Y Z, X) = -g(Z, ∇_Y X) = -g(∇_Y X, Z) [symm] = g(X, ∇_Y Z) [from above]
  -- And g(X, ∇_Y Z) = g(∇_Y Z, X) [symm]
  --
  -- From tf: ∇_Y Z = ∇_Z Y + [Y,Z]
  -- g(X, ∇_Y Z) = g(X, ∇_Z Y) + g(X, [Y,Z])
  --
  -- mc(Z,Y,X): g(∇_Z Y, X) + g(Y, ∇_Z X) = 0
  -- So g(∇_Z Y, X) = -g(Y, ∇_Z X) = -g(∇_Z X, Y) [symm]
  -- And g(X, ∇_Z Y) = g(∇_Z Y, X) [symm] = -g(Y, ∇_Z X)
  --
  -- tf: ∇_Z X = ∇_X Z + [Z,X]
  -- g(Y, ∇_Z X) = g(Y, ∇_X Z) + g(Y, [Z,X])
  --
  -- From mc(X,Y,Z) [eq 1]: g(Y, ∇_X Z) = -g(∇_X Y, Z)
  -- So: g(Y, ∇_Z X) = -g(∇_X Y, Z) + g(Y, [Z,X])
  -- And: g(X, ∇_Z Y) = -g(Y, ∇_Z X) = g(∇_X Y, Z) - g(Y, [Z,X])
  --
  -- Substituting back:
  -- g(∇_X Y, Z) = -g(X, ∇_Y Z) + g([X,Y], Z)
  --             = -(g(X, ∇_Z Y) + g(X, [Y,Z])) + g([X,Y], Z)
  --             = -(g(∇_X Y, Z) - g(Y, [Z,X]) + g(X, [Y,Z])) + g([X,Y], Z)
  -- 2·g(∇_X Y, Z) = g([X,Y], Z) + g(Y, [Z,X]) - g(X, [Y,Z])
  --               = g([X,Y], Z) - g([X,Z], Y) - g([Y,Z], X)   [using skew + symm]
  -- g(∇_X Y, Z) = g(∇_Y X + [X,Y], Z) = g(∇_Y X, Z) + g([X,Y], Z)
  have h1 : g (nabla X Y) Z = g (nabla Y X) Z + g ⁅X, Y⁆ Z := by
    have := congr_arg (fun x => g x Z) (htf X Y)
    simp only [map_sub, LinearMap.sub_apply] at this; linarith
  -- g(∇_Y X, Z) = -g(X, ∇_Y Z) [mc(Y,X,Z)]
  have h2 : g (nabla Y X) Z = - g X (nabla Y Z) := by
    linarith [hmc Y X Z]
  -- g(X, ∇_Y Z) = g(X, ∇_Z Y + [Y,Z]) = g(X, ∇_Z Y) + g(X, [Y,Z])
  have h3 : g X (nabla Y Z) = g X (nabla Z Y) + g X ⁅Y, Z⁆ := by
    have := congr_arg (g X) (htf Y Z)
    simp only [map_sub] at this; linarith
  -- g(X, ∇_Z Y) = g(∇_Z Y, X) [symm] = -g(Y, ∇_Z X) [mc(Z,Y,X)]
  have h4 : g X (nabla Z Y) = - g Y (nabla Z X) := by
    rw [gsymm]; linarith [hmc Z Y X]
  -- g(Y, ∇_Z X) = g(Y, ∇_X Z + [Z,X]) = g(Y, ∇_X Z) + g(Y, [Z,X])
  have h5 : g Y (nabla Z X) = g Y (nabla X Z) + g Y ⁅Z, X⁆ := by
    have := congr_arg (g Y) (htf Z X)
    simp only [map_sub] at this; linarith
  -- g(Y, ∇_X Z) = -g(∇_X Y, Z) [mc(X,Y,Z)]
  have h6 : g Y (nabla X Z) = - g (nabla X Y) Z := by
    linarith [hmc X Y Z]
  -- Chain: g(∇_X Y, Z) = -g(X, ∇_Y Z) + g([X,Y], Z)   [h1 + h2]
  --        g(X, ∇_Y Z) = g(X, ∇_Z Y) + g(X, [Y,Z])     [h3]
  --        g(X, ∇_Z Y) = -g(Y, ∇_Z X)                    [h4]
  --        g(Y, ∇_Z X) = g(Y, ∇_X Z) + g(Y, [Z,X])      [h5]
  --        g(Y, ∇_X Z) = -g(∇_X Y, Z)                    [h6]
  -- => g(∇_X Y, Z) = -(-(-(- g(∇_X Y, Z) + g(Y,[Z,X])) + g(X,[Y,Z]))) + g([X,Y],Z)
  -- => 2·g(∇_X Y, Z) = g([X,Y], Z) - g(X, [Y,Z]) + g(Y, [Z,X])
  -- Rewrite [Z,X] = -[X,Z] and use g symmetry:
  -- g(Y, [Z,X]) = -g(Y, [X,Z]) = -g([X,Z], Y) [by symm... no, g(Y,[Z,X]) ≠ g([X,Z],Y)]
  -- Actually g(Y, [Z,X]) = g(Y, -[X,Z]) = -g(Y, [X,Z])
  -- And g(X, [Y,Z]) = g([Y,Z], X) [by symm]
  -- So: 2g(∇_X Y, Z) = g([X,Y], Z) - g([Y,Z], X) - g(Y, [X,Z])
  -- Now g(Y, [X,Z]) = g([X,Z], Y) [by symm]
  -- So: 2g(∇_X Y, Z) = g([X,Y], Z) - g([X,Z], Y) - g([Y,Z], X)  ✓
  have sk : g ⁅Z, X⁆ Y = - g ⁅X, Z⁆ Y := by
    rw [show (⁅Z, X⁆ : L) = -⁅X, Z⁆ from (lie_skew ..).symm, map_neg, LinearMap.neg_apply]
  rw [two_smul]
  linarith [h1, h2, h3, h4, h5, h6, gsymm Y ⁅Z, X⁆, gsymm X ⁅Y, Z⁆, sk]

/-- Uniqueness of Levi-Civita: if g is non-degenerate, symmetric, and ad-invariant,
    then any torsion-free metric-compatible connection equals 1/2[·,·]. -/
theorem levi_civita_unique
    (g : L →ₗ[ℚ] L →ₗ[ℚ] ℚ)
    (gsymm : ∀ x y, g x y = g y x)
    (hnd : ∀ x, (∀ y, g x y = 0) → x = 0)
    (hinv : ∀ x y z : L, g ⁅x, y⁆ z = - g y ⁅x, z⁆)
    (nabla : L → L → L)
    (htf : ∀ X Y, nabla X Y - nabla Y X = ⁅X, Y⁆)
    (hmc : ∀ X Y Z, g (nabla X Y) Z + g Y (nabla X Z) = 0)
    (X Y : L) :
    nabla X Y = conn X Y := by
  -- Show nabla X Y - conn X Y = 0 via non-degeneracy
  suffices h : ∀ Z, g (nabla X Y - conn X Y) Z = 0 by
    exact sub_eq_zero.mp (hnd (nabla X Y - conn X Y) h)
  intro Z
  rw [map_sub, LinearMap.sub_apply]
  -- From Koszul: 2·g(nabla X Y, Z) = g([X,Y],Z) - g([X,Z],Y) - g([Y,Z],X)
  have hk := koszul_formula nabla g gsymm htf hmc X Y Z
  -- Use ad-invariance to simplify the RHS to g([X,Y],Z)
  have hinv1 : g ⁅X, Z⁆ Y = - g ⁅X, Y⁆ Z := by
    rw [gsymm (⁅X, Z⁆) Y]
    have := hinv X Z Y
    rw [gsymm Z ⁅X, Y⁆] at this
    linarith [hinv X Y Z]
  have hinv2 : g ⁅Y, Z⁆ X = g ⁅X, Y⁆ Z := by
    have h := hinv Y Z X
    rw [gsymm ⁅Y, Z⁆ X]
    have : g X ⁅Y, Z⁆ = - g Z ⁅Y, X⁆ := by rw [gsymm]; exact h
    rw [← lie_skew Y X] at this
    simp only [map_neg, neg_neg] at this
    rw [gsymm Z ⁅X, Y⁆] at this
    linarith
  -- 2·g(nabla X Y, Z) = g([X,Y],Z)
  have hk' : 2 • g (nabla X Y) Z = g ⁅X, Y⁆ Z := by linarith [hk, hinv1, hinv2]
  -- 2·g(conn X Y, Z) = g([X,Y], Z)
  have hc : 2 • g (conn X Y) Z = g ⁅X, Y⁆ Z := by
    simp only [conn, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  -- Convert nsmul to addition for linarith
  simp only [two_smul] at hk' hc
  linarith

-- ═══════════════════════════════════════════════════════════
-- Section 3: Geodesic equation
-- ═══════════════════════════════════════════════════════════

/-- **Geodesic equation**: ∇_X X = 0 for all X.
    On a Lie group, this means one-parameter subgroups exp(tX) are geodesics.
    The body angular velocity is constant along geodesics: dΩ/dt = 0. -/
theorem geodesic_equation (X : L) : conn X X = 0 := by
  simp [conn, lie_self]

/-- The connection is antisymmetric: ∇_X Y = -∇_Y X.
    (Follows from conn X Y = 1/2[X,Y] and [X,Y] = -[Y,X].) -/
theorem conn_antisymm (X Y : L) : conn X Y = - conn Y X := by
  unfold conn
  rw [← lie_skew X Y, smul_neg]

-- ═══════════════════════════════════════════════════════════
-- Section 4: Instantiation on so(8,ℚ)
-- ═══════════════════════════════════════════════════════════

section SO8

open BLD.Lie BLD.Lie.KillingForm

/-- The Levi-Civita connection on so(8,ℚ): ∇_X Y = 1/2 [X, Y].
    This is the unique torsion-free metric-compatible connection for
    the bi-invariant Killing metric on SO(8). -/
noncomputable def conn_so8 (X Y : so8 ℚ) : so8 ℚ := conn X Y

/-- The Killing form on so(8) is ad-invariant (from Mathlib).
    κ([x,y],z) = -κ(y,[x,z]) -/
theorem killing_ad_invariant (x y z : so8 ℚ) :
    killingForm ℚ (so8 ℚ) ⁅x, y⁆ z = - killingForm ℚ (so8 ℚ) y ⁅x, z⁆ :=
  LieModule.traceForm_apply_lie_apply' ℚ (so8 ℚ) (so8 ℚ) x y z

/-- The connection on so(8) is torsion-free. -/
theorem conn_so8_torsion_free (X Y : so8 ℚ) :
    torsion conn X Y = 0 := conn_torsion_free X Y

/-- The connection on so(8) is compatible with the Killing form. -/
theorem conn_so8_metric_compatible (X Y Z : so8 ℚ) :
    killingForm ℚ (so8 ℚ) (conn X Y) Z +
    killingForm ℚ (so8 ℚ) Y (conn X Z) = 0 :=
  conn_metric_compatible (killingForm ℚ (so8 ℚ)) killing_ad_invariant X Y Z

/-- **Levi-Civita uniqueness on so(8)**: any torsion-free connection compatible
    with the Killing form must equal 1/2[·,·]. -/
theorem conn_so8_unique
    (nabla : so8 ℚ → so8 ℚ → so8 ℚ)
    (htf : ∀ X Y, nabla X Y - nabla Y X = ⁅X, Y⁆)
    (hmc : ∀ X Y Z, killingForm ℚ (so8 ℚ) (nabla X Y) Z +
                     killingForm ℚ (so8 ℚ) Y (nabla X Z) = 0)
    (X Y : so8 ℚ) :
    nabla X Y = conn X Y := by
  apply levi_civita_unique (killingForm ℚ (so8 ℚ))
  · -- symmetry of Killing form
    exact fun x y => LieModule.traceForm_comm ℚ (so8 ℚ) (so8 ℚ) x y
  · -- non-degeneracy (from IsKilling)
    intro x hx
    have : x ∈ LinearMap.ker (killingForm ℚ (so8 ℚ)) := by
      rw [LinearMap.mem_ker]
      ext y; exact hx y
    rwa [LieAlgebra.IsKilling.ker_killingForm_eq_bot] at this
  · exact killing_ad_invariant
  · exact htf
  · exact hmc

/-- The geodesic equation on so(8): ∇_X X = 0.
    One-parameter subgroups of SO(8) are geodesics. -/
theorem conn_so8_geodesic (X : so8 ℚ) : conn_so8 X X = 0 :=
  geodesic_equation X

end SO8

end BLD.Connection
