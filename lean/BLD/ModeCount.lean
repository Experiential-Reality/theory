/- BLD Calculus — Type-level Mode Count and α⁻¹

   The electromagnetic fine structure constant α⁻¹ = 137 computed
   from mode counts of three BLD types:

     τ_geom  = Π₄(Π₂₀(1))           μ = 4 × 20 = 80
     τ_bound = 1 + 1 + ... + 1       μ = 56     (56-fold sum of unit)
     τ_trav  = 1                      μ = 1

   α⁻¹ = μ(τ_geom) + μ(τ_bound) + μ(τ_trav) = 80 + 56 + 1 = 137

   Constants.lean proves n*L + B + 1 = 137 (arithmetic on constants).
   This file proves the same from actual BLD types and their mode counts.

   Reference: bld-calculus.md Proposition 8.5
-/

import BLD.Basic
import BLD.Cardinality

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- n-fold sum of unit
-- ═══════════════════════════════════════════════════════════

/-- Left-leaning binary tree of n+1 unit leaves.
    unitSum k has k+1 leaves, so modeCount = k+1.
    Used to build the boundary type τ_bound. -/
def unitSum : Nat → Ty
  | 0     => .unit
  | n + 1 => .sum .unit (unitSum n)

@[simp] theorem modeCount_unitSum (k : Nat) :
    (unitSum k).modeCount = k + 1 := by
  induction k with
  | zero => rfl
  | succ n ih => simp [unitSum, modeCount, ih]; omega

@[simp] theorem cardinality_unitSum (k : Nat) :
    (unitSum k).cardinality = k + 1 := by
  induction k with
  | zero => rfl
  | succ n ih => simp [unitSum, cardinality, ih]; omega

-- ═══════════════════════════════════════════════════════════
-- The three electromagnetic structure types
-- Reference: bld-calculus.md Proposition 8.5
-- ═══════════════════════════════════════════════════════════

/-- Geometric structure: Π₄(Π₂₀(1)).
    4 spacetime dimensions × 20 Riemann components. -/
def tau_geom : Ty := .prod 4 (.prod 20 .unit)

/-- Boundary structure: 56-fold sum of unit.
    56 = dim(Spin(8)) × 2 boundary modes. -/
def tau_bound : Ty := unitSum 55

/-- Traversal structure: unit.
    The observer contributes +1. -/
def tau_trav : Ty := .unit

-- ═══════════════════════════════════════════════════════════
-- Mode counts of the three types
-- ═══════════════════════════════════════════════════════════

theorem modeCount_geom : tau_geom.modeCount = 80 := by decide

theorem modeCount_bound : tau_bound.modeCount = 56 :=
  modeCount_unitSum 55

theorem modeCount_trav : tau_trav.modeCount = 1 := rfl

-- ═══════════════════════════════════════════════════════════
-- α⁻¹ = 137 from type-level mode counts
-- ═══════════════════════════════════════════════════════════

/-- **Proposition 8.5 (Type-level α⁻¹).**
    α⁻¹ = μ(τ_geom) + μ(τ_bound) + μ(τ_trav) = 80 + 56 + 1 = 137.

    This is α⁻¹ computed from actual BLD types, not just arithmetic
    on named constants. The types τ_geom, τ_bound, τ_trav are
    constructed from the BLD grammar and their mode counts sum to 137. -/
theorem alpha_inv_type_level :
    tau_geom.modeCount + tau_bound.modeCount + tau_trav.modeCount = 137 := by
  simp [modeCount_geom, modeCount_bound, modeCount_trav]

end Ty
