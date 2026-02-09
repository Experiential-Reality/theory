/- BLD Calculus — Cardinality and Mode Count

   Cardinality: number of distinct closed values of a type.
   Reference: bld-calculus.md Proposition 7.2

   Mode count: structural dimensions (differs from cardinality for products).
   Reference: bld-calculus.md Definition 8.3
-/

import BLD.Basic

namespace Ty

/-- Cardinality of inhabitants of a type.

    |1|         = 1
    |τ₁ + τ₂|  = |τ₁| + |τ₂|
    |τ₁ → τ₂|  = |τ₂| ^ |τ₁|
    |Πₙ(τ)|    = |τ| ^ n
-/
def cardinality : Ty → Nat
  | .unit       => 1
  | .sum a b    => a.cardinality + b.cardinality
  | .fn a b     => b.cardinality ^ a.cardinality
  | .prod n t   => t.cardinality ^ n

/-- Structural mode count.

    μ(1)         = 1
    μ(τ₁ + τ₂)  = μ(τ₁) + μ(τ₂)
    μ(τ₁ → τ₂)  = μ(τ₂) ^ μ(τ₁)
    μ(Πₙ(τ))    = n × μ(τ)

    Differs from cardinality in the product case:
    cardinality counts inhabitants (|τ|^n),
    mode count counts structural dimensions (n × μ(τ)).
-/
def modeCount : Ty → Nat
  | .unit       => 1
  | .sum a b    => a.modeCount + b.modeCount
  | .fn a b     => b.modeCount ^ a.modeCount
  | .prod n t   => n * t.modeCount

-- ═══════════════════════════════════════════════════════════
-- Simp lemmas
-- ═══════════════════════════════════════════════════════════

@[simp] theorem cardinality_unit : Ty.unit.cardinality = 1 := rfl
@[simp] theorem cardinality_sum (a b : Ty) :
    (Ty.sum a b).cardinality = a.cardinality + b.cardinality := rfl
@[simp] theorem cardinality_fn (a b : Ty) :
    (Ty.fn a b).cardinality = b.cardinality ^ a.cardinality := rfl
@[simp] theorem cardinality_prod (n : Nat) (t : Ty) :
    (Ty.prod n t).cardinality = t.cardinality ^ n := rfl

@[simp] theorem modeCount_unit : Ty.unit.modeCount = 1 := rfl
@[simp] theorem modeCount_sum (a b : Ty) :
    (Ty.sum a b).modeCount = a.modeCount + b.modeCount := rfl
@[simp] theorem modeCount_fn (a b : Ty) :
    (Ty.fn a b).modeCount = b.modeCount ^ a.modeCount := rfl
@[simp] theorem modeCount_prod (n : Nat) (t : Ty) :
    (Ty.prod n t).modeCount = n * t.modeCount := rfl

-- ═══════════════════════════════════════════════════════════
-- Positivity: all types have cardinality ≥ 1
-- (Every BLD type is inhabited.)
-- ═══════════════════════════════════════════════════════════

private theorem pow_pos_of_pos {m : Nat} (n : Nat) (hm : 0 < m) : 0 < m ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih hm

/-- Every BLD type has at least one inhabitant. -/
theorem cardinality_pos (t : Ty) : 0 < t.cardinality := by
  induction t with
  | unit => decide
  | sum a b iha ihb => simp; omega
  | fn a b _ ihb => simp; exact pow_pos_of_pos _ ihb
  | prod n t iht => simp; exact pow_pos_of_pos _ iht

/-- Every sum type has cardinality ≥ 2.
    This is WHY Sum (B) is needed: it's the only way to get multiple values. -/
theorem cardinality_sum_ge_two (a b : Ty) :
    (Ty.sum a b).cardinality ≥ 2 := by
  simp
  have ha := cardinality_pos a
  have hb := cardinality_pos b
  omega

-- ═══════════════════════════════════════════════════════════
-- Mode count: NOT universally positive
--
-- μ(Π₀(τ)) = 0 × μ(τ) = 0 by definition.
-- The empty product has no structural modes.
-- This contrasts with cardinality: |Π₀(τ)| = |τ|^0 = 1.
-- ═══════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════
-- Cardinality vs mode count: when they agree and when they differ
-- ═══════════════════════════════════════════════════════════

/-- Cardinality and mode count agree on unit. -/
theorem card_eq_mode_unit : Ty.unit.cardinality = Ty.unit.modeCount := rfl

/-- Cardinality and mode count DIFFER on products of non-unit types.
    |Π₃(Bool)| = 2³ = 8, but μ(Π₃(Bool)) = 3 × 2 = 6. -/
theorem card_ne_mode_example :
    (Ty.prod 3 Ty.Bool).cardinality ≠ (Ty.prod 3 Ty.Bool).modeCount := by
  simp [Ty.Bool, cardinality, modeCount]

end Ty
