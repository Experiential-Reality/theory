/- BLD Calculus — Concrete Octonion Algebra

   The octonions 𝕆 as an 8-dimensional algebra over a commutative ring,
   with multiplication matching Degen's eight-square identity.

   Key result: normSq is multiplicative (normSq(ab) = normSq(a)·normSq(b)),
   proved via Mathlib's `sum_eight_sq_mul_sum_eight_sq`.

   Octonions are a NonAssocRing (not associative), but they have:
   - Multiplicative norm (composition algebra)
   - Star (conjugation) anti-involution
   - No zero divisors (over ordered fields)

   Reference: Baez, "The Octonions", Bull. AMS 39 (2002).
-/

import Mathlib.Algebra.Ring.Identities
import Mathlib.Algebra.Star.SelfAdjoint

set_option autoImplicit false

namespace BLD

-- ═══════════════════════════════════════════════════════════
-- Structure
-- ═══════════════════════════════════════════════════════════

/-- The octonions over a commutative ring R.
    Eight components: one real part (x1) and seven imaginary (x2-x8). -/
@[ext]
structure Octonion (R : Type*) where
  x1 : R
  x2 : R
  x3 : R
  x4 : R
  x5 : R
  x6 : R
  x7 : R
  x8 : R

variable {R : Type*}

-- ═══════════════════════════════════════════════════════════
-- Additive structure
-- ═══════════════════════════════════════════════════════════

instance [Zero R] : Zero (Octonion R) :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩⟩

instance [One R] [Zero R] : One (Octonion R) :=
  ⟨⟨1, 0, 0, 0, 0, 0, 0, 0⟩⟩

instance [Add R] : Add (Octonion R) :=
  ⟨fun a b => ⟨a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3, a.x4 + b.x4,
               a.x5 + b.x5, a.x6 + b.x6, a.x7 + b.x7, a.x8 + b.x8⟩⟩

instance [Neg R] : Neg (Octonion R) :=
  ⟨fun a => ⟨-a.x1, -a.x2, -a.x3, -a.x4, -a.x5, -a.x6, -a.x7, -a.x8⟩⟩

instance [Sub R] : Sub (Octonion R) :=
  ⟨fun a b => ⟨a.x1 - b.x1, a.x2 - b.x2, a.x3 - b.x3, a.x4 - b.x4,
               a.x5 - b.x5, a.x6 - b.x6, a.x7 - b.x7, a.x8 - b.x8⟩⟩

-- Simp lemmas for projections
section Simp

variable [CommRing R]

@[simp] theorem zero_x1 : (0 : Octonion R).x1 = 0 := rfl
@[simp] theorem zero_x2 : (0 : Octonion R).x2 = 0 := rfl
@[simp] theorem zero_x3 : (0 : Octonion R).x3 = 0 := rfl
@[simp] theorem zero_x4 : (0 : Octonion R).x4 = 0 := rfl
@[simp] theorem zero_x5 : (0 : Octonion R).x5 = 0 := rfl
@[simp] theorem zero_x6 : (0 : Octonion R).x6 = 0 := rfl
@[simp] theorem zero_x7 : (0 : Octonion R).x7 = 0 := rfl
@[simp] theorem zero_x8 : (0 : Octonion R).x8 = 0 := rfl

@[simp] theorem one_x1 : (1 : Octonion R).x1 = 1 := rfl
@[simp] theorem one_x2 : (1 : Octonion R).x2 = 0 := rfl
@[simp] theorem one_x3 : (1 : Octonion R).x3 = 0 := rfl
@[simp] theorem one_x4 : (1 : Octonion R).x4 = 0 := rfl
@[simp] theorem one_x5 : (1 : Octonion R).x5 = 0 := rfl
@[simp] theorem one_x6 : (1 : Octonion R).x6 = 0 := rfl
@[simp] theorem one_x7 : (1 : Octonion R).x7 = 0 := rfl
@[simp] theorem one_x8 : (1 : Octonion R).x8 = 0 := rfl

@[simp] theorem add_x1 (a b : Octonion R) : (a + b).x1 = a.x1 + b.x1 := rfl
@[simp] theorem add_x2 (a b : Octonion R) : (a + b).x2 = a.x2 + b.x2 := rfl
@[simp] theorem add_x3 (a b : Octonion R) : (a + b).x3 = a.x3 + b.x3 := rfl
@[simp] theorem add_x4 (a b : Octonion R) : (a + b).x4 = a.x4 + b.x4 := rfl
@[simp] theorem add_x5 (a b : Octonion R) : (a + b).x5 = a.x5 + b.x5 := rfl
@[simp] theorem add_x6 (a b : Octonion R) : (a + b).x6 = a.x6 + b.x6 := rfl
@[simp] theorem add_x7 (a b : Octonion R) : (a + b).x7 = a.x7 + b.x7 := rfl
@[simp] theorem add_x8 (a b : Octonion R) : (a + b).x8 = a.x8 + b.x8 := rfl

@[simp] theorem neg_x1 (a : Octonion R) : (-a).x1 = -a.x1 := rfl
@[simp] theorem neg_x2 (a : Octonion R) : (-a).x2 = -a.x2 := rfl
@[simp] theorem neg_x3 (a : Octonion R) : (-a).x3 = -a.x3 := rfl
@[simp] theorem neg_x4 (a : Octonion R) : (-a).x4 = -a.x4 := rfl
@[simp] theorem neg_x5 (a : Octonion R) : (-a).x5 = -a.x5 := rfl
@[simp] theorem neg_x6 (a : Octonion R) : (-a).x6 = -a.x6 := rfl
@[simp] theorem neg_x7 (a : Octonion R) : (-a).x7 = -a.x7 := rfl
@[simp] theorem neg_x8 (a : Octonion R) : (-a).x8 = -a.x8 := rfl

@[simp] theorem sub_x1 (a b : Octonion R) : (a - b).x1 = a.x1 - b.x1 := rfl
@[simp] theorem sub_x2 (a b : Octonion R) : (a - b).x2 = a.x2 - b.x2 := rfl
@[simp] theorem sub_x3 (a b : Octonion R) : (a - b).x3 = a.x3 - b.x3 := rfl
@[simp] theorem sub_x4 (a b : Octonion R) : (a - b).x4 = a.x4 - b.x4 := rfl
@[simp] theorem sub_x5 (a b : Octonion R) : (a - b).x5 = a.x5 - b.x5 := rfl
@[simp] theorem sub_x6 (a b : Octonion R) : (a - b).x6 = a.x6 - b.x6 := rfl
@[simp] theorem sub_x7 (a b : Octonion R) : (a - b).x7 = a.x7 - b.x7 := rfl
@[simp] theorem sub_x8 (a b : Octonion R) : (a - b).x8 = a.x8 - b.x8 := rfl

end Simp

-- ═══════════════════════════════════════════════════════════
-- Multiplication (Cayley-Dickson / Fano plane)
-- Sign conventions match sum_eight_sq_mul_sum_eight_sq
-- ═══════════════════════════════════════════════════════════

instance [CommRing R] : Mul (Octonion R) :=
  ⟨fun a b => ⟨
    a.x1 * b.x1 - a.x2 * b.x2 - a.x3 * b.x3 - a.x4 * b.x4 - a.x5 * b.x5 - a.x6 * b.x6 - a.x7 * b.x7 - a.x8 * b.x8,
    a.x1 * b.x2 + a.x2 * b.x1 + a.x3 * b.x4 - a.x4 * b.x3 + a.x5 * b.x6 - a.x6 * b.x5 - a.x7 * b.x8 + a.x8 * b.x7,
    a.x1 * b.x3 - a.x2 * b.x4 + a.x3 * b.x1 + a.x4 * b.x2 + a.x5 * b.x7 + a.x6 * b.x8 - a.x7 * b.x5 - a.x8 * b.x6,
    a.x1 * b.x4 + a.x2 * b.x3 - a.x3 * b.x2 + a.x4 * b.x1 + a.x5 * b.x8 - a.x6 * b.x7 + a.x7 * b.x6 - a.x8 * b.x5,
    a.x1 * b.x5 - a.x2 * b.x6 - a.x3 * b.x7 - a.x4 * b.x8 + a.x5 * b.x1 + a.x6 * b.x2 + a.x7 * b.x3 + a.x8 * b.x4,
    a.x1 * b.x6 + a.x2 * b.x5 - a.x3 * b.x8 + a.x4 * b.x7 - a.x5 * b.x2 + a.x6 * b.x1 - a.x7 * b.x4 + a.x8 * b.x3,
    a.x1 * b.x7 + a.x2 * b.x8 + a.x3 * b.x5 - a.x4 * b.x6 - a.x5 * b.x3 + a.x6 * b.x4 + a.x7 * b.x1 - a.x8 * b.x2,
    a.x1 * b.x8 - a.x2 * b.x7 + a.x3 * b.x6 + a.x4 * b.x5 - a.x5 * b.x4 - a.x6 * b.x3 + a.x7 * b.x2 + a.x8 * b.x1
  ⟩⟩

section MulSimp

variable [CommRing R] (a b : Octonion R)

@[simp] theorem mul_x1 : (a * b).x1 = a.x1 * b.x1 - a.x2 * b.x2 - a.x3 * b.x3 - a.x4 * b.x4 - a.x5 * b.x5 - a.x6 * b.x6 - a.x7 * b.x7 - a.x8 * b.x8 := rfl
@[simp] theorem mul_x2 : (a * b).x2 = a.x1 * b.x2 + a.x2 * b.x1 + a.x3 * b.x4 - a.x4 * b.x3 + a.x5 * b.x6 - a.x6 * b.x5 - a.x7 * b.x8 + a.x8 * b.x7 := rfl
@[simp] theorem mul_x3 : (a * b).x3 = a.x1 * b.x3 - a.x2 * b.x4 + a.x3 * b.x1 + a.x4 * b.x2 + a.x5 * b.x7 + a.x6 * b.x8 - a.x7 * b.x5 - a.x8 * b.x6 := rfl
@[simp] theorem mul_x4 : (a * b).x4 = a.x1 * b.x4 + a.x2 * b.x3 - a.x3 * b.x2 + a.x4 * b.x1 + a.x5 * b.x8 - a.x6 * b.x7 + a.x7 * b.x6 - a.x8 * b.x5 := rfl
@[simp] theorem mul_x5 : (a * b).x5 = a.x1 * b.x5 - a.x2 * b.x6 - a.x3 * b.x7 - a.x4 * b.x8 + a.x5 * b.x1 + a.x6 * b.x2 + a.x7 * b.x3 + a.x8 * b.x4 := rfl
@[simp] theorem mul_x6 : (a * b).x6 = a.x1 * b.x6 + a.x2 * b.x5 - a.x3 * b.x8 + a.x4 * b.x7 - a.x5 * b.x2 + a.x6 * b.x1 - a.x7 * b.x4 + a.x8 * b.x3 := rfl
@[simp] theorem mul_x7 : (a * b).x7 = a.x1 * b.x7 + a.x2 * b.x8 + a.x3 * b.x5 - a.x4 * b.x6 - a.x5 * b.x3 + a.x6 * b.x4 + a.x7 * b.x1 - a.x8 * b.x2 := rfl
@[simp] theorem mul_x8 : (a * b).x8 = a.x1 * b.x8 - a.x2 * b.x7 + a.x3 * b.x6 + a.x4 * b.x5 - a.x5 * b.x4 - a.x6 * b.x3 + a.x7 * b.x2 + a.x8 * b.x1 := rfl

end MulSimp

-- ═══════════════════════════════════════════════════════════
-- Casts (needed before NonAssocRing so simp lemmas are available)
-- ═══════════════════════════════════════════════════════════

instance [CommRing R] : NatCast (Octonion R) :=
  ⟨fun n => ⟨n, 0, 0, 0, 0, 0, 0, 0⟩⟩

instance [CommRing R] : IntCast (Octonion R) :=
  ⟨fun n => ⟨n, 0, 0, 0, 0, 0, 0, 0⟩⟩

section CastSimp

variable [CommRing R]

@[simp] theorem natCast_x1 (n : ℕ) : (↑n : Octonion R).x1 = ↑n := rfl
@[simp] theorem natCast_x2 (n : ℕ) : (↑n : Octonion R).x2 = 0 := rfl
@[simp] theorem natCast_x3 (n : ℕ) : (↑n : Octonion R).x3 = 0 := rfl
@[simp] theorem natCast_x4 (n : ℕ) : (↑n : Octonion R).x4 = 0 := rfl
@[simp] theorem natCast_x5 (n : ℕ) : (↑n : Octonion R).x5 = 0 := rfl
@[simp] theorem natCast_x6 (n : ℕ) : (↑n : Octonion R).x6 = 0 := rfl
@[simp] theorem natCast_x7 (n : ℕ) : (↑n : Octonion R).x7 = 0 := rfl
@[simp] theorem natCast_x8 (n : ℕ) : (↑n : Octonion R).x8 = 0 := rfl

@[simp] theorem intCast_x1 (n : ℤ) : (↑n : Octonion R).x1 = ↑n := rfl
@[simp] theorem intCast_x2 (n : ℤ) : (↑n : Octonion R).x2 = 0 := rfl
@[simp] theorem intCast_x3 (n : ℤ) : (↑n : Octonion R).x3 = 0 := rfl
@[simp] theorem intCast_x4 (n : ℤ) : (↑n : Octonion R).x4 = 0 := rfl
@[simp] theorem intCast_x5 (n : ℤ) : (↑n : Octonion R).x5 = 0 := rfl
@[simp] theorem intCast_x6 (n : ℤ) : (↑n : Octonion R).x6 = 0 := rfl
@[simp] theorem intCast_x7 (n : ℤ) : (↑n : Octonion R).x7 = 0 := rfl
@[simp] theorem intCast_x8 (n : ℤ) : (↑n : Octonion R).x8 = 0 := rfl

end CastSimp

-- ═══════════════════════════════════════════════════════════
-- NonAssocRing instance
-- ═══════════════════════════════════════════════════════════

instance [CommRing R] : NonAssocRing (Octonion R) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by ext <;> simp [add_comm]
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  zsmul := zsmulRec
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp [Nat.cast_succ]
  intCast_ofNat n := by ext <;> simp [Int.cast_natCast]
  intCast_negSucc n := by ext <;> simp [Int.cast_negSucc]

-- ═══════════════════════════════════════════════════════════
-- Star (conjugation)
-- ═══════════════════════════════════════════════════════════

instance [CommRing R] : Star (Octonion R) :=
  ⟨fun a => ⟨a.x1, -a.x2, -a.x3, -a.x4, -a.x5, -a.x6, -a.x7, -a.x8⟩⟩

section StarSimp

variable [CommRing R] (a : Octonion R)

@[simp] theorem star_x1 : (star a).x1 = a.x1 := rfl
@[simp] theorem star_x2 : (star a).x2 = -a.x2 := rfl
@[simp] theorem star_x3 : (star a).x3 = -a.x3 := rfl
@[simp] theorem star_x4 : (star a).x4 = -a.x4 := rfl
@[simp] theorem star_x5 : (star a).x5 = -a.x5 := rfl
@[simp] theorem star_x6 : (star a).x6 = -a.x6 := rfl
@[simp] theorem star_x7 : (star a).x7 = -a.x7 := rfl
@[simp] theorem star_x8 : (star a).x8 = -a.x8 := rfl

end StarSimp

instance [CommRing R] : StarRing (Octonion R) where
  star_involutive a := by ext <;> simp
  star_mul a b := by ext <;> simp <;> ring
  star_add a b := by ext <;> simp [add_comm]

-- ═══════════════════════════════════════════════════════════
-- Norm squared and Degen's identity
-- ═══════════════════════════════════════════════════════════

/-- The squared norm of an octonion: sum of squares of all 8 components. -/
def Octonion.normSq [CommRing R] (a : Octonion R) : R :=
  a.x1 ^ 2 + a.x2 ^ 2 + a.x3 ^ 2 + a.x4 ^ 2 +
  a.x5 ^ 2 + a.x6 ^ 2 + a.x7 ^ 2 + a.x8 ^ 2

/-- normSq is multiplicative: normSq(ab) = normSq(a) · normSq(b).
    This is the fundamental property of a composition algebra.
    Proved via Degen's eight-square identity (Mathlib). -/
theorem Octonion.normSq_mul [CommRing R] (a b : Octonion R) :
    Octonion.normSq (a * b) = Octonion.normSq a * Octonion.normSq b := by
  simp only [normSq, mul_x1, mul_x2, mul_x3, mul_x4, mul_x5, mul_x6, mul_x7, mul_x8]
  ring

theorem Octonion.normSq_zero [CommRing R] :
    Octonion.normSq (0 : Octonion R) = 0 := by
  simp [normSq]

theorem Octonion.normSq_one [CommRing R] :
    Octonion.normSq (1 : Octonion R) = 1 := by
  simp [normSq]

theorem Octonion.normSq_star [CommRing R] (a : Octonion R) :
    Octonion.normSq (star a) = Octonion.normSq a := by
  simp [normSq]

/-- normSq(a) = (a * star a).x1 (the real part of a times its conjugate). -/
theorem Octonion.normSq_eq_mul_star [CommRing R] (a : Octonion R) :
    Octonion.normSq a = (a * star a).x1 := by
  simp [normSq]
  ring

-- ═══════════════════════════════════════════════════════════
-- Non-associativity witness
-- ═══════════════════════════════════════════════════════════

/-- The octonions are NOT associative: e2 * (e3 * e5) ≠ (e2 * e3) * e5.
    This distinguishes them from quaternions and confirms the algebra
    is genuinely non-associative. -/
theorem Octonion.not_associative :
    ∃ (a b c : Octonion ℤ), a * (b * c) ≠ (a * b) * c := by
  -- e2 * (e3 * e5) = -e8 but (e2 * e3) * e5 = e8: x8 is -1 vs 1
  refine ⟨⟨0,1,0,0,0,0,0,0⟩, ⟨0,0,1,0,0,0,0,0⟩, ⟨0,0,0,0,1,0,0,0⟩, ?_⟩
  intro h
  have := congrArg Octonion.x8 h
  simp at this

end BLD
