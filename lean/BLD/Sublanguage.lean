/- BLD Calculus — Sublanguage Predicates

   Three fragments obtained by removing one constructor:
     LD = no Sum       (Link + Dimension only)
     BD = no Function  (Boundary + Dimension only)
     BL = no Product   (Boundary + Link only)

   Reference: bld-calculus.md Definitions 6.1–6.3
-/

import BLD.Basic

namespace Ty

-- ═══════════════════════════════════════════════════════════
-- Sublanguage predicates (inductive)
-- ═══════════════════════════════════════════════════════════

/-- A type is in the LD fragment (no Sum constructor).
    Reference: bld-calculus.md Definition 6.1 -/
inductive IsLD : Ty → Prop where
  | unit : IsLD .unit
  | fn   {a b : Ty} : IsLD a → IsLD b → IsLD (.fn a b)
  | prod {n : Nat} {t : Ty} : IsLD t → IsLD (.prod n t)

/-- A type is in the BD fragment (no Function constructor).
    Reference: bld-calculus.md Definition 6.2 -/
inductive IsBD : Ty → Prop where
  | unit : IsBD .unit
  | sum  {a b : Ty} : IsBD a → IsBD b → IsBD (.sum a b)
  | prod {n : Nat} {t : Ty} : IsBD t → IsBD (.prod n t)

/-- A type is in the BL fragment (no n-Product for n ≥ 2).
    Reference: bld-calculus.md Definition 6.3 -/
inductive IsBL : Ty → Prop where
  | unit : IsBL .unit
  | sum  {a b : Ty} : IsBL a → IsBL b → IsBL (.sum a b)
  | fn   {a b : Ty} : IsBL a → IsBL b → IsBL (.fn a b)

-- ═══════════════════════════════════════════════════════════
-- Boolean decision functions
-- Note: _root_.Bool avoids shadowing by Ty.Bool
-- ═══════════════════════════════════════════════════════════

/-- Decidable check: is a type in the LD fragment? -/
def isLD : Ty → _root_.Bool
  | .unit       => true
  | .sum _ _    => false
  | .fn a b     => isLD a && isLD b
  | .prod _ t   => isLD t

/-- Decidable check: is a type in the BD fragment? -/
def isBD : Ty → _root_.Bool
  | .unit       => true
  | .sum a b    => isBD a && isBD b
  | .fn _ _     => false
  | .prod _ t   => isBD t

/-- Decidable check: is a type in the BL fragment? -/
def isBL : Ty → _root_.Bool
  | .unit       => true
  | .sum a b    => isBL a && isBL b
  | .fn a b     => isBL a && isBL b
  | .prod _ _   => false

-- Helper for Bool.and proofs
private theorem band_eq_true {a b : _root_.Bool} :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

-- ═══════════════════════════════════════════════════════════
-- Soundness and completeness of decision functions
-- ═══════════════════════════════════════════════════════════

theorem isLD_iff (t : Ty) : isLD t = true ↔ IsLD t := by
  induction t with
  | unit => exact ⟨fun _ => .unit, fun _ => rfl⟩
  | sum a b _ _ => constructor <;> intro h <;> nomatch h
  | fn a b iha ihb =>
    constructor
    · intro h
      have h' := band_eq_true.mp h
      exact .fn (iha.mp h'.1) (ihb.mp h'.2)
    · intro h
      cases h with
      | fn ha hb => exact band_eq_true.mpr ⟨iha.mpr ha, ihb.mpr hb⟩
  | prod n t iht =>
    constructor
    · intro h; exact .prod (iht.mp h)
    · intro h; cases h with | prod ht => exact iht.mpr ht

theorem isBD_iff (t : Ty) : isBD t = true ↔ IsBD t := by
  induction t with
  | unit => exact ⟨fun _ => .unit, fun _ => rfl⟩
  | sum a b iha ihb =>
    constructor
    · intro h
      have h' := band_eq_true.mp h
      exact .sum (iha.mp h'.1) (ihb.mp h'.2)
    · intro h
      cases h with
      | sum ha hb => exact band_eq_true.mpr ⟨iha.mpr ha, ihb.mpr hb⟩
  | fn a b _ _ => constructor <;> intro h <;> nomatch h
  | prod n t iht =>
    constructor
    · intro h; exact .prod (iht.mp h)
    · intro h; cases h with | prod ht => exact iht.mpr ht

theorem isBL_iff (t : Ty) : isBL t = true ↔ IsBL t := by
  induction t with
  | unit => exact ⟨fun _ => .unit, fun _ => rfl⟩
  | sum a b iha ihb =>
    constructor
    · intro h
      have h' := band_eq_true.mp h
      exact .sum (iha.mp h'.1) (ihb.mp h'.2)
    · intro h
      cases h with
      | sum ha hb => exact band_eq_true.mpr ⟨iha.mpr ha, ihb.mpr hb⟩
  | fn a b iha ihb =>
    constructor
    · intro h
      have h' := band_eq_true.mp h
      exact .fn (iha.mp h'.1) (ihb.mp h'.2)
    · intro h
      cases h with
      | fn ha hb => exact band_eq_true.mpr ⟨iha.mpr ha, ihb.mpr hb⟩
  | prod n t _ => constructor <;> intro h <;> nomatch h

-- ═══════════════════════════════════════════════════════════
-- Decidable instances
-- ═══════════════════════════════════════════════════════════

instance : DecidablePred IsLD := fun t =>
  if h : isLD t = true then isTrue ((isLD_iff t).mp h)
  else isFalse (fun hld => h ((isLD_iff t).mpr hld))

instance : DecidablePred IsBD := fun t =>
  if h : isBD t = true then isTrue ((isBD_iff t).mp h)
  else isFalse (fun hbd => h ((isBD_iff t).mpr hbd))

instance : DecidablePred IsBL := fun t =>
  if h : isBL t = true then isTrue ((isBL_iff t).mp h)
  else isFalse (fun hbl => h ((isBL_iff t).mpr hbl))

-- ═══════════════════════════════════════════════════════════
-- Exclusion lemmas: each fragment excludes one constructor
-- ═══════════════════════════════════════════════════════════

/-- LD types contain no Sum. -/
theorem ld_not_sum {a b : Ty} : ¬ IsLD (.sum a b) := fun h => nomatch h

/-- BD types contain no Function. -/
theorem bd_not_fn {a b : Ty} : ¬ IsBD (.fn a b) := fun h => nomatch h

/-- BL types contain no Product. -/
theorem bl_not_prod {n : Nat} {t : Ty} : ¬ IsBL (.prod n t) := fun h => nomatch h

/-- Unit is in all three fragments. -/
theorem unit_in_all : IsLD .unit ∧ IsBD .unit ∧ IsBL .unit :=
  ⟨.unit, .unit, .unit⟩

-- ═══════════════════════════════════════════════════════════
-- Sublanguage intersection
-- ═══════════════════════════════════════════════════════════

/-- The intersection of all three sublanguages is exactly unit.
    LD excludes sum, BD excludes function, BL excludes product.
    Only unit remains. -/
theorem sublanguage_intersection (t : Ty) :
    IsLD t ∧ IsBD t ∧ IsBL t ↔ t = .unit := by
  constructor
  · intro ⟨hld, hbd, hbl⟩
    cases hld with
    | unit => rfl
    | fn _ _ => exact absurd hbd bd_not_fn
    | prod _ => exact absurd hbl bl_not_prod
  · intro h; subst h; exact unit_in_all

end Ty
