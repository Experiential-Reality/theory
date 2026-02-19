/- BLD Calculus — Killing Form on so(8)

   The Killing form κ on so(8) is computed explicitly on the standard
   basis {E_{ij} : i < j} and shown to equal -12·I₂₈ (diagonal with
   all entries -12). This proves non-degeneracy.

   Method: for each basis pair, compute
     κ(E_{ij}, E_{kl}) = tr(ad_{E_{ij}} ∘ ad_{E_{kl}})
   where the trace is over the 28-dimensional adjoint representation.
   The adjoint action is the matrix commutator.

   Result: κ(E_{ij}, E_{kl}) = -12·δ_{(i,j),(k,l)}

   This is the standard formula κ(X,Y) = (n-2)·tr(XY) at n=8,
   combined with tr(E_{ij}²) = -2.
-/

import BLD.Lie.Bracket
import BLD.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Lie.Killing
import Mathlib.LinearAlgebra.Trace

namespace BLD.Lie.KillingForm

/-- The Killing form entry for so(8) basis elements.
    Computes tr(ad_{E_{ij}} ∘ ad_{E_{kl}}) on the 28-dim adjoint rep.

    The sum iterates over all basis elements E_{ab} (a < b) and
    extracts the (a,b) coefficient of [E_{ij}, [E_{kl}, E_{ab}]]. -/
def killingEntry (i j k l : Fin 8) : ℚ :=
  ∑ a : Fin 8, ∑ b : Fin 8,
    if a < b then
      let inner := skewBasis8 k l * skewBasis8 a b - skewBasis8 a b * skewBasis8 k l
      let outer := skewBasis8 i j * inner - inner * skewBasis8 i j
      outer a b
    else 0

/-- **Killing form diagonal: κ(E_{ij}, E_{ij}) = -12 for all i < j.**
    This is the Casimir value (n-2)·tr(E_{ij}²) = 6·(-2) = -12. -/
theorem killing_diagonal : ∀ i j : Fin 8, i < j →
    killingEntry i j i j = -12 := by native_decide

/-- **Killing form orthogonality: κ(E_{ij}, E_{kl}) = 0 when (i,j) ≠ (k,l).**
    The standard basis is orthogonal under the Killing form. -/
theorem killing_orthogonal : ∀ i j k l : Fin 8, i < j → k < l →
    (i, j) ≠ (k, l) → killingEntry i j k l = 0 := by native_decide

/-- Combined: the Killing matrix is -12 times the identity. -/
theorem killing_matrix : ∀ i j k l : Fin 8, i < j → k < l →
    killingEntry i j k l = if (i, j) = (k, l) then -12 else 0 := by native_decide

/-- **Non-degeneracy of the Killing form on so(8).**
    If κ(X, E_{kl}) = 0 for all basis elements E_{kl}, then X = 0.

    Proof: X = ∑ c_{ij} E_{ij}. Then κ(X, E_{kl}) = -12·c_{kl} = 0,
    so c_{kl} = 0 for all k < l, hence X = 0. -/
theorem killing_nondegenerate :
    ∀ i j : Fin 8, i < j → killingEntry i j i j ≠ 0 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Trace form and proportionality
-- ═══════════════════════════════════════════════════════════

/-- Matrix trace form: tr(X·Y) for 8×8 matrices. -/
def traceForm (X Y : Matrix (Fin 8) (Fin 8) ℚ) : ℚ :=
  Matrix.trace (X * Y)

/-- Trace form on basis: tr(E_{ij}·E_{kl}) = -2·δ_{(i,j),(k,l)}. -/
theorem trace_form_basis : ∀ i j k l : Fin 8, i < j → k < l →
    traceForm (skewBasis8 i j) (skewBasis8 k l) =
    if (i, j) = (k, l) then -2 else 0 := by native_decide

/-- **κ = 6·tr on so(8) basis.**
    The Killing form equals (n-2) times the trace form at n=8. -/
theorem killing_eq_6_trace : ∀ i j k l : Fin 8, i < j → k < l →
    killingEntry i j k l = 6 * traceForm (skewBasis8 i j) (skewBasis8 k l) := by
  native_decide

-- ═══════════════════════════════════════════════════════════
-- Ricci = -1/4 κ (concrete verification on so(8))
-- ═══════════════════════════════════════════════════════════

/-- Ricci entry: Ric(E_{ij}, E_{kl}) = ∑_{a<b} (E_{ij}-coefficient of R(E_{ab}, E_{ij})E_{kl}).
    Using R(Z,X)Y = -1/4 ⁅⁅Z,X⁆,Y⁆:
    = -1/4 · ∑_{a<b} (coefficient of E_{ab} in ⁅⁅E_{ab}, E_{ij}⁆, E_{kl}⁆) -/
def ricciEntry (i j k l : Fin 8) : ℚ :=
  ∑ a : Fin 8, ∑ b : Fin 8,
    if a < b then
      let brack1 := skewBasis8 a b * skewBasis8 i j - skewBasis8 i j * skewBasis8 a b
      let brack2 := brack1 * skewBasis8 k l - skewBasis8 k l * brack1
      (-(1 : ℚ) / 4) * brack2 a b
    else (0 : ℚ)

/-- **Ricci = -1/4 · Killing on so(8) basis.**
    Verified entry-by-entry: Ric(E_{ij}, E_{kl}) = -1/4 · κ(E_{ij}, E_{kl}). -/
theorem ricci_eq_quarter_killing : ∀ i j k l : Fin 8, i < j → k < l →
    ricciEntry i j k l = -(1/4 : ℚ) * killingEntry i j k l := by
  native_decide

/-- Ricci diagonal: Ric(E_{ij}, E_{ij}) = -1/4 · (-12) = 3. -/
theorem ricci_diagonal : ∀ i j : Fin 8, i < j →
    ricciEntry i j i j = 3 := by native_decide

/-- With metric g = -κ = 12·I: Ric = 1/4·g (Einstein with Λ = 1/4).
    -1/4 · κ = -1/4 · (-12)·I = 3·I = (1/4)·(12·I) = (1/4)·g. -/
theorem einstein_lambda : (-(1/4 : ℚ)) * (-12) = 3 := by norm_num

-- ═══════════════════════════════════════════════════════════
-- IsKilling instance for so(8,ℚ)
-- ═══════════════════════════════════════════════════════════

section IsKilling

open BLD.Lie Module

/-- The canonical basis for so(8,ℚ), indexed by pairs (i,j) with i < j. -/
noncomputable def basis_so8 : Basis SkewIdx ℚ (so8 ℚ) :=
  Basis.mk bv_li bv_span

/-- skewBasis8 agrees with skewMat on valid index pairs. -/
theorem skewBasis8_eq_skewMat (p : SkewIdx) :
    skewBasis8 p.val.1 p.val.2 = skewMat p := rfl

/-- Lie bracket on so(8) = matrix commutator (val projection). -/
theorem lie_val (x y : so8 ℚ) :
    (⁅x, y⁆ : so8 ℚ).val = x.val * y.val - y.val * x.val := by
  have := LieSubalgebra.coe_bracket (L' := LieAlgebra.Orthogonal.so (Fin 8) ℚ) x y
  simp only [Ring.lie_def] at this
  exact this

/-- Extract matrix entry (i,j) as a linear map on so(8,ℚ). -/
private def entryAt (q : SkewIdx) : so8 ℚ →ₗ[ℚ] ℚ where
  toFun x := x.val q.val.1 q.val.2
  map_add' x y := by
    show (x + y).val q.val.1 q.val.2 = x.val q.val.1 q.val.2 + y.val q.val.1 q.val.2
    simp [AddMemClass.add_def]
  map_smul' r x := by
    show (r • x).val q.val.1 q.val.2 = r * x.val q.val.1 q.val.2
    simp [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul]

/-- entryAt agrees with basis_so8.coord on basis elements (both are Kronecker delta). -/
private theorem entryAt_basis (p q : SkewIdx) :
    entryAt q (basis_so8 p) = basis_so8.coord q (basis_so8 p) := by
  simp only [entryAt, LinearMap.coe_mk, AddHom.coe_mk, Basis.coord_apply,
             Basis.repr_self, Finsupp.single_apply]
  rw [show (basis_so8 p : so8 ℚ).val = skewMat p from by
    simp [basis_so8, Basis.mk_apply, bv]]
  by_cases hpq : p = q
  · subst hpq; rw [skewMat_self, if_pos rfl]
  · rw [skewMat_other p q hpq, if_neg hpq]

/-- The two linear maps (entry extraction and basis coordinate) agree. -/
private theorem entryAt_eq_coord (q : SkewIdx) :
    entryAt q = basis_so8.coord q :=
  basis_so8.ext fun p => entryAt_basis p q

/-- Basis representation extracts the upper-triangular matrix entry.
    For x ∈ so(8), the coefficient of E_{ij} in the basis decomposition
    equals the (i,j) entry of the matrix. -/
theorem basis_repr_eq_entry (x : so8 ℚ) (q : SkewIdx) :
    basis_so8.repr x q = x.val q.val.1 q.val.2 := by
  rw [← Basis.coord_apply, ← entryAt_eq_coord]; rfl

/-- Computable Killing form on SkewIdx (sum over SkewIdx instead of Fin 8 × Fin 8). -/
private def killingEntryIdx (p q : SkewIdx) : ℚ :=
  ∑ r : SkewIdx,
    let inner := skewBasis8 q.val.1 q.val.2 * skewBasis8 r.val.1 r.val.2 -
                 skewBasis8 r.val.1 r.val.2 * skewBasis8 q.val.1 q.val.2
    let outer := skewBasis8 p.val.1 p.val.2 * inner - inner * skewBasis8 p.val.1 p.val.2
    outer r.val.1 r.val.2

/-- killingEntryIdx = killingEntry (verified by kernel computation). -/
private theorem killingEntryIdx_eq :
    ∀ p q : SkewIdx,
    killingEntryIdx p q = killingEntry p.val.1 p.val.2 q.val.1 q.val.2 := by native_decide

/-- **Bridge theorem**: Mathlib's abstract killingForm on basis elements
    equals our concrete killingEntry computation.

    Proof chain:
    killingForm (bv p) (bv q)
    = trace (ad(bv p) ∘ ad(bv q))              [killingForm_apply_apply]
    = ∑ r, b.repr(ad(bv p)(ad(bv q)(bv r))) r  [trace_eq_matrix_trace]
    = ∑ r, (⁅bv p, ⁅bv q, bv r⁆⁆).val r.1 r.2 [basis_repr_eq_entry]
    = killingEntryIdx p q                        [lie_val + skewBasis8_eq_skewMat]
    = killingEntry ...                           [native_decide] -/
theorem killingForm_bv_eq (p q : SkewIdx) :
    killingForm ℚ (so8 ℚ) (bv p) (bv q) =
    killingEntry p.val.1 p.val.2 q.val.1 q.val.2 := by
  rw [← killingEntryIdx_eq]
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℚ basis_so8]
  unfold killingEntryIdx
  simp only [Matrix.trace, Matrix.diag]
  congr 1; ext r
  simp only [LinearMap.toMatrix_apply]
  rw [basis_repr_eq_entry]
  simp only [LinearMap.comp_apply]
  -- The goal has basis_so8 r; convert to bv r
  rw [show basis_so8 r = bv r from Basis.mk_apply bv_li bv_span r]
  -- Unfold ad to bracket, then bracket to matrix commutator
  simp only [LieAlgebra.ad_apply]
  rw [lie_val, lie_val]
  -- (bv x).val = skewMat x = skewBasis8 x.1 x.2 all by rfl
  rfl

/-- killingForm (bv q) as a linear map = -12 × entry extraction.
    This uses the bridge + killing_matrix (κ = -12·I₂₈). -/
private theorem killingForm_bv_neg12 (q : SkewIdx) :
    killingForm ℚ (so8 ℚ) (bv q) = (-12 : ℚ) • entryAt q := by
  apply basis_so8.ext
  intro p
  simp only [LinearMap.smul_apply, smul_eq_mul]
  -- LHS: killingForm (bv q) (basis_so8 p)
  rw [show basis_so8 p = bv p from Basis.mk_apply bv_li bv_span p]
  rw [killingForm_bv_eq]
  rw [killing_matrix q.val.1 q.val.2 p.val.1 p.val.2 q.property p.property]
  -- RHS: -12 * entryAt q (bv p)
  simp only [entryAt, LinearMap.coe_mk, AddHom.coe_mk, bv]
  by_cases hpq : (q.val.1, q.val.2) = (p.val.1, p.val.2)
  · rw [if_pos hpq]
    have : p = q := Subtype.ext (Prod.ext (congr_arg Prod.fst hpq).symm
                                          (congr_arg Prod.snd hpq).symm)
    subst this; rw [skewMat_self]; ring
  · rw [if_neg hpq]
    have : p ≠ q := fun h => hpq (by subst h; rfl)
    rw [skewMat_other p q this]; ring

/-- Killing form bilinear expansion: κ(x,y) = -12 · Σ_p (x_p)·(y_p).
    Follows from basis decomposition in the second argument, symmetry,
    and κ = -12·I₂₈ (killingForm_bv_neg12). -/
private theorem killingForm_expansion (x y : so8 ℚ) :
    killingForm ℚ (so8 ℚ) x y =
    -12 * ∑ p : SkewIdx, x.val p.val.1 p.val.2 * y.val p.val.1 p.val.2 := by
  -- Decompose second argument: y = ∑_p c_p • bv p
  have hy : y = ∑ p : SkewIdx, basis_so8.repr y p • bv p := by
    conv_lhs => rw [← basis_so8.sum_repr y]
    simp_rw [show ∀ p : SkewIdx, basis_so8 p = bv p from
      fun p => Basis.mk_apply bv_li bv_span p]
  -- Expand via linearity in second argument (only LHS)
  conv_lhs => rw [hy]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  -- Swap arguments using symmetry of killing form
  have hsymm : ∀ p : SkewIdx, killingForm ℚ (so8 ℚ) x (bv p) =
    killingForm ℚ (so8 ℚ) (bv p) x := fun p =>
    LieModule.traceForm_comm ℚ (so8 ℚ) (so8 ℚ) x (bv p)
  simp_rw [hsymm]
  -- Use killingForm_bv_neg12: killingForm (bv p) = -12 • entryAt p
  simp_rw [killingForm_bv_neg12, LinearMap.smul_apply, smul_eq_mul,
           show ∀ q : SkewIdx, entryAt q x = x.val q.val.1 q.val.2 from fun _ => rfl,
           basis_repr_eq_entry]
  -- Normalize each term and factor out -12
  have hterm : ∀ p ∈ Finset.univ,
    (y.val (p : SkewIdx).val.1 p.val.2) * ((-12 : ℚ) * (x.val p.val.1 p.val.2)) =
    (-12 : ℚ) * (x.val p.val.1 p.val.2 * y.val p.val.1 p.val.2) := fun p _ => by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

/-- **Killing form on self**: κ(x,x) = -12 · Σ_p (x_p)².
    The Killing form on any element decomposes as -12 times the sum of
    squared basis coordinates. -/
theorem killingForm_self_eq (x : so8 ℚ) :
    killingForm ℚ (so8 ℚ) x x =
    -12 * ∑ p : SkewIdx, (x.val p.val.1 p.val.2) ^ 2 := by
  rw [killingForm_expansion]; congr 1
  apply Finset.sum_congr rfl; intro p _; ring

/-- **Negative Killing form is PSD**: -κ(x,x) ≥ 0 for all x ∈ so(8,ℚ).
    Since κ(x,x) = -12·Σ(x_p²), we have -κ(x,x) = 12·Σ(x_p²) ≥ 0. -/
theorem neg_killing_nonneg (x : so8 ℚ) :
    - killingForm ℚ (so8 ℚ) x x ≥ 0 := by
  rw [killingForm_self_eq]
  have : 0 ≤ ∑ p : SkewIdx, (x.val p.val.1 p.val.2) ^ 2 :=
    Finset.sum_nonneg fun p _ => sq_nonneg _
  linarith

/-- **IsKilling instance for so(8,ℚ).**
    The Killing form κ = -12·I₂₈ on so(8) is non-degenerate, closing
    Step 1 of the completeness proof chain. -/
instance : LieAlgebra.IsKilling ℚ (so8 ℚ) where
  killingCompl_top_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    rw [LieIdeal.mem_killingCompl] at hx
    simp only [LieSubmodule.mem_top, forall_true_left] at hx
    rw [LieSubmodule.mem_bot]
    -- hx : ∀ y, killingForm ℚ (so8 ℚ) y x = 0
    -- Show all basis coordinates are 0, hence x = 0
    suffices h : basis_so8.repr x = 0 by
      exact_mod_cast basis_so8.repr.injective (by rw [h, map_zero])
    ext q
    rw [Finsupp.zero_apply, basis_repr_eq_entry]
    -- killingForm (bv q) x = 0 implies x.val q.1 q.2 = 0
    have hq := hx (bv q)
    rw [killingForm_bv_neg12] at hq
    simp only [LinearMap.smul_apply, smul_eq_mul, entryAt, LinearMap.coe_mk, AddHom.coe_mk] at hq
    linarith

end IsKilling

end BLD.Lie.KillingForm
