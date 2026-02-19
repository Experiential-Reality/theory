/- BLD Calculus — Complement of u(4) in so(8)

   The 28-dimensional so(8) decomposes as u(4) ⊕ complement.
   The 16 u(4) generators (GaugeAlgebra.lean) each pair a "primary"
   skewBasis8 element with a "secondary" one. The 12 secondary elements
   are the complement: they carry the color-triplet interactions.

   Primary entries of u(4): (0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),
     (2,3),(2,4),(2,5),(2,6),(2,7),(3,5),(3,6),(3,7),(5,6)   [16 total]

   Complement (secondary entries, carrying chiral content):
     (1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(3,4),(4,5),(4,6),(4,7),(5,7),(6,7)
                                                                [12 total]

   Together: 16 + 12 = 28 = dim(so(8)).
-/

import BLD.Lie.Classical
import BLD.Lie.Bracket
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace BLD.Lie.Complement

open BLD.Lie

/-- The 12 complement generators: skewBasis8 elements not primary to u(4). -/
private def comp : Fin 12 → Matrix (Fin 8) (Fin 8) ℚ
  | ⟨0, _⟩ => skewBasis8 1 2
  | ⟨1, _⟩ => skewBasis8 1 3
  | ⟨2, _⟩ => skewBasis8 1 4
  | ⟨3, _⟩ => skewBasis8 1 5
  | ⟨4, _⟩ => skewBasis8 1 6
  | ⟨5, _⟩ => skewBasis8 1 7
  | ⟨6, _⟩ => skewBasis8 3 4
  | ⟨7, _⟩ => skewBasis8 4 5
  | ⟨8, _⟩ => skewBasis8 4 6
  | ⟨9, _⟩ => skewBasis8 4 7
  | ⟨10, _⟩ => skewBasis8 5 7
  | ⟨11, _⟩ => skewBasis8 6 7
  | ⟨n + 12, h⟩ => absurd h (by omega)

/-- Each complement element has a unique nonzero position. -/
private def comp_primary : Fin 12 → Fin 8 × Fin 8
  | ⟨0, _⟩ => (1, 2)
  | ⟨1, _⟩ => (1, 3)
  | ⟨2, _⟩ => (1, 4)
  | ⟨3, _⟩ => (1, 5)
  | ⟨4, _⟩ => (1, 6)
  | ⟨5, _⟩ => (1, 7)
  | ⟨6, _⟩ => (3, 4)
  | ⟨7, _⟩ => (4, 5)
  | ⟨8, _⟩ => (4, 6)
  | ⟨9, _⟩ => (4, 7)
  | ⟨10, _⟩ => (5, 7)
  | ⟨11, _⟩ => (6, 7)
  | ⟨n + 12, h⟩ => absurd h (by omega)

private theorem comp_primary_nonzero : ∀ i : Fin 12,
    comp i (comp_primary i).1 (comp_primary i).2 ≠ 0 := by native_decide

private theorem comp_cross_zero : ∀ i j : Fin 12, j ≠ i →
    comp j (comp_primary i).1 (comp_primary i).2 = 0 := by native_decide

/-- The 12 complement elements are linearly independent.
    Primary entry extraction: each element has a unique nonzero matrix position. -/
theorem comp_li : LinearIndependent ℚ comp := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h : (∑ j : Fin 12, g j • comp j) (comp_primary i).1 (comp_primary i).2 = 0 := by
    rw [hg]; rfl
  rw [Matrix.sum_apply, Finset.sum_eq_single i
    (fun j _ hji => by rw [Matrix.smul_apply, smul_eq_mul, comp_cross_zero i j hji, mul_zero])
    (fun h' => absurd (Finset.mem_univ _) h'),
    Matrix.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right (comp_primary_nonzero i)

/-- The complement spans a 12-dimensional subspace. -/
theorem complement_finrank :
    Module.finrank ℚ (Submodule.span ℚ (Set.range comp)) = 12 :=
  finrank_span_eq_card comp_li

/-- All 12 complement elements are skew-symmetric (in so(8)). -/
theorem comp_skew : ∀ i : Fin 12,
    Matrix.transpose (comp i) = -(comp i) := by native_decide

end BLD.Lie.Complement
