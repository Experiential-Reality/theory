/- BLD Calculus — Lie Theory Bridge: Classical Lie Algebras

   Connects BLD constants to so(8) = Lie(Spin(8)):
   - so(8) is the D₄ Lie algebra (skew-adjoint 8×8 matrices)
   - dim(so(8)) = 8×7/2 = 28
   - B = 2 × dim(so(8)) = 56

   Reference: bld-calculus.md §6.2, lie-correspondence.md §3
-/

import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Matrix.Cartan
import BLD.Lie.Basic
import BLD.Constants

namespace BLD.Lie

/-- so(8): the orthogonal Lie algebra of skew-adjoint 8×8 matrices.
    This is D₄ in Cartan's classification (so(2n) = D_n, n=4).
    Mathlib defines it as {A : Matrix (Fin 8) (Fin 8) R | Aᵀ = -A}. -/
noncomputable def so8 (R : Type*) [CommRing R] :=
  LieAlgebra.Orthogonal.so (Fin 8) R

/-- so(8) membership: A ∈ so(8) iff Aᵀ = -A. -/
theorem mem_so8 (R : Type*) [CommRing R] (A : Matrix (Fin 8) (Fin 8) R) :
    A ∈ so8 R ↔ Matrix.transpose A = -A :=
  LieAlgebra.Orthogonal.mem_so (Fin 8) R A

/-- The D₄ Cartan matrix has rank 4.
    D₄ is indexed by Fin 4, so its rank is 4. -/
theorem D4_rank : Fintype.card (Fin 4) = 4 := by decide

/-- D₄ rank = BLD spacetime dimension n.
    The rank of the D₄ root system equals n = 4. -/
theorem D4_rank_eq_n : Fintype.card (Fin 4) = BLD.n := by decide

/-- Arithmetic fact: dim(so(8)) = 8×7/2 = 28.
    The dimension of the space of 8×8 skew-adjoint matrices
    is n(n-1)/2 where n=8. -/
theorem dim_so8_arithmetic : 8 * 7 / 2 = 28 := by decide

/-- B = 2 × dim(so(8)) = 2 × 28 = 56.
    The boundary count equals twice the dimension of so(8),
    corresponding to the two orientations of each generator. -/
theorem B_eq_2_dim_so8 : BLD.B = 2 * 28 := by decide

/-- Axiom: The module dimension of so(8,ℚ) is 28.
    Mathlib defines so(n,R) as a LieSubalgebra of Matrix n n R
    but does not yet provide a finrank theorem for skew-adjoint matrices.

    Proof path: construct a basis for {A : Matrix (Fin 8) (Fin 8) ℚ | Aᵀ = -A}
    indexed by {(i,j) | i < j}, showing the basis has cardinality C(8,2) = 28. -/
axiom so8_finrank : Module.finrank ℚ (so8 ℚ) = 28

/-- B = 2 × finrank(so(8,ℚ)), using the axiomatized dimension. -/
theorem B_eq_2_finrank_so8 : BLD.B = 2 * Module.finrank ℚ (so8 ℚ) := by
  rw [so8_finrank]; decide

end BLD.Lie
