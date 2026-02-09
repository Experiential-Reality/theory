/- BLD Calculus — Lie Theory Bridge: Basic Structures

   The three components of any Lie algebra correspond to BLD primitives:
     D (Dimension) ↔ generators (basis of the algebra)
     L (Link)      ↔ structure constants (bracket coefficients fᵢⱼᵏ)
     B (Boundary)  ↔ topology (compact vs non-compact classification)

   Reference: bld-calculus.md §6, lie-correspondence.md
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import BLD.Constants

namespace BLD.Lie

/-- The three components of any Lie algebra that correspond to BLD primitives.
    Every simple Lie algebra decomposes into (generators, structure constants, topology),
    which maps to (D, L, B) in the BLD calculus.

    - `rank`: number of generators (D-count), equal to the rank of the root system
    - `structureConstantCount`: number of independent structure constants (L-count)
    - `boundaryCount`: number of boundary modes (B-count) -/
structure BLDDecomposition (R : Type*) [CommRing R] where
  /-- The Lie algebra carrier type -/
  algebra : Type*
  [instLieRing : LieRing algebra]
  [instLieAlgebra : LieAlgebra R algebra]
  /-- Number of generators (D-count = rank of root system) -/
  rank : Nat
  /-- Number of independent structure constants (L-count) -/
  structureConstantCount : Nat
  /-- Number of boundary modes (B-count) -/
  boundaryCount : Nat

attribute [instance] BLDDecomposition.instLieRing BLDDecomposition.instLieAlgebra

/-- A BLD correspondence connects BLD type-level constants to a Lie algebra decomposition.
    The key constraint: the BLD constants (B, L, n from Constants.lean)
    must equal the corresponding Lie algebra quantities. -/
structure BLDCorrespondence (R : Type*) [CommRing R] extends BLDDecomposition R where
  /-- D-count matches spacetime dimension n -/
  rank_eq : rank = BLD.n
  /-- L-count matches link count L -/
  struct_eq : structureConstantCount = BLD.L
  /-- B-count matches boundary count B -/
  boundary_eq : boundaryCount = BLD.B

end BLD.Lie
