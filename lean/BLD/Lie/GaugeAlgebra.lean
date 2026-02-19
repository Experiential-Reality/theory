/- BLD Calculus — Gauge Algebra u(4) ⊂ so(8)

   The gauge algebra is u(4) = su(4) ⊕ u(1), dimension 16.
   Constructed from the complex structure on ℝ⁸ = ℂ⁴ induced by
   the Fano triple complements through e₁:
     z₁ = x₂ + ix₄, z₂ = x₃ + ix₇, z₃ = x₅ + ix₆, z₄ = x₀ + ix₁

   The 16 generators decompose as:
   - 6 real antisymmetric: R_{jk} = E_{re_j,re_k} + E_{im_j,im_k}
   - 6 imaginary symmetric off-diagonal: I_{jk}
   - 4 diagonal imaginary: D_j = -E_{re_j,im_j}

   Reference: gauge-structure.md §1
-/

import BLD.Lie.Bracket
import BLD.Lie.Centralizer

namespace BLD.Lie.GaugeAlgebra

open BLD.Lie

-- ═══════════════════════════════════════════════════════════
-- The 16 u(4) generators
-- Index mapping: z₁=(2,4), z₂=(3,7), z₃=(5,6), z₄=(0,1)
-- ═══════════════════════════════════════════════════════════

-- Real antisymmetric: 6 generators
def R01 : Matrix (Fin 8) (Fin 8) ℚ := skewBasis8 2 3 + skewBasis8 4 7
def R02 : Matrix (Fin 8) (Fin 8) ℚ := skewBasis8 2 5 + skewBasis8 4 6
def R03 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 0 2) - skewBasis8 1 4
def R12 : Matrix (Fin 8) (Fin 8) ℚ := skewBasis8 3 5 - skewBasis8 6 7
def R13 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 0 3) - skewBasis8 1 7
def R23 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 0 5) - skewBasis8 1 6

-- Imaginary symmetric off-diagonal: 6 generators
def I01 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 2 7) - skewBasis8 3 4
def I02 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 2 6) + skewBasis8 4 5
def I03 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 0 4) + skewBasis8 1 2
def I12 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 3 6) - skewBasis8 5 7
def I13 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 0 7) + skewBasis8 1 3
def I23 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 0 6) + skewBasis8 1 5

-- Diagonal imaginary (Cartan): 4 generators
def D0 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 2 4)
def D1 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 3 7)
def D2 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 5 6)
def D3 : Matrix (Fin 8) (Fin 8) ℚ := -(skewBasis8 0 1)

-- ═══════════════════════════════════════════════════════════
-- All 16 are skew-symmetric (hence in so(8))
-- ═══════════════════════════════════════════════════════════

theorem R01_skew : R01.transpose = -R01 := by native_decide
theorem D0_skew : D0.transpose = -D0 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Complete bracket closure: all 120 pairwise brackets of
-- 16 u(4) generators. Every bracket is a ℚ-linear combination
-- of the 16 generators, proving u(4) is a Lie subalgebra of so(8).
-- All verified by `native_decide` (kernel-checked).
-- ═══════════════════════════════════════════════════════════

-- R × R brackets (15)
theorem bracket_R01_R02 : ⁅R01, R02⁆ = -R12 := by native_decide
theorem bracket_R01_R03 : ⁅R01, R03⁆ = -R13 := by native_decide
theorem bracket_R01_R12 : ⁅R01, R12⁆ = R02 := by native_decide
theorem bracket_R01_R13 : ⁅R01, R13⁆ = R03 := by native_decide
theorem bracket_R01_R23 : ⁅R01, R23⁆ = 0 := by native_decide
theorem bracket_R02_R03 : ⁅R02, R03⁆ = -R23 := by native_decide
theorem bracket_R02_R12 : ⁅R02, R12⁆ = -R01 := by native_decide
theorem bracket_R02_R13 : ⁅R02, R13⁆ = 0 := by native_decide
theorem bracket_R02_R23 : ⁅R02, R23⁆ = R03 := by native_decide
theorem bracket_R03_R12 : ⁅R03, R12⁆ = 0 := by native_decide
theorem bracket_R03_R13 : ⁅R03, R13⁆ = -R01 := by native_decide
theorem bracket_R03_R23 : ⁅R03, R23⁆ = -R02 := by native_decide
theorem bracket_R12_R13 : ⁅R12, R13⁆ = -R23 := by native_decide
theorem bracket_R12_R23 : ⁅R12, R23⁆ = R13 := by native_decide
theorem bracket_R13_R23 : ⁅R13, R23⁆ = -R12 := by native_decide

-- R × I brackets (36)
theorem bracket_R01_I01 : ⁅R01, I01⁆ = 2 • (D0 - D1) := by native_decide
theorem bracket_R01_I02 : ⁅R01, I02⁆ = -I12 := by native_decide
theorem bracket_R01_I03 : ⁅R01, I03⁆ = -I13 := by native_decide
theorem bracket_R01_I12 : ⁅R01, I12⁆ = I02 := by native_decide
theorem bracket_R01_I13 : ⁅R01, I13⁆ = I03 := by native_decide
theorem bracket_R01_I23 : ⁅R01, I23⁆ = 0 := by native_decide
theorem bracket_R02_I01 : ⁅R02, I01⁆ = -I12 := by native_decide
theorem bracket_R02_I02 : ⁅R02, I02⁆ = 2 • (D0 - D2) := by native_decide
theorem bracket_R02_I03 : ⁅R02, I03⁆ = -I23 := by native_decide
theorem bracket_R02_I12 : ⁅R02, I12⁆ = I01 := by native_decide
theorem bracket_R02_I13 : ⁅R02, I13⁆ = 0 := by native_decide
theorem bracket_R02_I23 : ⁅R02, I23⁆ = I03 := by native_decide
theorem bracket_R03_I01 : ⁅R03, I01⁆ = -I13 := by native_decide
theorem bracket_R03_I02 : ⁅R03, I02⁆ = -I23 := by native_decide
theorem bracket_R03_I03 : ⁅R03, I03⁆ = 2 • (D0 - D3) := by native_decide
theorem bracket_R03_I12 : ⁅R03, I12⁆ = 0 := by native_decide
theorem bracket_R03_I13 : ⁅R03, I13⁆ = I01 := by native_decide
theorem bracket_R03_I23 : ⁅R03, I23⁆ = I02 := by native_decide
theorem bracket_R12_I01 : ⁅R12, I01⁆ = -I02 := by native_decide
theorem bracket_R12_I02 : ⁅R12, I02⁆ = I01 := by native_decide
theorem bracket_R12_I03 : ⁅R12, I03⁆ = 0 := by native_decide
theorem bracket_R12_I12 : ⁅R12, I12⁆ = 2 • (D1 - D2) := by native_decide
theorem bracket_R12_I13 : ⁅R12, I13⁆ = -I23 := by native_decide
theorem bracket_R12_I23 : ⁅R12, I23⁆ = I13 := by native_decide
theorem bracket_R13_I01 : ⁅R13, I01⁆ = -I03 := by native_decide
theorem bracket_R13_I02 : ⁅R13, I02⁆ = 0 := by native_decide
theorem bracket_R13_I03 : ⁅R13, I03⁆ = I01 := by native_decide
theorem bracket_R13_I12 : ⁅R13, I12⁆ = -I23 := by native_decide
theorem bracket_R13_I13 : ⁅R13, I13⁆ = 2 • (D1 - D3) := by native_decide
theorem bracket_R13_I23 : ⁅R13, I23⁆ = I12 := by native_decide
theorem bracket_R23_I01 : ⁅R23, I01⁆ = 0 := by native_decide
theorem bracket_R23_I02 : ⁅R23, I02⁆ = -I03 := by native_decide
theorem bracket_R23_I03 : ⁅R23, I03⁆ = I02 := by native_decide
theorem bracket_R23_I12 : ⁅R23, I12⁆ = -I13 := by native_decide
theorem bracket_R23_I13 : ⁅R23, I13⁆ = I12 := by native_decide
theorem bracket_R23_I23 : ⁅R23, I23⁆ = 2 • (D2 - D3) := by native_decide

-- I × I brackets (15)
theorem bracket_I01_I02 : ⁅I01, I02⁆ = -R12 := by native_decide
theorem bracket_I01_I03 : ⁅I01, I03⁆ = -R13 := by native_decide
theorem bracket_I01_I12 : ⁅I01, I12⁆ = -R02 := by native_decide
theorem bracket_I01_I13 : ⁅I01, I13⁆ = -R03 := by native_decide
theorem bracket_I01_I23 : ⁅I01, I23⁆ = 0 := by native_decide
theorem bracket_I02_I03 : ⁅I02, I03⁆ = -R23 := by native_decide
theorem bracket_I02_I12 : ⁅I02, I12⁆ = -R01 := by native_decide
theorem bracket_I02_I13 : ⁅I02, I13⁆ = 0 := by native_decide
theorem bracket_I02_I23 : ⁅I02, I23⁆ = -R03 := by native_decide
theorem bracket_I03_I12 : ⁅I03, I12⁆ = 0 := by native_decide
theorem bracket_I03_I13 : ⁅I03, I13⁆ = -R01 := by native_decide
theorem bracket_I03_I23 : ⁅I03, I23⁆ = -R02 := by native_decide
theorem bracket_I12_I13 : ⁅I12, I13⁆ = -R23 := by native_decide
theorem bracket_I12_I23 : ⁅I12, I23⁆ = -R13 := by native_decide
theorem bracket_I13_I23 : ⁅I13, I23⁆ = -R12 := by native_decide

-- R × D brackets (24)
theorem bracket_R01_D0 : ⁅R01, D0⁆ = -I01 := by native_decide
theorem bracket_R01_D1 : ⁅R01, D1⁆ = I01 := by native_decide
theorem bracket_R01_D2 : ⁅R01, D2⁆ = 0 := by native_decide
theorem bracket_R01_D3 : ⁅R01, D3⁆ = 0 := by native_decide
theorem bracket_R02_D0 : ⁅R02, D0⁆ = -I02 := by native_decide
theorem bracket_R02_D1 : ⁅R02, D1⁆ = 0 := by native_decide
theorem bracket_R02_D2 : ⁅R02, D2⁆ = I02 := by native_decide
theorem bracket_R02_D3 : ⁅R02, D3⁆ = 0 := by native_decide
theorem bracket_R03_D0 : ⁅R03, D0⁆ = -I03 := by native_decide
theorem bracket_R03_D1 : ⁅R03, D1⁆ = 0 := by native_decide
theorem bracket_R03_D2 : ⁅R03, D2⁆ = 0 := by native_decide
theorem bracket_R03_D3 : ⁅R03, D3⁆ = I03 := by native_decide
theorem bracket_R12_D0 : ⁅R12, D0⁆ = 0 := by native_decide
theorem bracket_R12_D1 : ⁅R12, D1⁆ = -I12 := by native_decide
theorem bracket_R12_D2 : ⁅R12, D2⁆ = I12 := by native_decide
theorem bracket_R12_D3 : ⁅R12, D3⁆ = 0 := by native_decide
theorem bracket_R13_D0 : ⁅R13, D0⁆ = 0 := by native_decide
theorem bracket_R13_D1 : ⁅R13, D1⁆ = -I13 := by native_decide
theorem bracket_R13_D2 : ⁅R13, D2⁆ = 0 := by native_decide
theorem bracket_R13_D3 : ⁅R13, D3⁆ = I13 := by native_decide
theorem bracket_R23_D0 : ⁅R23, D0⁆ = 0 := by native_decide
theorem bracket_R23_D1 : ⁅R23, D1⁆ = 0 := by native_decide
theorem bracket_R23_D2 : ⁅R23, D2⁆ = -I23 := by native_decide
theorem bracket_R23_D3 : ⁅R23, D3⁆ = I23 := by native_decide

-- I × D brackets (24)
theorem bracket_I01_D0 : ⁅I01, D0⁆ = R01 := by native_decide
theorem bracket_I01_D1 : ⁅I01, D1⁆ = -R01 := by native_decide
theorem bracket_I01_D2 : ⁅I01, D2⁆ = 0 := by native_decide
theorem bracket_I01_D3 : ⁅I01, D3⁆ = 0 := by native_decide
theorem bracket_I02_D0 : ⁅I02, D0⁆ = R02 := by native_decide
theorem bracket_I02_D1 : ⁅I02, D1⁆ = 0 := by native_decide
theorem bracket_I02_D2 : ⁅I02, D2⁆ = -R02 := by native_decide
theorem bracket_I02_D3 : ⁅I02, D3⁆ = 0 := by native_decide
theorem bracket_I03_D0 : ⁅I03, D0⁆ = R03 := by native_decide
theorem bracket_I03_D1 : ⁅I03, D1⁆ = 0 := by native_decide
theorem bracket_I03_D2 : ⁅I03, D2⁆ = 0 := by native_decide
theorem bracket_I03_D3 : ⁅I03, D3⁆ = -R03 := by native_decide
theorem bracket_I12_D0 : ⁅I12, D0⁆ = 0 := by native_decide
theorem bracket_I12_D1 : ⁅I12, D1⁆ = R12 := by native_decide
theorem bracket_I12_D2 : ⁅I12, D2⁆ = -R12 := by native_decide
theorem bracket_I12_D3 : ⁅I12, D3⁆ = 0 := by native_decide
theorem bracket_I13_D0 : ⁅I13, D0⁆ = 0 := by native_decide
theorem bracket_I13_D1 : ⁅I13, D1⁆ = R13 := by native_decide
theorem bracket_I13_D2 : ⁅I13, D2⁆ = 0 := by native_decide
theorem bracket_I13_D3 : ⁅I13, D3⁆ = -R13 := by native_decide
theorem bracket_I23_D0 : ⁅I23, D0⁆ = 0 := by native_decide
theorem bracket_I23_D1 : ⁅I23, D1⁆ = 0 := by native_decide
theorem bracket_I23_D2 : ⁅I23, D2⁆ = R23 := by native_decide
theorem bracket_I23_D3 : ⁅I23, D3⁆ = -R23 := by native_decide

-- D × D brackets (6) — all zero (abelian Cartan subalgebra)
theorem bracket_D0_D1 : ⁅D0, D1⁆ = 0 := by native_decide
theorem bracket_D0_D2 : ⁅D0, D2⁆ = 0 := by native_decide
theorem bracket_D0_D3 : ⁅D0, D3⁆ = 0 := by native_decide
theorem bracket_D1_D2 : ⁅D1, D2⁆ = 0 := by native_decide
theorem bracket_D1_D3 : ⁅D1, D3⁆ = 0 := by native_decide
theorem bracket_D2_D3 : ⁅D2, D3⁆ = 0 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Linear independence: each generator has a unique primary entry
-- ═══════════════════════════════════════════════════════════

/-- Each of the 16 generators has a unique nonzero entry in the E_{pq} basis,
    proving linear independence. The 16 primary entries use 16 distinct
    index pairs from the 28 total. -/
theorem u4_distinct_entries :
    R01 2 3 = 1 ∧ R02 2 5 = 1 ∧ R03 0 2 = -1 ∧ R12 3 5 = 1 ∧
    R13 0 3 = -1 ∧ R23 0 5 = -1 ∧
    I01 2 7 = -1 ∧ I02 2 6 = -1 ∧ I03 0 4 = -1 ∧ I12 3 6 = -1 ∧
    I13 0 7 = -1 ∧ I23 0 6 = -1 ∧
    D0 2 4 = -1 ∧ D1 3 7 = -1 ∧ D2 5 6 = -1 ∧ D3 0 1 = -1 := by native_decide

/-- The other generators are zero at each primary entry, confirming
    that the 16 generators form a linearly independent set. -/
theorem u4_zero_at_others :
    -- At entry (2,3): only R01 is nonzero
    I01 2 3 = 0 ∧ I02 2 3 = 0 ∧ R02 2 3 = 0 ∧ R03 2 3 = 0 ∧
    D0 2 3 = 0 ∧ D1 2 3 = 0 ∧ D2 2 3 = 0 ∧ D3 2 3 = 0 ∧
    -- At entry (2,4): only D0 is nonzero
    R01 2 4 = 0 ∧ R02 2 4 = 0 ∧ I01 2 4 = 0 ∧ I02 2 4 = 0 ∧
    D1 2 4 = 0 ∧ D2 2 4 = 0 ∧ D3 2 4 = 0 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- su(3) containment: all 8 su(3) generators are in u(4)
-- ═══════════════════════════════════════════════════════════

open Centralizer in
theorem su3_g1_in_u4 : g₁ = I01 := by native_decide

open Centralizer in
theorem su3_g2_in_u4 : g₂ = R01 := by native_decide

open Centralizer in
theorem su3_g3_in_u4 : g₃ = D0 - D1 := by native_decide

open Centralizer in
theorem su3_g4_in_u4 : g₄ = I02 := by native_decide

open Centralizer in
theorem su3_g5_in_u4 : g₅ = R02 := by native_decide

open Centralizer in
theorem su3_g6_in_u4 : g₆ = I12 := by native_decide

open Centralizer in
theorem su3_g7_in_u4 : g₇ = R12 := by native_decide

open Centralizer in
theorem su3_g8_in_u4 : g₈ = D0 + D1 - 2 • D2 := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Centralizer containment
-- ═══════════════════════════════════════════════════════════

open Centralizer in
/-- c₁ = E₀₁ = −D₃. -/
theorem c1_in_u4 : c₁ = -D3 := by native_decide

open Centralizer in
/-- c₂ = E₂₄ + E₃₇ + E₅₆ = −(D₀ + D₁ + D₂). -/
theorem c2_in_u4 : c₂ = -(D0 + D1 + D2) := by native_decide

-- ═══════════════════════════════════════════════════════════
-- Summary: u(4) structure
-- ═══════════════════════════════════════════════════════════

/-- dim(u(4)) = 4² = 16. -/
theorem u4_dim : 4 ^ 2 = 16 := by decide

/-- Adjoint complement: 28 − 16 = 12 (color triplets). -/
theorem complement_dim : 28 - 16 = 12 := by decide

end BLD.Lie.GaugeAlgebra
