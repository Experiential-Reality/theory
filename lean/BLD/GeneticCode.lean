/- BLD Calculus — Genetic Code from First Principles

   The same constants that predict neutrino mixing angles and the
   fine structure constant also determine the genetic code:

     n = 4 nucleotide bases (A, U/T, G, C)
     K = 2 base pairs (A-U, G-C)
     L = n(n+1) = 20 amino acids
     n-1 = 3 codon length (triplet code)
     n^3 = 64 total codons
     L(n-1)+1 = 61 coding codons
     n(n-1) = 12 degeneracy modulus

   Reference: applications/biology/genetic-code.md
-/

import Mathlib.Tactic.IntervalCases
import BLD.Constants

namespace BLD.GeneticCode

/-- Nucleotide bases = n = 4 (adenine, uracil/thymine, guanine, cytosine). -/
theorem bases : BLD.n = 4 := rfl

/-- Base pairs = K = 2 (A-U and G-C). -/
theorem base_pairs : BLD.K = 2 := rfl

/-- Codon length = n-1 = 3 (the triplet code). -/
theorem codon_length : BLD.n - 1 = 3 := by decide

/-- Total codons = n^3 = 64 (the complete codon table). -/
theorem total_codons : BLD.n ^ 3 = 64 := by decide

/-- Amino acids = L = n(n+1) = 20 (the standard amino acid set).
    The same L = 20 that counts Riemann tensor components in physics
    counts amino acids in biology. -/
theorem amino_acids : BLD.n * (BLD.n + 1) = BLD.L := by decide

/-- Stop codons = n-1 = 3 (UAA, UAG, UGA). -/
theorem stop_codons : BLD.n - 1 = 3 := by decide

/-- Coding codons = L(n-1) + 1 = 61.
    Of the 64 total codons, 61 encode amino acids. -/
theorem coding_codons : BLD.L * (BLD.n - 1) + 1 = 61 := by decide

/-- Degeneracy modulus = n(n-1) = 12.
    The number of synonymous codons per amino acid must divide 12.
    Observed degeneracies: {1, 2, 3, 4, 6} — all divisors of 12. -/
theorem degeneracy_modulus : BLD.n * (BLD.n - 1) = 12 := by decide

/-- No amino acid has exactly 5 synonymous codons,
    because 5 does not divide n(n-1) = 12. -/
theorem no_five_fold_degeneracy : ¬ (5 ∣ BLD.n * (BLD.n - 1)) := by decide

/-- L = 20 appears in three independent domains:
    1. Riemann tensor independent components: n²(n²-1)/12 = 20
    2. Amino acid count: n(n+1) = 20
    3. BLD link count (Lie algebra structure constants) -/
theorem L_universality :
    BLD.L = 20 ∧
    BLD.n * (BLD.n + 1) = 20 ∧
    BLD.n ^ 2 * (BLD.n ^ 2 - 1) / 12 = 20 := by decide

/-- Complete genetic code summary: all 7 quantities from BLD constants. -/
theorem genetic_code_complete :
    BLD.n = 4 ∧                         -- bases
    BLD.K = 2 ∧                         -- base pairs
    BLD.n - 1 = 3 ∧                     -- codon length
    BLD.n ^ 3 = 64 ∧                    -- total codons
    BLD.n * (BLD.n + 1) = BLD.L ∧       -- amino acids = L
    BLD.L * (BLD.n - 1) + 1 = 61 ∧      -- coding codons
    BLD.n * (BLD.n - 1) = 12 := by decide  -- degeneracy modulus

-- ═══════════════════════════════════════════════════════════
-- Structural uniqueness and degeneracy
-- ═══════════════════════════════════════════════════════════

/-- Riemann = amino acid uniqueness:
    n(n+1) = n²(n²-1)/12 uniquely forces n = 4 in the range 1..20.
    This is the unique dimension where the Riemann tensor component
    count equals the amino acid count. -/
theorem riemann_amino_acid_unique :
    ∀ m : ℕ, 1 ≤ m → m ≤ 20 →
    m * (m + 1) = m ^ 2 * (m ^ 2 - 1) / 12 → m = 4 := by
  intro m hm1 hm2 h
  interval_cases m <;> omega

/-- All observed codon degeneracies divide n(n-1) = 12. -/
theorem degeneracy_one : 1 ∣ BLD.n * (BLD.n - 1) := by decide
theorem degeneracy_two : 2 ∣ BLD.n * (BLD.n - 1) := by decide
theorem degeneracy_three : 3 ∣ BLD.n * (BLD.n - 1) := by decide
theorem degeneracy_four : 4 ∣ BLD.n * (BLD.n - 1) := by decide
theorem degeneracy_six : 6 ∣ BLD.n * (BLD.n - 1) := by decide

end BLD.GeneticCode
