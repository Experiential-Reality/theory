/- BLD Calculus — Lean 4 Formalization

   21 files, 2612 lines, 0 sorry, 0 admit, 2 axioms.

   The BLD calculus derives physical constants from three irreducible
   structural primitives: Boundary (sum type), Link (function type),
   Dimension (product type). This formalization proves the mathematical
   derivation chain from axioms through Lie theory to physics predictions.

   DERIVATION CHAIN:
     Axioms.lean        Seven axioms (A1-A7) connected to the Ty inductive
     Basic.lean         Type grammar: unit | sum a b | fn a b | prod n a
     Irreducibility     B, L, D are mutually irreducible (main structural theorem)
     Constants          K=2 → n=4, L=20, S=13, B=56 → α⁻¹=137
     Lie/Classical      so(8) finrank = 28 (explicit basis, proved from scratch)
     Lie/Exceptional    E₇ Cartan matrix: det=2, simply-laced (Mathlib)
     Octonions          B=56 uniquely selects octonions among division algebras
     Predictions        12 exact rational predictions matching experiment
     Observer           K/X correction principle, α⁻¹ decomposition

   AXIOMS (2 total):
     hurwitz_theorem              Only ℝ, ℂ, ℍ, 𝕆 are normed division algebras
     cartan_classification_complete  Every semisimple Lie algebra has a Cartan matrix

   KEY THEOREMS:
     so8_finrank         Module.finrank ℚ (so8 ℚ) = 28
     K2_unique           K=2 is the only value in {1,...,5} giving α⁻¹ = 137
     only_octonion_gives_B56  B=56 uniquely selects octonions
     progress            Every closed term can step or is a value
     irreducibility      B cannot be expressed in the LD fragment
-/

import BLD.Basic
import BLD.Cardinality
import BLD.Sublanguage
import BLD.Irreducibility
import BLD.Constants
import BLD.ModeCount
import BLD.Term
import BLD.Subst
import BLD.Semantics
import BLD.MultiStep
import BLD.Eval
import BLD.SubIrred
import BLD.Lie.Basic
import BLD.Lie.Classical
import BLD.Lie.Exceptional
import BLD.Lie.Killing
import BLD.Lie.Completeness
import BLD.Axioms
import BLD.Predictions
import BLD.Observer
import BLD.Octonions
