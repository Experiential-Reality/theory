/- BLD Calculus — Cartan Classification of Dynkin Diagrams

   The classification of connected positive-definite generalized Cartan
   matrices: every such matrix is equivalent to one of A_n, B_n, C_n, D_n,
   E₆, E₇, E₈, F₄, G₂.

   Split into 7 files for manageability:
   - Defs: Core definitions and GCM/symmetrizability proofs
   - Forbidden: Forbidden subgraph analysis and affine diagrams
   - Structure: Coxeter weight bounds, acyclicity, vertex deletion
   - EntryLemmas: Parametric entry lemmas, extension helpers, marks vectors
   - Exceptional: E₆ and E₈ extension proofs
   - F4: F₄ and A_k extension proofs
   - Classification: Main theorem (extend_dynkin_type + cartan_classification)
-/

import BLD.Lie.Cartan.Defs
import BLD.Lie.Cartan.Forbidden
import BLD.Lie.Cartan.Structure
import BLD.Lie.Cartan.EntryLemmas
import BLD.Lie.Cartan.Exceptional
import BLD.Lie.Cartan.F4
import BLD.Lie.Cartan.Classification
