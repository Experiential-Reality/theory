/- BLD Calculus — Cartan Classification: Definitions

   Core definitions for the Cartan classification: Dynkin types,
   generalized Cartan matrix axioms, symmetrizability, positive definiteness,
   graph structure, and matrix equivalence.

   Reference: Humphreys, Introduction to Lie Algebras, Chapter 11.
-/

import Mathlib.Data.Matrix.Cartan
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import BLD.Constants

set_option autoImplicit false

namespace BLD.Lie.Cartan

open Matrix Finset

-- ═══════════════════════════════════════════════════════════
-- Dynkin types
-- ═══════════════════════════════════════════════════════════

/-- The 9 families of finite-type Dynkin diagrams.
    Each corresponds to a family of simple Lie algebras. -/
inductive DynkinType where
  | A (n : ℕ) (h : 1 ≤ n)
  | B (n : ℕ) (h : 2 ≤ n)
  | C (n : ℕ) (h : 3 ≤ n)
  | D (n : ℕ) (h : 4 ≤ n)
  | E₆ | E₇ | E₈ | F₄ | G₂

/-- The rank (= size of Cartan matrix) for each type. -/
def DynkinType.rank : DynkinType → ℕ
  | .A n _ => n
  | .B n _ => n
  | .C n _ => n
  | .D n _ => n
  | .E₆ => 6
  | .E₇ => 7
  | .E₈ => 8
  | .F₄ => 4
  | .G₂ => 2

/-- The dimension of the corresponding Lie algebra. -/
def DynkinType.dim : DynkinType → ℕ
  | .A n _ => n * (n + 2)
  | .B n _ => n * (2 * n + 1)
  | .C n _ => n * (2 * n + 1)
  | .D n _ => n * (2 * n - 1)
  | .E₆ => 78
  | .E₇ => 133
  | .E₈ => 248
  | .F₄ => 52
  | .G₂ => 14

/-- The number of positive roots. -/
def DynkinType.positiveRoots : DynkinType → ℕ
  | .A n _ => n * (n + 1) / 2
  | .B n _ => n * n
  | .C n _ => n * n
  | .D n _ => n * (n - 1)
  | .E₆ => 36
  | .E₇ => 63
  | .E₈ => 120
  | .F₄ => 24
  | .G₂ => 6

/-- The Cartan matrix for each Dynkin type, as a dependent pair (rank, matrix).
    Delegates to Mathlib's `CartanMatrix.*` definitions. -/
def DynkinType.cartanMatrix : DynkinType → (n : ℕ) × Matrix (Fin n) (Fin n) ℤ
  | .A n _ => ⟨n, CartanMatrix.A n⟩
  | .B n _ => ⟨n, CartanMatrix.B n⟩
  | .C n _ => ⟨n, CartanMatrix.C n⟩
  | .D n _ => ⟨n, CartanMatrix.D n⟩
  | .E₆ => ⟨6, CartanMatrix.E₆⟩
  | .E₇ => ⟨7, CartanMatrix.E₇⟩
  | .E₈ => ⟨8, CartanMatrix.E₈⟩
  | .F₄ => ⟨4, CartanMatrix.F₄⟩
  | .G₂ => ⟨2, CartanMatrix.G₂⟩

-- ═══════════════════════════════════════════════════════════
-- Generalized Cartan matrix axioms
-- ═══════════════════════════════════════════════════════════

/-- A generalized Cartan matrix (GCM): diagonal entries are 2,
    off-diagonal entries are non-positive, and A_ij = 0 ↔ A_ji = 0. -/
structure IsGCM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop where
  diag : ∀ i, A i i = 2
  off_diag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  zero_iff : ∀ i j, i ≠ j → (A i j = 0 ↔ A j i = 0)

/-- A GCM is symmetrizable if there exist positive rational weights d_i
    such that d_i · A_ij = d_j · A_ji for all i, j.
    Simply-laced types (A, D, E) have all d_i = 1 (the matrix is already symmetric). -/
structure IsSymmetrizable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) where
  d : Fin n → ℚ
  d_pos : ∀ i, 0 < d i
  sym : ∀ i j, d i * (A i j : ℚ) = d j * (A j i : ℚ)

/-- The symmetrized quadratic form: q(x) = Σᵢ Σⱼ dᵢ · Aᵢⱼ · xᵢ · xⱼ.
    Positive definiteness of this form characterizes finite-type Cartan matrices. -/
def qform {n : ℕ} (d : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, ∑ j : Fin n, d i * (A i j : ℚ) * x i * x j

/-- A symmetrizable GCM is positive definite if q(x) > 0 for all nonzero x. -/
def IsPosDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hS : IsSymmetrizable A) : Prop :=
  ∀ x : Fin n → ℚ, x ≠ 0 → 0 < qform hS.d A x

-- ═══════════════════════════════════════════════════════════
-- Graph structure
-- ═══════════════════════════════════════════════════════════

/-- The underlying simple graph of a GCM: vertices i, j are adjacent
    iff A_ij ≠ 0 (equivalently A_ji ≠ 0, by the zero_iff axiom). -/
def toGraph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGCM A) :
    SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ A i j ≠ 0
  symm := by
    intro i j ⟨hne, hA⟩
    exact ⟨hne.symm, fun h => hA ((hGCM.zero_iff i j hne).mpr h)⟩
  loopless := by
    intro i ⟨h, _⟩
    exact h rfl

/-- A GCM is connected if its underlying graph is connected. -/
def IsConnected {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGCM A) : Prop :=
  (toGraph A hGCM).Connected

-- ═══════════════════════════════════════════════════════════
-- Matrix equivalence (up to simultaneous row/column permutation)
-- ═══════════════════════════════════════════════════════════

/-- Two Cartan matrices are equivalent if one can be obtained from the other
    by simultaneous row and column permutation (= graph isomorphism). -/
def CartanEquiv {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (B : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∃ e : Fin n ≃ Fin m, ∀ i j, B (e i) (e j) = A i j

-- ═══════════════════════════════════════════════════════════
-- IsGCM proofs
-- ═══════════════════════════════════════════════════════════

/-- A symmetric matrix satisfies zero_iff trivially. -/
theorem zero_iff_of_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hS : A.IsSymm)
    (i j : Fin n) (_ : i ≠ j) : A i j = 0 ↔ A j i = 0 := by
  have h : A j i = A i j := by
    have := congr_fun (congr_fun (hS : Aᵀ = A) i) j
    rwa [transpose_apply] at this
  exact ⟨fun h0 => h.trans h0, fun h0 => h.symm.trans h0⟩

theorem isGCM_A (n : ℕ) : IsGCM (CartanMatrix.A n) where
  diag i := by simp [CartanMatrix.A]
  off_diag_nonpos := CartanMatrix.A_apply_le_zero_of_ne n
  zero_iff i j h := zero_iff_of_symm (CartanMatrix.A_isSymm n) i j h

theorem isGCM_D (n : ℕ) : IsGCM (CartanMatrix.D n) where
  diag := CartanMatrix.D_diag n
  off_diag_nonpos := CartanMatrix.D_off_diag_nonpos n
  zero_iff i j h := zero_iff_of_symm (CartanMatrix.D_isSymm n) i j h

theorem isGCM_B (n : ℕ) : IsGCM (CartanMatrix.B n) where
  diag := CartanMatrix.B_diag n
  off_diag_nonpos := CartanMatrix.B_off_diag_nonpos n
  zero_iff i j _ := by
    simp only [CartanMatrix.B, of_apply]
    constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

theorem isGCM_C (n : ℕ) : IsGCM (CartanMatrix.C n) where
  diag := CartanMatrix.C_diag n
  off_diag_nonpos := CartanMatrix.C_off_diag_nonpos n
  zero_iff i j _ := by
    simp only [CartanMatrix.C, of_apply]
    constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

theorem isGCM_E₆ : IsGCM CartanMatrix.E₆ where
  diag := CartanMatrix.E₆_diag
  off_diag_nonpos := CartanMatrix.E₆_off_diag_nonpos
  zero_iff i j h := zero_iff_of_symm CartanMatrix.E₆_isSymm i j h

theorem isGCM_E₇ : IsGCM CartanMatrix.E₇ where
  diag := CartanMatrix.E₇_diag
  off_diag_nonpos := CartanMatrix.E₇_off_diag_nonpos
  zero_iff i j h := zero_iff_of_symm CartanMatrix.E₇_isSymm i j h

theorem isGCM_E₈ : IsGCM CartanMatrix.E₈ where
  diag := CartanMatrix.E₈_diag
  off_diag_nonpos := CartanMatrix.E₈_off_diag_nonpos
  zero_iff i j h := zero_iff_of_symm CartanMatrix.E₈_isSymm i j h

theorem isGCM_F₄ : IsGCM CartanMatrix.F₄ where
  diag := CartanMatrix.F₄_diag
  off_diag_nonpos := CartanMatrix.F₄_off_diag_nonpos
  zero_iff i j _ := by fin_cases i <;> fin_cases j <;> simp_all [CartanMatrix.F₄]

theorem isGCM_G₂ : IsGCM CartanMatrix.G₂ where
  diag := CartanMatrix.G₂_diag
  off_diag_nonpos := CartanMatrix.G₂_off_diag_nonpos
  zero_iff i j _ := by fin_cases i <;> fin_cases j <;> simp_all [CartanMatrix.G₂]

-- ═══════════════════════════════════════════════════════════
-- IsSymmetrizable proofs
-- ═══════════════════════════════════════════════════════════

/-- A symmetric integer matrix is trivially symmetrizable with d_i = 1. -/
def symmetrizable_of_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hS : A.IsSymm) : IsSymmetrizable A where
  d := fun _ => 1
  d_pos := fun _ => one_pos
  sym i j := by
    have h : A j i = A i j := by
      have := congr_fun (congr_fun (hS : Aᵀ = A) i) j
      rwa [transpose_apply] at this
    simp [h]

def symmetrizable_A (n : ℕ) : IsSymmetrizable (CartanMatrix.A n) :=
  symmetrizable_of_symm _ (CartanMatrix.A_isSymm n)

def symmetrizable_D (n : ℕ) : IsSymmetrizable (CartanMatrix.D n) :=
  symmetrizable_of_symm _ (CartanMatrix.D_isSymm n)

def symmetrizable_E₆ : IsSymmetrizable CartanMatrix.E₆ :=
  symmetrizable_of_symm _ CartanMatrix.E₆_isSymm

def symmetrizable_E₇ : IsSymmetrizable CartanMatrix.E₇ :=
  symmetrizable_of_symm _ CartanMatrix.E₇_isSymm

def symmetrizable_E₈ : IsSymmetrizable CartanMatrix.E₈ :=
  symmetrizable_of_symm _ CartanMatrix.E₈_isSymm

/-- G₂ is symmetrizable with d = (1, 3). -/
def symmetrizable_G₂ : IsSymmetrizable CartanMatrix.G₂ where
  d := ![1, 3]
  d_pos i := by fin_cases i <;> simp
  sym i j := by fin_cases i <;> fin_cases j <;> simp [CartanMatrix.G₂]

/-- F₄ is symmetrizable with d = (1, 1, 2, 2). -/
def symmetrizable_F₄ : IsSymmetrizable CartanMatrix.F₄ where
  d := ![1, 1, 2, 2]
  d_pos i := by fin_cases i <;> simp
  sym i j := by fin_cases i <;> fin_cases j <;> simp [CartanMatrix.F₄]

-- B_n and C_n symmetrizability for arbitrary n:
-- B_n: d = (1,...,1,2). C_n: d = (1,...,1,1/2) (or via C = B^T).
-- The classification theorem receives the symmetrizer as a hypothesis,
-- so these are not needed for the main result.

-- ═══════════════════════════════════════════════════════════
-- D₄ = so(8) is type D with rank 4
-- ═══════════════════════════════════════════════════════════

/-- D₄ has rank 4. -/
theorem D4_rank : (DynkinType.D 4 (by omega)).rank = BLD.n := by decide

/-- D₄ has dimension 28. -/
theorem D4_dim : (DynkinType.D 4 (by omega)).dim = 28 := by decide

/-- D₄ boundary count = 2 × dim = 56 = B. -/
theorem D4_boundary : 2 * (DynkinType.D 4 (by omega)).dim = BLD.B := by decide

/-- D₄ has 12 positive roots. -/
theorem D4_positiveRoots : (DynkinType.D 4 (by omega)).positiveRoots = 12 := by decide

end BLD.Lie.Cartan
