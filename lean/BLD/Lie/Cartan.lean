/- BLD Calculus — Cartan Classification of Dynkin Diagrams

   The classification of connected positive-definite generalized Cartan
   matrices: every such matrix is equivalent to one of A_n, B_n, C_n, D_n,
   E₆, E₇, E₈, F₄, G₂. This is the exhaustiveness direction of Cartan's
   theorem — the forward direction (Cartan matrix → Lie algebra) is in
   Mathlib via the Serre construction.

   The proof uses forbidden subgraph analysis: affine Dynkin diagrams have
   null vectors for the symmetrized quadratic form, and any matrix not in
   the classification contains an affine subdiagram.

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

-- ═══════════════════════════════════════════════════════════
-- Forbidden subgraph analysis — infrastructure
-- ═══════════════════════════════════════════════════════════

/-- qform as Σᵢ dᵢ·xᵢ·(Σⱼ Aᵢⱼ·xⱼ), pulling xᵢ out of the inner sum. -/
theorem qform_eq_sum_mul {n : ℕ} (d : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℚ) :
    qform d A x = ∑ i, d i * x i * ∑ j, (A i j : ℚ) * x j := by
  simp only [qform, Finset.mul_sum]
  congr 1; ext i; congr 1; ext j; ring

/-- If every outer term vanishes (either xᵢ = 0 or the inner sum is 0), qform is 0. -/
theorem qform_zero_of_null {n : ℕ} (d : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℚ)
    (h : ∀ i, x i = 0 ∨ ∑ j, (A i j : ℚ) * x j = 0) :
    qform d A x = 0 := by
  rw [qform_eq_sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  rcases h i with h0 | h0 <;> simp [h0]

/-- If there exists a nonzero vector with qform ≤ 0, A is not positive definite. -/
theorem not_posDef_of_nonpos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSymmetrizable A) (v : Fin n → ℚ) (hv : v ≠ 0)
    (hq : qform hS.d A v ≤ 0) : ¬ IsPosDef A hS :=
  fun hPD => absurd (hPD v hv) (not_lt.mpr hq)

-- ═══════════════════════════════════════════════════════════
-- Submatrix null vector extension
-- ═══════════════════════════════════════════════════════════

/-- Extend a vector on Fin m to Fin n via an embedding, zero outside the range. -/
noncomputable def indicator {n m : ℕ} (f : Fin m ↪ Fin n) (v : Fin m → ℚ) : Fin n → ℚ :=
  fun j => if h : ∃ l, f l = j then v h.choose else 0

theorem indicator_apply {n m : ℕ} (f : Fin m ↪ Fin n) (v : Fin m → ℚ) (i : Fin m) :
    indicator f v (f i) = v i := by
  unfold indicator
  have hex : ∃ l, f l = f i := ⟨i, rfl⟩
  rw [dif_pos hex]
  exact congr_arg v (f.injective hex.choose_spec)

theorem indicator_zero {n m : ℕ} (f : Fin m ↪ Fin n) (v : Fin m → ℚ) (j : Fin n)
    (hj : ∀ l, f l ≠ j) : indicator f v j = 0 := by
  simp only [indicator, dif_neg (not_exists.mpr hj)]

theorem indicator_ne_zero {n m : ℕ} (f : Fin m ↪ Fin n) (v : Fin m → ℚ) (hv : v ≠ 0) :
    indicator f v ≠ 0 := by
  intro h; apply hv; ext i
  have := congr_fun h (f i)
  rwa [indicator_apply] at this

/-- Core theorem: if a principal submatrix (indexed by f) has a null vector v
    (meaning each restricted row applied to v gives 0), then the full matrix
    is not positive definite. The null vector is extended by zeros. -/
theorem not_posDef_of_submatrix_null {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℤ} (hS : IsSymmetrizable A)
    (f : Fin m ↪ Fin n) (v : Fin m → ℚ) (hv : v ≠ 0)
    (hNull : ∀ i : Fin m, ∑ j : Fin m, (A (f i) (f j) : ℚ) * v j = 0) :
    ¬ IsPosDef A hS := by
  let w := indicator f v
  apply not_posDef_of_nonpos hS w (indicator_ne_zero f v hv) (le_of_eq _)
  apply qform_zero_of_null
  intro k
  by_cases hk : ∃ l, f l = k
  · obtain ⟨i, rfl⟩ := hk
    right
    -- Need: ∑ j, (A (f i) j : ℚ) * w j = 0
    -- w j ≠ 0 only when j = f l for some l, and then w (f l) = v l
    -- So the sum reduces to ∑ l, A(f i, f l) * v l = 0 by hNull
    show ∑ j : Fin n, (↑(A (f i) j) : ℚ) * indicator f v j = 0
    -- Step 1: terms outside range(f) vanish, reduce to sum over image
    rw [show ∑ j : Fin n, (↑(A (f i) j) : ℚ) * indicator f v j
        = ∑ j ∈ Finset.univ.map f, (↑(A (f i) j) : ℚ) * indicator f v j from by
      symm; apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists] at hj
      simp [indicator_zero f v j hj]]
    -- Step 2: reindex sum over image to sum over Fin m
    rw [Finset.sum_map]
    -- Step 3: replace indicator f v (f l) with v l
    simp_rw [indicator_apply]
    exact hNull i
  · left
    exact indicator_zero f v k (not_exists.mp hk)

/-- Submatrix version of not_posDef_of_int_null: if a principal submatrix
    A(f·,f·) has an integer null vector, then A is not positive definite. -/
theorem not_posDef_of_submatrix_int_null {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℤ} (hS : IsSymmetrizable A)
    (f : Fin m ↪ Fin n) (M : Matrix (Fin m) (Fin m) ℤ)
    (hM : ∀ i j, A (f i) (f j) = M i j)
    (v : Fin m → ℤ) (hv : v ≠ 0)
    (hNull : M.mulVec v = 0) : ¬ IsPosDef A hS := by
  apply not_posDef_of_submatrix_null hS f (fun i => (v i : ℚ))
  · intro h; apply hv; ext i
    have := congr_fun h i; simp only [Pi.zero_apply] at this
    exact_mod_cast this
  · intro i
    have hi : (M.mulVec v) i = 0 := by rw [hNull]; rfl
    simp only [mulVec, dotProduct] at hi
    have hcast : (↑(∑ j, M i j * v j) : ℚ) = 0 := by exact_mod_cast hi
    simp only [Int.cast_sum, Int.cast_mul] at hcast
    convert hcast using 1
    congr 1; ext j; rw [hM]

-- ═══════════════════════════════════════════════════════════
-- Affine Dynkin diagrams and their null vectors
-- ═══════════════════════════════════════════════════════════

/-- Cyclic adjacency: i and j are cyclically adjacent in Fin k.
    Avoids Nat.mod so that omega can reason about it. -/
def cyclicAdj (k : ℕ) (i j : Fin k) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
  (i.val + 1 = k ∧ j.val = 0) ∨ (j.val + 1 = k ∧ i.val = 0)

instance (k : ℕ) (i j : Fin k) : Decidable (cyclicAdj k i j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- The affine Ã_{k-1} Cartan matrix (k × k circulant).
    For k ≥ 3: diagonal 2, cyclic-adjacent entries -1, rest 0.
    The null vector is (1,1,...,1). -/
def affineA (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if cyclicAdj k i j then -1
    else 0

/-- Each row of the affine Ã matrix sums to 0 (for k ≥ 3).
    Proof: decompose entry as 2·[diag] - [succ] - [pred], sum each indicator. -/
theorem affineA_row_sum_zero (k : ℕ) (hk : 3 ≤ k) (i : Fin k) :
    ∑ j : Fin k, affineA k i j = 0 := by
  simp only [affineA, of_apply]
  -- Define successor and predecessor
  have h_succ_lt : (if i.val + 1 < k then i.val + 1 else 0) < k := by split_ifs <;> omega
  have h_pred_lt : (if 0 < i.val then i.val - 1 else k - 1) < k := by split_ifs <;> omega
  let s : Fin k := ⟨if i.val + 1 < k then i.val + 1 else 0, h_succ_lt⟩
  let p : Fin k := ⟨if 0 < i.val then i.val - 1 else k - 1, h_pred_lt⟩
  have hs_adj : cyclicAdj k i s := by simp only [cyclicAdj, s]; split_ifs <;> omega
  have hp_adj : cyclicAdj k i p := by simp only [cyclicAdj, p]; split_ifs <;> omega
  have hs_ne : s ≠ i := by intro h; have := congr_arg Fin.val h; simp [s] at this; split_ifs at this <;> omega
  have hp_ne : p ≠ i := by intro h; have := congr_arg Fin.val h; simp [p] at this; split_ifs at this <;> omega
  have hsp : s ≠ p := by intro h; have := congr_arg Fin.val h; simp [s, p] at this; split_ifs at this <;> omega
  -- Any adjacent vertex is s or p
  have h_only : ∀ j : Fin k, cyclicAdj k i j → j = s ∨ j = p := by
    intro j hj; simp only [cyclicAdj] at hj; simp only [s, p, Fin.ext_iff]
    rcases hj with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (split_ifs <;> omega)
  -- The 3 distinct elements {i, s, p} give entries 2, -1, -1
  -- All other entries are 0. Extract these 3 terms.
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hs_ne, Finset.mem_univ s⟩)]
  simp only [show (i : Fin k) = s ↔ False from ⟨fun h => hs_ne h.symm, False.elim⟩, ite_false,
    show cyclicAdj k i s = True from propext ⟨fun _ => trivial, fun _ => hs_adj⟩, ite_true]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr
    ⟨hsp.symm, Finset.mem_erase.mpr ⟨hp_ne, Finset.mem_univ p⟩⟩)]
  simp only [show (i : Fin k) = p ↔ False from ⟨fun h => hp_ne h.symm, False.elim⟩, ite_false,
    show cyclicAdj k i p = True from propext ⟨fun _ => trivial, fun _ => hp_adj⟩, ite_true]
  -- Remaining sum: all entries are 0
  have h_rest : ∀ j ∈ ((Finset.univ.erase i).erase s).erase p,
      (if i = j then (2 : ℤ) else if cyclicAdj k i j then -1 else 0) = 0 := by
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, ne_eq] at hj
    have hji : j ≠ i := hj.2.2.1
    have hjs : j ≠ s := hj.2.1
    have hjp : j ≠ p := hj.1
    simp only [show i = j ↔ False from ⟨fun h => hji h.symm, False.elim⟩, ite_false]
    have : ¬ cyclicAdj k i j := fun h => by
      rcases h_only j h with rfl | rfl <;> contradiction
    simp [this]
  rw [Finset.sum_eq_zero h_rest]
  norm_num

/-- The affine Ã matrix (k ≥ 3) is not positive definite:
    the all-ones vector gives qform = 0. -/
theorem affineA_not_posDef (k : ℕ) (hk : 3 ≤ k)
    (hS : IsSymmetrizable (affineA k)) :
    ¬ IsPosDef (affineA k) hS := by
  have hv : (fun (_ : Fin k) => (1 : ℚ)) ≠ 0 :=
    fun h => absurd (congr_fun h ⟨0, by omega⟩) one_ne_zero
  apply not_posDef_of_nonpos hS (fun _ => 1) hv
  -- Show qform = 0 via row sums
  have hq : qform hS.d (affineA k) (fun _ => 1) = 0 := by
    simp only [qform, mul_one]
    conv_lhs => arg 2; ext i; rw [← Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [show (∑ j : Fin k, (affineA k i j : ℚ)) =
        ((∑ j, affineA k i j : ℤ) : ℚ) from by push_cast; rfl]
    rw [affineA_row_sum_zero k hk i]; simp
  exact le_of_eq hq

-- ═══════════════════════════════════════════════════════════
-- Exceptional affine Dynkin diagrams
-- ═══════════════════════════════════════════════════════════

/-- Affine D̃₄: the D₄ diagram with one extra node.
    5 vertices: center (0) connected to 4 leaves (1,2,3,4).
    Null vector: (2,1,1,1,1). -/
def affineD4 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![ 2, -1, -1, -1, -1;
     -1,  2,  0,  0,  0;
     -1,  0,  2,  0,  0;
     -1,  0,  0,  2,  0;
     -1,  0,  0,  0,  2]

theorem affineD4_null : affineD4.mulVec ![2, 1, 1, 1, 1] = 0 := by decide

/-- Affine Ẽ₆ matrix (7 × 7): branch at node 2 with three arms of length 2.
    Diagram: 0-1-2-3-4 with branch 2-5-6.
    Null vector: (1,2,3,2,1,2,1). -/
def affineE6 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0;
      0, -1,  2, -1,  0, -1,  0;
      0,  0, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2,  0,  0;
      0,  0, -1,  0,  0,  2, -1;
      0,  0,  0,  0,  0, -1,  2]

theorem affineE6_null : affineE6.mulVec ![1, 2, 3, 2, 1, 2, 1] = 0 := by decide

/-- Affine Ẽ₇ matrix (8 × 8): path 0-1-2-3-4-5-6 with branch 3-7.
    Arms from branch (node 3): (3, 3, 1).
    Null vector: (1,2,3,4,3,2,1,2). -/
def affineE7 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0,  0;
      0, -1,  2, -1,  0,  0,  0,  0;
      0,  0, -1,  2, -1,  0,  0, -1;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2,  0;
      0,  0,  0, -1,  0,  0,  0,  2]

theorem affineE7_null : affineE7.mulVec ![1, 2, 3, 4, 3, 2, 1, 2] = 0 := by decide

/-- Affine Ẽ₈ matrix (9 × 9): path 0-1-2-3-4-5-6-7 with branch 2-8.
    Arms from branch (node 2): (2, 5, 1).
    Null vector: (2,4,6,5,4,3,2,1,3). -/
def affineE8 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![ 2, -1,  0,  0,  0,  0,  0,  0,  0;
     -1,  2, -1,  0,  0,  0,  0,  0,  0;
      0, -1,  2, -1,  0,  0,  0,  0, -1;
      0,  0, -1,  2, -1,  0,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0,  0, -1,  2,  0;
      0,  0, -1,  0,  0,  0,  0,  0,  2]

theorem affineE8_null : affineE8.mulVec ![2, 4, 6, 5, 4, 3, 2, 1, 3] = 0 := by decide

-- ═══════════════════════════════════════════════════════════
-- Affine types are not positive definite
-- ═══════════════════════════════════════════════════════════

/-- If A has an integer null vector (A·v = 0), then A is not positive definite
    for any symmetrizer. This bridges integer mulVec to rational qform. -/
theorem not_posDef_of_int_null {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hS : IsSymmetrizable A) (v : Fin n → ℤ) (hv : v ≠ 0)
    (hNull : A.mulVec v = 0) : ¬ IsPosDef A hS := by
  let w : Fin n → ℚ := fun i => (v i : ℚ)
  have hw : w ≠ 0 := by
    intro h; apply hv; ext i
    have hi := congr_fun h i
    simp only [Pi.zero_apply] at hi ⊢
    exact_mod_cast (show (v i : ℚ) = 0 from hi)
  apply not_posDef_of_nonpos hS w hw (le_of_eq _)
  rw [qform_eq_sum_mul]
  apply Finset.sum_eq_zero; intro i _
  suffices h : ∑ j, (A i j : ℚ) * w j = 0 by simp [h]
  have hi : (A.mulVec v) i = 0 := by rw [hNull]; rfl
  simp only [mulVec, dotProduct] at hi
  have : (↑(∑ j, A i j * v j) : ℚ) = 0 := by exact_mod_cast hi
  simpa [Int.cast_sum, Int.cast_mul] using this

theorem affineD4_not_posDef (hS : IsSymmetrizable affineD4) :
    ¬ IsPosDef affineD4 hS :=
  not_posDef_of_int_null hS _ (by decide) affineD4_null

theorem affineE6_not_posDef (hS : IsSymmetrizable affineE6) :
    ¬ IsPosDef affineE6 hS :=
  not_posDef_of_int_null hS _ (by decide) affineE6_null

theorem affineE7_not_posDef (hS : IsSymmetrizable affineE7) :
    ¬ IsPosDef affineE7 hS :=
  not_posDef_of_int_null hS _ (by decide) affineE7_null

theorem affineE8_not_posDef (hS : IsSymmetrizable affineE8) :
    ¬ IsPosDef affineE8 hS :=
  not_posDef_of_int_null hS _ (by decide) affineE8_null

-- ═══════════════════════════════════════════════════════════
-- Coxeter weight bound
-- ═══════════════════════════════════════════════════════════

/-- The Coxeter weight of an edge in a GCM: w(i,j) = A(i,j) * A(j,i).
    For connected vertices i ≠ j, this is a positive integer ≤ 3
    in a positive definite GCM. -/
def coxeterWeight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℤ :=
  A i j * A j i

/-- Helper: a sum over Fin n with only 2 nonzero terms at i, j. -/
private theorem sum_two {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (f : Fin n → ℚ) (hf : ∀ k, k ≠ i → k ≠ j → f k = 0) :
    ∑ k, f k = f i + f j := by
  rw [show ∑ k, f k = ∑ k ∈ ({i, j} : Finset (Fin n)), f k from by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk; exact hf k hk.1 hk.2]
  exact Finset.sum_pair hij

/-- Helper: a sum over Fin n with only 3 nonzero terms at i, j, k. -/
private theorem sum_three {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (f : Fin n → ℚ) (hf : ∀ l, l ≠ i → l ≠ j → l ≠ k → f l = 0) :
    ∑ l, f l = f i + f j + f k := by
  rw [show ∑ l, f l = ∑ l ∈ ({i, j, k} : Finset (Fin n)), f l from by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    push_neg at hl; exact hf l hl.1 hl.2.1 hl.2.2]
  rw [Finset.sum_insert (show i ∉ ({j, k} : Finset _) by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hij, hik⟩)]
  rw [Finset.sum_pair hjk]; ring

/-- In a positive definite GCM, A(i,j) * A(j,i) < 4 (Coxeter weight ≤ 3).
    Proof: the test vector v(i) = 1, v(j) = -A(j,i)/2 gives
    qform = d_i · (4 - A(i,j)·A(j,i)) / 2, which is ≤ 0 when the product ≥ 4. -/
theorem coxeter_weight_lt_four {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (hS : IsSymmetrizable A) (hPD : IsPosDef A hS)
    (i j : Fin n) (hij : i ≠ j) :
    coxeterWeight A i j < 4 := by
  unfold coxeterWeight; by_contra hge; push_neg at hge
  -- hge : 4 ≤ A i j * A j i
  -- Test vector: v(i) = 1, v(j) = -(A j i)/2, else 0
  -- We avoid `let` to prevent normalization issues with rw
  set v : Fin n → ℚ := fun k =>
    if k = i then 1 else if k = j then -(↑(A j i : ℤ) : ℚ) / 2 else 0
  -- Key properties of v
  have v0 : ∀ k, k ≠ i → k ≠ j → v k = 0 := fun k h1 h2 => by
    simp only [v, if_neg h1, if_neg h2]
  have hv : v ≠ 0 := by
    intro h0; have := congr_fun h0 i
    simp only [v, if_pos rfl, Pi.zero_apply] at this
    exact one_ne_zero this
  -- Inner sum at row i: reduces to 2 - A(i,j)*A(j,i)/2
  have inner_i : ∑ s, (↑(A i s) : ℚ) * v s =
      2 - (↑(A i j : ℤ) : ℚ) * (↑(A j i : ℤ) : ℚ) / 2 := by
    rw [sum_two hij (fun s => (↑(A i s) : ℚ) * v s)
      (fun k h1 h2 => by simp only [v0 k h1 h2, mul_zero])]
    simp only [v, if_pos rfl, if_neg (Ne.symm hij), hGCM.diag i]
    push_cast; ring
  -- Inner sum at row j: vanishes (A(j,i) - A(j,i) = 0)
  have inner_j : ∑ s, (↑(A j s) : ℚ) * v s = 0 := by
    rw [sum_two hij (fun s => (↑(A j s) : ℚ) * v s)
      (fun k h1 h2 => by simp only [v0 k h1 h2, mul_zero])]
    simp only [v, if_pos rfl, if_neg (Ne.symm hij), hGCM.diag j]
    push_cast; ring
  -- Outer sum: reduces to d_i * inner_i (the j term vanishes)
  have hq : qform hS.d A v =
      hS.d i * (2 - (↑(A i j : ℤ) : ℚ) * (↑(A j i : ℤ) : ℚ) / 2) := by
    rw [qform_eq_sum_mul,
        sum_two hij (fun r => hS.d r * v r * ∑ s, (↑(A r s) : ℚ) * v s)
          (fun k h1 h2 => by simp only [v0 k h1 h2]; ring)]
    simp only [v, if_pos rfl, if_neg (Ne.symm hij)]
    rw [inner_i, inner_j]; ring
  -- Show qform ≤ 0 (contradicting pos-def)
  have h_cast : (4 : ℚ) ≤ (↑(A i j : ℤ) : ℚ) * (↑(A j i : ℤ) : ℚ) := by
    exact_mod_cast hge
  have hq_le : qform hS.d A v ≤ 0 := by
    rw [hq]; nlinarith [hS.d_pos i]
  exact absurd (hPD v hv) (not_lt.mpr hq_le)

-- ═══════════════════════════════════════════════════════════
-- Coxeter weight properties
-- ═══════════════════════════════════════════════════════════

/-- In a GCM, Coxeter weights are non-negative (both off-diagonal entries ≤ 0). -/
theorem coxeter_weight_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (i j : Fin n) (hij : i ≠ j) :
    0 ≤ coxeterWeight A i j := by
  unfold coxeterWeight
  nlinarith [hGCM.off_diag_nonpos i j hij, hGCM.off_diag_nonpos j i hij.symm]

-- ═══════════════════════════════════════════════════════════
-- Acyclicity: no cycles in pos-def GCM graph
-- ═══════════════════════════════════════════════════════════

/-- If a principal submatrix (via embedding f : Fin m ↪ Fin n) has all
    integer row sums ≤ 0 and m ≥ 1, the full matrix is not positive definite.
    Proof: the all-ones vector on the image gives qform ≤ 0. -/
theorem not_posDef_of_submatrix_rowsum_nonpos {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℤ} (hS : IsSymmetrizable A)
    (f : Fin m ↪ Fin n) (hm : 0 < m)
    (hrow : ∀ i : Fin m, ∑ j : Fin m, A (f i) (f j) ≤ 0) :
    ¬ IsPosDef A hS := by
  apply not_posDef_of_nonpos hS (indicator f (fun _ => 1))
    (indicator_ne_zero f _ (fun h => absurd (congr_fun h ⟨0, hm⟩) one_ne_zero))
  rw [qform_eq_sum_mul]
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : ∃ l, f l = i
  · obtain ⟨l, rfl⟩ := hi
    simp only [indicator_apply]
    suffices h : ∑ j, (↑(A (f l) j) : ℚ) * indicator f (fun _ => (1 : ℚ)) j ≤ 0 by
      nlinarith [hS.d_pos (f l)]
    rw [show ∑ j : Fin n, (↑(A (f l) j) : ℚ) * indicator f (fun _ => (1 : ℚ)) j =
        ∑ j ∈ Finset.univ.map f, (↑(A (f l) j) : ℚ) * indicator f (fun _ => 1) j from by
      symm; apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists] at hj
      simp [indicator_zero f _ j hj],
    Finset.sum_map]
    simp_rw [indicator_apply, mul_one]
    exact_mod_cast hrow l
  · simp [indicator_zero f _ i (not_exists.mp hi)]

/-- A pos-def GCM graph has no cycles: if k ≥ 3 distinct vertices form a cycle
    (each adjacent to the next, cyclically), the matrix is not positive definite.
    Proof: each cycle row sum is 2 + (≤ -1) + (≤ -1) + (rest ≤ 0) ≤ 0. -/
theorem not_posDef_of_cycle {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (hS : IsSymmetrizable A) (hk : 3 ≤ k)
    (f : Fin k ↪ Fin n)
    (hadj : ∀ l : Fin k,
      A (f l) (f ⟨(l.val + 1) % k, Nat.mod_lt _ (by omega)⟩) ≠ 0) :
    ¬ IsPosDef A hS := by
  apply not_posDef_of_submatrix_rowsum_nonpos hS f (by omega)
  intro l
  -- Decompose: diagonal + off-diagonal
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), hGCM.diag (f l)]
  -- Need: Σ_{m ≠ l} A(f l, f m) ≤ -2
  suffices h : ∑ m ∈ Finset.univ.erase l, A (f l) (f m) ≤ -2 by omega
  -- Successor and predecessor in the cycle
  let s : Fin k := ⟨(l.val + 1) % k, Nat.mod_lt _ (by omega)⟩
  let p : Fin k := ⟨(l.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  -- Eliminate % using Nat.mod_eq_of_lt / Nat.mod_self before omega
  have hsl : s ≠ l := by
    intro h; have hv : (l.val + 1) % k = l.val := congrArg Fin.val h
    by_cases heq : l.val + 1 = k
    · rw [heq, Nat.mod_self] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega : l.val + 1 < k)] at hv; omega
  have hpl : p ≠ l := by
    intro h; have hv : (l.val + k - 1) % k = l.val := congrArg Fin.val h
    by_cases h0 : l.val = 0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)] at hv; omega
    · rw [show l.val + k - 1 = l.val - 1 + k from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.val - 1 < k)] at hv; omega
  have hsp : s ≠ p := by
    intro h; have hv : (l.val + 1) % k = (l.val + k - 1) % k := congrArg Fin.val h
    by_cases heq : l.val + 1 = k
    · rw [heq, Nat.mod_self] at hv
      by_cases h0 : l.val = 0
      · omega  -- h0 + heq give k = 1, contradicts hk
      · rw [show l.val + k - 1 = l.val - 1 + k from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.val - 1 < k)] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega : l.val + 1 < k)] at hv
      by_cases h0 : l.val = 0
      · simp only [h0, Nat.zero_add] at hv
        rw [Nat.mod_eq_of_lt (by omega : k - 1 < k)] at hv; omega
      · rw [show l.val + k - 1 = l.val - 1 + k from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.val - 1 < k)] at hv; omega
  -- Helper: distinctness of images
  have hne_ls : f l ≠ f s := fun h => absurd (f.injective h).symm hsl
  have hne_lp : f l ≠ f p := fun h => absurd (f.injective h).symm hpl
  -- Both ≤ -1: successor by hypothesis, predecessor by zero_iff
  have hs_adj : A (f l) (f s) ≤ -1 := by
    have h1 : A (f l) (f s) ≤ 0 := hGCM.off_diag_nonpos (f l) (f s) hne_ls
    have h2 : A (f l) (f s) ≠ 0 := hadj l
    omega
  have hp_adj : A (f l) (f p) ≤ -1 := by
    have h_eq : (⟨(p.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = l := by
      ext; show ((l.val + k - 1) % k + 1) % k = l.val
      by_cases h0 : l.val = 0
      · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k),
            show k - 1 + 1 = k from by omega, Nat.mod_self]
      · rw [show l.val + k - 1 = l.val - 1 + k from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : l.val - 1 < k),
            show l.val - 1 + 1 = l.val from by omega, Nat.mod_eq_of_lt l.isLt]
    have h1 := hadj p; rw [h_eq] at h1  -- h1 : A (f p) (f l) ≠ 0
    have h2 : A (f l) (f p) ≠ 0 := mt (hGCM.zero_iff (f l) (f p) hne_lp).mp h1
    have h3 : A (f l) (f p) ≤ 0 := hGCM.off_diag_nonpos (f l) (f p) hne_lp
    omega
  -- Extract s and p from the sum, bound the rest ≤ 0
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hsl, Finset.mem_univ s⟩),
      ← Finset.add_sum_erase _ _
        (Finset.mem_erase.mpr ⟨Ne.symm hsp, Finset.mem_erase.mpr ⟨hpl, Finset.mem_univ p⟩⟩)]
  have h_rest : ∑ m ∈ ((Finset.univ.erase l).erase s).erase p, A (f l) (f m) ≤ 0 :=
    Finset.sum_nonpos fun m hm => by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm
      exact hGCM.off_diag_nonpos (f l) (f m)
        (fun h => absurd (f.injective h).symm hm.2.2)
  linarith

-- ═══════════════════════════════════════════════════════════
-- D₄ uniqueness among Dynkin types
-- ═══════════════════════════════════════════════════════════

/-- D₄ is the unique Dynkin type with rank 4 and dimension 28.
    This means BLD's identification of so(8) is forced by the constants. -/
theorem D4_unique_type (t : DynkinType) (hr : t.rank = 4) (hd : t.dim = 28) :
    t = .D 4 (by omega) := by
  cases t with
  | A n h => simp [DynkinType.rank] at hr; subst hr; simp [DynkinType.dim] at hd
  | B n h => simp [DynkinType.rank] at hr; subst hr; simp [DynkinType.dim] at hd
  | C n h => simp [DynkinType.rank] at hr; subst hr; simp [DynkinType.dim] at hd
  | D n h => simp [DynkinType.rank] at hr; subst hr; rfl
  | E₆ => simp [DynkinType.rank] at hr
  | E₇ => simp [DynkinType.rank] at hr
  | E₈ => simp [DynkinType.rank] at hr
  | F₄ => simp [DynkinType.dim] at hd
  | G₂ => simp [DynkinType.rank] at hr

-- ═══════════════════════════════════════════════════════════
-- Classification infrastructure
-- ═══════════════════════════════════════════════════════════

/-- Delete vertex v from a matrix, giving a principal submatrix. -/
def deleteVertex {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (v : Fin (n+1)) :
    Matrix (Fin n) (Fin n) ℤ :=
  A.submatrix v.succAbove v.succAbove

theorem deleteVertex_isGCM {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ}
    (hGCM : IsGCM A) (v : Fin (n+1)) : IsGCM (deleteVertex A v) where
  diag i := by simp [deleteVertex, submatrix_apply, hGCM.diag]
  off_diag_nonpos i j h := by
    simp only [deleteVertex, submatrix_apply]
    exact hGCM.off_diag_nonpos _ _ (fun e => h (Fin.succAbove_right_injective e))
  zero_iff i j h := by
    simp only [deleteVertex, submatrix_apply]
    exact hGCM.zero_iff _ _ (fun e => h (Fin.succAbove_right_injective e))

noncomputable def deleteVertex_symmetrizable {n : ℕ}
    {A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ}
    (hSym : IsSymmetrizable A) (v : Fin (n+1)) :
    IsSymmetrizable (deleteVertex A v) where
  d i := hSym.d (v.succAbove i)
  d_pos i := hSym.d_pos _
  sym i j := by simp only [deleteVertex, submatrix_apply]; exact hSym.sym _ _

theorem deleteVertex_isPosDef {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ}
    {hSym : IsSymmetrizable A} (hPD : IsPosDef A hSym) (v : Fin (n+1)) :
    IsPosDef (deleteVertex A v) (deleteVertex_symmetrizable hSym v) := by
  intro x hx
  -- Reuse the existing indicator infrastructure to extend x by zero at v
  let f : Fin n ↪ Fin (n+1) := ⟨v.succAbove, Fin.succAbove_right_injective⟩
  have hy := indicator_ne_zero f x hx
  have hyv : indicator f x v = 0 :=
    indicator_zero f x v (fun l => Fin.succAbove_ne v l)
  have hyi : ∀ i, indicator f x (v.succAbove i) = x i := indicator_apply f x
  -- Relate submatrix qform to full-matrix qform with indicator extension
  suffices h : qform (deleteVertex_symmetrizable hSym v).d (deleteVertex A v) x =
      qform hSym.d A (indicator f x) by
    rw [h]; exact hPD _ hy
  simp only [qform, deleteVertex, submatrix_apply, deleteVertex_symmetrizable]
  -- Decompose full-matrix double sum: v-terms vanish, rest matches submatrix
  symm
  rw [Fin.sum_univ_succAbove _ v]
  simp only [hyv, zero_mul, mul_zero, sum_const_zero, zero_add]
  congr 1; ext i
  rw [Fin.sum_univ_succAbove _ v]
  simp only [hyv, mul_zero, zero_add, hyi]

/-- The number of neighbors of vertex i in a GCM. -/
noncomputable def gcmDegree {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => j ≠ i ∧ A i j ≠ 0)).card

/-- In a pos-def GCM, every vertex has degree ≤ 3.
    Proof: degree ≥ 4 would give a test vector with qform ≤ 0. -/
theorem gcmDegree_le_three {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (i : Fin n) : gcmDegree A i ≤ 3 := by
  by_contra hge; push_neg at hge
  let S := Finset.univ.filter (fun j : Fin n => j ≠ i ∧ A i j ≠ 0)
  change 4 ≤ S.card at hge
  have hS_sub : S ⊆ Finset.univ.erase i := fun k hk => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact Finset.mem_erase.mpr ⟨hk.1, Finset.mem_univ k⟩
  have hS_adj : ∀ k ∈ S, A i k ≤ -1 := fun k hk => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have := hGCM.off_diag_nonpos i k hk.1.symm; omega
  -- Test vector: w(i) = 2, w(j) = 1 for j ∈ S, else 0
  let w : Fin n → ℚ := fun k => if k = i then 2 else if k ∈ S then 1 else 0
  have hw : w ≠ 0 := by
    intro h; have := congr_fun h i
    simp only [w, if_pos rfl, Pi.zero_apply] at this; norm_num at this
  -- Inner sum at center row i ≤ 0
  have h_center : ∑ k, (A i k : ℚ) * w k ≤ 0 := by
    -- Extract the i-term, bound the rest
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [w, if_pos rfl, hGCM.diag i]; push_cast
    -- Goal: 2 * 2 + Σ_{k≠i} (↑(A i k)) * w k ≤ 0
    suffices h : ∑ k ∈ Finset.univ.erase i, (A i k : ℚ) * w k ≤ -4 by linarith
    calc ∑ k ∈ Finset.univ.erase i, (A i k : ℚ) * w k
        ≤ ∑ k ∈ Finset.univ.erase i, (if k ∈ S then (A i k : ℚ) else 0) := by
          apply Finset.sum_le_sum; intro k hk
          simp only [Finset.mem_erase] at hk
          simp only [w, if_neg hk.1]
          split_ifs with hkS
          · simp
          · simp
      _ = ∑ k ∈ S, (A i k : ℚ) := by
          rw [← Finset.sum_subset hS_sub (fun k _ hkS => if_neg hkS)]
          exact Finset.sum_congr rfl (fun k hk => if_pos hk)
      _ ≤ ∑ _k ∈ S, (-1 : ℚ) := by
          apply Finset.sum_le_sum; intro k hk
          exact_mod_cast hS_adj k hk
      _ = -(S.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ -4 := by
          have : (4 : ℚ) ≤ S.card := by exact_mod_cast hge
          linarith
  -- Inner sum at neighbor row r ∈ S ≤ 0
  have h_nbr : ∀ r, r ≠ i → r ∈ S → ∑ k, (A r k : ℚ) * w k ≤ 0 := by
    intro r hr_ne hr_S
    have hri : (A r i : ℚ) ≤ -1 := by
      have h1 := hGCM.off_diag_nonpos r i hr_ne
      have h2 : A i r ≠ 0 := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hr_S
        exact hr_S.2
      have h3 : A r i ≠ 0 := fun h => h2 ((hGCM.zero_iff r i hr_ne).mp h)
      have : A r i ≤ -1 := by omega
      exact_mod_cast this
    -- Extract i-term and r-term, bound the rest
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [w, if_pos rfl]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hr_ne, Finset.mem_univ r⟩)]
    simp only [if_neg hr_ne, if_pos hr_S, mul_one, hGCM.diag r]; push_cast
    -- Goal: ↑(A r i) * 2 + (2 + Σ rest) ≤ 0
    suffices h : ∑ k ∈ (Finset.univ.erase i).erase r, (A r k : ℚ) * w k ≤ 0 by linarith
    apply Finset.sum_nonpos; intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    simp only [w, if_neg hk.2]
    split_ifs with hkS
    · exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hGCM.off_diag_nonpos r k hk.1.symm) (by norm_num)
    · simp
  -- Combine: qform ≤ 0
  apply absurd (hPD w hw); push_neg
  rw [qform_eq_sum_mul]
  apply Finset.sum_nonpos; intro r _
  by_cases hr_i : r = i
  · rw [hr_i]; simp only [w, if_pos rfl]
    nlinarith [hSym.d_pos i, h_center]
  · by_cases hr_S : r ∈ S
    · simp only [w, if_neg hr_i, if_pos hr_S]
      nlinarith [hSym.d_pos r, h_nbr r hr_i hr_S]
    · simp only [w, if_neg hr_i, if_neg hr_S, mul_zero, zero_mul]; exact le_refl _

/-- The adjacency relation of toGraph is decidable. -/
instance toGraph_decRel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hGCM : IsGCM A) :
    DecidableRel (toGraph A hGCM).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ A i j ≠ 0))

/-- gcmDegree equals the SimpleGraph degree of the associated graph. -/
theorem gcmDegree_eq_degree {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (v : Fin n) :
    gcmDegree A v = (toGraph A hGCM).degree v := by
  simp only [gcmDegree, SimpleGraph.degree]
  congr 1; ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset, toGraph]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩

/-- A pos-def GCM graph is acyclic: any cycle would contradict positive-definiteness
    via not_posDef_of_cycle. -/
theorem isAcyclic_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym) :
    (toGraph A hGCM).IsAcyclic := by
  intro v c hc
  -- c is a cycle at v in toGraph A hGCM, with length ≥ 3
  have hlen : 3 ≤ c.length := by
    have h1 := hc.three_le_length
    exact h1
  -- Extract vertices: getVert is injective on {0, ..., length-1}
  let k := c.length
  let f : Fin k → Fin n := fun i => c.getVert i
  -- f is injective (from IsCycle.getVert_injOn')
  have hf_inj : Function.Injective f := by
    intro a b hab
    have ha : (a : ℕ) ≤ k - 1 := by omega
    have hb : (b : ℕ) ≤ k - 1 := by omega
    exact Fin.ext (hc.getVert_injOn' (Set.mem_setOf.mpr ha) (Set.mem_setOf.mpr hb) hab)
  -- Each vertex is adjacent to its successor (cyclically)
  have hadj : ∀ l : Fin k,
      A (f l) (f ⟨(l.val + 1) % k, Nat.mod_lt _ (by omega)⟩) ≠ 0 := by
    intro l
    have h_adj := c.adj_getVert_succ (by omega : l.val < c.length)
    simp only [toGraph] at h_adj
    by_cases hl : l.val + 1 < k
    · -- l+1 < k: getVert (l+1 % k) = getVert (l+1)
      simp only [f, Nat.mod_eq_of_lt hl]
      exact h_adj.2
    · -- l+1 = k: wrap around, getVert (l+1) = getVert k = v = getVert 0
      have hlk : l.val + 1 = k := by omega
      simp only [f, hlk, Nat.mod_self]
      -- h_adj says Adj (getVert l) (getVert (l+1))
      -- getVert (l+1) = getVert k = v = getVert 0
      have hgk : c.getVert (l.val + 1) = c.getVert 0 := by
        rw [hlk]; rw [c.getVert_length]; exact c.getVert_zero.symm
      rw [hgk] at h_adj
      exact h_adj.2
  -- Apply not_posDef_of_cycle
  exact absurd hPD (not_posDef_of_cycle hGCM hSym hlen ⟨f, hf_inj⟩ hadj)

/-- In a connected pos-def GCM on ≥ 3 vertices, some vertex has degree 1. -/
theorem exists_leaf {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A)
    (hConn : IsConnected A hGCM) (hPD : IsPosDef A hSym) :
    ∃ v : Fin (n+3), gcmDegree A v = 1 := by
  -- The graph is a tree (connected + acyclic)
  have hTree : (toGraph A hGCM).IsTree :=
    ⟨hConn, isAcyclic_of_posDef hGCM hSym hPD⟩
  -- Nontrivial: Fin (n+3) has ≥ 2 elements
  haveI : Nontrivial (Fin (n+3)) := inferInstance
  -- A nontrivial tree has a vertex of degree 1
  obtain ⟨v, hv⟩ := hTree.exists_vert_degree_one_of_nontrivial
  exact ⟨v, by rw [gcmDegree_eq_degree hGCM]; exact hv⟩

/-- Deleting a leaf from a connected GCM preserves connectivity.
    The leaf's unique neighbor remains connected to all other vertices
    via paths that didn't use the leaf. -/
theorem deleteVertex_connected_of_leaf {n : ℕ}
    {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hConn : IsConnected A hGCM)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1) :
    IsConnected (deleteVertex A v) (deleteVertex_isGCM hGCM v) := by
  -- Translate gcmDegree to graph degree
  have hdeg : (toGraph A hGCM).degree v = 1 := by
    rw [← gcmDegree_eq_degree hGCM]; exact hleaf
  -- Mathlib: removing a degree-1 vertex preserves connectivity
  have hind := hConn.induce_compl_singleton_of_degree_eq_one hdeg
  -- Build graph isomorphism: deleted graph ≃g induced subgraph on {v}ᶜ
  let e : toGraph (deleteVertex A v) (deleteVertex_isGCM hGCM v) ≃g
      (toGraph A hGCM).induce ({v}ᶜ : Set (Fin (n+3))) := {
    toEquiv := Equiv.ofBijective
      (fun i => ⟨v.succAbove i,
        Set.mem_compl_singleton_iff.mpr (Fin.succAbove_ne v i)⟩)
      ⟨fun a b h => Fin.succAbove_right_injective (congrArg Subtype.val h),
       fun ⟨w, hw⟩ => by
         rw [Set.mem_compl_singleton_iff] at hw
         obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hw
         exact ⟨z, Subtype.ext hz⟩⟩
    map_rel_iff' {a b} := by
      simp only [Equiv.ofBijective_apply, toGraph, deleteVertex, submatrix_apply]
      constructor
      · rintro ⟨hne, hA⟩
        exact ⟨fun h => hne (congrArg (Fin.succAbove v) h), hA⟩
      · rintro ⟨hne, hA⟩
        exact ⟨fun h => hne (Fin.succAbove_right_injective h), hA⟩ }
  -- Transfer connectivity via the isomorphism
  exact e.connected_iff.mpr hind

/-- Given a sub-matrix matching DynkinType t' and a leaf vertex v,
    determine the full DynkinType of the extended matrix.
    This is the combinatorial heart of the Cartan classification. -/
-- Helper: the rank of t' must equal n+2 (since CartanEquiv requires matching sizes)
private theorem cartanEquiv_rank_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {t : DynkinType} (h : CartanEquiv A t.cartanMatrix.2) : n = t.cartanMatrix.1 := by
  obtain ⟨e, _⟩ := h
  have := e.bijective
  exact Fintype.card_fin n ▸ Fintype.card_fin t.cartanMatrix.1 ▸
    Fintype.card_congr e ▸ rfl

/-- In a connected GCM on ≥ 2 vertices, every vertex has at least one neighbor. -/
private theorem exists_neighbor_of_connected {m : ℕ} {B : Matrix (Fin (m+2)) (Fin (m+2)) ℤ}
    (hGCM : IsGCM B) (hConn : IsConnected B hGCM) (i : Fin (m+2)) :
    ∃ j, j ≠ i ∧ B i j ≠ 0 := by
  by_contra hall; push_neg at hall
  have hiso : ∀ j, ¬(toGraph B hGCM).Adj i j := by
    intro j ⟨hne, hA⟩; exact hA (hall j hne.symm)
  -- Pick any other vertex (exists since m+2 ≥ 2)
  obtain ⟨k, hk⟩ := exists_ne i
  -- Connected: walk from i to k
  obtain ⟨w⟩ := hConn.preconnected i k
  -- Walk has positive length since i ≠ k
  have hlen : 0 < w.length := by
    rcases w with _ | ⟨_, _⟩
    · exact absurd rfl hk
    · simp [SimpleGraph.Walk.length]
  -- First step: getVert 0 and getVert 1 are adjacent
  have hadj := w.adj_getVert_succ (i := 0) hlen
  rw [w.getVert_zero] at hadj
  exact hiso _ hadj
-- ═══════════════════════════════════════════════════════════
-- E₈ marks (dual Coxeter labels)
-- ═══════════════════════════════════════════════════════════

/-- The marks (dual Coxeter labels) of E₈: components of the null vector
    of the affine extension Ẽ₈. These satisfy E₈ · marks = (0,...,0,1)
    where only the vertex-7 component is nonzero. -/
def marksE8 : Fin 8 → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

/-- The E₈ marks are ≥ 2. -/
theorem marksE8_ge_two : ∀ i : Fin 8, 2 ≤ marksE8 i := by decide

/-- E₈ · marks has a single nonzero entry at vertex 7. -/
theorem E8_mulVec_marks : CartanMatrix.E₈.mulVec marksE8 = fun i =>
    if i = 7 then 1 else 0 := by decide

/-- Marks vector for F₄: dual Coxeter labels. F₄ · marksF4 = (1,0,0,0). -/
def marksF4 : Fin 4 → ℤ := ![2, 3, 2, 1]

theorem F4_mulVec_marks : CartanMatrix.F₄.mulVec marksF4 = fun i =>
    if i = 0 then 1 else 0 := by decide

/-- Affine null marks for F₄: F₄ · affmarksF4 = (0,0,0,1).
    Used for vertex-3 attachment contradictions. -/
def affmarksF4 : Fin 4 → ℤ := ![2, 4, 3, 2]

theorem F4_mulVec_affmarks : CartanMatrix.F₄.mulVec affmarksF4 = fun i =>
    if i = 3 then 1 else 0 := by decide

/-- Marks vector for E₇: dual Coxeter labels. E₇ · marksE7 = (1,0,...,0). -/
def marksE7 : Fin 7 → ℤ := ![2, 2, 3, 4, 3, 2, 1]

theorem E7_mulVec_marks : CartanMatrix.E₇.mulVec marksE7 = fun i =>
    if i = 0 then 1 else 0 := by decide

/-- E₈ restricted to first 7 indices equals E₇. -/
theorem E8_castSucc_eq_E7 : ∀ i j : Fin 7,
    CartanMatrix.E₈ (Fin.castSucc i) (Fin.castSucc j) = CartanMatrix.E₇ i j := by decide

/-- E₈ last row/column: vertex 7 connects only to vertex 6. -/
theorem E8_last_row : ∀ i : Fin 7,
    CartanMatrix.E₈ 7 (Fin.castSucc i) = if i = 6 then -1 else 0 := by decide

/-- E₇ weight-2 submatrix, case A(v,u)=-1, A(u,v)=-2.
    Rows/cols 0-5 = E₇ vertices 1-6, row/col 6 = leaf v. -/
private def e7w2c1 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2, -1,  0,  0,  0,  0;
     -1, -1,  2, -1,  0,  0,  0;
      0,  0, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -2;
      0,  0,  0,  0,  0, -1,  2]

private theorem e7w2c1_null : e7w2c1.mulVec ![1, 1, 2, 2, 2, 2, 1] = 0 := by decide

/-- E₇ weight-2 submatrix, case A(v,u)=-2, A(u,v)=-1. -/
private def e7w2c2 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2, -1,  0,  0,  0,  0;
     -1, -1,  2, -1,  0,  0,  0;
      0,  0, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0, -2,  2]

private theorem e7w2c2_null : e7w2c2.mulVec ![1, 1, 2, 2, 2, 2, 2] = 0 := by decide

/-- E₇ vertices 1-6 sub-block equals first 6×6 of e7w2c1 (= e7w2c2). -/
private theorem E7_sub_eq : ∀ i j : Fin 6,
    CartanMatrix.E₇ (Fin.succ i) (Fin.succ j) =
    e7w2c1 (Fin.castSucc i) (Fin.castSucc j) := by decide

/-- Weight 3 is impossible when rank ≥ 3: a 3-vertex path with Coxeter weight 3
    on one edge always has a non-positive-definite symmetrization. -/
private theorem weight3_impossible {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1)
    (u : Fin (n+3)) (huv : u ≠ v) (hAvu : A v u ≠ 0)
    (w : Fin (n+3)) (hwu : w ≠ u) (hwv : w ≠ v) (hAuw : A u w ≠ 0)
    (hw3 : A v u * A u v = 3) : False := by
  have hAvu_neg : A v u ≤ -1 := by have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_ne : A u v ≠ 0 := fun h => hAvu ((hGCM.zero_iff u v huv).mp h)
  have hAuv_neg : A u v ≤ -1 := by have := hGCM.off_diag_nonpos u v huv; omega
  have hAuw_neg : A u w ≤ -1 := by have := hGCM.off_diag_nonpos u w hwu.symm; omega
  have hAwu_ne : A w u ≠ 0 := fun h => hAuw ((hGCM.zero_iff w u hwu).mp h)
  have hAwu_neg : A w u ≤ -1 := by have := hGCM.off_diag_nonpos w u hwu; omega
  -- v is a leaf, so A v w = 0 (v only connects to u)
  have hAvw : A v w = 0 := by
    by_contra hvw
    have hmem_u : u ∈ Finset.univ.filter (fun j => j ≠ v ∧ A v j ≠ 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨huv, hAvu⟩
    have hmem_w : w ∈ Finset.univ.filter (fun j => j ≠ v ∧ A v j ≠ 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hwv, hvw⟩
    have hcard : 2 ≤ (Finset.univ.filter (fun j => j ≠ v ∧ A v j ≠ 0)).card :=
      Finset.one_lt_card.mpr ⟨u, hmem_u, w, hmem_w, hwu.symm⟩
    unfold gcmDegree at hleaf; omega
  have hAwv : A w v = 0 := by rwa [← hGCM.zero_iff v w hwv.symm]
  have huw_wt : 1 ≤ A u w * A w u := by nlinarith
  -- Test vector: x(v) = -A(v,u), x(u) = 2, x(w) = -A(w,u), rest = 0.
  -- Inner sums at rows v and w vanish by construction.
  -- Row u gives d(u)·2·(1 - coxeterWeight(u,w)) ≤ 0.
  set x : Fin (n+3) → ℚ := fun i =>
    if i = v then -(↑(A v u : ℤ) : ℚ)
    else if i = u then 2
    else if i = w then -(↑(A w u : ℤ) : ℚ)
    else 0
  have hx : x ≠ 0 := by
    intro h; have := congr_fun h u
    simp only [x, if_neg huv, ↓reduceIte, Pi.zero_apply] at this; norm_num at this
  have x0 : ∀ k, k ≠ v → k ≠ u → k ≠ w → x k = 0 :=
    fun k h1 h2 h3 => by simp [x, h1, h2, h3]
  -- Inner sum at row v vanishes
  have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 0 := by
    rw [sum_two huv.symm _ (fun k hkv hku => by
      by_cases hkw : k = w
      · subst hkw; simp only [hAvw, Int.cast_zero, zero_mul]
      · simp [x0 k hkv hku hkw])]
    simp only [x, ↓reduceIte, if_neg huv, hGCM.diag v]; push_cast; ring
  -- Inner sum at row w vanishes
  have inner_w : ∑ j, (↑(A w j) : ℚ) * x j = 0 := by
    rw [sum_two hwu _ (fun k hkw hku => by
      by_cases hkv : k = v
      · subst hkv; simp only [hAwv, Int.cast_zero, zero_mul]
      · simp [x0 k hkv hku hkw])]
    simp only [x, if_neg hwv, if_neg hwu, if_neg huv, ↓reduceIte, hGCM.diag w]
    push_cast; ring
  -- qform reduces to the single row-u contribution
  have hq : qform hSym.d A x = hSym.d u * 2 * ∑ j, (↑(A u j) : ℚ) * x j := by
    rw [qform_eq_sum_mul]
    have hsingle := Finset.sum_eq_single u
      (fun b _ hb => show hSym.d b * x b * ∑ j, (↑(A b j) : ℚ) * x j = 0 from by
        by_cases hbv : b = v
        · subst hbv; simp [inner_v]
        · by_cases hbw : b = w
          · subst hbw; simp [inner_w]
          · simp [x0 b hbv hb hbw])
      (fun h => absurd (Finset.mem_univ u) h)
    rw [hsingle]; simp only [x, if_neg huv, ↓reduceIte]
  -- qform ≤ 0 (contradicting positive definiteness)
  have hq_le : qform hSym.d A x ≤ 0 := by
    rw [hq]
    suffices h : ∑ j, (↑(A u j) : ℚ) * x j ≤ 0 by nlinarith [hSym.d_pos u]
    rw [sum_three huv.symm hwv.symm hwu.symm _ (fun l hlv hlu hlw => by
      simp [x0 l hlv hlu hlw])]
    simp only [x, ↓reduceIte, if_neg huv, if_neg hwv, if_neg hwu, hGCM.diag u]; push_cast
    have h1 : (↑(A v u * A u v) : ℚ) = 3 := by exact_mod_cast hw3
    have h2 : (1 : ℚ) ≤ ↑(A u w * A w u) := by exact_mod_cast huw_wt
    simp only [Int.cast_mul] at h1 h2; nlinarith [mul_comm (↑(A v u) : ℚ) (↑(A u v) : ℚ)]
  exact absurd hPD (not_posDef_of_nonpos hSym x hx hq_le)

/-- E₈ cannot be extended: any pos-def GCM whose principal submatrix is
    CartanEquiv to E₈ is a contradiction.
    Proof: the E₈ marks vector extended with -A(v,u) at the leaf gives a
    non-positive qform. Key ingredients:
    - E₈·marks = (0,...,0,1) with only vertex-7 nonzero
    - marks ≥ 2 everywhere
    - d-values on E₈ subgraph are all equal (E₈ symmetric + connected)
    - symmetrizability converts cross-terms to use d(v) -/
private theorem e8_no_extension {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1)
    (ht' : CartanEquiv (deleteVertex A v) CartanMatrix.E₈) : False := by
  -- Rank: n + 2 = 8, so the matrix is 9×9
  have hn : n = 6 := by
    obtain ⟨e, _⟩ := ht'; have := Fintype.card_congr e
    simp only [Fintype.card_fin] at this; omega
  subst hn
  -- Extract leaf structure
  have hleaf' := hleaf; unfold gcmDegree at hleaf'
  obtain ⟨u, hu_set⟩ := Finset.card_eq_one.mp hleaf'
  have hu_mem := hu_set ▸ Finset.mem_singleton_self u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu_mem
  have huv : u ≠ v := hu_mem.1
  have hAvu : A v u ≠ 0 := hu_mem.2
  have huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u := by
    intro j hjv hjA
    have hmem : j ∈ Finset.univ.filter (fun j : Fin 9 => j ≠ v ∧ A v j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjv, hjA⟩
    rw [hu_set] at hmem; exact Finset.mem_singleton.mp hmem
  obtain ⟨e', he'⟩ := ht'
  obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
  have hAvu_neg : A v u ≤ -1 := by
    have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_ne : A u v ≠ 0 := fun h => hAvu ((hGCM.zero_iff u v huv).mp h)
  have hAuv_neg : A u v ≤ -1 := by
    have := hGCM.off_diag_nonpos u v huv; omega
  -- Leaf zero entries: v only connects to u
  have hAv0 : ∀ k : Fin 8, k ≠ u_idx → A v (v.succAbove k) = 0 := by
    intro k hk
    have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
    have hne_u : v.succAbove k ≠ u := fun h =>
      hk (Fin.succAbove_right_injective (hu_idx ▸ h))
    by_contra hvk; exact hne_u (huniq _ hne_v hvk)
  -- Submatrix entries = E₈ entries via CartanEquiv
  have hsub : ∀ i j : Fin 8, A (v.succAbove i) (v.succAbove j) =
      CartanMatrix.E₈ (e' i) (e' j) := fun i j => (he' i j).symm
  -- D-value equality on E₈ subgraph: E₈ is symmetric + connected → all d equal
  have hedge : ∀ p q : Fin 8, p ≠ q → CartanMatrix.E₈ p q ≠ 0 →
      hSym.d (v.succAbove (e'.symm p)) = hSym.d (v.succAbove (e'.symm q)) := by
    intro p q _ hE
    have h := hSym.sym (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))
    have hA_pq : A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q)) =
        CartanMatrix.E₈ p q := by rw [hsub]; simp [Equiv.apply_symm_apply]
    have hA_qp : A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p)) =
        CartanMatrix.E₈ q p := by rw [hsub]; simp [Equiv.apply_symm_apply]
    have hEsym : CartanMatrix.E₈ q p = CartanMatrix.E₈ p q := by
      have := congr_fun (congr_fun CartanMatrix.E₈_isSymm p) q
      rwa [Matrix.transpose_apply] at this
    rw [show (↑(A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))) : ℚ)
        = ↑(CartanMatrix.E₈ p q) from by rw [hA_pq],
      show (↑(A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p))) : ℚ)
        = ↑(CartanMatrix.E₈ p q) from by rw [hA_qp, hEsym]] at h
    exact mul_right_cancel₀ (by exact_mod_cast hE : (↑(CartanMatrix.E₈ p q) : ℚ) ≠ 0) h
  -- Chain along E₈ edges: 0↔2, 1↔3, 2↔3, 3↔4, 4↔5, 5↔6, 6↔7
  have h02 := hedge 0 2 (by decide) (by decide)
  have h23 := hedge 2 3 (by decide) (by decide)
  have h13 := hedge 1 3 (by decide) (by decide)
  have h34 := hedge 3 4 (by decide) (by decide)
  have h45 := hedge 4 5 (by decide) (by decide)
  have h56 := hedge 5 6 (by decide) (by decide)
  have h67 := hedge 6 7 (by decide) (by decide)
  -- All d values equal (chain to vertex 3, which connects to 0,1,2,4 directly/transitively)
  have hD_all : ∀ p : Fin 8,
      hSym.d (v.succAbove (e'.symm p)) = hSym.d (v.succAbove (e'.symm 3)) := by
    intro p; fin_cases p
    · exact h02.trans h23                                          -- 0→2→3
    · exact h13                                                     -- 1→3
    · exact h23                                                     -- 2→3
    · rfl                                                           -- 3
    · exact h34.symm                                                -- 4→3
    · exact h45.symm.trans h34.symm                                 -- 5→4→3
    · exact h56.symm.trans (h45.symm.trans h34.symm)                -- 6→5→4→3
    · exact h67.symm.trans (h56.symm.trans (h45.symm.trans h34.symm)) -- 7→6→5→4→3
  -- Key: d at vertex mapping to E₈-7 = d at u
  have hd7_eq_u : hSym.d (v.succAbove (e'.symm 7)) = hSym.d u := by
    have h1 := hD_all 7
    have h2 := hD_all (e' u_idx)
    rw [Equiv.symm_apply_apply] at h2
    rw [hu_idx] at h2
    exact h1.trans h2.symm
  -- Test vector: x(v) = -A(v,u), x(sA k) = marks(e' k)
  set c : ℚ := -(↑(A v u) : ℚ)
  have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
  have hc_pos : 0 < c := by simp only [c]; linarith
  set x : Fin 9 → ℚ := fun i =>
    if h : ∃ k : Fin 8, v.succAbove k = i then ↑(marksE8 (e' h.choose))
    else c
  have hx_sub : ∀ k : Fin 8, x (v.succAbove k) = ↑(marksE8 (e' k)) := by
    intro k; simp only [x]
    have hex : ∃ k' : Fin 8, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
    rw [dif_pos hex]
    have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
    rw [heq]
  have hx_v : x v = c := by
    simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
  have hx : x ≠ 0 := by
    intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
  -- Inner sum at leaf row v
  set mj : ℤ := marksE8 (e' u_idx)
  have hmj : (2 : ℤ) ≤ mj := marksE8_ge_two _
  have inner_v : ∑ j, (↑(A v j) : ℚ) * x j =
      2 * c + ↑(A v u) * ↑mj := by
    rw [Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hGCM.diag v, hx_sub]
    have hsum : ∑ k : Fin 8, (↑(A v (v.succAbove k)) : ℚ) * ↑(marksE8 (e' k)) =
        ↑(A v u) * ↑mj := by
      have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksE8 (e' u_idx)) =
          ↑(A v u) * ↑mj := by rw [hu_idx]
      rw [← hval]
      exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
    rw [hsum]; push_cast; ring
  -- E₈·marks reindexing
  have e8marks_sum : ∀ k : Fin 8,
      ∑ l : Fin 8, (↑(CartanMatrix.E₈ (e' k) (e' l)) : ℚ) * ↑(marksE8 (e' l)) =
      if e' k = 7 then 1 else 0 := by
    intro k
    have hreindex : ∑ l, (↑(CartanMatrix.E₈ (e' k) (e' l)) : ℚ) * ↑(marksE8 (e' l))
        = ∑ p, (↑(CartanMatrix.E₈ (e' k) p) : ℚ) * ↑(marksE8 p) := by
      exact Equiv.sum_comp e' (fun p => (↑(CartanMatrix.E₈ (e' k) p) : ℚ) * ↑(marksE8 p))
    rw [hreindex]
    have h := congr_fun E8_mulVec_marks (e' k)
    simp only [mulVec, dotProduct] at h
    have hcast : ∑ p, (↑(CartanMatrix.E₈ (e' k) p) : ℚ) * ↑(marksE8 p)
        = (↑(∑ p, CartanMatrix.E₈ (e' k) p * marksE8 p) : ℚ) := by push_cast; rfl
    rw [hcast, h]; push_cast; split_ifs <;> simp
  -- Inner sum at non-v vertex k
  have inner_sub : ∀ k : Fin 8, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
      ↑(A (v.succAbove k) v) * c +
      (if e' k = 7 then 1 else 0) := by
    intro k
    rw [Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hx_sub]; congr 1
    -- Rewrite A entries as E₈ entries, then use e8marks_sum
    have : ∀ l : Fin 8, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(marksE8 (e' l))
        = (↑(CartanMatrix.E₈ (e' k) (e' l)) : ℚ) * ↑(marksE8 (e' l)) := by
      intro l; rw [hsub]
    simp_rw [this]
    exact e8marks_sum k
  -- Symmetrizability trick: d(sA k)*A(sA k, v) = d(v)*A(v, sA k)
  have sym_trick : ∀ k : Fin 8,
      hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ) =
      hSym.d v * (↑(A v (v.succAbove k)) : ℚ) := by
    intro k; have := hSym.sym (v.succAbove k) v; linarith
  -- Show qform ≤ 0
  apply absurd hPD
  apply not_posDef_of_nonpos hSym x hx
  rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
  simp only [hx_v, hx_sub, inner_v, inner_sub]
  -- Split non-v sum: cross-terms + residual
  have hsplit : ∀ k : Fin 8,
      hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) *
      (↑(A (v.succAbove k) v) * c + if e' k = (7 : Fin 8) then (1 : ℚ) else 0) =
      c * (hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ)) * ↑(marksE8 (e' k)) +
      hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) *
      (if e' k = (7 : Fin 8) then (1 : ℚ) else 0) := by intro k; ring
  simp_rw [hsplit, sym_trick]
  rw [Finset.sum_add_distrib]
  -- Cross-term sum = c*d(v)*A(v,u)*mj (only u_idx term nonzero)
  have hcross : ∑ k : Fin 8, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
      ↑(marksE8 (e' k)) = c * hSym.d v * (↑(A v u) * ↑mj) := by
    simp_rw [show ∀ k : Fin 8, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
        ↑(marksE8 (e' k)) = c * hSym.d v * ((↑(A v (v.succAbove k)) : ℚ) *
        ↑(marksE8 (e' k))) from fun k => by ring]
    rw [← Finset.mul_sum]
    congr 1
    have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksE8 (e' u_idx)) =
        ↑(A v u) * ↑mj := by rw [hu_idx]
    rw [← hval]
    exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
  -- Residual sum = d(u)*2 (only vertex 7 contributes, via D-equality)
  have hresid : ∑ k : Fin 8, hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) *
      (if e' k = (7 : Fin 8) then (1 : ℚ) else 0) =
      2 * hSym.d u := by
    simp_rw [show ∀ k : Fin 8, hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) *
        (if e' k = (7 : Fin 8) then (1 : ℚ) else 0) =
        if e' k = 7 then hSym.d (v.succAbove k) * ↑(marksE8 (e' k)) else 0 from
      fun k => by split_ifs <;> ring]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hmem : Finset.univ.filter (fun k : Fin 8 => e' k = 7) = {e'.symm 7} := by
      ext k; simp [Finset.mem_filter, Equiv.eq_symm_apply]
    rw [hmem, Finset.sum_singleton, Equiv.apply_symm_apply]
    show hSym.d (v.succAbove (e'.symm 7)) * ↑(marksE8 7) = 2 * hSym.d u
    rw [hd7_eq_u]; simp [marksE8]; ring
  rw [hcross, hresid]
  -- Total: d(v)*c*(2c + A(v,u)*mj) + c*d(v)*A(v,u)*mj + 2*d(u) ≤ 0
  have hsym_vu := hSym.sym v u
  have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
  have hdv : 0 < hSym.d v := hSym.d_pos v
  have hdu : 0 < hSym.d u := hSym.d_pos u
  have hmj_q : (2 : ℚ) ≤ ↑mj := by exact_mod_cast hmj
  -- Algebraic simplification: unfold c = -↑(A v u) and rearrange
  have htotal : hSym.d v * c * (2 * c + ↑(A v u) * ↑mj) +
      (c * hSym.d v * (↑(A v u) * ↑mj) + 2 * hSym.d u) =
      2 * (hSym.d u + hSym.d v * (↑(A v u) : ℚ) ^ 2 * (1 - (↑mj : ℚ))) := by
    simp only [c]; ring
  rw [htotal]
  -- Symmetrizability: d(v)*A(v,u) = d(u)*A(u,v)
  have hsym_vu' : hSym.d v * (↑(A v u) : ℚ) = hSym.d u * (↑(A u v) : ℚ) := by
    linarith [hsym_vu]
  -- d(v)*A(v,u)² = d(u)*A(u,v)*A(v,u)
  have hkey : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
      hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) := by
    have : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
        (hSym.d v * (↑(A v u) : ℚ)) * (↑(A v u) : ℚ) := by ring
    rw [this, hsym_vu']; ring
  rw [hkey]
  -- Goal: 2*du + 2*(du*(auv*avu))*(1-mj) ≤ 0
  -- A(u,v)*A(v,u) ≥ 1 (product of two ≤ -1 values)
  have hab : 1 ≤ (↑(A u v) : ℚ) * (↑(A v u) : ℚ) := by
    have := mul_le_mul_of_nonpos_left hAuv_q (show (↑(A v u) : ℚ) ≤ 0 by linarith)
    linarith
  -- du ≤ du*(auv*avu) since auv*avu ≥ 1
  have hdu_ab : hSym.d u ≤ hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) :=
    le_mul_of_one_le_right (le_of_lt hdu) hab
  -- (du*(auv*avu))*(1-mj) ≤ du*(1-mj) since du*(auv*avu) ≥ du and 1-mj ≤ 0
  have hbound := mul_le_mul_of_nonpos_right hdu_ab
    (show (1 : ℚ) - (↑mj : ℚ) ≤ 0 by linarith)
  -- du*(1-mj) ≤ -du since mj ≥ 2
  have hdu_mj : 0 ≤ hSym.d u * ((↑mj : ℚ) - 2) :=
    mul_nonneg (le_of_lt hdu) (by linarith)
  linarith

/-- F₄ cannot be extended: any pos-def GCM whose principal submatrix is
    CartanEquiv to F₄ yields a contradiction.
    Proof: for attachment vertices 0,1,2 (marks ≥ 2), the marksF4 test vector
    gives qform ≤ 0. For vertex 3 (marks = 1), the affine F₄ test vector gives
    qform ≤ 0. -/
private theorem f4_no_extension {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1)
    (ht' : CartanEquiv (deleteVertex A v) CartanMatrix.F₄) : False := by
  -- Rank: n + 2 = 4
  have hn : n = 2 := by
    obtain ⟨e, _⟩ := ht'; have := Fintype.card_congr e
    simp only [Fintype.card_fin] at this; omega
  subst hn
  -- Extract leaf structure
  have hleaf' := hleaf; unfold gcmDegree at hleaf'
  obtain ⟨u, hu_set⟩ := Finset.card_eq_one.mp hleaf'
  have hu_mem := hu_set ▸ Finset.mem_singleton_self u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu_mem
  have huv : u ≠ v := hu_mem.1
  have hAvu : A v u ≠ 0 := hu_mem.2
  have huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u := by
    intro j hjv hjA
    have hmem : j ∈ Finset.univ.filter (fun j : Fin 5 => j ≠ v ∧ A v j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjv, hjA⟩
    rw [hu_set] at hmem; exact Finset.mem_singleton.mp hmem
  obtain ⟨e', he'⟩ := ht'
  obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
  have hAvu_neg : A v u ≤ -1 := by
    have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_ne : A u v ≠ 0 := fun h => hAvu ((hGCM.zero_iff u v huv).mp h)
  have hAuv_neg : A u v ≤ -1 := by
    have := hGCM.off_diag_nonpos u v huv; omega
  have hAv0 : ∀ k : Fin 4, k ≠ u_idx → A v (v.succAbove k) = 0 := by
    intro k hk
    have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
    have hne_u : v.succAbove k ≠ u := fun h =>
      hk (Fin.succAbove_right_injective (hu_idx ▸ h))
    by_contra hvk; exact hne_u (huniq _ hne_v hvk)
  have hsub : ∀ i j : Fin 4, A (v.succAbove i) (v.succAbove j) =
      CartanMatrix.F₄ (e' i) (e' j) := fun i j => (he' i j).symm
  -- Case split on attachment vertex
  -- Vertex 3: use affmarksF4 test vector [2,4,3,2] on F₄ subgraph, 1 on v
  -- Vertices 0,1,2: use marksF4 test vector [2,3,2,1] with c = -A(v,u)
  by_cases h3 : e' u_idx = 3
  · -- Vertex 3: affmarksF4 approach
    -- Test vector: x(v) = 1, x(sA k) = affmarksF4(e' k)
    set x : Fin 5 → ℚ := fun i =>
      if h : ∃ k : Fin 4, v.succAbove k = i then ↑(affmarksF4 (e' h.choose))
      else 1
    have hx_sub : ∀ k : Fin 4, x (v.succAbove k) = ↑(affmarksF4 (e' k)) := by
      intro k; simp only [x]
      have hex : ∃ k' : Fin 4, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
      rw [dif_pos hex]
      have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
      rw [heq]
    have hx_v : x v = 1 := by
      simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
    have hx : x ≠ 0 := by
      intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
    -- qform ≤ 0: each term d(i)*x(i)*inner(i) ≤ 0
    apply absurd hPD
    apply not_posDef_of_nonpos hSym x hx
    rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hx_sub]
    -- Inner sum at v: 2*1 + A(v,u)*affmarksF4(3) = 2 + 2*A(v,u)
    have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 2 + 2 * ↑(A v u) := by
      rw [Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hGCM.diag v, hx_sub]
      have hsum : ∑ k : Fin 4, (↑(A v (v.succAbove k)) : ℚ) * ↑(affmarksF4 (e' k)) =
          ↑(A v u) * ↑(affmarksF4 (e' u_idx)) := by
        have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(affmarksF4 (e' u_idx)) =
            ↑(A v u) * ↑(affmarksF4 (e' u_idx)) := by rw [hu_idx]
        rw [← hval]
        exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
      rw [hsum, h3]; simp [affmarksF4]; push_cast; ring
    -- Inner sum at u (vertex mapping to F₄-3):
    -- A(u,v)*1 + (F₄·affmarks)(3) = A(u,v) + 1
    have f4_affmarks_sum : ∀ k : Fin 4,
        ∑ l : Fin 4, (↑(CartanMatrix.F₄ (e' k) (e' l)) : ℚ) * ↑(affmarksF4 (e' l)) =
        if e' k = 3 then 1 else 0 := by
      intro k
      have hreindex := Equiv.sum_comp e'
        (fun p => (↑(CartanMatrix.F₄ (e' k) p) : ℚ) * ↑(affmarksF4 p))
      rw [hreindex]
      have h := congr_fun F4_mulVec_affmarks (e' k)
      simp only [mulVec, dotProduct] at h
      have hcast : ∑ p, (↑(CartanMatrix.F₄ (e' k) p) : ℚ) * ↑(affmarksF4 p)
          = (↑(∑ p, CartanMatrix.F₄ (e' k) p * affmarksF4 p) : ℚ) := by push_cast; rfl
      rw [hcast, h]; push_cast; split_ifs <;> simp
    have inner_sub : ∀ k : Fin 4, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
        ↑(A (v.succAbove k) v) * 1 +
        (if e' k = 3 then 1 else 0) := by
      intro k
      rw [Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hx_sub]; congr 1
      have : ∀ l : Fin 4, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(affmarksF4 (e' l))
          = (↑(CartanMatrix.F₄ (e' k) (e' l)) : ℚ) * ↑(affmarksF4 (e' l)) := by
        intro l; rw [hsub]
      simp_rw [this]
      exact f4_affmarks_sum k
    simp only [inner_v, inner_sub, mul_one]
    -- Total: d(v)*(2+2A(v,u)) + ∑_k d(sA k)*affmarks(e'k)*(A(sA k,v) + if_3)
    -- Non-v: only k with e'(k)=3 (i.e., u_idx) has nonzero inner. Others have inner=0.
    -- The term at u_idx: d(u)*2*(A(u,v)+1) ≤ 0
    -- All other terms: d(sA k)*affmarks(e'k)*0 = 0 (if e'k≠3 and k≠u_idx)
    --                  or d(sA k)*affmarks(e'k)*A(sA k,v) where A(sA k,v)=0 (leaf)
    have hsplit : ∀ k : Fin 4,
        hSym.d (v.succAbove k) * ↑(affmarksF4 (e' k)) *
        (↑(A (v.succAbove k) v) + if e' k = (3 : Fin 4) then (1 : ℚ) else 0) =
        if k = u_idx then hSym.d u * ↑(affmarksF4 (e' u_idx)) *
          (↑(A u v) + 1)
        else 0 := by
      intro k
      by_cases hku : k = u_idx
      · subst hku; simp [hu_idx, h3]
      · have hAkv : A (v.succAbove k) v = 0 := by
          have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
          have hAvk : A v (v.succAbove k) = 0 := hAv0 k hku
          exact (hGCM.zero_iff v _ (Ne.symm hne_v)).mp hAvk
        have hek3 : e' k ≠ 3 := by
          intro hek; exact hku (e'.injective (hek.trans h3.symm))
        simp [hAkv, hek3, hku]
    simp_rw [hsplit]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hmem : Finset.univ.filter (fun k : Fin 4 => k = u_idx) = {u_idx} := by
      ext k; simp
    rw [hmem, Finset.sum_singleton, h3]
    simp [affmarksF4]
    -- Goal: 1 * (2 + 2 * ↑(A v u)) + hSym.d u * 2 * (↑(A u v) + 1) ≤ 0
    -- = 2*(d(v)*(1+A(v,u)) + d(u)*(1+A(u,v)))
    -- Both d(v)*(1+A(v,u)) ≤ 0 and d(u)*(1+A(u,v)) ≤ 0 since A(v,u),A(u,v) ≤ -1
    have hdv : 0 < hSym.d v := hSym.d_pos v
    have hdu : 0 < hSym.d u := hSym.d_pos u
    have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
    have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
    nlinarith [mul_nonneg (le_of_lt hdv) (show (0 : ℚ) ≤ -(1 + ↑(A v u)) by linarith),
               mul_nonneg (le_of_lt hdu) (show (0 : ℚ) ≤ -(1 + ↑(A u v)) by linarith)]
  · -- Vertices 0,1,2: marksF4 approach (same structure as E₈)
    -- marksF4(e'(u_idx)) ≥ 2 since e'(u_idx) ≠ 3
    set mj : ℤ := marksF4 (e' u_idx)
    have hmj : (2 : ℤ) ≤ mj := by
      have : ∀ i : Fin 4, i ≠ 3 → 2 ≤ marksF4 i := by decide
      exact this _ h3
    set c : ℚ := -(↑(A v u) : ℚ)
    have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
    have hc_pos : 0 < c := by simp only [c]; linarith
    set x : Fin 5 → ℚ := fun i =>
      if h : ∃ k : Fin 4, v.succAbove k = i then ↑(marksF4 (e' h.choose))
      else c
    have hx_sub : ∀ k : Fin 4, x (v.succAbove k) = ↑(marksF4 (e' k)) := by
      intro k; simp only [x]
      have hex : ∃ k' : Fin 4, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
      rw [dif_pos hex]
      have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
      rw [heq]
    have hx_v : x v = c := by
      simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
    have hx : x ≠ 0 := by
      intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
    -- Inner sum at v: 2c + A(v,u)*mj
    have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 2 * c + ↑(A v u) * ↑mj := by
      rw [Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hGCM.diag v, hx_sub]
      have hsum : ∑ k : Fin 4, (↑(A v (v.succAbove k)) : ℚ) * ↑(marksF4 (e' k)) =
          ↑(A v u) * ↑mj := by
        have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksF4 (e' u_idx)) =
            ↑(A v u) * ↑mj := by rw [hu_idx]
        rw [← hval]
        exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
      rw [hsum]; push_cast; ring
    -- F₄·marks reindexing
    have f4marks_sum : ∀ k : Fin 4,
        ∑ l : Fin 4, (↑(CartanMatrix.F₄ (e' k) (e' l)) : ℚ) * ↑(marksF4 (e' l)) =
        if e' k = 0 then 1 else 0 := by
      intro k
      have hreindex := Equiv.sum_comp e'
        (fun p => (↑(CartanMatrix.F₄ (e' k) p) : ℚ) * ↑(marksF4 p))
      rw [hreindex]
      have h := congr_fun F4_mulVec_marks (e' k)
      simp only [mulVec, dotProduct] at h
      have hcast : ∑ p, (↑(CartanMatrix.F₄ (e' k) p) : ℚ) * ↑(marksF4 p)
          = (↑(∑ p, CartanMatrix.F₄ (e' k) p * marksF4 p) : ℚ) := by push_cast; rfl
      rw [hcast, h]; push_cast; split_ifs <;> simp
    -- Inner sum at non-v vertex k
    have inner_sub : ∀ k : Fin 4, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
        ↑(A (v.succAbove k) v) * c +
        (if e' k = 0 then 1 else 0) := by
      intro k
      rw [Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hx_sub]; congr 1
      have : ∀ l : Fin 4, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(marksF4 (e' l))
          = (↑(CartanMatrix.F₄ (e' k) (e' l)) : ℚ) * ↑(marksF4 (e' l)) := by
        intro l; rw [hsub]
      simp_rw [this]
      exact f4marks_sum k
    -- Symmetrizability trick
    have sym_trick : ∀ k : Fin 4,
        hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ) =
        hSym.d v * (↑(A v (v.succAbove k)) : ℚ) := by
      intro k; have := hSym.sym (v.succAbove k) v; linarith
    -- Show qform ≤ 0
    apply absurd hPD
    apply not_posDef_of_nonpos hSym x hx
    rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
    simp only [hx_v, hx_sub, inner_v, inner_sub]
    -- Split non-v sum: cross-terms + residual (same structure as E₈)
    have hsplit : ∀ k : Fin 4,
        hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) *
        (↑(A (v.succAbove k) v) * c + if e' k = (0 : Fin 4) then (1 : ℚ) else 0) =
        c * (hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ)) * ↑(marksF4 (e' k)) +
        hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) *
        (if e' k = (0 : Fin 4) then (1 : ℚ) else 0) := by intro k; ring
    simp_rw [hsplit, sym_trick]
    rw [Finset.sum_add_distrib]
    -- Cross-term sum = c*d(v)*A(v,u)*mj
    have hcross : ∑ k : Fin 4, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
        ↑(marksF4 (e' k)) = c * hSym.d v * (↑(A v u) * ↑mj) := by
      simp_rw [show ∀ k : Fin 4, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
          ↑(marksF4 (e' k)) = c * hSym.d v * ((↑(A v (v.succAbove k)) : ℚ) *
          ↑(marksF4 (e' k))) from fun k => by ring]
      rw [← Finset.mul_sum]
      congr 1
      have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksF4 (e' u_idx)) =
          ↑(A v u) * ↑mj := by rw [hu_idx]
      rw [← hval]
      exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
    -- Residual sum: only vertex 0 contributes. Need d(sA(e'⁻¹(0))) relationship.
    have hresid : ∑ k : Fin 4, hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) *
        (if e' k = (0 : Fin 4) then (1 : ℚ) else 0) =
        2 * hSym.d (v.succAbove (e'.symm 0)) := by
      simp_rw [show ∀ k : Fin 4, hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) *
          (if e' k = (0 : Fin 4) then (1 : ℚ) else 0) =
          if e' k = 0 then hSym.d (v.succAbove k) * ↑(marksF4 (e' k)) else 0 from
        fun k => by split_ifs <;> ring]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      have hmem : Finset.univ.filter (fun k : Fin 4 => e' k = 0) = {e'.symm 0} := by
        ext k; simp [Finset.mem_filter, Equiv.eq_symm_apply]
      rw [hmem, Finset.sum_singleton, Equiv.apply_symm_apply]
      simp [marksF4]; ring
    rw [hcross, hresid]
    -- Need: d(sA(e'⁻¹(0))) ≤ d(u)
    -- This follows from the F₄ d-value chain:
    -- Edge 0↔1: d₀=d₁ (symmetric). Edge 1↔2: d₂=2d₁.
    -- So d₀ ≤ d₂ ≤ d(u) depending on which vertex u maps to.
    have hd0_le_du : hSym.d (v.succAbove (e'.symm 0)) ≤ hSym.d u := by
      have hsub_sym := fun p q => hSym.sym (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))
      -- Edge 0↔1 is symmetric: d₀ = d₁
      have h01 : hSym.d (v.succAbove (e'.symm 0)) = hSym.d (v.succAbove (e'.symm 1)) := by
        have h := hsub_sym 0 1
        have hA01 : A (v.succAbove (e'.symm 0)) (v.succAbove (e'.symm 1)) = CartanMatrix.F₄ 0 1 := by
          rw [hsub]; simp [Equiv.apply_symm_apply]
        have hA10 : A (v.succAbove (e'.symm 1)) (v.succAbove (e'.symm 0)) = CartanMatrix.F₄ 1 0 := by
          rw [hsub]; simp [Equiv.apply_symm_apply]
        rw [show (↑(A (v.succAbove (e'.symm 0)) (v.succAbove (e'.symm 1))) : ℚ)
            = ↑(CartanMatrix.F₄ 0 1) from by rw [hA01],
          show (↑(A (v.succAbove (e'.symm 1)) (v.succAbove (e'.symm 0))) : ℚ)
            = ↑(CartanMatrix.F₄ 1 0) from by rw [hA10]] at h
        -- F₄(0,1) = F₄(1,0) = -1, so cancel
        have hf01 : (↑(CartanMatrix.F₄ 0 1) : ℚ) = -1 := by decide
        have hf10 : (↑(CartanMatrix.F₄ 1 0) : ℚ) = -1 := by decide
        rw [hf01, hf10] at h; linarith
      -- Edge 1↔2: d₁*(-2) = d₂*(-1), so d₂ = 2*d₁
      have h12 : hSym.d (v.succAbove (e'.symm 2)) =
          2 * hSym.d (v.succAbove (e'.symm 1)) := by
        have h := hsub_sym 1 2
        have hA12 : A (v.succAbove (e'.symm 1)) (v.succAbove (e'.symm 2)) = CartanMatrix.F₄ 1 2 := by
          rw [hsub]; simp [Equiv.apply_symm_apply]
        have hA21 : A (v.succAbove (e'.symm 2)) (v.succAbove (e'.symm 1)) = CartanMatrix.F₄ 2 1 := by
          rw [hsub]; simp [Equiv.apply_symm_apply]
        rw [show (↑(A (v.succAbove (e'.symm 1)) (v.succAbove (e'.symm 2))) : ℚ)
            = ↑(CartanMatrix.F₄ 1 2) from by rw [hA12],
          show (↑(A (v.succAbove (e'.symm 2)) (v.succAbove (e'.symm 1))) : ℚ)
            = ↑(CartanMatrix.F₄ 2 1) from by rw [hA21]] at h
        -- F₄(1,2) = -2, F₄(2,1) = -1
        have hf12 : (↑(CartanMatrix.F₄ 1 2) : ℚ) = -2 := by decide
        have hf21 : (↑(CartanMatrix.F₄ 2 1) : ℚ) = -1 := by decide
        rw [hf12, hf21] at h; linarith
      -- Now case on e'(u_idx) to relate d₀ to d(u)
      have hkey : e'.symm (e' u_idx) = u_idx := e'.symm_apply_apply u_idx
      have heu_cases : e' u_idx = 0 ∨ e' u_idx = 1 ∨ e' u_idx = 2 := by
        have : ∀ i : Fin 4, i ≠ 3 → (i = 0 ∨ i = 1 ∨ i = 2) := by decide
        exact this _ h3
      rcases heu_cases with h0 | h1 | h2
      · -- e'(u_idx) = 0: d₀ = d(u)
        rw [show e'.symm 0 = u_idx from h0 ▸ hkey, hu_idx]
      · -- e'(u_idx) = 1: d₀ = d₁ = d(u)
        rw [h01, show e'.symm 1 = u_idx from h1 ▸ hkey, hu_idx]
      · -- e'(u_idx) = 2: d₀ ≤ 2*d₁ = d(u)
        have hd1_pos : 0 < hSym.d (v.succAbove (e'.symm 1)) := hSym.d_pos _
        have : e'.symm 2 = u_idx := h2 ▸ hkey
        rw [this, hu_idx] at h12; linarith [h01]
    -- Final bound: d(v)*c*(2c+A(v,u)*mj) + c*d(v)*A(v,u)*mj + 2*d(sA(e'⁻¹0)) ≤ 0
    have hsym_vu := hSym.sym v u
    have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
    have hdu : 0 < hSym.d u := hSym.d_pos u
    have hdv : 0 < hSym.d v := hSym.d_pos v
    have hmj_q : (2 : ℚ) ≤ ↑mj := by exact_mod_cast hmj
    have hd0 := hSym.d_pos (v.succAbove (e'.symm 0))
    -- Algebraic simplification
    have htotal : hSym.d v * c * (2 * c + ↑(A v u) * ↑mj) +
        (c * hSym.d v * (↑(A v u) * ↑mj) + 2 * hSym.d (v.succAbove (e'.symm 0))) =
        2 * (hSym.d (v.succAbove (e'.symm 0)) +
        hSym.d v * (↑(A v u) : ℚ) ^ 2 * (1 - (↑mj : ℚ))) := by
      simp only [c]; ring
    rw [htotal]
    -- Symmetrizability: d(v)*A(v,u) = d(u)*A(u,v)
    have hsym_vu' : hSym.d v * (↑(A v u) : ℚ) = hSym.d u * (↑(A u v) : ℚ) := by
      linarith [hsym_vu]
    -- d(v)*A(v,u)² = d(u)*A(u,v)*A(v,u)
    have hkey : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
        hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) := by
      have : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
          (hSym.d v * (↑(A v u) : ℚ)) * (↑(A v u) : ℚ) := by ring
      rw [this, hsym_vu']; ring
    rw [hkey]
    -- Goal: 2*(d₀ + d(u)*auv*avu*(1-mj)) ≤ 0
    have hab : 1 ≤ (↑(A u v) : ℚ) * (↑(A v u) : ℚ) := by
      have := mul_le_mul_of_nonpos_left hAuv_q (show (↑(A v u) : ℚ) ≤ 0 by linarith)
      linarith
    -- d(u)*auv*avu ≥ d(u) ≥ d₀
    have hdu_ab : hSym.d (v.succAbove (e'.symm 0)) ≤
        hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) :=
      le_trans hd0_le_du (le_mul_of_one_le_right (le_of_lt hdu) hab)
    have hbound := mul_le_mul_of_nonpos_right hdu_ab
      (show (1 : ℚ) - (↑mj : ℚ) ≤ 0 by linarith)
    -- d₀ + d(u)*auv*avu*(1-mj) ≤ d₀ + d₀*(1-mj) = d₀*(2-mj) ≤ 0
    linarith [mul_nonneg (le_of_lt hd0) (show (0 : ℚ) ≤ (↑mj : ℚ) - 2 by linarith)]

/-- Given a sub-matrix matching DynkinType t' and a leaf vertex v,
    determine the full DynkinType of the extended matrix.
    This is the combinatorial heart of the Cartan classification. -/
theorem extend_dynkin_type {n : ℕ} {A : Matrix (Fin (n+3)) (Fin (n+3)) ℤ}
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A) (hPD : IsPosDef A hSym)
    (hConn : IsConnected A hGCM)
    (v : Fin (n+3)) (hleaf : gcmDegree A v = 1)
    (t' : DynkinType) (ht' : CartanEquiv (deleteVertex A v) t'.cartanMatrix.2) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  -- Extract the unique neighbor u of leaf v
  have hleaf' := hleaf
  unfold gcmDegree at hleaf'
  obtain ⟨u, hu_set⟩ := Finset.card_eq_one.mp hleaf'
  have hu_mem : u ∈ Finset.univ.filter (fun j : Fin (n+3) => j ≠ v ∧ A v j ≠ 0) :=
    hu_set ▸ Finset.mem_singleton_self u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu_mem
  have huv : u ≠ v := hu_mem.1
  have hAvu : A v u ≠ 0 := hu_mem.2
  have hAuv : A u v ≠ 0 := fun h => hAvu ((hGCM.zero_iff u v huv).mp h)
  have huniq : ∀ j, j ≠ v → A v j ≠ 0 → j = u := by
    intro j hjv hjA
    have : j ∈ Finset.univ.filter (fun j : Fin (n+3) => j ≠ v ∧ A v j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjv, hjA⟩
    rw [hu_set] at this; exact Finset.mem_singleton.mp this
  -- Rank equation
  have hrank : n + 2 = t'.cartanMatrix.1 := cartanEquiv_rank_eq ht'
  -- Get u's preimage in the submatrix
  obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
  -- u has a neighbor w in the connected subdiagram (rank ≥ 2)
  have hsubConn := deleteVertex_connected_of_leaf hGCM hConn v hleaf
  obtain ⟨w_sub, hw_ne, hBuw⟩ := exists_neighbor_of_connected
    (deleteVertex_isGCM hGCM v) hsubConn u_idx
  -- Translate to full matrix
  set w := v.succAbove w_sub with hw_def
  have hwv : w ≠ v := Fin.succAbove_ne v w_sub
  have hwu : w ≠ u := fun h => hw_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
  have hAuw : A u w ≠ 0 := by rw [← hu_idx]; exact hBuw
  -- Weight of the new edge (v, u) is ≤ 2: weight 3 → contradiction
  have hcw_lt : A v u * A u v < 4 :=
    coxeter_weight_lt_four hGCM hSym hPD v u huv.symm
  have hAvu_neg : A v u ≤ -1 := by
    have := hGCM.off_diag_nonpos v u huv.symm; omega
  have hAuv_neg : A u v ≤ -1 := by
    have := hGCM.off_diag_nonpos u v huv; omega
  have hcw_pos : 1 ≤ A v u * A u v := by nlinarith
  have hcw_le2 : A v u * A u v ≤ 2 := by
    by_contra h; push_neg at h
    have hcw3 : A v u * A u v = 3 := by omega
    exact weight3_impossible hGCM hSym hPD v hleaf u huv hAvu
      w hwu hwv hAuw hcw3
  -- Case split on Dynkin type
  cases t' with
  | G₂ =>
    exfalso
    -- G₂ has rank 2: n + 2 = 2, so n = 0. A is 3×3.
    simp only [DynkinType.cartanMatrix] at hrank
    have hn : n = 0 := by omega
    subst hn
    obtain ⟨e', he'⟩ := ht'
    -- Get u's preimage in the 2-element submatrix
    obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
    -- The other submatrix vertex
    let w_idx : Fin 2 := if u_idx = 0 then 1 else 0
    have hw_ne : w_idx ≠ u_idx := by
      fin_cases u_idx <;> simp [w_idx]
    set w := v.succAbove w_idx with hw_def
    have hwu : w ≠ u := fun h => hw_ne (Fin.succAbove_right_injective (hu_idx ▸ h))
    have hwv : w ≠ v := Fin.succAbove_ne v w_idx
    -- The G₂ Coxeter weight is 3 in the submatrix
    have hw3_sub : (deleteVertex A v) w_idx u_idx * (deleteVertex A v) u_idx w_idx = 3 := by
      rw [show (deleteVertex A v) w_idx u_idx = CartanMatrix.G₂ (e' w_idx) (e' u_idx) from
            (he' w_idx u_idx).symm,
          show (deleteVertex A v) u_idx w_idx = CartanMatrix.G₂ (e' u_idx) (e' w_idx) from
            (he' u_idx w_idx).symm]
      have hne : e' w_idx ≠ e' u_idx := e'.injective.ne hw_ne
      have key : ∀ (i j : Fin 2), i ≠ j →
          CartanMatrix.G₂ i j * CartanMatrix.G₂ j i = 3 := by decide
      exact key (e' w_idx) (e' u_idx) hne
    -- Translate to full matrix
    have hw3 : A w u * A u w = 3 := by rw [← hu_idx]; exact hw3_sub
    have hAwu : A w u ≠ 0 := by intro h; rw [h] at hw3; simp at hw3
    -- w is a leaf in the full matrix (connects only to u)
    have hleaf_w : gcmDegree A w = 1 := by
      unfold gcmDegree
      have hAvw : A v w = 0 := by
        by_contra h; exact hwu (huniq w hwv h)
      have hAwv : A w v = 0 := (hGCM.zero_iff v w (Ne.symm hwv)).mp hAvw
      suffices Finset.univ.filter (fun j : Fin 3 => j ≠ w ∧ A w j ≠ 0) = {u} by
        rw [this]; simp
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ⟨hjw, hjA⟩
        by_contra hju
        have hjv : j ≠ v := fun h => hjA (h ▸ hAwv)
        obtain ⟨j_idx, hj_idx⟩ := Fin.exists_succAbove_eq hjv
        have : j_idx ≠ u_idx := by intro h; exact hju (by rw [← hj_idx, h, hu_idx])
        have : j_idx ≠ w_idx := by intro h; exact hjw (by rw [← hj_idx, h])
        fin_cases j_idx <;> fin_cases u_idx <;> simp_all [w_idx]
      · intro hju; subst hju; exact ⟨hwu.symm, hAwu⟩
    -- Apply weight3_impossible: w is leaf, u is neighbor, v is third vertex
    exact weight3_impossible hGCM hSym hPD w hleaf_w u (Ne.symm hwu) hAwu
      v (Ne.symm huv) (Ne.symm hwv) hAuv hw3
  | A k hk => sorry
  | B k hk => sorry
  | C k hk => sorry
  | D k hk => sorry
  | E₆ => sorry
  | E₇ =>
    -- Rank: n + 2 = 7, so n = 5, A is 8×8.
    simp only [DynkinType.cartanMatrix] at hrank
    change CartanEquiv (deleteVertex A v) CartanMatrix.E₇ at ht'
    have hn : n = 5 := by omega
    subst hn
    obtain ⟨e', he'⟩ := ht'
    obtain ⟨u_idx, hu_idx⟩ := Fin.exists_succAbove_eq huv
    have hsub : ∀ i j : Fin 7, A (v.succAbove i) (v.succAbove j) =
        CartanMatrix.E₇ (e' i) (e' j) := fun i j => (he' i j).symm
    have hAv0 : ∀ k : Fin 7, k ≠ u_idx → A v (v.succAbove k) = 0 := by
      intro k hk
      have hne_v : v.succAbove k ≠ v := Fin.succAbove_ne v k
      have hne_u : v.succAbove k ≠ u := fun h =>
        hk (Fin.succAbove_right_injective (hu_idx ▸ h))
      by_contra hvk; exact hne_u (huniq _ hne_v hvk)
    by_cases h6 : e' u_idx = 6
    · -- Attachment at E₇ vertex 6 (marks = 1)
      by_cases hw1 : A v u * A u v = 1
      · -- Weight 1: both entries = -1. Construct E₈.
        have hAvu_eq : A v u = -1 := by nlinarith
        have hAuv_eq : A u v = -1 := by nlinarith
        -- Build CartanEquiv A E₈
        -- Map: v ↦ 7, v.succAbove k ↦ castSucc (e' k)
        refine ⟨DynkinType.E₈, ?_⟩
        -- For i : Fin 8, either i = v or i = v.succAbove k for unique k
        let f : Fin 8 → Fin 8 := fun i =>
          if h : ∃ k : Fin 7, v.succAbove k = i then Fin.castSucc (e' h.choose) else 7
        have hf_v : f v = 7 := by
          simp only [f]; rw [dif_neg]; push_neg
          exact fun k => Fin.succAbove_ne v k
        have hf_sub : ∀ k : Fin 7, f (v.succAbove k) = Fin.castSucc (e' k) := by
          intro k; simp only [f]
          have hex : ∃ k' : Fin 7, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
          rw [dif_pos hex]
          have : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
          rw [this]
        have hf_inj : Function.Injective f := by
          intro i j hij
          rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
          · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
            · exact hi.trans hj.symm
            · exfalso; rw [hi, hj, hf_v, hf_sub] at hij
              exact absurd (congr_arg Fin.val hij) (by simp [Fin.val_castSucc]; omega)
          · rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
            · exfalso; rw [hi, hj, hf_sub, hf_v] at hij
              exact absurd (congr_arg Fin.val hij) (by simp [Fin.val_castSucc]; omega)
            · rw [hi, hj]; congr 1
              rw [hi, hj, hf_sub, hf_sub] at hij
              exact e'.injective (Fin.castSucc_injective _ hij)
        have hf_bij := hf_inj.bijective_of_finite
        let σ := Equiv.ofBijective f hf_bij
        refine ⟨σ, fun i j => ?_⟩
        -- Verify: E₈ (σ i) (σ j) = A i j
        show CartanMatrix.E₈ (f i) (f j) = A i j
        rcases Fin.eq_self_or_eq_succAbove v i with hi | ⟨ki, hi⟩
        · -- i = v
          rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
          · -- j = v: E₈(7,7) = 2 = A(v,v)
            rw [hi, hj]; simp only [hf_v, hGCM.diag]; decide
          · -- j = sA kj: E₈(7, castSucc(e' kj)) vs A(v, sA kj)
            rw [hi, hj, hf_v, hf_sub, E8_last_row]
            by_cases hkj : kj = u_idx
            · subst hkj; rw [h6]; simp [hu_idx, hAvu_eq]
            · rw [if_neg (show e' kj ≠ 6 from fun h => hkj (e'.injective (h.trans h6.symm)))]
              simp [hAv0 kj hkj]
        · -- i = sA ki
          rcases Fin.eq_self_or_eq_succAbove v j with hj | ⟨kj, hj⟩
          · -- j = v: E₈(castSucc(e' ki), 7) vs A(sA ki, v)
            rw [hi, hj, hf_sub, hf_v]
            have hE8_sym : CartanMatrix.E₈ (Fin.castSucc (e' ki)) 7 =
                CartanMatrix.E₈ 7 (Fin.castSucc (e' ki)) := by
              have : ∀ a b : Fin 8, CartanMatrix.E₈ a b = CartanMatrix.E₈ b a := by decide
              exact this _ _
            rw [hE8_sym, E8_last_row]
            by_cases hki : ki = u_idx
            · subst hki; rw [h6]; simp [hu_idx, hAuv_eq]
            · rw [if_neg (show e' ki ≠ 6 from fun h => hki (e'.injective (h.trans h6.symm)))]
              simp
              have hne_v : v.succAbove ki ≠ v := Fin.succAbove_ne v ki
              have hAvk : A v (v.succAbove ki) = 0 := hAv0 ki hki
              exact ((hGCM.zero_iff v _ (Ne.symm hne_v)).mp hAvk).symm
          · -- Both submatrix: E₈(castSucc(e' ki), castSucc(e' kj)) = A(sA ki, sA kj)
            rw [hi, hj, hf_sub, hf_sub, E8_castSucc_eq_E7, ← hsub]
      · -- Weight 2 at vertex 6: contradiction
        exfalso
        have hw2 : A v u * A u v = 2 := by omega
        -- Case split on which entry is -2
        have hcases : (A v u = -1 ∧ A u v = -2) ∨ (A v u = -2 ∧ A u v = -1) := by
          have : A v u = -1 ∨ A v u = -2 := by
            have hAvu_ge : -2 ≤ A v u := by
              by_contra hlt; push_neg at hlt
              have h3 : A v u ≤ -3 := by omega
              nlinarith [mul_nonneg_of_nonpos_of_nonpos (show A v u + 2 ≤ 0 by omega)
                (show A u v + 1 ≤ 0 by omega)]
            omega
          rcases this with h | h <;> [left; right] <;> constructor <;> [exact h; nlinarith; exact h; nlinarith]
        -- Embedding: φ(k) = v.succAbove(e'⁻¹(k+1)) for k<6, φ(6) = v
        let g : Fin 6 → Fin 8 := fun k => v.succAbove (e'.symm (Fin.succ k))
        let φ : Fin 7 → Fin 8 := fun i =>
          if h : (i : ℕ) < 6 then g ⟨i, h⟩ else v
        have hφ_lt : ∀ (i : Fin 7) (hi : (i : ℕ) < 6), φ i = g ⟨i, hi⟩ := by
          intro i hi; simp only [φ, hi, ↓reduceDIte]
        have hφ6 : ∀ (i : Fin 7), ¬ (i : ℕ) < 6 → φ i = v := by
          intro i hi; simp only [φ, hi, ↓reduceDIte]
        have he'symm6 : e'.symm 6 = u_idx := by rw [← h6, e'.symm_apply_apply]
        -- φ is injective
        have hφ_inj : Function.Injective φ := by
          intro i j hij; simp only [φ] at hij
          by_cases hi : (i : ℕ) < 6 <;> by_cases hj : (j : ℕ) < 6 <;>
            simp only [hi, hj, ↓reduceDIte] at hij
          · exact Fin.ext (show (i : ℕ) = j from by
              have := Fin.ext_iff.mp (Fin.succ_injective _
                (e'.symm.injective (Fin.succAbove_right_injective hij)))
              simpa using this)
          · exact absurd hij (Fin.succAbove_ne v _)
          · exact absurd hij.symm (Fin.succAbove_ne v _)
          · exact Fin.ext (by omega)
        let φ_emb : Fin 7 ↪ Fin 8 := ⟨φ, hφ_inj⟩
        -- Key: e'.symm (Fin.succ k) ≠ u_idx when k ≠ 5
        have hk_ne_u : ∀ k : Fin 6, k ≠ 5 → e'.symm (Fin.succ k) ≠ u_idx := by
          intro k hk heq; apply hk
          have h1 := e'.symm.injective (heq.trans he'symm6.symm)
          exact Fin.ext (by have := Fin.ext_iff.mp h1; simp at this; omega)
        -- Entry proof helper: A(g k, v) and A(v, g k)
        have hAg_v : ∀ k : Fin 6, k ≠ 5 → A (g k) v = 0 := by
          intro k hk; show A (v.succAbove _) v = 0
          have h0 := hAv0 _ (hk_ne_u k hk)
          exact (hGCM.zero_iff v _ (Ne.symm (Fin.succAbove_ne v _))).mp h0
        have hAv_g : ∀ k : Fin 6, k ≠ 5 → A v (g k) = 0 := by
          intro k hk; show A v (v.succAbove _) = 0; exact hAv0 _ (hk_ne_u k hk)
        have hsucc5_eq_6 : Fin.succ (5 : Fin 6) = (6 : Fin 7) := by decide
        have hg5_eq : g 5 = u := by
          show v.succAbove (e'.symm (Fin.succ 5)) = u
          rw [hsucc5_eq_6, he'symm6, hu_idx]
        -- Submatrix entries = E₇ subblock
        have hgg : ∀ ki kj : Fin 6, A (g ki) (g kj) =
            CartanMatrix.E₇ (Fin.succ ki) (Fin.succ kj) := by
          intro ki kj; simp only [g]
          rw [hsub, e'.apply_symm_apply, e'.apply_symm_apply]
        -- Entry proof: A(φ i, φ j) = M i j (for given M, Avu, Auv)
        -- 4 cases: (g-g) submatrix, (g-v)/(v-g) leaf, (v-v) diagonal
        have hentry : ∀ (Avu Auv : ℤ) (hAvu : A v u = Avu) (hAuv : A u v = Auv)
            (M : Matrix (Fin 7) (Fin 7) ℤ)
            (hM1 : ∀ ki kj : Fin 6,
              M (Fin.castSucc ki) (Fin.castSucc kj) =
              CartanMatrix.E₇ (Fin.succ ki) (Fin.succ kj))
            (hM2 : M 6 6 = 2) (hM3 : M 5 6 = Auv) (hM4 : M 6 5 = Avu)
            (hM5 : ∀ k : Fin 6, k ≠ 5 → M (Fin.castSucc k) 6 = 0)
            (hM6 : ∀ k : Fin 6, k ≠ 5 → M 6 (Fin.castSucc k) = 0),
            ∀ i j : Fin 7, A (φ i) (φ j) = M i j := by
          intro Avu Auv hAvu hAuv M hM1 hM2 hM3 hM4 hM5 hM6 i j
          have hcs : ∀ (k : Fin 7) (hk : (k : ℕ) < 6),
              Fin.castSucc (⟨k, hk⟩ : Fin 6) = k := fun _ _ => Fin.ext rfl
          by_cases hi : (i : ℕ) < 6 <;> by_cases hj : (j : ℕ) < 6
          · -- Both in submatrix
            rw [hφ_lt i hi, hφ_lt j hj, hgg, ← hM1, hcs i hi, hcs j hj]
          · -- i in submatrix, j = v
            have hj6 : j = 6 := Fin.ext (by omega)
            subst hj6; rw [hφ_lt i hi, hφ6 6 (by omega)]
            by_cases hki5 : (⟨(i : ℕ), hi⟩ : Fin 6) = 5
            · rw [show g ⟨i, hi⟩ = u from by
                rw [show (⟨(i : ℕ), hi⟩ : Fin 6) = 5 from hki5]; exact hg5_eq]
              rw [hAuv, ← hM3]; congr 1; exact Fin.ext (by simp [Fin.ext_iff] at hki5; omega)
            · rw [hAg_v _ hki5, ← hM5 _ hki5, hcs i hi]
          · -- i = v, j in submatrix
            have hi6 : i = 6 := Fin.ext (by omega)
            subst hi6; rw [hφ6 6 (by omega), hφ_lt j hj]
            by_cases hkj5 : (⟨(j : ℕ), hj⟩ : Fin 6) = 5
            · rw [show g ⟨j, hj⟩ = u from by
                rw [show (⟨(j : ℕ), hj⟩ : Fin 6) = 5 from hkj5]; exact hg5_eq]
              rw [hAvu, ← hM4]; congr 1; exact Fin.ext (by simp [Fin.ext_iff] at hkj5; omega)
            · rw [hAv_g _ hkj5, ← hM6 _ hkj5, hcs j hj]
          · -- Both = v
            have hi6 : i = 6 := Fin.ext (by omega)
            have hj6 : j = 6 := Fin.ext (by omega)
            subst hi6; subst hj6
            rw [hGCM.diag, ← hM2]
        rcases hcases with ⟨hvu_eq, huv_eq⟩ | ⟨hvu_eq, huv_eq⟩
        · apply absurd hPD
          exact not_posDef_of_submatrix_int_null hSym φ_emb e7w2c1
            (hentry (-1) (-2) hvu_eq huv_eq e7w2c1
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide))
            _ (by decide) e7w2c1_null
        · apply absurd hPD
          exact not_posDef_of_submatrix_int_null hSym φ_emb e7w2c2
            (hentry (-2) (-1) hvu_eq huv_eq e7w2c2
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide))
            _ (by decide) e7w2c2_null
    · -- Attachment at E₇ vertex ≠ 6 (marks ≥ 2): contradiction
      exfalso
      -- Same marks approach as E₈/F₄
      set mj : ℤ := marksE7 (e' u_idx)
      have hmj : (2 : ℤ) ≤ mj := by
        have : ∀ i : Fin 7, i ≠ 6 → 2 ≤ marksE7 i := by decide
        exact this _ h6
      set c : ℚ := -(↑(A v u) : ℚ)
      have hAvu_q : (↑(A v u) : ℚ) ≤ -1 := by exact_mod_cast hAvu_neg
      have hc_pos : 0 < c := by simp only [c]; linarith
      set x : Fin 8 → ℚ := fun i =>
        if h : ∃ k : Fin 7, v.succAbove k = i then ↑(marksE7 (e' h.choose))
        else c
      have hx_sub : ∀ k : Fin 7, x (v.succAbove k) = ↑(marksE7 (e' k)) := by
        intro k; simp only [x]
        have hex : ∃ k' : Fin 7, v.succAbove k' = v.succAbove k := ⟨k, rfl⟩
        rw [dif_pos hex]
        have heq : hex.choose = k := Fin.succAbove_right_injective hex.choose_spec
        rw [heq]
      have hx_v : x v = c := by
        simp only [x]; rw [dif_neg (not_exists.mpr (fun k => Fin.succAbove_ne v k))]
      have hx : x ≠ 0 := by
        intro h; have := congr_fun h v; rw [hx_v, Pi.zero_apply] at this; linarith
      have inner_v : ∑ j, (↑(A v j) : ℚ) * x j = 2 * c + ↑(A v u) * ↑mj := by
        rw [Fin.sum_univ_succAbove _ v]
        simp only [hx_v, hGCM.diag v, hx_sub]
        have hsum : ∑ k : Fin 7, (↑(A v (v.succAbove k)) : ℚ) * ↑(marksE7 (e' k)) =
            ↑(A v u) * ↑mj := by
          have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksE7 (e' u_idx)) =
              ↑(A v u) * ↑mj := by rw [hu_idx]
          rw [← hval]
          exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
        rw [hsum]; push_cast; ring
      have e7marks_sum : ∀ k : Fin 7,
          ∑ l : Fin 7, (↑(CartanMatrix.E₇ (e' k) (e' l)) : ℚ) * ↑(marksE7 (e' l)) =
          if e' k = 0 then 1 else 0 := by
        intro k
        have hreindex := Equiv.sum_comp e'
          (fun p => (↑(CartanMatrix.E₇ (e' k) p) : ℚ) * ↑(marksE7 p))
        rw [hreindex]
        have h := congr_fun E7_mulVec_marks (e' k)
        simp only [mulVec, dotProduct] at h
        have hcast : ∑ p, (↑(CartanMatrix.E₇ (e' k) p) : ℚ) * ↑(marksE7 p)
            = (↑(∑ p, CartanMatrix.E₇ (e' k) p * marksE7 p) : ℚ) := by push_cast; rfl
        rw [hcast, h]; push_cast; split_ifs <;> simp
      have inner_sub : ∀ k : Fin 7, ∑ j, (↑(A (v.succAbove k) j) : ℚ) * x j =
          ↑(A (v.succAbove k) v) * c +
          (if e' k = 0 then 1 else 0) := by
        intro k
        rw [Fin.sum_univ_succAbove _ v]
        simp only [hx_v, hx_sub]; congr 1
        have : ∀ l : Fin 7, (↑(A (v.succAbove k) (v.succAbove l)) : ℚ) * ↑(marksE7 (e' l))
            = (↑(CartanMatrix.E₇ (e' k) (e' l)) : ℚ) * ↑(marksE7 (e' l)) := by
          intro l; rw [hsub]
        simp_rw [this]
        exact e7marks_sum k
      have sym_trick : ∀ k : Fin 7,
          hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ) =
          hSym.d v * (↑(A v (v.succAbove k)) : ℚ) := by
        intro k; have := hSym.sym (v.succAbove k) v; linarith
      apply absurd hPD
      apply not_posDef_of_nonpos hSym x hx
      rw [qform_eq_sum_mul, Fin.sum_univ_succAbove _ v]
      simp only [hx_v, hx_sub, inner_v, inner_sub]
      have hsplit : ∀ k : Fin 7,
          hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) *
          (↑(A (v.succAbove k) v) * c + if e' k = (0 : Fin 7) then (1 : ℚ) else 0) =
          c * (hSym.d (v.succAbove k) * (↑(A (v.succAbove k) v) : ℚ)) * ↑(marksE7 (e' k)) +
          hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) *
          (if e' k = (0 : Fin 7) then (1 : ℚ) else 0) := by intro k; ring
      simp_rw [hsplit, sym_trick]
      rw [Finset.sum_add_distrib]
      have hcross : ∑ k : Fin 7, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
          ↑(marksE7 (e' k)) = c * hSym.d v * (↑(A v u) * ↑mj) := by
        simp_rw [show ∀ k : Fin 7, c * (hSym.d v * (↑(A v (v.succAbove k)) : ℚ)) *
            ↑(marksE7 (e' k)) = c * hSym.d v * ((↑(A v (v.succAbove k)) : ℚ) *
            ↑(marksE7 (e' k))) from fun k => by ring]
        rw [← Finset.mul_sum]
        congr 1
        have hval : (↑(A v (v.succAbove u_idx)) : ℚ) * ↑(marksE7 (e' u_idx)) =
            ↑(A v u) * ↑mj := by rw [hu_idx]
        rw [← hval]
        exact Fintype.sum_eq_single u_idx (fun k hk => by rw [hAv0 k hk]; push_cast; ring)
      have hresid : ∑ k : Fin 7, hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) *
          (if e' k = (0 : Fin 7) then (1 : ℚ) else 0) =
          2 * hSym.d (v.succAbove (e'.symm 0)) := by
        simp_rw [show ∀ k : Fin 7, hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) *
            (if e' k = (0 : Fin 7) then (1 : ℚ) else 0) =
            if e' k = 0 then hSym.d (v.succAbove k) * ↑(marksE7 (e' k)) else 0 from
          fun k => by split_ifs <;> ring]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        have hmem : Finset.univ.filter (fun k : Fin 7 => e' k = 0) = {e'.symm 0} := by
          ext k; simp [Finset.mem_filter, Equiv.eq_symm_apply]
        rw [hmem, Finset.sum_singleton, Equiv.apply_symm_apply]
        simp [marksE7]; ring
      rw [hcross, hresid]
      -- Need d(e'⁻¹(0)) ≤ d(u). E₇ is symmetric so all d-values on subgraph equal.
      have hedge : ∀ p q : Fin 7, p ≠ q → CartanMatrix.E₇ p q ≠ 0 →
          hSym.d (v.succAbove (e'.symm p)) = hSym.d (v.succAbove (e'.symm q)) := by
        intro p q hpq hE
        have h := hSym.sym (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))
        have hApq : A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q)) =
            CartanMatrix.E₇ p q := by rw [hsub]; simp [Equiv.apply_symm_apply]
        have hAqp : A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p)) =
            CartanMatrix.E₇ q p := by rw [hsub]; simp [Equiv.apply_symm_apply]
        have hE_sym : CartanMatrix.E₇ p q = CartanMatrix.E₇ q p := by
          have : ∀ a b : Fin 7, CartanMatrix.E₇ a b = CartanMatrix.E₇ b a := by decide
          exact this _ _
        rw [show (↑(A (v.succAbove (e'.symm p)) (v.succAbove (e'.symm q))) : ℚ) =
            ↑(CartanMatrix.E₇ p q) from by push_cast; rw [hApq],
          show (↑(A (v.succAbove (e'.symm q)) (v.succAbove (e'.symm p))) : ℚ) =
            ↑(CartanMatrix.E₇ q p) from by push_cast; rw [hAqp],
          ← hE_sym] at h
        have hne : (↑(CartanMatrix.E₇ p q) : ℚ) ≠ 0 := by exact_mod_cast hE
        exact mul_right_cancel₀ hne h
      -- Chain along E₇ edges to get all d-values equal
      have h02 := hedge 0 2 (by decide) (by decide)
      have h13 := hedge 1 3 (by decide) (by decide)
      have h23 := hedge 2 3 (by decide) (by decide)
      have h34 := hedge 3 4 (by decide) (by decide)
      have h45 := hedge 4 5 (by decide) (by decide)
      have h56 := hedge 5 6 (by decide) (by decide)
      have hD_all : ∀ p : Fin 7, hSym.d (v.succAbove (e'.symm p)) =
          hSym.d (v.succAbove (e'.symm 3)) := by
        intro p; fin_cases p
        · exact h02.trans h23
        · exact h13
        · exact h23
        · rfl
        · exact h34.symm
        · exact h45.symm.trans h34.symm
        · exact h56.symm.trans (h45.symm.trans h34.symm)
      have hd0_eq_u : hSym.d (v.succAbove (e'.symm 0)) = hSym.d u := by
        rw [hD_all 0, ← hD_all (e' u_idx), e'.symm_apply_apply, hu_idx]
      -- Final algebraic bound (same structure as E₈)
      have hsym_vu := hSym.sym v u
      have hAuv_q : (↑(A u v) : ℚ) ≤ -1 := by exact_mod_cast hAuv_neg
      have hdu : 0 < hSym.d u := hSym.d_pos u
      have hdv : 0 < hSym.d v := hSym.d_pos v
      have hmj_q : (2 : ℚ) ≤ ↑mj := by exact_mod_cast hmj
      have hd0 := hSym.d_pos (v.succAbove (e'.symm 0))
      have htotal : hSym.d v * c * (2 * c + ↑(A v u) * ↑mj) +
          (c * hSym.d v * (↑(A v u) * ↑mj) + 2 * hSym.d (v.succAbove (e'.symm 0))) =
          2 * (hSym.d (v.succAbove (e'.symm 0)) +
          hSym.d v * (↑(A v u) : ℚ) ^ 2 * (1 - (↑mj : ℚ))) := by
        simp only [c]; ring
      rw [htotal]
      have hsym_vu' : hSym.d v * (↑(A v u) : ℚ) = hSym.d u * (↑(A u v) : ℚ) := by
        linarith [hsym_vu]
      have hkey : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
          hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) := by
        have : hSym.d v * (↑(A v u) : ℚ) ^ 2 =
            (hSym.d v * (↑(A v u) : ℚ)) * (↑(A v u) : ℚ) := by ring
        rw [this, hsym_vu']; ring
      rw [hkey, hd0_eq_u]
      have hab : 1 ≤ (↑(A u v) : ℚ) * (↑(A v u) : ℚ) := by
        have := mul_le_mul_of_nonpos_left hAuv_q (show (↑(A v u) : ℚ) ≤ 0 by linarith)
        linarith
      have hdu_ab : hSym.d u ≤
          hSym.d u * ((↑(A u v) : ℚ) * (↑(A v u) : ℚ)) :=
        le_mul_of_one_le_right (le_of_lt hdu) hab
      have hbound := mul_le_mul_of_nonpos_right hdu_ab
        (show (1 : ℚ) - (↑mj : ℚ) ≤ 0 by linarith)
      have hdu_mj : 0 ≤ hSym.d u * ((↑mj : ℚ) - 2) :=
        mul_nonneg (le_of_lt hdu) (by linarith)
      linarith
  | E₈ => exact (e8_no_extension hGCM hSym hPD v hleaf ht').elim
  | F₄ => exact (f4_no_extension hGCM hSym hPD v hleaf ht').elim

-- ═══════════════════════════════════════════════════════════
-- Cartan classification theorem
-- ═══════════════════════════════════════════════════════════

/-- The Cartan classification: every indecomposable positive-definite
    generalized Cartan matrix is equivalent to one of the 9 Dynkin types
    (A_n, B_n, C_n, D_n, E₆, E₇, E₈, F₄, G₂).

    The proof uses strong induction on n with leaf removal.
    1. The graph is a tree (not_posDef_of_cycle)
    2. Coxeter weights < 4 (coxeter_weight_lt_four)
    3. Each vertex has degree ≤ 3 (gcmDegree_le_three)
    4. Delete a leaf, classify the submatrix by IH
    5. Classify how the leaf re-attaches

    Reference: Humphreys, Introduction to Lie Algebras, Chapter 11. -/
theorem cartan_classification {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A)
    (hConn : IsConnected A hGCM) (hPD : IsPosDef A hSym) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2 := by
  -- Case split on matrix size
  match n with
  | 0 =>
    -- Fin 0 is empty, so Connected requires Nonempty (Fin 0) which is false
    exact absurd hConn.nonempty (not_nonempty_iff.mpr inferInstance)
  | 1 =>
    -- The only 1×1 GCM is [[2]] = A₁
    refine ⟨.A 1 (by omega), Equiv.refl _, fun i j => ?_⟩
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    subst hi; subst hj
    simp only [DynkinType.cartanMatrix, Equiv.refl_apply]
    rw [hGCM.diag 0]; decide
  | 2 =>
    -- Connectivity: the two vertices must be adjacent
    have h01 : A 0 1 ≠ 0 := by
      intro h
      have h10 := (hGCM.zero_iff 0 1 (by decide)).mp h
      have hnoedge : ∀ i j : Fin 2, ¬(toGraph A hGCM).Adj i j := by
        intro i j ⟨_, hA⟩; fin_cases i <;> fin_cases j <;> simp_all
      have ⟨w⟩ := hConn.preconnected (0 : Fin 2) 1
      exact w.rec (motive := fun u v _ => u ≠ v → False)
        (fun h => absurd rfl h)
        (fun hadj _ _ _ => absurd hadj (hnoedge _ _))
        (by decide)
    have h10 : A 1 0 ≠ 0 := fun h => h01 ((hGCM.zero_iff 1 0 (by decide)).mp h)
    -- Off-diagonal entries ≤ -1
    have ha1 : A 0 1 ≤ -1 := by
      have := hGCM.off_diag_nonpos 0 1 (by decide); omega
    have hb1 : A 1 0 ≤ -1 := by
      have := hGCM.off_diag_nonpos 1 0 (by decide); omega
    -- Coxeter weight in {1, 2, 3}
    have hw := coxeter_weight_lt_four hGCM hSym hPD 0 1 (by decide)
    unfold coxeterWeight at hw
    have hp_lo : 1 ≤ A 0 1 * A 1 0 := by nlinarith
    have hp_hi : A 0 1 * A 1 0 ≤ 3 := by omega
    -- Case split on the Coxeter weight (1, 2, or 3)
    have hcases : A 0 1 * A 1 0 = 1 ∨ A 0 1 * A 1 0 = 2 ∨ A 0 1 * A 1 0 = 3 := by omega
    rcases hcases with hw1 | hw2 | hw3
    · -- weight 1: a = b = -1 → A₂
      have ha : A 0 1 = -1 := by nlinarith
      have hb : A 1 0 = -1 := by nlinarith
      refine ⟨.A 2 (by omega), Equiv.refl _, fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;>
        simp only [DynkinType.cartanMatrix, Equiv.refl_apply, CartanMatrix.A_two] <;>
        first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
    · -- weight 2: (a,b) ∈ {(-2,-1), (-1,-2)} → B₂ or C₂
      have hab : (A 0 1 = -2 ∧ A 1 0 = -1) ∨ (A 0 1 = -1 ∧ A 1 0 = -2) := by
        have : -2 ≤ A 0 1 := by nlinarith
        have : -2 ≤ A 1 0 := by nlinarith
        have h1 : A 0 1 = -2 ∨ A 0 1 = -1 := by omega
        have h2 : A 1 0 = -2 ∨ A 1 0 = -1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; rw [h1, h2] at hw2; norm_num at hw2
        · exact .inl ⟨h1, h2⟩
        · exact .inr ⟨h1, h2⟩
        · exfalso; rw [h1, h2] at hw2; norm_num at hw2
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · refine ⟨.B 2 (by omega), Equiv.refl _, fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, Equiv.refl_apply, CartanMatrix.B_two] <;>
          first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
      · -- A 0 1 = -1, A 1 0 = -2: this is B₂ with swapped indices
        have s01 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by decide
        have s10 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by decide
        refine ⟨.B 2 (by omega), Equiv.swap 0 1, fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, CartanMatrix.B_two, s01, s10] <;>
          first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
    · -- weight 3: (a,b) ∈ {(-3,-1), (-1,-3)} → G₂
      have hab : (A 0 1 = -3 ∧ A 1 0 = -1) ∨ (A 0 1 = -1 ∧ A 1 0 = -3) := by
        have : -3 ≤ A 0 1 := by nlinarith
        have : -3 ≤ A 1 0 := by nlinarith
        have : A 0 1 ≠ -2 := fun h => by rw [h] at hw3; omega
        have : A 1 0 ≠ -2 := fun h => by rw [h] at hw3; omega
        have h1 : A 0 1 = -3 ∨ A 0 1 = -1 := by omega
        have h2 : A 1 0 = -3 ∨ A 1 0 = -1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; rw [h1, h2] at hw3; norm_num at hw3
        · exact .inl ⟨h1, h2⟩
        · exact .inr ⟨h1, h2⟩
        · exfalso; rw [h1, h2] at hw3; norm_num at hw3
      rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · refine ⟨.G₂, Equiv.refl _, fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, Equiv.refl_apply, CartanMatrix.G₂] <;>
          first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
      · refine ⟨.G₂, Equiv.swap 0 1, fun i j => ?_⟩
        have s01 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := by decide
        have s10 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := by decide
        fin_cases i <;> fin_cases j <;>
          simp only [DynkinType.cartanMatrix, CartanMatrix.G₂, s01, s10] <;>
          first | exact (hGCM.diag _).symm | exact ha.symm | exact hb.symm
  | n + 3 =>
    -- Find a leaf
    obtain ⟨v, hleaf⟩ := exists_leaf hGCM hSym hConn hPD
    -- Delete the leaf: gives (n+2) × (n+2) matrix
    -- Inductive hypothesis: sub-matrix is a Dynkin type
    obtain ⟨t', ht'⟩ := cartan_classification (deleteVertex A v)
      (deleteVertex_isGCM hGCM v) (deleteVertex_symmetrizable hSym v)
      (deleteVertex_connected_of_leaf hGCM hConn v hleaf)
      (deleteVertex_isPosDef hPD v)
    -- Classify the extension: leaf v connects to exactly one vertex u
    -- with Coxeter weight 1, 2, or 3. The extension determines the full type.
    exact extend_dynkin_type hGCM hSym hPD hConn v hleaf t' ht'
termination_by n

end BLD.Lie.Cartan
