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
-- Cartan classification theorem (statement)
-- ═══════════════════════════════════════════════════════════

/-- The Cartan classification: every indecomposable positive-definite
    generalized Cartan matrix is equivalent to one of the 9 Dynkin types
    (A_n, B_n, C_n, D_n, E₆, E₇, E₈, F₄, G₂).

    The proof proceeds by forbidden subgraph analysis:
    1. The graph is a tree (not_posDef_of_cycle)
    2. Coxeter weights < 4 (coxeter_weight_lt_four)
    3. Each vertex has degree ≤ 3 (from the D̃₄ forbidden subgraph)
    4. At most one branch point, at most one multiple bond
    5. Enumeration of remaining cases yields exactly the 9 types

    Steps 1-2 are proved above. The full enumeration (steps 3-5) is
    standard but lengthy (~400 lines of case analysis).

    Reference: Humphreys, Introduction to Lie Algebras, Chapter 11. -/
proof_wanted cartan_classification {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hGCM : IsGCM A) (hSym : IsSymmetrizable A)
    (hConn : IsConnected A hGCM) (hPD : IsPosDef A hSym) :
    ∃ t : DynkinType, CartanEquiv A t.cartanMatrix.2

end BLD.Lie.Cartan
