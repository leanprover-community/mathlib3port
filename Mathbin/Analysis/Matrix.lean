/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Matrices as a normed space

In this file we provide the following non-instances on matrices, using the elementwise norm:

* `matrix.semi_normed_group`
* `matrix.normed_group`
* `matrix.normed_space`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.
-/


noncomputable section

open Nnreal Matrix

namespace Matrix

variable {R m n α β : Type _} [Fintype m] [Fintype n]

section SemiNormedGroup

variable [SemiNormedGroup α] [SemiNormedGroup β]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def semiNormedGroup : SemiNormedGroup (Matrix m n α) :=
  Pi.semiNormedGroup

attribute [local instance] Matrix.semiNormedGroup

theorem norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : Matrix m n α} : ∥A∥ ≤ r ↔ ∀ i j, ∥A i j∥ ≤ r := by
  simp [pi_norm_le_iff hr]

theorem nnnorm_le_iff {r : ℝ≥0 } {A : Matrix m n α} : ∥A∥₊ ≤ r ↔ ∀ i j, ∥A i j∥₊ ≤ r := by
  simp [pi_nnnorm_le_iff]

theorem norm_lt_iff {r : ℝ} (hr : 0 < r) {A : Matrix m n α} : ∥A∥ < r ↔ ∀ i j, ∥A i j∥ < r := by
  simp [pi_norm_lt_iff hr]

theorem nnnorm_lt_iff {r : ℝ≥0 } (hr : 0 < r) {A : Matrix m n α} : ∥A∥₊ < r ↔ ∀ i j, ∥A i j∥₊ < r := by
  simp [pi_nnnorm_lt_iff hr]

theorem norm_entry_le_entrywise_sup_norm (A : Matrix m n α) {i : m} {j : n} : ∥A i j∥ ≤ ∥A∥ :=
  (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

theorem nnnorm_entry_le_entrywise_sup_nnorm (A : Matrix m n α) {i : m} {j : n} : ∥A i j∥₊ ≤ ∥A∥₊ :=
  (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

@[simp]
theorem nnnorm_transpose (A : Matrix m n α) : ∥Aᵀ∥₊ = ∥A∥₊ := by
  simp_rw [Pi.nnnorm_def]
  exact Finset.sup_comm _ _ _

@[simp]
theorem norm_transpose (A : Matrix m n α) : ∥Aᵀ∥ = ∥A∥ :=
  congr_argₓ coe <| nnnorm_transpose A

@[simp]
theorem nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ∥f a∥₊ = ∥a∥₊) : ∥A.map f∥₊ = ∥A∥₊ := by
  simp_rw [Pi.nnnorm_def, Matrix.map, hf]

@[simp]
theorem norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ∥f a∥ = ∥a∥) : ∥A.map f∥ = ∥A∥ :=
  (congr_argₓ (coe : ℝ≥0 → ℝ) <| (nnnorm_map_eq A f) fun a => Subtype.ext <| hf a : _)

@[simp]
theorem nnnorm_col (v : m → α) : ∥colₓ v∥₊ = ∥v∥₊ := by
  simp [Pi.nnnorm_def]

@[simp]
theorem norm_col (v : m → α) : ∥colₓ v∥ = ∥v∥ :=
  congr_argₓ coe <| nnnorm_col v

@[simp]
theorem nnnorm_row (v : n → α) : ∥rowₓ v∥₊ = ∥v∥₊ := by
  simp [Pi.nnnorm_def]

@[simp]
theorem norm_row (v : n → α) : ∥rowₓ v∥ = ∥v∥ :=
  congr_argₓ coe <| nnnorm_row v

@[simp]
theorem nnnorm_diagonal [DecidableEq n] (v : n → α) : ∥diagonalₓ v∥₊ = ∥v∥₊ := by
  simp_rw [Pi.nnnorm_def]
  congr 1 with i : 1
  refine' le_antisymmₓ (Finset.sup_le fun j hj => _) _
  · obtain rfl | hij := eq_or_ne i j
    · rw [diagonal_apply_eq]
      
    · rw [diagonal_apply_ne _ hij, nnnorm_zero]
      exact zero_le _
      
    
  · refine' Eq.trans_le _ (Finset.le_sup (Finset.mem_univ i))
    rw [diagonal_apply_eq]
    

@[simp]
theorem norm_diagonal [DecidableEq n] (v : n → α) : ∥diagonalₓ v∥ = ∥v∥ :=
  congr_argₓ coe <| nnnorm_diagonal v

/-- Note this is safe as an instance as it carries no data. -/
instance [Nonempty n] [DecidableEq n] [One α] [NormOneClass α] : NormOneClass (Matrix n n α) :=
  ⟨(norm_diagonal _).trans <| norm_one⟩

end SemiNormedGroup

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normedGroup [NormedGroup α] : NormedGroup (Matrix m n α) :=
  Pi.normedGroup

section NormedSpace

attribute [local instance] Matrix.semiNormedGroup

variable [NormedField R] [SemiNormedGroup α] [NormedSpace R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normedSpace : NormedSpace R (Matrix m n α) :=
  Pi.normedSpace

end NormedSpace

end Matrix

