import Mathbin.Data.Matrix.Basic 
import Mathbin.LinearAlgebra.Matrix.Trace

/-!
# Matrices with a single non-zero element.

This file provides `matrix.std_basis_matrix`. The matrix `matrix.std_basis_matrix i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/


variable {l m n : Type _}

variable {R α : Type _}

namespace Matrix

open_locale Matrix

open_locale BigOperators

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [Semiringₓ α]

/--
`std_basis_matrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def std_basis_matrix (i : m) (j : n) (a : α) : Matrix m n α :=
  fun i' j' => if i = i' ∧ j = j' then a else 0

@[simp]
theorem smul_std_basis_matrix (i : m) (j : n) (a b : α) : b • std_basis_matrix i j a = std_basis_matrix i j (b • a) :=
  by 
    unfold std_basis_matrix 
    ext 
    simp 

@[simp]
theorem std_basis_matrix_zero (i : m) (j : n) : std_basis_matrix i j (0 : α) = 0 :=
  by 
    unfold std_basis_matrix 
    ext 
    simp 

theorem std_basis_matrix_add (i : m) (j : n) (a b : α) :
  std_basis_matrix i j (a+b) = std_basis_matrix i j a+std_basis_matrix i j b :=
  by 
    unfold std_basis_matrix 
    ext 
    splitIfs with h <;> simp [h]

theorem matrix_eq_sum_std_basis (x : Matrix n m α) [Fintype n] [Fintype m] :
  x = ∑ (i : n)(j : m), std_basis_matrix i j (x i j) :=
  by 
    ext 
    symm 
    iterate 2 
      rw [Finset.sum_apply]
    convert Fintype.sum_eq_single i _
    ·
      simp [std_basis_matrix]
    ·
      intro j hj 
      simp [std_basis_matrix, hj]

theorem std_basis_eq_basis_mul_basis (i : m) (j : n) :
  std_basis_matrix i j 1 = vec_mul_vec (fun i' => ite (i = i') 1 0) fun j' => ite (j = j') 1 0 :=
  by 
    ext 
    normNum [std_basis_matrix, vec_mul_vec]
    exact ite_and _ _ _ _

@[elab_as_eliminator]
protected theorem induction_on' [Fintype m] [Fintype n] {P : Matrix m n α → Prop} (M : Matrix m n α) (h_zero : P 0)
  (h_add : ∀ p q, P p → P q → P (p+q)) (h_std_basis : ∀ i : m j : n x : α, P (std_basis_matrix i j x)) : P M :=
  by 
    rw [matrix_eq_sum_std_basis M, ←Finset.sum_product']
    apply Finset.sum_induction _ _ h_add h_zero
    ·
      intros 
      apply h_std_basis

@[elab_as_eliminator]
protected theorem induction_on [Fintype m] [Fintype n] [Nonempty m] [Nonempty n] {P : Matrix m n α → Prop}
  (M : Matrix m n α) (h_add : ∀ p q, P p → P q → P (p+q)) (h_std_basis : ∀ i j x, P (std_basis_matrix i j x)) : P M :=
  Matrix.induction_on' M
    (by 
      inhabit m 
      inhabit n 
      simpa using h_std_basis (default m) (default n) 0)
    h_add h_std_basis

namespace StdBasisMatrix

section 

variable (i : m) (j : n) (c : α) (i' : m) (j' : n)

@[simp]
theorem apply_same : std_basis_matrix i j c i j = c :=
  if_pos (And.intro rfl rfl)

@[simp]
theorem apply_of_ne (h : ¬(i = i' ∧ j = j')) : std_basis_matrix i j c i' j' = 0 :=
  by 
    simp only [std_basis_matrix, and_imp, ite_eq_right_iff]
    tauto

@[simp]
theorem apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) : std_basis_matrix i j a i' j' = 0 :=
  by 
    simp [hi]

@[simp]
theorem apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) : std_basis_matrix i j a i' j' = 0 :=
  by 
    simp [hj]

end 

section 

variable (i j : n) (c : α) (i' j' : n)

@[simp]
theorem diag_zero (h : j ≠ i) : diag n α α (std_basis_matrix i j c) = 0 :=
  funext$ fun k => if_neg$ fun ⟨e₁, e₂⟩ => h (e₂.trans e₁.symm)

variable [Fintype n]

theorem trace_zero (h : j ≠ i) : trace n α α (std_basis_matrix i j c) = 0 :=
  by 
    simp [h]

@[simp]
theorem mul_left_apply_same (b : n) (M : Matrix n n α) : (std_basis_matrix i j c ⬝ M) i b = c*M j b :=
  by 
    simp [mul_apply, std_basis_matrix]

@[simp]
theorem mul_right_apply_same (a : n) (M : Matrix n n α) : (M ⬝ std_basis_matrix i j c) a j = M a i*c :=
  by 
    simp [mul_apply, std_basis_matrix, mul_commₓ]

@[simp]
theorem mul_left_apply_of_ne (a b : n) (h : a ≠ i) (M : Matrix n n α) : (std_basis_matrix i j c ⬝ M) a b = 0 :=
  by 
    simp [mul_apply, h.symm]

@[simp]
theorem mul_right_apply_of_ne (a b : n) (hbj : b ≠ j) (M : Matrix n n α) : (M ⬝ std_basis_matrix i j c) a b = 0 :=
  by 
    simp [mul_apply, hbj.symm]

@[simp]
theorem mul_same (k : n) (d : α) : std_basis_matrix i j c ⬝ std_basis_matrix j k d = std_basis_matrix i k (c*d) :=
  by 
    ext a b 
    simp only [mul_apply, std_basis_matrix, boole_mul]
    byCases' h₁ : i = a <;> byCases' h₂ : k = b <;> simp [h₁, h₂]

@[simp]
theorem mul_of_ne {k l : n} (h : j ≠ k) (d : α) : std_basis_matrix i j c ⬝ std_basis_matrix k l d = 0 :=
  by 
    ext a b 
    simp only [mul_apply, boole_mul, std_basis_matrix]
    byCases' h₁ : i = a <;> simp [h₁, h, h.symm]

end 

end StdBasisMatrix

end Matrix

