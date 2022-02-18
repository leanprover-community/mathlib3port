import Mathbin.LinearAlgebra.Matrix.Adjugate
import Mathbin.RingTheory.MatrixAlgebra
import Mathbin.RingTheory.PolynomialAlgebra
import Mathbin.Tactic.ApplyFun
import Mathbin.Tactic.Squeeze

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

## Main definitions

* `matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/


noncomputable section

universe u v w

open Polynomial Matrix

open_locale BigOperators Polynomial

variable {R : Type u} [CommRingₓ R]

variable {n : Type w} [DecidableEq n] [Fintype n]

open Finset

/-- The "characteristic matrix" of `M : matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (x : R[X]) - (c : R →+* R[X]).mapMatrix M

@[simp]
theorem charmatrix_apply_eq (M : Matrix n n R) (i : n) : charmatrix M i i = (x : R[X]) - c (M i i) := by
  simp only [charmatrix, sub_left_inj, Pi.sub_apply, scalar_apply_eq, RingHom.map_matrix_apply, map_apply,
    Dmatrix.sub_apply]

@[simp]
theorem charmatrix_apply_ne (M : Matrix n n R) (i j : n) (h : i ≠ j) : charmatrix M i j = -c (M i j) := by
  simp only [charmatrix, Pi.sub_apply, scalar_apply_ne _ _ _ h, zero_sub, RingHom.map_matrix_apply, map_apply,
    Dmatrix.sub_apply]

theorem mat_poly_equiv_charmatrix (M : Matrix n n R) : matPolyEquiv (charmatrix M) = X - c M := by
  ext k i j
  simp only [mat_poly_equiv_coeff_apply, coeff_sub, Pi.sub_apply]
  by_cases' h : i = j
  · subst h
    rw [charmatrix_apply_eq, coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
    
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]
    

theorem charmatrix_reindex {m : Type v} [DecidableEq m] [Fintype m] (e : n ≃ m) (M : Matrix n n R) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by
  ext i j x
  by_cases' h : i = j
  all_goals
    simp [h]

/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$.
-/
def Matrix.charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det

theorem Matrix.charpoly_reindex {m : Type v} [DecidableEq m] [Fintype m] (e : n ≃ m) (M : Matrix n n R) :
    (reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_reindex, Matrix.det_reindex_self]

/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.
-/
theorem Matrix.aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M := (adjugate_mul _).symm
  apply_fun matPolyEquiv  at h
  simp only [mat_poly_equiv.map_mul, mat_poly_equiv_charmatrix] at h
  apply_fun fun p => p.eval M  at h
  rw [eval_mul_X_sub_C] at h
  rw [mat_poly_equiv_smul_one, eval_map] at h
  exact h

