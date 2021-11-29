import Mathbin.LinearAlgebra.Matrix.Determinant 
import Mathbin.Data.MvPolynomial.Basic 
import Mathbin.Data.MvPolynomial.CommRing

/-!
# Matrices of multivariate polynomials

In this file, we prove results about matrices over an mv_polynomial ring.
In particular, we provide `matrix.mv_polynomial_X` which associates every entry of a matrix with a
unique variable.

## Tags

matrix determinant, multivariate polynomial
-/


variable {m n R S : Type _}

namespace Matrix

variable (m n R)

/-- The matrix with variable `X (i,j)` at location `(i,j)`. -/
@[simp]
noncomputable def mv_polynomial_X [CommSemiringₓ R] : Matrix m n (MvPolynomial (m × n) R)
| i, j => MvPolynomial.x (i, j)

variable {m n R S}

/-- Any matrix `A` can be expressed as the evaluation of `matrix.mv_polynomial_X`.

This is of particular use when `mv_polynomial (m × n) R` is an integral domain but `S` is
not, as if the `mv_polynomial.eval₂` can be pulled to the outside of a goal, it can be solved in
under cancellative assumptions. -/
theorem mv_polynomial_X_map_eval₂ [CommSemiringₓ R] [CommSemiringₓ S] (f : R →+* S) (A : Matrix m n S) :
  (mv_polynomial_X m n R).map (MvPolynomial.eval₂ f$ fun p : m × n => A p.1 p.2) = A :=
  ext$ fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)

/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `ring_hom` on the LHS. -/
theorem mv_polynomial_X_map_matrix_eval [Fintype m] [DecidableEq m] [CommSemiringₓ R] (A : Matrix m m R) :
  (MvPolynomial.eval$ fun p : m × m => A p.1 p.2).mapMatrix (mv_polynomial_X m m R) = A :=
  mv_polynomial_X_map_eval₂ _ A

variable (R)

/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `alg_hom` on the LHS. -/
theorem mv_polynomial_X_map_matrix_aeval [Fintype m] [DecidableEq m] [CommSemiringₓ R] [CommSemiringₓ S] [Algebra R S]
  (A : Matrix m m S) : (MvPolynomial.aeval$ fun p : m × m => A p.1 p.2).mapMatrix (mv_polynomial_X m m R) = A :=
  mv_polynomial_X_map_eval₂ _ A

variable (m R)

-- error in LinearAlgebra.Matrix.MvPolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a nontrivial ring, `matrix.mv_polynomial_X m m R` has non-zero determinant. -/
theorem det_mv_polynomial_X_ne_zero
[decidable_eq m]
[fintype m]
[comm_ring R]
[nontrivial R] : «expr ≠ »(det (mv_polynomial_X m m R), 0) :=
begin
  intro [ident h_det],
  have [] [] [":=", expr congr_arg matrix.det (mv_polynomial_X_map_matrix_eval (1 : matrix m m R))],
  rw ["[", expr det_one, ",", "<-", expr ring_hom.map_det, ",", expr h_det, ",", expr ring_hom.map_zero, "]"] ["at", ident this],
  exact [expr zero_ne_one this]
end

end Matrix

