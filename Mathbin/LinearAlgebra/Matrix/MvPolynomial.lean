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


variable{m n R S : Type _}

namespace Matrix

variable(m n R)

/-- The matrix with variable `X (i,j)` at location `(i,j)`. -/
@[simp]
noncomputable def mv_polynomial_X [CommSemiringₓ R] : Matrix m n (MvPolynomial (m × n) R)
| i, j => MvPolynomial.x (i, j)

variable{m n R S}

-- error in LinearAlgebra.Matrix.MvPolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Any matrix `A` can be expressed as the evaluation of `matrix.mv_polynomial_X`.

This is of particular use when `mv_polynomial (m × n) R` is an integral domain but `S` is
not, as if the `mv_polynomial.eval₂` can be pulled to the outside of a goal, it can be solved in
under cancellative assumptions. -/
theorem mv_polynomial_X_map_eval₂
[comm_semiring R]
[comm_semiring S]
(f : «expr →+* »(R, S))
(A : matrix m n S) : «expr = »((mv_polynomial_X m n R).map «expr $ »(mv_polynomial.eval₂ f, λ
  p : «expr × »(m, n), A p.1 p.2), A) :=
«expr $ »(ext, λ i j, mv_polynomial.eval₂_X _ (λ p : «expr × »(m, n), A p.1 p.2) (i, j))

-- error in LinearAlgebra.Matrix.MvPolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `ring_hom` on the LHS. -/
theorem mv_polynomial_X_map_matrix_eval
[fintype m]
[decidable_eq m]
[comm_semiring R]
(A : matrix m m R) : «expr = »(«expr $ »(mv_polynomial.eval, λ
  p : «expr × »(m, m), A p.1 p.2).map_matrix (mv_polynomial_X m m R), A) :=
mv_polynomial_X_map_eval₂ _ A

variable(R)

-- error in LinearAlgebra.Matrix.MvPolynomial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `alg_hom` on the LHS. -/
theorem mv_polynomial_X_map_matrix_aeval
[fintype m]
[decidable_eq m]
[comm_semiring R]
[comm_semiring S]
[algebra R S]
(A : matrix m m S) : «expr = »(«expr $ »(mv_polynomial.aeval, λ
  p : «expr × »(m, m), A p.1 p.2).map_matrix (mv_polynomial_X m m R), A) :=
mv_polynomial_X_map_eval₂ _ A

variable(m R)

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

