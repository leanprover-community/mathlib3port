/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import LinearAlgebra.Matrix.Determinant
import Algebra.MvPolynomial.Basic
import Algebra.MvPolynomial.CommRing

#align_import linear_algebra.matrix.mv_polynomial from "leanprover-community/mathlib"@"86d1873c01a723aba6788f0b9051ae3d23b4c1c3"

/-!
# Matrices of multivariate polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we prove results about matrices over an mv_polynomial ring.
In particular, we provide `matrix.mv_polynomial_X` which associates every entry of a matrix with a
unique variable.

## Tags

matrix determinant, multivariate polynomial
-/


variable {m n R S : Type _}

namespace Matrix

variable (m n R)

#print Matrix.mvPolynomialX /-
/-- The matrix with variable `X (i,j)` at location `(i,j)`. -/
noncomputable def mvPolynomialX [CommSemiring R] : Matrix m n (MvPolynomial (m × n) R) :=
  of fun i j => MvPolynomial.X (i, j)
#align matrix.mv_polynomial_X Matrix.mvPolynomialX
-/

#print Matrix.mvPolynomialX_apply /-
-- TODO: set as an equation lemma for `mv_polynomial_X`, see mathlib4#3024
@[simp]
theorem mvPolynomialX_apply [CommSemiring R] (i j) :
    mvPolynomialX m n R i j = MvPolynomial.X (i, j) :=
  rfl
#align matrix.mv_polynomial_X_apply Matrix.mvPolynomialX_apply
-/

variable {m n R S}

#print Matrix.mvPolynomialX_map_eval₂ /-
/-- Any matrix `A` can be expressed as the evaluation of `matrix.mv_polynomial_X`.

This is of particular use when `mv_polynomial (m × n) R` is an integral domain but `S` is
not, as if the `mv_polynomial.eval₂` can be pulled to the outside of a goal, it can be solved in
under cancellative assumptions. -/
theorem mvPolynomialX_map_eval₂ [CommSemiring R] [CommSemiring S] (f : R →+* S) (A : Matrix m n S) :
    (mvPolynomialX m n R).map (MvPolynomial.eval₂ f fun p : m × n => A p.1 p.2) = A :=
  ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)
#align matrix.mv_polynomial_X_map_eval₂ Matrix.mvPolynomialX_map_eval₂
-/

#print Matrix.mvPolynomialX_mapMatrix_eval /-
/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `ring_hom` on the LHS. -/
theorem mvPolynomialX_mapMatrix_eval [Fintype m] [DecidableEq m] [CommSemiring R]
    (A : Matrix m m R) :
    (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A
#align matrix.mv_polynomial_X_map_matrix_eval Matrix.mvPolynomialX_mapMatrix_eval
-/

variable (R)

#print Matrix.mvPolynomialX_mapMatrix_aeval /-
/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `alg_hom` on the LHS. -/
theorem mvPolynomialX_mapMatrix_aeval [Fintype m] [DecidableEq m] [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Matrix m m S) :
    (MvPolynomial.aeval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A
#align matrix.mv_polynomial_X_map_matrix_aeval Matrix.mvPolynomialX_mapMatrix_aeval
-/

variable (m R)

#print Matrix.det_mvPolynomialX_ne_zero /-
/-- In a nontrivial ring, `matrix.mv_polynomial_X m m R` has non-zero determinant. -/
theorem det_mvPolynomialX_ne_zero [DecidableEq m] [Fintype m] [CommRing R] [Nontrivial R] :
    det (mvPolynomialX m m R) ≠ 0 := by
  intro h_det
  have := congr_arg Matrix.det (mv_polynomial_X_map_matrix_eval (1 : Matrix m m R))
  rw [det_one, ← RingHom.map_det, h_det, RingHom.map_zero] at this
  exact zero_ne_one this
#align matrix.det_mv_polynomial_X_ne_zero Matrix.det_mvPolynomialX_ne_zero
-/

end Matrix

