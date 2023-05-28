/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.matrix.mv_polynomial
! leanprover-community/mathlib commit 86d1873c01a723aba6788f0b9051ae3d23b4c1c3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.Data.MvPolynomial.Basic
import Mathbin.Data.MvPolynomial.CommRing

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

/- warning: matrix.mv_polynomial_X_apply -> Matrix.mvPolynomialX_apply is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u1}) (n : Type.{u2}) (R : Type.{u3}) [_inst_1 : CommSemiring.{u3} R] (i : m) (j : n), Eq.{max (succ (max u1 u2)) (succ u3)} (MvPolynomial.{max u1 u2, u3} (Prod.{u1, u2} m n) R _inst_1) (Matrix.mvPolynomialX.{u1, u2, u3} m n R _inst_1 i j) (MvPolynomial.X.{u3, max u1 u2} R (Prod.{u1, u2} m n) _inst_1 (Prod.mk.{u1, u2} m n i j))
but is expected to have type
  forall (m : Type.{u2}) (n : Type.{u1}) (R : Type.{u3}) [_inst_1 : CommSemiring.{u3} R] (i : m) (j : n), Eq.{max (max (succ u2) (succ u1)) (succ u3)} (MvPolynomial.{max u1 u2, u3} (Prod.{u2, u1} m n) R _inst_1) (Matrix.mvPolynomialX.{u2, u1, u3} m n R _inst_1 i j) (MvPolynomial.X.{u3, max u1 u2} R (Prod.{u2, u1} m n) _inst_1 (Prod.mk.{u2, u1} m n i j))
Case conversion may be inaccurate. Consider using '#align matrix.mv_polynomial_X_apply Matrix.mvPolynomialX_applyₓ'. -/
-- TODO: set as an equation lemma for `mv_polynomial_X`, see mathlib4#3024
@[simp]
theorem mvPolynomialX_apply [CommSemiring R] (i j) :
    mvPolynomialX m n R i j = MvPolynomial.X (i, j) :=
  rfl
#align matrix.mv_polynomial_X_apply Matrix.mvPolynomialX_apply

variable {m n R S}

/- warning: matrix.mv_polynomial_X_map_eval₂ -> Matrix.mvPolynomialX_map_eval₂ is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} {S : Type.{u4}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : CommSemiring.{u4} S] (f : RingHom.{u3, u4} R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u4} S (CommSemiring.toSemiring.{u4} S _inst_2))) (A : Matrix.{u1, u2, u4} m n S), Eq.{succ (max u1 u2 u4)} (Matrix.{u1, u2, u4} m n S) (Matrix.map.{max (max u1 u2) u3, u4, u1, u2} m n (MvPolynomial.{max u1 u2, u3} (Prod.{u1, u2} m n) R _inst_1) S (Matrix.mvPolynomialX.{u1, u2, u3} m n R _inst_1) (MvPolynomial.eval₂.{u3, u4, max u1 u2} R S (Prod.{u1, u2} m n) _inst_1 _inst_2 f (fun (p : Prod.{u1, u2} m n) => A (Prod.fst.{u1, u2} m n p) (Prod.snd.{u1, u2} m n p)))) A
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u4}} {S : Type.{u3}} [_inst_1 : CommSemiring.{u4} R] [_inst_2 : CommSemiring.{u3} S] (f : RingHom.{u4, u3} R S (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2))) (A : Matrix.{u2, u1, u3} m n S), Eq.{max (max (succ u2) (succ u1)) (succ u3)} (Matrix.{u2, u1, u3} m n S) (Matrix.map.{max (max u2 u1) u4, u3, u2, u1} m n (MvPolynomial.{max u1 u2, u4} (Prod.{u2, u1} m n) R _inst_1) S (Matrix.mvPolynomialX.{u2, u1, u4} m n R _inst_1) (MvPolynomial.eval₂.{u4, u3, max u2 u1} R S (Prod.{u2, u1} m n) _inst_1 _inst_2 f (fun (p : Prod.{u2, u1} m n) => A (Prod.fst.{u2, u1} m n p) (Prod.snd.{u2, u1} m n p)))) A
Case conversion may be inaccurate. Consider using '#align matrix.mv_polynomial_X_map_eval₂ Matrix.mvPolynomialX_map_eval₂ₓ'. -/
/-- Any matrix `A` can be expressed as the evaluation of `matrix.mv_polynomial_X`.

This is of particular use when `mv_polynomial (m × n) R` is an integral domain but `S` is
not, as if the `mv_polynomial.eval₂` can be pulled to the outside of a goal, it can be solved in
under cancellative assumptions. -/
theorem mvPolynomialX_map_eval₂ [CommSemiring R] [CommSemiring S] (f : R →+* S) (A : Matrix m n S) :
    (mvPolynomialX m n R).map (MvPolynomial.eval₂ f fun p : m × n => A p.1 p.2) = A :=
  ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)
#align matrix.mv_polynomial_X_map_eval₂ Matrix.mvPolynomialX_map_eval₂

/- warning: matrix.mv_polynomial_X_map_matrix_eval -> Matrix.mvPolynomialX_mapMatrix_eval is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mv_polynomial_X_map_matrix_eval Matrix.mvPolynomialX_mapMatrix_evalₓ'. -/
/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `ring_hom` on the LHS. -/
theorem mvPolynomialX_mapMatrix_eval [Fintype m] [DecidableEq m] [CommSemiring R]
    (A : Matrix m m R) :
    (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A
#align matrix.mv_polynomial_X_map_matrix_eval Matrix.mvPolynomialX_mapMatrix_eval

variable (R)

/- warning: matrix.mv_polynomial_X_map_matrix_aeval -> Matrix.mvPolynomialX_mapMatrix_aeval is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.mv_polynomial_X_map_matrix_aeval Matrix.mvPolynomialX_mapMatrix_aevalₓ'. -/
/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `alg_hom` on the LHS. -/
theorem mvPolynomialX_mapMatrix_aeval [Fintype m] [DecidableEq m] [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Matrix m m S) :
    (MvPolynomial.aeval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A
#align matrix.mv_polynomial_X_map_matrix_aeval Matrix.mvPolynomialX_mapMatrix_aeval

variable (m R)

/- warning: matrix.det_mv_polynomial_X_ne_zero -> Matrix.det_mvPolynomialX_ne_zero is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u1}) (R : Type.{u2}) [_inst_1 : DecidableEq.{succ u1} m] [_inst_2 : Fintype.{u1} m] [_inst_3 : CommRing.{u2} R] [_inst_4 : Nontrivial.{u2} R], Ne.{succ (max u1 u2)} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (Matrix.det.{max u1 u2, u1} m (fun (a : m) (b : m) => _inst_1 a b) _inst_2 (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (MvPolynomial.commRing.{u2, u1} R (Prod.{u1, u1} m m) _inst_3) (Matrix.mvPolynomialX.{u1, u1, u2} m m R (CommRing.toCommSemiring.{u2} R _inst_3))) (OfNat.ofNat.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) 0 (OfNat.mk.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) 0 (Zero.zero.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (MulZeroClass.toHasZero.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (NonAssocRing.toNonUnitalNonAssocRing.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (Ring.toNonAssocRing.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (CommRing.toRing.{max u1 u2} (MvPolynomial.{u1, u2} (Prod.{u1, u1} m m) R (CommRing.toCommSemiring.{u2} R _inst_3)) (MvPolynomial.commRing.{u2, u1} R (Prod.{u1, u1} m m) _inst_3))))))))))
but is expected to have type
  forall (m : Type.{u2}) (R : Type.{u1}) [_inst_1 : DecidableEq.{succ u2} m] [_inst_2 : Fintype.{u2} m] [_inst_3 : CommRing.{u1} R] [_inst_4 : Nontrivial.{u1} R], Ne.{succ (max u2 u1)} (MvPolynomial.{u2, u1} (Prod.{u2, u2} m m) R (CommRing.toCommSemiring.{u1} R _inst_3)) (Matrix.det.{max u2 u1, u2} m (fun (a : m) (b : m) => _inst_1 a b) _inst_2 (MvPolynomial.{u2, u1} (Prod.{u2, u2} m m) R (CommRing.toCommSemiring.{u1} R _inst_3)) (MvPolynomial.instCommRingMvPolynomialToCommSemiring.{u1, u2} R (Prod.{u2, u2} m m) _inst_3) (Matrix.mvPolynomialX.{u2, u2, u1} m m R (CommRing.toCommSemiring.{u1} R _inst_3))) (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u2, u1} (Prod.{u2, u2} m m) R (CommRing.toCommSemiring.{u1} R _inst_3)) 0 (Zero.toOfNat0.{max u2 u1} (MvPolynomial.{u2, u1} (Prod.{u2, u2} m m) R (CommRing.toCommSemiring.{u1} R _inst_3)) (CommMonoidWithZero.toZero.{max u2 u1} (MvPolynomial.{u2, u1} (Prod.{u2, u2} m m) R (CommRing.toCommSemiring.{u1} R _inst_3)) (CommSemiring.toCommMonoidWithZero.{max u2 u1} (MvPolynomial.{u2, u1} (Prod.{u2, u2} m m) R (CommRing.toCommSemiring.{u1} R _inst_3)) (CommRing.toCommSemiring.{max u2 u1} (MvPolynomial.{u2, u1} (Prod.{u2, u2} m m) R (CommRing.toCommSemiring.{u1} R _inst_3)) (MvPolynomial.instCommRingMvPolynomialToCommSemiring.{u1, u2} R (Prod.{u2, u2} m m) _inst_3))))))
Case conversion may be inaccurate. Consider using '#align matrix.det_mv_polynomial_X_ne_zero Matrix.det_mvPolynomialX_ne_zeroₓ'. -/
/-- In a nontrivial ring, `matrix.mv_polynomial_X m m R` has non-zero determinant. -/
theorem det_mvPolynomialX_ne_zero [DecidableEq m] [Fintype m] [CommRing R] [Nontrivial R] :
    det (mvPolynomialX m m R) ≠ 0 := by
  intro h_det
  have := congr_arg Matrix.det (mv_polynomial_X_map_matrix_eval (1 : Matrix m m R))
  rw [det_one, ← RingHom.map_det, h_det, RingHom.map_zero] at this
  exact zero_ne_one this
#align matrix.det_mv_polynomial_X_ne_zero Matrix.det_mvPolynomialX_ne_zero

end Matrix

