/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.matrix.charpoly.minpoly
! leanprover-community/mathlib commit 61db041ab8e4aaf8cb5c7dc10a7d4ff261997536
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.RingTheory.PowerBasis

/-!
# The minimal polynomial divides the characteristic polynomial of a matrix.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This also includes some miscellaneous results about `minpoly` on matrices.
-/


noncomputable section

universe u v w

open Polynomial Matrix

variable {R : Type u} [CommRing R]

variable {n : Type v} [DecidableEq n] [Fintype n]

variable {N : Type w} [AddCommGroup N] [Module R N]

open Finset

namespace Matrix

open Matrix

variable (M : Matrix n n R)

/- warning: matrix.minpoly_to_lin' -> Matrix.minpoly_toLin' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.minpoly_to_lin' Matrix.minpoly_toLin'ₓ'. -/
@[simp]
theorem minpoly_toLin' : minpoly R M.toLin' = minpoly R M :=
  minpoly.minpoly_algEquiv (toLinAlgEquiv' : Matrix n n R ≃ₐ[R] _) M
#align matrix.minpoly_to_lin' Matrix.minpoly_toLin'

/- warning: matrix.minpoly_to_lin -> Matrix.minpoly_toLin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix.minpoly_to_lin Matrix.minpoly_toLinₓ'. -/
@[simp]
theorem minpoly_toLin (b : Basis n R N) (M : Matrix n n R) :
    minpoly R (toLin b b M) = minpoly R M :=
  minpoly.minpoly_algEquiv (toLinAlgEquiv b : Matrix n n R ≃ₐ[R] _) M
#align matrix.minpoly_to_lin Matrix.minpoly_toLin

/- warning: matrix.is_integral -> Matrix.isIntegral is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Fintype.{u2} n] (M : Matrix.{u2, u2, u1} n n R), IsIntegral.{u1, max u2 u1} R (Matrix.{u2, u2, u1} n n R) _inst_1 (Matrix.ring.{u1, u2} n R _inst_3 (fun (a : n) (b : n) => _inst_2 a b) (CommRing.toRing.{u1} R _inst_1)) (Matrix.algebra.{u1, u2, u1} n R R _inst_3 (fun (i : n) (j : n) => _inst_2 i j) (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) M
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Fintype.{u2} n] (M : Matrix.{u2, u2, u1} n n R), IsIntegral.{u1, max u1 u2} R (Matrix.{u2, u2, u1} n n R) _inst_1 (Matrix.instRingMatrix.{u1, u2} n R _inst_3 (fun (a : n) (b : n) => _inst_2 a b) (CommRing.toRing.{u1} R _inst_1)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_3 (fun (i : n) (j : n) => _inst_2 i j) (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) M
Case conversion may be inaccurate. Consider using '#align matrix.is_integral Matrix.isIntegralₓ'. -/
theorem isIntegral : IsIntegral R M :=
  ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩
#align matrix.is_integral Matrix.isIntegral

/- warning: matrix.minpoly_dvd_charpoly -> Matrix.minpoly_dvd_charpoly is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : Fintype.{u1} n] {K : Type.{u2}} [_inst_6 : Field.{u2} K] (M : Matrix.{u1, u1, u2} n n K), Dvd.Dvd.{u2} (Polynomial.{u2} K (Ring.toSemiring.{u2} K (CommRing.toRing.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))) (semigroupDvd.{u2} (Polynomial.{u2} K (Ring.toSemiring.{u2} K (CommRing.toRing.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))) (SemigroupWithZero.toSemigroup.{u2} (Polynomial.{u2} K (Ring.toSemiring.{u2} K (CommRing.toRing.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))) (NonUnitalSemiring.toSemigroupWithZero.{u2} (Polynomial.{u2} K (Ring.toSemiring.{u2} K (CommRing.toRing.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))) (NonUnitalRing.toNonUnitalSemiring.{u2} (Polynomial.{u2} K (Ring.toSemiring.{u2} K (CommRing.toRing.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))) (NonUnitalCommRing.toNonUnitalRing.{u2} (Polynomial.{u2} K (Ring.toSemiring.{u2} K (CommRing.toRing.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))) (CommRing.toNonUnitalCommRing.{u2} (Polynomial.{u2} K (Ring.toSemiring.{u2} K (CommRing.toRing.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))) (Polynomial.commRing.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))))))) (minpoly.{u2, max u1 u2} K (Matrix.{u1, u1, u2} n n K) (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6)) (Matrix.ring.{u2, u1} n K _inst_3 (fun (a : n) (b : n) => _inst_2 a b) (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_6))) (Matrix.algebra.{u2, u1, u2} n K K _inst_3 (fun (i : n) (j : n) => _inst_2 i j) (CommRing.toCommSemiring.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_6))) (Algebra.id.{u2} K (CommRing.toCommSemiring.{u2} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6))))) M) (Matrix.charpoly.{u2, u1} K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_6)) n (fun (a : n) (b : n) => _inst_2 a b) _inst_3 M)
but is expected to have type
  forall {n : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Fintype.{u2} n] {K : Type.{u1}} [_inst_6 : Field.{u1} K] (M : Matrix.{u2, u2, u1} n n K), Dvd.dvd.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))) (semigroupDvd.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))) (SemigroupWithZero.toSemigroup.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))) (NonUnitalSemiring.toSemigroupWithZero.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))) (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))) (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))) (CommRing.toNonUnitalCommRing.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))) (Polynomial.commRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))))))) (minpoly.{u1, max u2 u1} K (Matrix.{u2, u2, u1} n n K) (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6)) (Matrix.instRingMatrix.{u1, u2} n K _inst_3 (fun (a : n) (b : n) => _inst_2 a b) (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_6))) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n K K _inst_3 (fun (i : n) (j : n) => _inst_2 i j) (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))) (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_6))) (Algebra.id.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6))))) M) (Matrix.charpoly.{u1, u2} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_6)) n (fun (a : n) (b : n) => _inst_2 a b) _inst_3 M)
Case conversion may be inaccurate. Consider using '#align matrix.minpoly_dvd_charpoly Matrix.minpoly_dvd_charpolyₓ'. -/
theorem minpoly_dvd_charpoly {K : Type _} [Field K] (M : Matrix n n K) : minpoly K M ∣ M.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly M)
#align matrix.minpoly_dvd_charpoly Matrix.minpoly_dvd_charpoly

end Matrix

namespace LinearMap

/- warning: linear_map.minpoly_to_matrix' -> LinearMap.minpoly_toMatrix' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.minpoly_to_matrix' LinearMap.minpoly_toMatrix'ₓ'. -/
@[simp]
theorem minpoly_toMatrix' (f : (n → R) →ₗ[R] n → R) : minpoly R f.toMatrix' = minpoly R f :=
  minpoly.minpoly_algEquiv (toMatrixAlgEquiv' : _ ≃ₐ[R] Matrix n n R) f
#align linear_map.minpoly_to_matrix' LinearMap.minpoly_toMatrix'

/- warning: linear_map.minpoly_to_matrix -> LinearMap.minpoly_toMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.minpoly_to_matrix LinearMap.minpoly_toMatrixₓ'. -/
@[simp]
theorem minpoly_toMatrix (b : Basis n R N) (f : N →ₗ[R] N) :
    minpoly R (toMatrix b b f) = minpoly R f :=
  minpoly.minpoly_algEquiv (toMatrixAlgEquiv b : _ ≃ₐ[R] Matrix n n R) f
#align linear_map.minpoly_to_matrix LinearMap.minpoly_toMatrix

end LinearMap

section PowerBasis

open Algebra

/- warning: charpoly_left_mul_matrix -> charpoly_leftMulMatrix is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align charpoly_left_mul_matrix charpoly_leftMulMatrixₓ'. -/
/-- The characteristic polynomial of the map `λ x, a * x` is the minimal polynomial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
theorem charpoly_leftMulMatrix {S : Type _} [Ring S] [Algebra R S] (h : PowerBasis R S) :
    (leftMulMatrix h.Basis h.gen).charpoly = minpoly R h.gen :=
  by
  cases subsingleton_or_nontrivial R; · apply Subsingleton.elim
  apply minpoly.unique' R h.gen (charpoly_monic _)
  · apply (injective_iff_map_eq_zero (left_mul_matrix _)).mp (left_mul_matrix_injective h.basis)
    rw [← Polynomial.aeval_algHom_apply, aeval_self_charpoly]
  refine' fun q hq => or_iff_not_imp_left.2 fun h0 => _
  rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at hq
  contrapose! hq; exact h.dim_le_degree_of_root h0 hq
#align charpoly_left_mul_matrix charpoly_leftMulMatrix

end PowerBasis

