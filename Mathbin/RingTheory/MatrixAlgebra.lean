/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Eric Wieser

! This file was ported from Lean 3 source module ring_theory.matrix_algebra
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basis
import Mathbin.RingTheory.TensorProduct

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/


universe u v w

open TensorProduct

open BigOperators

open TensorProduct

open Algebra.TensorProduct

open Matrix

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [Semiring A] [Algebra R A]

variable {n : Type w}

variable (R A n)

namespace matrixEquivTensor

#print MatrixEquivTensor.toFunBilinear /-
/-- (Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-bilinear map.
-/
def toFunBilinear : A →ₗ[R] Matrix n n R →ₗ[R] Matrix n n A :=
  (Algebra.lsmul R (Matrix n n A)).toLinearMap.compl₂ (Algebra.linearMap R A).mapMatrix
#align matrix_equiv_tensor.to_fun_bilinear MatrixEquivTensor.toFunBilinear
-/

/- warning: matrix_equiv_tensor.to_fun_bilinear_apply -> MatrixEquivTensor.toFunBilinear_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor.to_fun_bilinear_apply MatrixEquivTensor.toFunBilinear_applyₓ'. -/
@[simp]
theorem toFunBilinear_apply (a : A) (m : Matrix n n R) :
    toFunBilinear R A n a m = a • m.map (algebraMap R A) :=
  rfl
#align matrix_equiv_tensor.to_fun_bilinear_apply MatrixEquivTensor.toFunBilinear_apply

/- warning: matrix_equiv_tensor.to_fun_linear -> MatrixEquivTensor.toFunLinear is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (n : Type.{u3}), LinearMap.{u1, u1, max u2 u3 u1, max u3 u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (TensorProduct.{u1, u2, max u3 u1} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.{u3, u3, u2} n n A) (TensorProduct.addCommMonoid.{u1, u2, max u3 u1} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.addCommMonoid.{u2, u3, u3} n n A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (TensorProduct.module.{u1, u2, max u3 u1} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.module.{u2, u3, u3, u1} n n R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (n : Type.{u3}), LinearMap.{u1, u1, max (max u1 u3) u2, max u2 u3} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (TensorProduct.{u1, u2, max u1 u3} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.{u3, u3, u2} n n A) (TensorProduct.addCommMonoid.{u1, u2, max u1 u3} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.addCommMonoid.{u2, u3, u3} n n A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u1, u2, max u1 u3} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.module.{u2, u3, u3, u1} n n R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor.to_fun_linear MatrixEquivTensor.toFunLinearₓ'. -/
/-- (Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-linear map.
-/
def toFunLinear : A ⊗[R] Matrix n n R →ₗ[R] Matrix n n A :=
  TensorProduct.lift (toFunBilinear R A n)
#align matrix_equiv_tensor.to_fun_linear MatrixEquivTensor.toFunLinear

variable [DecidableEq n] [Fintype n]

/- warning: matrix_equiv_tensor.to_fun_alg_hom -> MatrixEquivTensor.toFunAlgHom is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (n : Type.{u3}) [_inst_4 : DecidableEq.{succ u3} n] [_inst_5 : Fintype.{u3} n], AlgHom.{u1, max u2 u3 u1, max u3 u2} R (TensorProduct.{u1, u2, max u3 u1} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.{u3, u3, u2} n n A) _inst_1 (Algebra.TensorProduct.TensorProduct.semiring.{u1, u2, max u3 u1} R _inst_1 A _inst_2 _inst_3 (Matrix.{u3, u3, u1} n n R) (Matrix.semiring.{u1, u3} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Matrix.algebra.{u1, u3, u1} n R R _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Matrix.semiring.{u2, u3} n A _inst_2 _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Algebra.TensorProduct.TensorProduct.algebra.{u1, u2, max u3 u1} R _inst_1 A _inst_2 _inst_3 (Matrix.{u3, u3, u1} n n R) (Matrix.semiring.{u1, u3} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Matrix.algebra.{u1, u3, u1} n R R _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Matrix.algebra.{u2, u3, u1} n R A _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (n : Type.{u3}) [_inst_4 : DecidableEq.{succ u3} n] [_inst_5 : Fintype.{u3} n], AlgHom.{u1, max (max u1 u3) u2, max u2 u3} R (TensorProduct.{u1, u2, max u1 u3} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Matrix.{u3, u3, u2} n n A) _inst_1 (Algebra.TensorProduct.instSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, max u1 u3} R _inst_1 A _inst_2 _inst_3 (Matrix.{u3, u3, u1} n n R) (Matrix.semiring.{u1, u3} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u3, u1} n R R _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Matrix.semiring.{u2, u3} n A _inst_2 _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Algebra.TensorProduct.instAlgebraTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModuleInstSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, max u1 u3} R _inst_1 A _inst_2 _inst_3 (Matrix.{u3, u3, u1} n n R) (Matrix.semiring.{u1, u3} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u3, u1} n R R _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Matrix.instAlgebraMatrixSemiring.{u2, u3, u1} n R A _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor.to_fun_alg_hom MatrixEquivTensor.toFunAlgHomₓ'. -/
/-- The function `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`, as an algebra homomorphism.
-/
def toFunAlgHom : A ⊗[R] Matrix n n R →ₐ[R] Matrix n n A :=
  algHomOfLinearMapTensorProduct (toFunLinear R A n)
    (by
      intros
      simp_rw [to_fun_linear, lift.tmul, to_fun_bilinear_apply, mul_eq_mul, Matrix.map_mul]
      ext
      dsimp
      simp_rw [Matrix.mul_apply, Pi.smul_apply, Matrix.map_apply, smul_eq_mul, Finset.mul_sum,
        _root_.mul_assoc, Algebra.left_comm])
    (by
      intros
      simp_rw [to_fun_linear, lift.tmul, to_fun_bilinear_apply,
        Matrix.map_one (algebraMap R A) (map_zero _) (map_one _), algebraMap_smul,
        Algebra.algebraMap_eq_smul_one])
#align matrix_equiv_tensor.to_fun_alg_hom MatrixEquivTensor.toFunAlgHom

#print MatrixEquivTensor.toFunAlgHom_apply /-
@[simp]
theorem toFunAlgHom_apply (a : A) (m : Matrix n n R) :
    toFunAlgHom R A n (a ⊗ₜ m) = a • m.map (algebraMap R A) := by
  simp [to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear]
#align matrix_equiv_tensor.to_fun_alg_hom_apply MatrixEquivTensor.toFunAlgHom_apply
-/

#print MatrixEquivTensor.invFun /-
/-- (Implementation detail.)

The bare function `matrix n n A → A ⊗[R] matrix n n R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def invFun (M : Matrix n n A) : A ⊗[R] Matrix n n R :=
  ∑ p : n × n, M p.1 p.2 ⊗ₜ stdBasisMatrix p.1 p.2 1
#align matrix_equiv_tensor.inv_fun MatrixEquivTensor.invFun
-/

/- warning: matrix_equiv_tensor.inv_fun_zero -> MatrixEquivTensor.invFun_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor.inv_fun_zero MatrixEquivTensor.invFun_zeroₓ'. -/
@[simp]
theorem invFun_zero : invFun R A n 0 = 0 := by simp [inv_fun]
#align matrix_equiv_tensor.inv_fun_zero MatrixEquivTensor.invFun_zero

/- warning: matrix_equiv_tensor.inv_fun_add -> MatrixEquivTensor.invFun_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor.inv_fun_add MatrixEquivTensor.invFun_addₓ'. -/
@[simp]
theorem invFun_add (M N : Matrix n n A) : invFun R A n (M + N) = invFun R A n M + invFun R A n N :=
  by simp [inv_fun, add_tmul, Finset.sum_add_distrib]
#align matrix_equiv_tensor.inv_fun_add MatrixEquivTensor.invFun_add

/- warning: matrix_equiv_tensor.inv_fun_smul -> MatrixEquivTensor.invFun_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor.inv_fun_smul MatrixEquivTensor.invFun_smulₓ'. -/
@[simp]
theorem invFun_smul (a : A) (M : Matrix n n A) : invFun R A n (a • M) = a ⊗ₜ 1 * invFun R A n M :=
  by simp [inv_fun, Finset.mul_sum]
#align matrix_equiv_tensor.inv_fun_smul MatrixEquivTensor.invFun_smul

/- warning: matrix_equiv_tensor.inv_fun_algebra_map -> MatrixEquivTensor.invFun_algebraMap is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (n : Type.{u3}) [_inst_4 : DecidableEq.{succ u3} n] [_inst_5 : Fintype.{u3} n] (M : Matrix.{u3, u3, u1} n n R), Eq.{succ (max u2 u3 u1)} (TensorProduct.{u1, u2, max u3 u1} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MatrixEquivTensor.invFun.{u1, u2, u3} R _inst_1 A _inst_2 _inst_3 n (fun (a : n) (b : n) => _inst_4 a b) _inst_5 (Matrix.map.{u1, u2, u3, u3} n n R A M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3)))) (TensorProduct.tmul.{u1, u2, max u3 u1} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (OfNat.ofNat.{u2} A 1 (OfNat.mk.{u2} A 1 (One.one.{u2} A (AddMonoidWithOne.toOne.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))))) M)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (n : Type.{u3}) [_inst_4 : DecidableEq.{succ u3} n] [_inst_5 : Fintype.{u3} n] (M : Matrix.{u3, u3, u1} n n R), Eq.{max (max (succ u1) (succ u2)) (succ u3)} (TensorProduct.{u1, u2, max u1 u3} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MatrixEquivTensor.invFun.{u1, u2, u3} R _inst_1 A _inst_2 _inst_3 n (fun (a : n) (b : n) => _inst_4 a b) _inst_5 (Matrix.map.{u1, u2, u3, u3} n n R A M (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3)))) (TensorProduct.tmul.{u1, u2, max u1 u3} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (OfNat.ofNat.{u2} A 1 (One.toOfNat1.{u2} A (Semiring.toOne.{u2} A _inst_2))) M)
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor.inv_fun_algebra_map MatrixEquivTensor.invFun_algebraMapₓ'. -/
@[simp]
theorem invFun_algebraMap (M : Matrix n n R) : invFun R A n (M.map (algebraMap R A)) = 1 ⊗ₜ M :=
  by
  dsimp [inv_fun]
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_sum, mul_boole]
  congr
  conv_rhs => rw [matrix_eq_sum_std_basis M]
  convert Finset.sum_product; simp
#align matrix_equiv_tensor.inv_fun_algebra_map MatrixEquivTensor.invFun_algebraMap

#print MatrixEquivTensor.right_inv /-
theorem right_inv (M : Matrix n n A) : (toFunAlgHom R A n) (invFun R A n M) = M :=
  by
  simp only [inv_fun, AlgHom.map_sum, std_basis_matrix, apply_ite ⇑(algebraMap R A), smul_eq_mul,
    mul_boole, to_fun_alg_hom_apply, RingHom.map_zero, RingHom.map_one, Matrix.map_apply,
    Pi.smul_def]
  convert Finset.sum_product; apply matrix_eq_sum_std_basis
#align matrix_equiv_tensor.right_inv MatrixEquivTensor.right_inv
-/

#print MatrixEquivTensor.left_inv /-
theorem left_inv (M : A ⊗[R] Matrix n n R) : invFun R A n (toFunAlgHom R A n M) = M :=
  by
  induction' M using TensorProduct.induction_on with a m x y hx hy
  · simp
  · simp
  · simp [AlgHom.map_sum, hx, hy]
#align matrix_equiv_tensor.left_inv MatrixEquivTensor.left_inv
-/

#print MatrixEquivTensor.equiv /-
/-- (Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] matrix n n R) ≃ matrix n n A`.
-/
def equiv : A ⊗[R] Matrix n n R ≃ Matrix n n A
    where
  toFun := toFunAlgHom R A n
  invFun := invFun R A n
  left_inv := left_inv R A n
  right_inv := right_inv R A n
#align matrix_equiv_tensor.equiv MatrixEquivTensor.equiv
-/

end matrixEquivTensor

variable [Fintype n] [DecidableEq n]

/- warning: matrix_equiv_tensor -> matrixEquivTensor is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (n : Type.{u3}) [_inst_4 : Fintype.{u3} n] [_inst_5 : DecidableEq.{succ u3} n], AlgEquiv.{u1, max u3 u2, max u2 u3 u1} R (Matrix.{u3, u3, u2} n n A) (TensorProduct.{u1, u2, max u3 u1} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) _inst_1 (Matrix.semiring.{u2, u3} n A _inst_2 _inst_4 (fun (a : n) (b : n) => _inst_5 a b)) (Algebra.TensorProduct.TensorProduct.semiring.{u1, u2, max u3 u1} R _inst_1 A _inst_2 _inst_3 (Matrix.{u3, u3, u1} n n R) (Matrix.semiring.{u1, u3} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.algebra.{u1, u3, u1} n R R _inst_4 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Matrix.algebra.{u2, u3, u1} n R A _inst_4 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 _inst_2 _inst_3) (Algebra.TensorProduct.TensorProduct.algebra.{u1, u2, max u3 u1} R _inst_1 A _inst_2 _inst_3 (Matrix.{u3, u3, u1} n n R) (Matrix.semiring.{u1, u3} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.algebra.{u1, u3, u1} n R R _inst_4 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (n : Type.{u3}) [_inst_4 : Fintype.{u3} n] [_inst_5 : DecidableEq.{succ u3} n], AlgEquiv.{u1, max u2 u3, max (max u1 u3) u2} R (Matrix.{u3, u3, u2} n n A) (TensorProduct.{u1, u2, max u1 u3} R _inst_1 A (Matrix.{u3, u3, u1} n n R) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Matrix.addCommMonoid.{u1, u3, u3} n n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u3, u1} n n R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) _inst_1 (Matrix.semiring.{u2, u3} n A _inst_2 _inst_4 (fun (a : n) (b : n) => _inst_5 a b)) (Algebra.TensorProduct.instSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, max u1 u3} R _inst_1 A _inst_2 _inst_3 (Matrix.{u3, u3, u1} n n R) (Matrix.semiring.{u1, u3} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u3, u1} n R R _inst_4 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Matrix.instAlgebraMatrixSemiring.{u2, u3, u1} n R A _inst_4 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 _inst_2 _inst_3) (Algebra.TensorProduct.instAlgebraTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModuleInstSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, max u1 u3} R _inst_1 A _inst_2 _inst_3 (Matrix.{u3, u3, u1} n n R) (Matrix.semiring.{u1, u3} n R (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 (fun (a : n) (b : n) => _inst_5 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u3, u1} n R R _inst_4 (fun (a : n) (b : n) => _inst_5 a b) _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor matrixEquivTensorₓ'. -/
/-- The `R`-algebra isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom R A n, MatrixEquivTensor.equiv R A n with }
#align matrix_equiv_tensor matrixEquivTensor

open matrixEquivTensor

/- warning: matrix_equiv_tensor_apply -> matrixEquivTensor_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor_apply matrixEquivTensor_applyₓ'. -/
@[simp]
theorem matrixEquivTensor_apply (M : Matrix n n A) :
    matrixEquivTensor R A n M = ∑ p : n × n, M p.1 p.2 ⊗ₜ stdBasisMatrix p.1 p.2 1 :=
  rfl
#align matrix_equiv_tensor_apply matrixEquivTensor_apply

/- warning: matrix_equiv_tensor_apply_std_basis -> matrixEquivTensor_apply_std_basis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor_apply_std_basis matrixEquivTensor_apply_std_basisₓ'. -/
@[simp]
theorem matrixEquivTensor_apply_std_basis (i j : n) (x : A) :
    matrixEquivTensor R A n (stdBasisMatrix i j x) = x ⊗ₜ stdBasisMatrix i j 1 :=
  by
  have t : ∀ p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by tidy
  simp [ite_tmul, t, std_basis_matrix]
#align matrix_equiv_tensor_apply_std_basis matrixEquivTensor_apply_std_basis

/- warning: matrix_equiv_tensor_apply_symm -> matrixEquivTensor_apply_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align matrix_equiv_tensor_apply_symm matrixEquivTensor_apply_symmₓ'. -/
@[simp]
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor R A n).symm (a ⊗ₜ M) = M.map fun x => a * algebraMap R A x :=
  by
  simp [matrixEquivTensor, to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear]
  rfl
#align matrix_equiv_tensor_apply_symm matrixEquivTensor_apply_symm

