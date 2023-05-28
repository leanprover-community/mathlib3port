/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module ring_theory.polynomial_algebra
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.MatrixAlgebra
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Matrix.Basis
import Mathbin.Data.Matrix.Dmatrix

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given `[comm_ring R] [ring A] [algebra R A]`
we show `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
Combining this with the isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)` proved earlier
in `ring_theory.matrix_algebra`, we obtain the algebra isomorphism
```
def mat_poly_equiv :
  matrix n n R[X] ≃ₐ[R] (matrix n n R)[X]
```
which is characterized by
```
coeff (mat_poly_equiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/


universe u v w

open Polynomial TensorProduct

open Polynomial

open TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R A : Type _)

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

namespace polyEquivTensor

#print PolyEquivTensor.toFunBilinear /-
/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a bilinear function of two arguments.
-/
@[simps apply_apply]
def toFunBilinear : A →ₗ[A] R[X] →ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap
#align poly_equiv_tensor.to_fun_bilinear PolyEquivTensor.toFunBilinear
-/

/- warning: poly_equiv_tensor.to_fun_bilinear_apply_eq_sum -> PolyEquivTensor.toFunBilinear_apply_eq_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_bilinear_apply_eq_sum PolyEquivTensor.toFunBilinear_apply_eq_sumₓ'. -/
theorem toFunBilinear_apply_eq_sum (a : A) (p : R[X]) :
    toFunBilinear R A a p = p.Sum fun n r => monomial n (a * algebraMap R A r) :=
  by
  simp only [to_fun_bilinear_apply_apply, aeval_def, eval₂_eq_sum, Polynomial.sum, Finset.smul_sum]
  congr with i : 1
  rw [← Algebra.smul_def, ← C_mul', mul_smul_comm, C_mul_X_pow_eq_monomial, ← Algebra.commutes, ←
    Algebra.smul_def, smul_monomial]
#align poly_equiv_tensor.to_fun_bilinear_apply_eq_sum PolyEquivTensor.toFunBilinear_apply_eq_sum

/- warning: poly_equiv_tensor.to_fun_linear -> PolyEquivTensor.toFunLinear is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2], LinearMap.{u1, u1, max u2 u1, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (TensorProduct.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Polynomial.{u2} A _inst_2) (TensorProduct.addCommMonoid.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} (Polynomial.{u2} A _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (Polynomial.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} (Polynomial.{u2} A _inst_2) (Polynomial.semiring.{u2} A _inst_2)))) (TensorProduct.module.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Polynomial.module.{u2, u1} A _inst_2 R (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2], LinearMap.{u1, u1, max u1 u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (TensorProduct.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Polynomial.{u2} A _inst_2) (Algebra.TensorProduct.instAddCommMonoidTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} (Polynomial.{u2} A _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (Polynomial.{u2} A _inst_2) (Semiring.toNonAssocSemiring.{u2} (Polynomial.{u2} A _inst_2) (Polynomial.semiring.{u2} A _inst_2)))) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Polynomial.module.{u2, u1} A _inst_2 R (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_linear PolyEquivTensor.toFunLinearₓ'. -/
/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a linear map.
-/
def toFunLinear : A ⊗[R] R[X] →ₗ[R] A[X] :=
  TensorProduct.lift (toFunBilinear R A)
#align poly_equiv_tensor.to_fun_linear PolyEquivTensor.toFunLinear

/- warning: poly_equiv_tensor.to_fun_linear_tmul_apply -> PolyEquivTensor.toFunLinear_tmul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_linear_tmul_apply PolyEquivTensor.toFunLinear_tmul_applyₓ'. -/
@[simp]
theorem toFunLinear_tmul_apply (a : A) (p : R[X]) :
    toFunLinear R A (a ⊗ₜ[R] p) = toFunBilinear R A a p :=
  rfl
#align poly_equiv_tensor.to_fun_linear_tmul_apply PolyEquivTensor.toFunLinear_tmul_apply

/- warning: poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_1 -> PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_1 is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (p : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (k : Nat) (h : Decidable (Not (Eq.{succ u1} R (Polynomial.coeff.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) p k) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))))) (a : A), Eq.{succ u2} A (ite.{succ u2} A (Not (Eq.{succ u1} R (Polynomial.coeff.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) p k) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))) h (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.coeff.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) p k))) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))))))) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.coeff.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) p k)))
but is expected to have type
  forall (R : Type.{u2}) (A : Type.{u1}) [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u1} A] [_inst_3 : Algebra.{u2, u1} R A _inst_1 _inst_2] (p : Polynomial.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (k : Nat) (h : Decidable (Not (Eq.{succ u2} R (Polynomial.coeff.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1) p k) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1))))))) (a : A), Eq.{succ u1} A (ite.{succ u1} A (Not (Eq.{succ u2} R (Polynomial.coeff.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1) p k) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1)))))) h (HMul.hMul.{u1, u1, u1} A ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) (Polynomial.coeff.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1) p k)) A (instHMul.{u1} A (NonUnitalNonAssocSemiring.toMul.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2)))) a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2) (RingHom.instRingHomClassRingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2))))) (algebraMap.{u2, u1} R A _inst_1 _inst_2 _inst_3) (Polynomial.coeff.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1) p k))) (OfNat.ofNat.{u1} A 0 (Zero.toOfNat0.{u1} A (MonoidWithZero.toZero.{u1} A (Semiring.toMonoidWithZero.{u1} A _inst_2))))) (HMul.hMul.{u1, u1, u1} A ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) (Polynomial.coeff.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1) p k)) A (instHMul.{u1} A (NonUnitalNonAssocSemiring.toMul.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2)))) a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2) (RingHom.instRingHomClassRingHom.{u2, u1} R A (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} A _inst_2))))) (algebraMap.{u2, u1} R A _inst_1 _inst_2 _inst_3) (Polynomial.coeff.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1) p k)))
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_1 PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_1ₓ'. -/
-- We apparently need to provide the decidable instance here
-- in order to successfully rewrite by this lemma.
theorem toFunLinear_mul_tmul_mul_aux_1 (p : R[X]) (k : ℕ) (h : Decidable ¬p.coeff k = 0) (a : A) :
    ite (¬coeff p k = 0) (a * (algebraMap R A) (coeff p k)) 0 = a * (algebraMap R A) (coeff p k) :=
  by classical split_ifs <;> simp [*]
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_1 PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_1

/- warning: poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_2 -> PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_2 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_2 PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_2ₓ'. -/
theorem toFunLinear_mul_tmul_mul_aux_2 (k : ℕ) (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    a₁ * a₂ * (algebraMap R A) ((p₁ * p₂).coeff k) =
      (Finset.Nat.antidiagonal k).Sum fun x =>
        a₁ * (algebraMap R A) (coeff p₁ x.1) * (a₂ * (algebraMap R A) (coeff p₂ x.2)) :=
  by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  congr
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, RingHom.map_sum, RingHom.map_mul]
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_2 PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_2

/- warning: poly_equiv_tensor.to_fun_linear_mul_tmul_mul -> PolyEquivTensor.toFunLinear_mul_tmul_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul PolyEquivTensor.toFunLinear_mul_tmul_mulₓ'. -/
theorem toFunLinear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    (toFunLinear R A) ((a₁ * a₂) ⊗ₜ[R] (p₁ * p₂)) =
      (toFunLinear R A) (a₁ ⊗ₜ[R] p₁) * (toFunLinear R A) (a₂ ⊗ₜ[R] p₂) :=
  by
  classical
    simp only [to_fun_linear_tmul_apply, to_fun_bilinear_apply_eq_sum]
    ext k
    simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne.def]
    conv_rhs => rw [coeff_mul]
    simp_rw [finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne.def, mul_ite,
      MulZeroClass.mul_zero, ite_mul, MulZeroClass.zero_mul]
    simp_rw [ite_mul_zero_left (¬coeff p₁ _ = 0) (a₁ * (algebraMap R A) (coeff p₁ _))]
    simp_rw [ite_mul_zero_right (¬coeff p₂ _ = 0) _ (_ * _)]
    simp_rw [to_fun_linear_mul_tmul_mul_aux_1, to_fun_linear_mul_tmul_mul_aux_2]
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul PolyEquivTensor.toFunLinear_mul_tmul_mul

/- warning: poly_equiv_tensor.to_fun_linear_algebra_map_tmul_one -> PolyEquivTensor.toFunLinear_algebraMap_tmul_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_linear_algebra_map_tmul_one PolyEquivTensor.toFunLinear_algebraMap_tmul_oneₓ'. -/
theorem toFunLinear_algebraMap_tmul_one (r : R) :
    (toFunLinear R A) ((algebraMap R A) r ⊗ₜ[R] 1) = (algebraMap R A[X]) r := by
  rw [to_fun_linear_tmul_apply, to_fun_bilinear_apply_apply, Polynomial.aeval_one, algebraMap_smul,
    Algebra.algebraMap_eq_smul_one]
#align poly_equiv_tensor.to_fun_linear_algebra_map_tmul_one PolyEquivTensor.toFunLinear_algebraMap_tmul_one

/- warning: poly_equiv_tensor.to_fun_alg_hom -> PolyEquivTensor.toFunAlgHom is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2], AlgHom.{u1, max u2 u1, u2} R (TensorProduct.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Polynomial.{u2} A _inst_2) _inst_1 (Algebra.TensorProduct.TensorProduct.semiring.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Polynomial.semiring.{u2} A _inst_2) (Algebra.TensorProduct.TensorProduct.algebra.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Polynomial.algebraOfAlgebra.{u1, u2} R A _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2], AlgHom.{u1, max u1 u2, u2} R (TensorProduct.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Polynomial.{u2} A _inst_2) _inst_1 (Algebra.TensorProduct.instSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Polynomial.semiring.{u2} A _inst_2) (Algebra.TensorProduct.instAlgebraTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModuleInstSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Polynomial.algebraOfAlgebra.{u1, u2} R A _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_alg_hom PolyEquivTensor.toFunAlgHomₓ'. -/
/-- (Implementation detail).
The algebra homomorphism `A ⊗[R] R[X] →ₐ[R] A[X]`.
-/
def toFunAlgHom : A ⊗[R] R[X] →ₐ[R] A[X] :=
  algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_algebraMap_tmul_one R A)
#align poly_equiv_tensor.to_fun_alg_hom PolyEquivTensor.toFunAlgHom

/- warning: poly_equiv_tensor.to_fun_alg_hom_apply_tmul -> PolyEquivTensor.toFunAlgHom_apply_tmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.to_fun_alg_hom_apply_tmul PolyEquivTensor.toFunAlgHom_apply_tmulₓ'. -/
@[simp]
theorem toFunAlgHom_apply_tmul (a : A) (p : R[X]) :
    toFunAlgHom R A (a ⊗ₜ[R] p) = p.Sum fun n r => monomial n (a * (algebraMap R A) r) :=
  toFunBilinear_apply_eq_sum R A _ _
#align poly_equiv_tensor.to_fun_alg_hom_apply_tmul PolyEquivTensor.toFunAlgHom_apply_tmul

#print PolyEquivTensor.invFun /-
/-- (Implementation detail.)

The bare function `A[X] → A ⊗[R] R[X]`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def invFun (p : A[X]) : A ⊗[R] R[X] :=
  p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X]))
#align poly_equiv_tensor.inv_fun PolyEquivTensor.invFun
-/

/- warning: poly_equiv_tensor.inv_fun_add -> PolyEquivTensor.invFun_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.inv_fun_add PolyEquivTensor.invFun_addₓ'. -/
@[simp]
theorem invFun_add {p q} : invFun R A (p + q) = invFun R A p + invFun R A q := by
  simp only [inv_fun, eval₂_add]
#align poly_equiv_tensor.inv_fun_add PolyEquivTensor.invFun_add

/- warning: poly_equiv_tensor.inv_fun_monomial -> PolyEquivTensor.invFun_monomial is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.inv_fun_monomial PolyEquivTensor.invFun_monomialₓ'. -/
theorem invFun_monomial (n : ℕ) (a : A) :
    invFun R A (monomial n a) = includeLeft a * (1 : A) ⊗ₜ[R] (X : R[X]) ^ n :=
  eval₂_monomial _ _
#align poly_equiv_tensor.inv_fun_monomial PolyEquivTensor.invFun_monomial

/- warning: poly_equiv_tensor.left_inv -> PolyEquivTensor.left_inv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor.left_inv PolyEquivTensor.left_invₓ'. -/
theorem left_inv (x : A ⊗ R[X]) : invFun R A ((toFunAlgHom R A) x) = x :=
  by
  apply TensorProduct.induction_on x
  · simp [inv_fun]
  · intro a p
    dsimp only [inv_fun]
    rw [to_fun_alg_hom_apply_tmul, eval₂_sum]
    simp_rw [eval₂_monomial, AlgHom.coe_toRingHom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, ← Algebra.commutes, ← Algebra.smul_def, smul_tmul, sum_def, ← tmul_sum]
    conv_rhs => rw [← sum_C_mul_X_pow_eq p]
    simp only [Algebra.smul_def]
    rfl
  · intro p q hp hq
    simp only [AlgHom.map_add, inv_fun_add, hp, hq]
#align poly_equiv_tensor.left_inv PolyEquivTensor.left_inv

#print PolyEquivTensor.right_inv /-
theorem right_inv (x : A[X]) : (toFunAlgHom R A) (invFun R A x) = x :=
  by
  apply Polynomial.induction_on' x
  · intro p q hp hq
    simp only [inv_fun_add, AlgHom.map_add, hp, hq]
  · intro n a
    rw [inv_fun_monomial, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_pow,
        one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, to_fun_alg_hom_apply_tmul,
        X_pow_eq_monomial, sum_monomial_index] <;>
      simp
#align poly_equiv_tensor.right_inv PolyEquivTensor.right_inv
-/

#print PolyEquivTensor.equiv /-
/-- (Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] R[X]) ≃ A[X]`.
-/
def equiv : A ⊗[R] R[X] ≃ A[X] where
  toFun := toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A
#align poly_equiv_tensor.equiv PolyEquivTensor.equiv
-/

end polyEquivTensor

open polyEquivTensor

/- warning: poly_equiv_tensor -> polyEquivTensor is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2], AlgEquiv.{u1, u2, max u2 u1} R (Polynomial.{u2} A _inst_2) (TensorProduct.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) _inst_1 (Polynomial.semiring.{u2} A _inst_2) (Algebra.TensorProduct.TensorProduct.semiring.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Polynomial.algebraOfAlgebra.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.TensorProduct.TensorProduct.algebra.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2], AlgEquiv.{u1, u2, max u1 u2} R (Polynomial.{u2} A _inst_2) (TensorProduct.{u1, u2, u1} R _inst_1 A (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Polynomial.module.{u1, u1} R (CommSemiring.toSemiring.{u1} R _inst_1) R (CommSemiring.toSemiring.{u1} R _inst_1) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) _inst_1 (Polynomial.semiring.{u2} A _inst_2) (Algebra.TensorProduct.instSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1))) (Polynomial.algebraOfAlgebra.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.TensorProduct.instAlgebraTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModuleInstSemiringTensorProductToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonAssocSemiringToModuleToModule.{u1, u2, u1} R _inst_1 A _inst_2 _inst_3 (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor polyEquivTensorₓ'. -/
/-- The `R`-algebra isomorphism `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/
def polyEquivTensor : A[X] ≃ₐ[R] A ⊗[R] R[X] :=
  AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }
#align poly_equiv_tensor polyEquivTensor

/- warning: poly_equiv_tensor_apply -> polyEquivTensor_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor_apply polyEquivTensor_applyₓ'. -/
@[simp]
theorem polyEquivTensor_apply (p : A[X]) :
    polyEquivTensor R A p =
      p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X])) :=
  rfl
#align poly_equiv_tensor_apply polyEquivTensor_apply

/- warning: poly_equiv_tensor_symm_apply_tmul -> polyEquivTensor_symm_apply_tmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align poly_equiv_tensor_symm_apply_tmul polyEquivTensor_symm_apply_tmulₓ'. -/
@[simp]
theorem polyEquivTensor_symm_apply_tmul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a ⊗ₜ p) = p.Sum fun n r => monomial n (a * algebraMap R A r) :=
  toFunAlgHom_apply_tmul _ _ _ _
#align poly_equiv_tensor_symm_apply_tmul polyEquivTensor_symm_apply_tmul

open DMatrix Matrix

open BigOperators

variable {R}

variable {n : Type w} [DecidableEq n] [Fintype n]

/- warning: mat_poly_equiv -> matPolyEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {n : Type.{u1}} [_inst_4 : DecidableEq.{succ u1} n] [_inst_5 : Fintype.{u1} n], AlgEquiv.{u2, max u1 u2, max u1 u2} R (Matrix.{u1, u1, u2} n n (Polynomial.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Polynomial.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b))) _inst_1 (Matrix.semiring.{u2, u1} n (Polynomial.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Polynomial.semiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Polynomial.semiring.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b))) (Matrix.algebra.{u2, u1, u2} n R (Polynomial.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (Polynomial.semiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Polynomial.algebraOfAlgebra.{u2, u2} R R _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1))) (Polynomial.algebraOfAlgebra.{u2, max u1 u2} R (Matrix.{u1, u1, u2} n n R) _inst_1 (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Matrix.algebra.{u2, u1, u2} n R R _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {n : Type.{u1}} [_inst_4 : DecidableEq.{succ u1} n] [_inst_5 : Fintype.{u1} n], AlgEquiv.{u2, max u2 u1, max u2 u1} R (Matrix.{u1, u1, u2} n n (Polynomial.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Polynomial.{max u2 u1} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b))) _inst_1 (Matrix.semiring.{u2, u1} n (Polynomial.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Polynomial.semiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Polynomial.semiring.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b))) (Matrix.instAlgebraMatrixSemiring.{u2, u1, u2} n R (Polynomial.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (Polynomial.semiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Polynomial.algebraOfAlgebra.{u2, u2} R R _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1))) (Polynomial.algebraOfAlgebra.{u2, max u1 u2} R (Matrix.{u1, u1, u2} n n R) _inst_1 (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_1) _inst_5 (fun (a : n) (b : n) => _inst_4 a b)) (Matrix.instAlgebraMatrixSemiring.{u2, u1, u2} n R R _inst_5 (fun (a : n) (b : n) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align mat_poly_equiv matPolyEquivₓ'. -/
/--
The algebra isomorphism stating "matrices of polynomials are the same as polynomials of matrices".

(You probably shouldn't attempt to use this underlying definition ---
it's an algebra equivalence, and characterised extensionally by the lemma
`mat_poly_equiv_coeff_apply` below.)
-/
noncomputable def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X] :=
  ((matrixEquivTensor R R[X] n).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm
#align mat_poly_equiv matPolyEquiv

open Finset

/- warning: mat_poly_equiv_coeff_apply_aux_1 -> matPolyEquiv_coeff_apply_aux_1 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mat_poly_equiv_coeff_apply_aux_1 matPolyEquiv_coeff_apply_aux_1ₓ'. -/
theorem matPolyEquiv_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
    matPolyEquiv (stdBasisMatrix i j <| monomial k x) = monomial k (stdBasisMatrix i j x) :=
  by
  simp only [matPolyEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply_std_basis]
  apply (polyEquivTensor R (Matrix n n R)).Injective
  simp only [AlgEquiv.apply_symm_apply]
  convert Algebra.TensorProduct.comm_tmul _ _ _ _ _
  simp only [polyEquivTensor_apply]
  convert eval₂_monomial _ _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul, Matrix.mul_one,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.includeLeft_apply, mul_eq_mul]
  rw [← smul_X_eq_monomial, ← TensorProduct.smul_tmul]
  congr with (i' j') <;> simp
#align mat_poly_equiv_coeff_apply_aux_1 matPolyEquiv_coeff_apply_aux_1

/- warning: mat_poly_equiv_coeff_apply_aux_2 -> matPolyEquiv_coeff_apply_aux_2 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mat_poly_equiv_coeff_apply_aux_2 matPolyEquiv_coeff_apply_aux_2ₓ'. -/
theorem matPolyEquiv_coeff_apply_aux_2 (i j : n) (p : R[X]) (k : ℕ) :
    coeff (matPolyEquiv (stdBasisMatrix i j p)) k = stdBasisMatrix i j (coeff p k) :=
  by
  apply Polynomial.induction_on' p
  · intro p q hp hq
    ext
    simp [hp, hq, coeff_add, add_apply, std_basis_matrix_add]
  · intro k x
    simp only [matPolyEquiv_coeff_apply_aux_1, coeff_monomial]
    split_ifs <;>
      · funext
        simp
#align mat_poly_equiv_coeff_apply_aux_2 matPolyEquiv_coeff_apply_aux_2

/- warning: mat_poly_equiv_coeff_apply -> matPolyEquiv_coeff_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mat_poly_equiv_coeff_apply matPolyEquiv_coeff_applyₓ'. -/
@[simp]
theorem matPolyEquiv_coeff_apply (m : Matrix n n R[X]) (k : ℕ) (i j : n) :
    coeff (matPolyEquiv m) k i j = coeff (m i j) k :=
  by
  apply Matrix.induction_on' m
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro i' j' x
    erw [matPolyEquiv_coeff_apply_aux_2]
    dsimp [std_basis_matrix]
    split_ifs
    · rcases h with ⟨rfl, rfl⟩
      simp [std_basis_matrix]
    · simp [std_basis_matrix, h]
#align mat_poly_equiv_coeff_apply matPolyEquiv_coeff_apply

/- warning: mat_poly_equiv_symm_apply_coeff -> matPolyEquiv_symm_apply_coeff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mat_poly_equiv_symm_apply_coeff matPolyEquiv_symm_apply_coeffₓ'. -/
@[simp]
theorem matPolyEquiv_symm_apply_coeff (p : (Matrix n n R)[X]) (i j : n) (k : ℕ) :
    coeff (matPolyEquiv.symm p i j) k = coeff p k i j :=
  by
  have t : p = matPolyEquiv (mat_poly_equiv.symm p) := by simp
  conv_rhs => rw [t]
  simp only [matPolyEquiv_coeff_apply]
#align mat_poly_equiv_symm_apply_coeff matPolyEquiv_symm_apply_coeff

/- warning: mat_poly_equiv_smul_one -> matPolyEquiv_smul_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mat_poly_equiv_smul_one matPolyEquiv_smul_oneₓ'. -/
theorem matPolyEquiv_smul_one (p : R[X]) :
    matPolyEquiv (p • 1) = p.map (algebraMap R (Matrix n n R)) :=
  by
  ext (m i j)
  simp only [coeff_map, one_apply, algebra_map_matrix_apply, mul_boole, Pi.smul_apply,
    matPolyEquiv_coeff_apply]
  split_ifs <;> simp
#align mat_poly_equiv_smul_one matPolyEquiv_smul_one

/- warning: support_subset_support_mat_poly_equiv -> support_subset_support_matPolyEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align support_subset_support_mat_poly_equiv support_subset_support_matPolyEquivₓ'. -/
theorem support_subset_support_matPolyEquiv (m : Matrix n n R[X]) (i j : n) :
    support (m i j) ⊆ support (matPolyEquiv m) :=
  by
  intro k
  contrapose
  simp only [not_mem_support_iff]
  intro hk
  rw [← matPolyEquiv_coeff_apply, hk]
  rfl
#align support_subset_support_mat_poly_equiv support_subset_support_matPolyEquiv

