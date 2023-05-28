/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

! This file was ported from Lean 3 source module linear_algebra.tensor_product_basis
! leanprover-community/mathlib commit f784cc6142443d9ee623a20788c282112c322081
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.DirectSum.Finsupp
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!
# Bases and dimensionality of tensor products of modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These can not go into `linear_algebra.tensor_product` since they depend on
`linear_algebra.finsupp_vector_space` which in turn imports `linear_algebra.tensor_product`.

-/


noncomputable section

open Set LinearMap Submodule

section CommRing

variable {R : Type _} {M : Type _} {N : Type _} {ι : Type _} {κ : Type _}

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/- warning: basis.tensor_product -> Basis.tensorProduct is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} {ι : Type.{u4}} {κ : Type.{u5}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : AddCommGroup.{u3} N] [_inst_5 : Module.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4)], (Basis.{u4, u1, u2} ι R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) -> (Basis.{u5, u1, u3} κ R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4) _inst_5) -> (Basis.{max u4 u5, u1, max u2 u3} (Prod.{u4, u5} ι κ) R (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4) _inst_3 _inst_5) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (TensorProduct.addCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4) _inst_3 _inst_5) (TensorProduct.module.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4) _inst_3 _inst_5))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} {ι : Type.{u4}} {κ : Type.{u5}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : AddCommGroup.{u3} N] [_inst_5 : Module.{u1, u3} R N (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4)], (Basis.{u4, u1, u2} ι R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) -> (Basis.{u5, u1, u3} κ R N (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4) _inst_5) -> (Basis.{max u5 u4, u1, max u3 u2} (Prod.{u4, u5} ι κ) R (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4) _inst_3 _inst_5) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (TensorProduct.addCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4) _inst_3 _inst_5) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_4) _inst_3 _inst_5))
Case conversion may be inaccurate. Consider using '#align basis.tensor_product Basis.tensorProductₓ'. -/
/-- If b : ι → M and c : κ → N are bases then so is λ i, b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N. -/
def Basis.tensorProduct (b : Basis ι R M) (c : Basis κ R N) :
    Basis (ι × κ) R (TensorProduct R M N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.congr b.repr c.repr).trans <|
        (finsuppTensorFinsupp R _ _ _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.lid R R)).symm
#align basis.tensor_product Basis.tensorProduct

/- warning: basis.tensor_product_apply -> Basis.tensorProduct_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.tensor_product_apply Basis.tensorProduct_applyₓ'. -/
@[simp]
theorem Basis.tensorProduct_apply (b : Basis ι R M) (c : Basis κ R N) (i : ι) (j : κ) :
    Basis.tensorProduct b c (i, j) = b i ⊗ₜ c j := by simp [Basis.tensorProduct]
#align basis.tensor_product_apply Basis.tensorProduct_apply

/- warning: basis.tensor_product_apply' -> Basis.tensorProduct_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.tensor_product_apply' Basis.tensorProduct_apply'ₓ'. -/
theorem Basis.tensorProduct_apply' (b : Basis ι R M) (c : Basis κ R N) (i : ι × κ) :
    Basis.tensorProduct b c i = b i.1 ⊗ₜ c i.2 := by simp [Basis.tensorProduct]
#align basis.tensor_product_apply' Basis.tensorProduct_apply'

/- warning: basis.tensor_product_repr_tmul_apply -> Basis.tensorProduct_repr_tmul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.tensor_product_repr_tmul_apply Basis.tensorProduct_repr_tmul_applyₓ'. -/
@[simp]
theorem Basis.tensorProduct_repr_tmul_apply (b : Basis ι R M) (c : Basis κ R N) (m : M) (n : N)
    (i : ι) (j : κ) : (Basis.tensorProduct b c).repr (m ⊗ₜ n) (i, j) = b.repr m i * c.repr n j := by
  simp [Basis.tensorProduct]
#align basis.tensor_product_repr_tmul_apply Basis.tensorProduct_repr_tmul_apply

end CommRing

