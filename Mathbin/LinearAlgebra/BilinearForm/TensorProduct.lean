/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import LinearAlgebra.BilinearForm.Basic
import LinearAlgebra.TensorProduct.Basic

#align_import linear_algebra.bilinear_form.tensor_product from "leanprover-community/mathlib"@"38df578a6450a8c5142b3727e3ae894c2300cae0"

/-!
# The bilinear form on a tensor product

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `bilin_form.tensor_distrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by applying
  `B₁` on `M₁` and `B₂` on `M₂`.
* `bilin_form.tensor_distrib_equiv`: `bilin_form.tensor_distrib` as an equivalence on finite free
  modules.

-/


universe u v w

variable {ι : Type _} {R : Type _} {M₁ M₂ : Type _}

open scoped TensorProduct

namespace BilinForm

section CommSemiring

variable [CommSemiring R]

variable [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M₁] [Module R M₂]

#print LinearMap.BilinMap.tensorDistrib /-
/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products. -/
def LinearMap.BilinMap.tensorDistrib :
    BilinForm R M₁ ⊗[R] BilinForm R M₂ →ₗ[R] BilinForm R (M₁ ⊗[R] M₂) :=
  ((TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
          (TensorProduct.lift.equiv R _ _ _).symm ≪≫ₗ
        LinearMap.toBilin).toLinearMap ∘ₗ
    TensorProduct.dualDistrib R _ _ ∘ₗ
      (TensorProduct.congr (LinearMap.BilinForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _)
          (LinearMap.BilinForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _)).toLinearMap
#align bilin_form.tensor_distrib LinearMap.BilinMap.tensorDistrib
-/

@[simp]
theorem LinearMap.BilinMap.tensorDistrib_tmul (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (m₁ : M₁)
    (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) :
    LinearMap.BilinMap.tensorDistrib (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂') = B₁ m₁ m₁' * B₂ m₂ m₂' :=
  rfl
#align bilin_form.tensor_distrib_tmul LinearMap.BilinMap.tensorDistrib_tmulₓ

#print LinearMap.BilinMap.tmul /-
/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
@[reducible]
protected def LinearMap.BilinMap.tmul (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) :
    BilinForm R (M₁ ⊗[R] M₂) :=
  LinearMap.BilinMap.tensorDistrib (B₁ ⊗ₜ[R] B₂)
#align bilin_form.tmul LinearMap.BilinMap.tmul
-/

end CommSemiring

section CommRing

variable [CommRing R]

variable [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Module.Free R M₁] [Module.Finite R M₁]

variable [Module.Free R M₂] [Module.Finite R M₂]

variable [Nontrivial R]

#print LinearMap.BilinMap.tensorDistribEquiv /-
/-- `tensor_distrib` as an equivalence. -/
noncomputable def LinearMap.BilinMap.tensorDistribEquiv :
    BilinForm R M₁ ⊗[R] BilinForm R M₂ ≃ₗ[R] BilinForm R (M₁ ⊗[R] M₂) :=
  -- the same `linear_equiv`s as from `tensor_distrib`, but with the inner linear map also as an
            -- equiv
            TensorProduct.congr
            (LinearMap.BilinForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _)
            (LinearMap.BilinForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _) ≪≫ₗ
          TensorProduct.dualDistribEquiv R (M₁ ⊗ M₁) (M₂ ⊗ M₂) ≪≫ₗ
        (TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
      (TensorProduct.lift.equiv R _ _ _).symm ≪≫ₗ
    LinearMap.toBilin
#align bilin_form.tensor_distrib_equiv LinearMap.BilinMap.tensorDistribEquiv
-/

#print LinearMap.BilinMap.tensorDistribEquiv_apply /-
@[simp]
theorem LinearMap.BilinMap.tensorDistribEquiv_apply (B : BilinForm R M₁ ⊗ BilinForm R M₂) :
    LinearMap.BilinMap.tensorDistribEquiv B = LinearMap.BilinMap.tensorDistrib B :=
  rfl
#align bilin_form.tensor_distrib_equiv_apply LinearMap.BilinMap.tensorDistribEquiv_apply
-/

end CommRing

end BilinForm

