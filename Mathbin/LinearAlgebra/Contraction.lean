/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.LinearAlgebra.Dual

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/


universe u v

section Contraction

open TensorProduct

open_locale TensorProduct

variable (R : Type u) (M N : Type v)

variable [CommRingₓ R] [AddCommGroupₓ M] [AddCommGroupₓ N] [Module R M] [Module R N]

/-- The natural left-handed pairing between a module and its dual. -/
def contractLeft : Module.Dual R M ⊗ M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun LinearMap.id

/-- The natural right-handed pairing between a module and its dual. -/
def contractRight : M ⊗ Module.Dual R M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

/-- The natural map associating a linear map to the tensor product of two modules. -/
def dualTensorHom : Module.Dual R M ⊗ N →ₗ[R] M →ₗ[R] N :=
  let M' := Module.Dual R M
  (uncurry R M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) LinearMap.smulRightₗ

variable {R M N}

@[simp]
theorem contract_left_apply (f : Module.Dual R M) (m : M) : contractLeft R M (f ⊗ₜ m) = f m := by
  apply uncurry_apply

@[simp]
theorem contract_right_apply (f : Module.Dual R M) (m : M) : contractRight R M (m ⊗ₜ f) = f m := by
  apply uncurry_apply

@[simp]
theorem dual_tensor_hom_apply (f : Module.Dual R M) (m : M) (n : N) : dualTensorHom R M N (f ⊗ₜ n) m = f m • n := by
  dunfold dualTensorHom
  rw [uncurry_apply]
  rfl

end Contraction

