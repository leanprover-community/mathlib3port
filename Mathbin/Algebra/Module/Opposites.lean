/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.module.opposites
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Equiv
import Mathbin.GroupTheory.GroupAction.Opposite

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`group_theory.group_action.opposite`.
-/


namespace MulOpposite

universe u v

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- `mul_opposite.distrib_mul_action` extends to a `module` -/
instance : Module R (MulOpposite M) :=
  {
    MulOpposite.distribMulAction M
      R with
    add_smul := fun r₁ r₂ x => unop_injective <| add_smul r₁ r₂ (unop x)
    zero_smul := fun x => unop_injective <| zero_smul _ (unop x) }

/-- The function `op` is a linear equivalence. -/
def opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ :=
  { opAddEquiv with map_smul' := MulOpposite.op_smul }
#align mul_opposite.op_linear_equiv MulOpposite.opLinearEquiv

@[simp]
theorem coe_op_linear_equiv : (opLinearEquiv R : M → Mᵐᵒᵖ) = op :=
  rfl
#align mul_opposite.coe_op_linear_equiv MulOpposite.coe_op_linear_equiv

@[simp]
theorem coe_op_linear_equiv_symm : ((opLinearEquiv R).symm : Mᵐᵒᵖ → M) = unop :=
  rfl
#align mul_opposite.coe_op_linear_equiv_symm MulOpposite.coe_op_linear_equiv_symm

@[simp]
theorem coe_op_linear_equiv_to_linear_map : ((opLinearEquiv R).toLinearMap : M → Mᵐᵒᵖ) = op :=
  rfl
#align mul_opposite.coe_op_linear_equiv_to_linear_map MulOpposite.coe_op_linear_equiv_to_linear_map

@[simp]
theorem coe_op_linear_equiv_symm_to_linear_map :
    ((opLinearEquiv R).symm.toLinearMap : Mᵐᵒᵖ → M) = unop :=
  rfl
#align
  mul_opposite.coe_op_linear_equiv_symm_to_linear_map MulOpposite.coe_op_linear_equiv_symm_to_linear_map

@[simp]
theorem op_linear_equiv_to_add_equiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = op_add_equiv :=
  rfl
#align mul_opposite.op_linear_equiv_to_add_equiv MulOpposite.op_linear_equiv_to_add_equiv

@[simp]
theorem op_linear_equiv_symm_to_add_equiv :
    (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAddEquiv = opAddEquiv.symm :=
  rfl
#align mul_opposite.op_linear_equiv_symm_to_add_equiv MulOpposite.op_linear_equiv_symm_to_add_equiv

end MulOpposite

