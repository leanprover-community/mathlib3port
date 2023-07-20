/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Module.Equiv
import Mathbin.GroupTheory.GroupAction.Opposite

#align_import algebra.module.opposites from "leanprover-community/mathlib"@"fac369018417f980cec5fcdafc766a69f88d8cfe"

/-!
# Module operations on `Mᵐᵒᵖ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print MulOpposite.opLinearEquiv /-
/-- The function `op` is a linear equivalence. -/
def opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ :=
  { opAddEquiv with map_smul' := MulOpposite.op_smul }
#align mul_opposite.op_linear_equiv MulOpposite.opLinearEquiv
-/

#print MulOpposite.coe_opLinearEquiv /-
@[simp]
theorem coe_opLinearEquiv : (opLinearEquiv R : M → Mᵐᵒᵖ) = op :=
  rfl
#align mul_opposite.coe_op_linear_equiv MulOpposite.coe_opLinearEquiv
-/

#print MulOpposite.coe_opLinearEquiv_symm /-
@[simp]
theorem coe_opLinearEquiv_symm : ((opLinearEquiv R).symm : Mᵐᵒᵖ → M) = unop :=
  rfl
#align mul_opposite.coe_op_linear_equiv_symm MulOpposite.coe_opLinearEquiv_symm
-/

#print MulOpposite.coe_opLinearEquiv_toLinearMap /-
@[simp]
theorem coe_opLinearEquiv_toLinearMap : ((opLinearEquiv R).toLinearMap : M → Mᵐᵒᵖ) = op :=
  rfl
#align mul_opposite.coe_op_linear_equiv_to_linear_map MulOpposite.coe_opLinearEquiv_toLinearMap
-/

#print MulOpposite.coe_opLinearEquiv_symm_toLinearMap /-
@[simp]
theorem coe_opLinearEquiv_symm_toLinearMap :
    ((opLinearEquiv R).symm.toLinearMap : Mᵐᵒᵖ → M) = unop :=
  rfl
#align mul_opposite.coe_op_linear_equiv_symm_to_linear_map MulOpposite.coe_opLinearEquiv_symm_toLinearMap
-/

#print MulOpposite.opLinearEquiv_toAddEquiv /-
@[simp]
theorem opLinearEquiv_toAddEquiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = opAddEquiv :=
  rfl
#align mul_opposite.op_linear_equiv_to_add_equiv MulOpposite.opLinearEquiv_toAddEquiv
-/

#print MulOpposite.opLinearEquiv_symm_toAddEquiv /-
@[simp]
theorem opLinearEquiv_symm_toAddEquiv :
    (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAddEquiv = opAddEquiv.symm :=
  rfl
#align mul_opposite.op_linear_equiv_symm_to_add_equiv MulOpposite.opLinearEquiv_symm_toAddEquiv
-/

end MulOpposite

