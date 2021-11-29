import Mathbin.GroupTheory.GroupAction.Opposite 
import Mathbin.Data.Equiv.Module

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`group_theory.group_action.opposite`.
-/


namespace MulOpposite

universe u v

variable (R : Type u) {M : Type v} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

/-- `mul_opposite.distrib_mul_action` extends to a `module` -/
instance : Module R (MulOpposite M) :=
  { MulOpposite.distribMulAction M R with add_smul := fun r₁ r₂ x => unop_injective$ add_smul r₁ r₂ (unop x),
    zero_smul := fun x => unop_injective$ zero_smul _ (unop x) }

/-- The function `op` is a linear equivalence. -/
def op_linear_equiv : M ≃ₗ[R] «expr ᵐᵒᵖ» M :=
  { op_add_equiv with map_smul' := MulOpposite.op_smul }

@[simp]
theorem coe_op_linear_equiv : (op_linear_equiv R : M → «expr ᵐᵒᵖ» M) = op :=
  rfl

@[simp]
theorem coe_op_linear_equiv_symm : ((op_linear_equiv R).symm : «expr ᵐᵒᵖ» M → M) = unop :=
  rfl

@[simp]
theorem coe_op_linear_equiv_to_linear_map : ((op_linear_equiv R).toLinearMap : M → «expr ᵐᵒᵖ» M) = op :=
  rfl

@[simp]
theorem coe_op_linear_equiv_symm_to_linear_map : ((op_linear_equiv R).symm.toLinearMap : «expr ᵐᵒᵖ» M → M) = unop :=
  rfl

@[simp]
theorem op_linear_equiv_to_add_equiv : (op_linear_equiv R : M ≃ₗ[R] «expr ᵐᵒᵖ» M).toAddEquiv = op_add_equiv :=
  rfl

@[simp]
theorem op_linear_equiv_symm_to_add_equiv :
  (op_linear_equiv R : M ≃ₗ[R] «expr ᵐᵒᵖ» M).symm.toAddEquiv = op_add_equiv.symm :=
  rfl

end MulOpposite

