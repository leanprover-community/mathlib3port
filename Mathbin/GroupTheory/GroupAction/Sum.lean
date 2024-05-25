/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Algebra.Group.Action.Defs

#align_import group_theory.group_action.sum from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Sum instances for additive and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for additive and multiplicative actions on the binary `sum` type.

## See also

* `group_theory.group_action.option`
* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
-/


variable {M N P α β γ : Type _}

namespace Sum

section SMul

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β) (x : Sum α β)

@[to_additive Sum.hasVadd]
instance : SMul M (Sum α β) :=
  ⟨fun a => Sum.map ((· • ·) a) ((· • ·) a)⟩

#print Sum.smul_def /-
@[to_additive]
theorem smul_def : a • x = x.map ((· • ·) a) ((· • ·) a) :=
  rfl
#align sum.smul_def Sum.smul_def
#align sum.vadd_def Sum.vadd_def
-/

#print Sum.smul_inl /-
@[simp, to_additive]
theorem smul_inl : a • (inl b : Sum α β) = inl (a • b) :=
  rfl
#align sum.smul_inl Sum.smul_inl
#align sum.vadd_inl Sum.vadd_inl
-/

#print Sum.smul_inr /-
@[simp, to_additive]
theorem smul_inr : a • (inr c : Sum α β) = inr (a • c) :=
  rfl
#align sum.smul_inr Sum.smul_inr
#align sum.vadd_inr Sum.vadd_inr
-/

#print Sum.smul_swap /-
@[simp, to_additive]
theorem smul_swap : (a • x).symm = a • x.symm := by cases x <;> rfl
#align sum.smul_swap Sum.smul_swap
#align sum.vadd_swap Sum.vadd_swap
-/

instance [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (Sum α β) :=
  ⟨fun a b x => by cases x;
    exacts [congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩

@[to_additive]
instance [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (Sum α β) :=
  ⟨fun a b x => by cases x;
    exacts [congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (Sum α β) :=
  ⟨fun a x => by cases x;
    exacts [congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩

#print Sum.FaithfulSMulLeft /-
@[to_additive]
instance FaithfulSMulLeft [FaithfulSMul M α] : FaithfulSMul M (Sum α β) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩
#align sum.has_faithful_smul_left Sum.FaithfulSMulLeft
#align sum.has_faithful_vadd_left Sum.FaithfulVAddLeft
-/

#print Sum.FaithfulSMulRight /-
@[to_additive]
instance FaithfulSMulRight [FaithfulSMul M β] : FaithfulSMul M (Sum α β) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩
#align sum.has_faithful_smul_right Sum.FaithfulSMulRight
#align sum.has_faithful_vadd_right Sum.FaithfulVAddRight
-/

end SMul

@[to_additive]
instance {m : Monoid M} [MulAction M α] [MulAction M β] : MulAction M (Sum α β)
    where
  hMul_smul a b x := by cases x;
    exacts [congr_arg inl (mul_smul _ _ _), congr_arg inr (mul_smul _ _ _)]
  one_smul x := by cases x; exacts [congr_arg inl (one_smul _ _), congr_arg inr (one_smul _ _)]

end Sum

