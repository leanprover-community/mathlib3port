/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module group_theory.group_action.sum
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Defs

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

/- warning: sum.smul_def -> Sum.smul_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u3} M β] (a : M) (x : Sum.{u2, u3} α β), Eq.{succ (max u2 u3)} (Sum.{u2, u3} α β) (SMul.smul.{u1, max u2 u3} M (Sum.{u2, u3} α β) (Sum.hasSmul.{u1, u2, u3} M α β _inst_1 _inst_2) a x) (Sum.map.{u2, u3, u2, u3} α α β β (SMul.smul.{u1, u2} M α _inst_1 a) (SMul.smul.{u1, u3} M β _inst_2 a) x)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M β] (a : M) (x : Sum.{u3, u2} α β), Eq.{max (succ u3) (succ u2)} (Sum.{u3, u2} α β) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Sum.{u3, u2} α β) (Sum.{u3, u2} α β) (instHSMul.{u1, max u3 u2} M (Sum.{u3, u2} α β) (Sum.instSMulSum.{u1, u3, u2} M α β _inst_1 _inst_2)) a x) (Sum.map.{u3, u2, u3, u2} α α β β ((fun (x._@.Mathlib.GroupTheory.GroupAction.Sum._hyg.201 : M) (x._@.Mathlib.GroupTheory.GroupAction.Sum._hyg.203 : α) => HSMul.hSMul.{u1, u3, u3} M α α (instHSMul.{u1, u3} M α _inst_1) x._@.Mathlib.GroupTheory.GroupAction.Sum._hyg.201 x._@.Mathlib.GroupTheory.GroupAction.Sum._hyg.203) a) ((fun (x._@.Mathlib.GroupTheory.GroupAction.Sum._hyg.220 : M) (x._@.Mathlib.GroupTheory.GroupAction.Sum._hyg.222 : β) => HSMul.hSMul.{u1, u2, u2} M β β (instHSMul.{u1, u2} M β _inst_2) x._@.Mathlib.GroupTheory.GroupAction.Sum._hyg.220 x._@.Mathlib.GroupTheory.GroupAction.Sum._hyg.222) a) x)
Case conversion may be inaccurate. Consider using '#align sum.smul_def Sum.smul_defₓ'. -/
@[to_additive]
theorem smul_def : a • x = x.map ((· • ·) a) ((· • ·) a) :=
  rfl
#align sum.smul_def Sum.smul_def
#align sum.vadd_def Sum.vadd_def

/- warning: sum.smul_inl -> Sum.smul_inl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u3} M β] (a : M) (b : α), Eq.{succ (max u2 u3)} (Sum.{u2, u3} α β) (SMul.smul.{u1, max u2 u3} M (Sum.{u2, u3} α β) (Sum.hasSmul.{u1, u2, u3} M α β _inst_1 _inst_2) a (Sum.inl.{u2, u3} α β b)) (Sum.inl.{u2, u3} α β (SMul.smul.{u1, u2} M α _inst_1 a b))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M β] (a : M) (b : α), Eq.{max (succ u3) (succ u2)} (Sum.{u3, u2} α β) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Sum.{u3, u2} α β) (Sum.{u3, u2} α β) (instHSMul.{u1, max u3 u2} M (Sum.{u3, u2} α β) (Sum.instSMulSum.{u1, u3, u2} M α β _inst_1 _inst_2)) a (Sum.inl.{u3, u2} α β b)) (Sum.inl.{u3, u2} α β (HSMul.hSMul.{u1, u3, u3} M α α (instHSMul.{u1, u3} M α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align sum.smul_inl Sum.smul_inlₓ'. -/
@[simp, to_additive]
theorem smul_inl : a • (inl b : Sum α β) = inl (a • b) :=
  rfl
#align sum.smul_inl Sum.smul_inl
#align sum.vadd_inl Sum.vadd_inl

/- warning: sum.smul_inr -> Sum.smul_inr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u3} M β] (a : M) (c : β), Eq.{succ (max u2 u3)} (Sum.{u2, u3} α β) (SMul.smul.{u1, max u2 u3} M (Sum.{u2, u3} α β) (Sum.hasSmul.{u1, u2, u3} M α β _inst_1 _inst_2) a (Sum.inr.{u2, u3} α β c)) (Sum.inr.{u2, u3} α β (SMul.smul.{u1, u3} M β _inst_2 a c))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M β] (a : M) (c : β), Eq.{max (succ u3) (succ u2)} (Sum.{u3, u2} α β) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Sum.{u3, u2} α β) (Sum.{u3, u2} α β) (instHSMul.{u1, max u3 u2} M (Sum.{u3, u2} α β) (Sum.instSMulSum.{u1, u3, u2} M α β _inst_1 _inst_2)) a (Sum.inr.{u3, u2} α β c)) (Sum.inr.{u3, u2} α β (HSMul.hSMul.{u1, u2, u2} M β β (instHSMul.{u1, u2} M β _inst_2) a c))
Case conversion may be inaccurate. Consider using '#align sum.smul_inr Sum.smul_inrₓ'. -/
@[simp, to_additive]
theorem smul_inr : a • (inr c : Sum α β) = inr (a • c) :=
  rfl
#align sum.smul_inr Sum.smul_inr
#align sum.vadd_inr Sum.vadd_inr

/- warning: sum.smul_swap -> Sum.smul_swap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u1, u2} M α] [_inst_2 : SMul.{u1, u3} M β] (a : M) (x : Sum.{u2, u3} α β), Eq.{max (succ u3) (succ u2)} (Sum.{u3, u2} β α) (Sum.swap.{u2, u3} α β (SMul.smul.{u1, max u2 u3} M (Sum.{u2, u3} α β) (Sum.hasSmul.{u1, u2, u3} M α β _inst_1 _inst_2) a x)) (SMul.smul.{u1, max u3 u2} M (Sum.{u3, u2} β α) (Sum.hasSmul.{u1, u3, u2} M β α _inst_2 _inst_1) a (Sum.swap.{u2, u3} α β x))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u3} M α] [_inst_2 : SMul.{u1, u2} M β] (a : M) (x : Sum.{u3, u2} α β), Eq.{max (succ u3) (succ u2)} (Sum.{u2, u3} β α) (Sum.swap.{u3, u2} α β (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Sum.{u3, u2} α β) (Sum.{u3, u2} α β) (instHSMul.{u1, max u3 u2} M (Sum.{u3, u2} α β) (Sum.instSMulSum.{u1, u3, u2} M α β _inst_1 _inst_2)) a x)) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} M (Sum.{u2, u3} β α) (Sum.{u2, u3} β α) (instHSMul.{u1, max u3 u2} M (Sum.{u2, u3} β α) (Sum.instSMulSum.{u1, u2, u3} M β α _inst_2 _inst_1)) a (Sum.swap.{u3, u2} α β x))
Case conversion may be inaccurate. Consider using '#align sum.smul_swap Sum.smul_swapₓ'. -/
@[simp, to_additive]
theorem smul_swap : (a • x).swap = a • x.swap := by cases x <;> rfl
#align sum.smul_swap Sum.smul_swap
#align sum.vadd_swap Sum.vadd_swap

instance [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (Sum α β) :=
  ⟨fun a b x => by
    cases x
    exacts[congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩

@[to_additive]
instance [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (Sum α β) :=
  ⟨fun a b x => by
    cases x
    exacts[congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (Sum α β) :=
  ⟨fun a x => by
    cases x
    exacts[congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩

#print Sum.FaithfulSMulLeft /-
@[to_additive]
instance FaithfulSMulLeft [FaithfulSMul M α] : FaithfulSMul M (Sum α β) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩
#align sum.has_faithful_smul_left Sum.FaithfulSMulLeft
-/

#print Sum.FaithfulSMulRight /-
@[to_additive]
instance FaithfulSMulRight [FaithfulSMul M β] : FaithfulSMul M (Sum α β) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩
#align sum.has_faithful_smul_right Sum.FaithfulSMulRight
-/

end SMul

@[to_additive]
instance {m : Monoid M} [MulAction M α] [MulAction M β] : MulAction M (Sum α β)
    where
  mul_smul a b x := by
    cases x
    exacts[congr_arg inl (mul_smul _ _ _), congr_arg inr (mul_smul _ _ _)]
  one_smul x := by
    cases x
    exacts[congr_arg inl (one_smul _ _), congr_arg inr (one_smul _ _)]

end Sum

