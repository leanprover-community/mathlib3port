/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module group_theory.group_action.option
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Option instances for additive and multiplicative actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for additive and multiplicative actions on `option` type. Scalar
multiplication is defined by `a • some b = some (a • b)` and `a • none = none`.

## See also

* `group_theory.group_action.pi`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/


variable {M N α : Type _}

namespace Option

section HasSmul

variable [HasSmul M α] [HasSmul N α] (a : M) (b : α) (x : Option α)

@[to_additive Option.hasVadd]
instance : HasSmul M (Option α) :=
  ⟨fun a => Option.map <| (· • ·) a⟩

/- warning: option.smul_def -> Option.smul_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] (a : M) (x : Option.{u2} α), Eq.{succ u2} (Option.{u2} α) (HasSmul.smul.{u1, u2} M (Option.{u2} α) (Option.hasSmul.{u1, u2} M α _inst_1) a x) (Option.map.{u2, u2} α α (HasSmul.smul.{u1, u2} M α _inst_1 a) x)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u1, u2} M α] (a : M) (x : Option.{u2} α), Eq.{succ u2} (Option.{u2} α) (HSMul.hSMul.{u1, u2, u2} M (Option.{u2} α) (Option.{u2} α) (instHSMul.{u1, u2} M (Option.{u2} α) (Option.instSMulOption.{u1, u2} M α _inst_1)) a x) (Option.map.{u2, u2} α α ((fun (x._@.Mathlib.GroupTheory.GroupAction.Option._hyg.120 : M) (x._@.Mathlib.GroupTheory.GroupAction.Option._hyg.122 : α) => HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) x._@.Mathlib.GroupTheory.GroupAction.Option._hyg.120 x._@.Mathlib.GroupTheory.GroupAction.Option._hyg.122) a) x)
Case conversion may be inaccurate. Consider using '#align option.smul_def Option.smul_defₓ'. -/
@[to_additive]
theorem smul_def : a • x = x.map ((· • ·) a) :=
  rfl
#align option.smul_def Option.smul_def

/- warning: option.smul_none -> Option.smul_none is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] (a : M), Eq.{succ u2} (Option.{u2} α) (HasSmul.smul.{u1, u2} M (Option.{u2} α) (Option.hasSmul.{u1, u2} M α _inst_1) a (Option.none.{u2} α)) (Option.none.{u2} α)
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u1, u2} M α] (a : M), Eq.{succ u2} (Option.{u2} α) (HSMul.hSMul.{u1, u2, u2} M (Option.{u2} α) (Option.{u2} α) (instHSMul.{u1, u2} M (Option.{u2} α) (Option.instSMulOption.{u1, u2} M α _inst_1)) a (Option.none.{u2} α)) (Option.none.{u2} α)
Case conversion may be inaccurate. Consider using '#align option.smul_none Option.smul_noneₓ'. -/
@[simp, to_additive]
theorem smul_none : a • (none : Option α) = none :=
  rfl
#align option.smul_none Option.smul_none

/- warning: option.smul_some -> Option.smul_some is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} M α] (a : M) (b : α), Eq.{succ u2} (Option.{u2} α) (HasSmul.smul.{u1, u2} M (Option.{u2} α) (Option.hasSmul.{u1, u2} M α _inst_1) a (Option.some.{u2} α b)) (Option.some.{u2} α (HasSmul.smul.{u1, u2} M α _inst_1 a b))
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u1, u2} M α] (a : M) (b : α), Eq.{succ u2} (Option.{u2} α) (HSMul.hSMul.{u1, u2, u2} M (Option.{u2} α) (Option.{u2} α) (instHSMul.{u1, u2} M (Option.{u2} α) (Option.instSMulOption.{u1, u2} M α _inst_1)) a (Option.some.{u2} α b)) (Option.some.{u2} α (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align option.smul_some Option.smul_someₓ'. -/
@[simp, to_additive]
theorem smul_some : a • some b = some (a • b) :=
  rfl
#align option.smul_some Option.smul_some

@[to_additive]
instance [HasSmul M N] [IsScalarTower M N α] : IsScalarTower M N (Option α) :=
  ⟨fun a b x => by
    cases x
    exacts[rfl, congr_arg some (smul_assoc _ _ _)]⟩

@[to_additive]
instance [SMulCommClass M N α] : SMulCommClass M N (Option α) :=
  ⟨fun a b => Function.Commute.option_map <| smul_comm _ _⟩

@[to_additive]
instance [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (Option α) :=
  ⟨fun a x => by
    cases x
    exacts[rfl, congr_arg some (op_smul_eq_smul _ _)]⟩

@[to_additive]
instance [FaithfulSMul M α] : FaithfulSMul M (Option α) :=
  ⟨fun x y h => eq_of_smul_eq_smul fun b : α => by injection h (some b)⟩

end HasSmul

instance [Monoid M] [MulAction M α] : MulAction M (Option α)
    where
  smul := (· • ·)
  one_smul b := by
    cases b
    exacts[rfl, congr_arg some (one_smul _ _)]
  mul_smul a₁ a₂ b := by
    cases b
    exacts[rfl, congr_arg some (mul_smul _ _ _)]

end Option

