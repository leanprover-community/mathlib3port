/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module data.set.pointwise.support
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Smul
import Mathbin.Algebra.Support

/-!
# Support of a function composed with a scalar action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that the support of `x ↦ f (c⁻¹ • x)` is equal to `c • support f`.
-/


open Pointwise

open Function Set

section Group

variable {α β γ : Type _} [Group α] [MulAction α β]

/- warning: mul_support_comp_inv_smul -> mulSupport_comp_inv_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_3 : One.{u3} γ] (c : α) (f : β -> γ), Eq.{succ u2} (Set.{u2} β) (Function.mulSupport.{u2, u3} β γ _inst_3 (fun (x : β) => f (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) c) x))) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) c (Function.mulSupport.{u2, u3} β γ _inst_3 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_3 : One.{u3} γ] (c : α) (f : β -> γ), Eq.{succ u2} (Set.{u2} β) (Function.mulSupport.{u2, u3} β γ _inst_3 (fun (x : β) => f (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) c) x))) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) c (Function.mulSupport.{u2, u3} β γ _inst_3 f))
Case conversion may be inaccurate. Consider using '#align mul_support_comp_inv_smul mulSupport_comp_inv_smulₓ'. -/
theorem mulSupport_comp_inv_smul [One γ] (c : α) (f : β → γ) :
    (mulSupport fun x => f (c⁻¹ • x)) = c • mulSupport f :=
  by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_mul_support]
#align mul_support_comp_inv_smul mulSupport_comp_inv_smul

/- warning: support_comp_inv_smul -> support_comp_inv_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_3 : Zero.{u3} γ] (c : α) (f : β -> γ), Eq.{succ u2} (Set.{u2} β) (Function.support.{u2, u3} β γ _inst_3 (fun (x : β) => f (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) c) x))) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) c (Function.support.{u2, u3} β γ _inst_3 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_3 : Zero.{u3} γ] (c : α) (f : β -> γ), Eq.{succ u2} (Set.{u2} β) (Function.support.{u2, u3} β γ _inst_3 (fun (x : β) => f (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) c) x))) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) c (Function.support.{u2, u3} β γ _inst_3 f))
Case conversion may be inaccurate. Consider using '#align support_comp_inv_smul support_comp_inv_smulₓ'. -/
theorem support_comp_inv_smul [Zero γ] (c : α) (f : β → γ) :
    (support fun x => f (c⁻¹ • x)) = c • support f :=
  by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_support]
#align support_comp_inv_smul support_comp_inv_smul

attribute [to_additive support_comp_inv_smul] mulSupport_comp_inv_smul

end Group

section GroupWithZero

variable {α β γ : Type _} [GroupWithZero α] [MulAction α β]

/- warning: mul_support_comp_inv_smul₀ -> mulSupport_comp_inv_smul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] [_inst_3 : One.{u3} γ] {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (f : β -> γ), Eq.{succ u2} (Set.{u2} β) (Function.mulSupport.{u2, u3} β γ _inst_3 (fun (x : β) => f (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) c) x))) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) c (Function.mulSupport.{u2, u3} β γ _inst_3 f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] [_inst_3 : One.{u3} γ] {c : α}, (Ne.{succ u2} α c (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall (f : β -> γ), Eq.{succ u1} (Set.{u1} β) (Function.mulSupport.{u1, u3} β γ _inst_3 (fun (x : β) => f (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2)) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) c) x))) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) c (Function.mulSupport.{u1, u3} β γ _inst_3 f)))
Case conversion may be inaccurate. Consider using '#align mul_support_comp_inv_smul₀ mulSupport_comp_inv_smul₀ₓ'. -/
theorem mulSupport_comp_inv_smul₀ [One γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
    (mulSupport fun x => f (c⁻¹ • x)) = c • mulSupport f :=
  by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_mul_support]
#align mul_support_comp_inv_smul₀ mulSupport_comp_inv_smul₀

/- warning: support_comp_inv_smul₀ -> support_comp_inv_smul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] [_inst_3 : Zero.{u3} γ] {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (f : β -> γ), Eq.{succ u2} (Set.{u2} β) (Function.support.{u2, u3} β γ _inst_3 (fun (x : β) => f (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) c) x))) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) c (Function.support.{u2, u3} β γ _inst_3 f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] [_inst_3 : Zero.{u3} γ] {c : α}, (Ne.{succ u2} α c (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall (f : β -> γ), Eq.{succ u1} (Set.{u1} β) (Function.support.{u1, u3} β γ _inst_3 (fun (x : β) => f (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2)) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) c) x))) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) c (Function.support.{u1, u3} β γ _inst_3 f)))
Case conversion may be inaccurate. Consider using '#align support_comp_inv_smul₀ support_comp_inv_smul₀ₓ'. -/
theorem support_comp_inv_smul₀ [Zero γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
    (support fun x => f (c⁻¹ • x)) = c • support f :=
  by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_support]
#align support_comp_inv_smul₀ support_comp_inv_smul₀

attribute [to_additive support_comp_inv_smul₀] mulSupport_comp_inv_smul₀

end GroupWithZero

