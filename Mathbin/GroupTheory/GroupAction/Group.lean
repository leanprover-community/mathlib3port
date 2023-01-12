/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module group_theory.group_action.group
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Aut
import Mathbin.GroupTheory.GroupAction.Units

/-!
# Group actions applied to various types of group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas about `smul` on `group_with_zero`, and `group`.
-/


open Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

section MulAction

/- warning: right_cancel_monoid.to_has_faithful_smul -> RightCancelMonoid.faithfulSMul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : RightCancelMonoid.{u1} α], FaithfulSMul.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : RightCancelMonoid.{u1} α], FaithfulSMul.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (RightCancelMonoid.toMonoid.{u1} α _inst_1) (Monoid.toMulAction.{u1} α (RightCancelMonoid.toMonoid.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align right_cancel_monoid.to_has_faithful_smul RightCancelMonoid.faithfulSMulₓ'. -/
/-- `monoid.to_mul_action` is faithful on cancellative monoids. -/
@[to_additive " `add_monoid.to_add_action` is faithful on additive cancellative monoids. "]
instance RightCancelMonoid.faithfulSMul [RightCancelMonoid α] : FaithfulSMul α α :=
  ⟨fun x y h => mul_right_cancel (h 1)⟩
#align right_cancel_monoid.to_has_faithful_smul RightCancelMonoid.faithfulSMul

section Group

variable [Group α] [MulAction α β]

/- warning: inv_smul_smul -> inv_smul_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (c : α) (x : β), Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) c) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) c x)) x
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (c : α) (x : β), Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) c) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) c x)) x
Case conversion may be inaccurate. Consider using '#align inv_smul_smul inv_smul_smulₓ'. -/
@[simp, to_additive]
theorem inv_smul_smul (c : α) (x : β) : c⁻¹ • c • x = x := by rw [smul_smul, mul_left_inv, one_smul]
#align inv_smul_smul inv_smul_smul

/- warning: smul_inv_smul -> smul_inv_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (c : α) (x : β), Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) c (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) c) x)) x
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (c : α) (x : β), Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) c (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) c) x)) x
Case conversion may be inaccurate. Consider using '#align smul_inv_smul smul_inv_smulₓ'. -/
@[simp, to_additive]
theorem smul_inv_smul (c : α) (x : β) : c • c⁻¹ • x = x := by
  rw [smul_smul, mul_right_inv, one_smul]
#align smul_inv_smul smul_inv_smul

#print MulAction.toPerm /-
/-- Given an action of a group `α` on `β`, each `g : α` defines a permutation of `β`. -/
@[to_additive, simps]
def MulAction.toPerm (a : α) : Equiv.Perm β :=
  ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩
#align mul_action.to_perm MulAction.toPerm
-/

/-- Given an action of an additive group `α` on `β`, each `g : α` defines a permutation of `β`. -/
add_decl_doc AddAction.toPerm

#print MulAction.toPerm_injective /-
/-- `mul_action.to_perm` is injective on faithful actions. -/
@[to_additive "`add_action.to_perm` is injective on faithful actions."]
theorem MulAction.toPerm_injective [FaithfulSMul α β] :
    Function.Injective (MulAction.toPerm : α → Equiv.Perm β) :=
  (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp
#align mul_action.to_perm_injective MulAction.toPerm_injective
-/

variable (α) (β)

#print MulAction.toPermHom /-
/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
@[simps]
def MulAction.toPermHom : α →* Equiv.Perm β
    where
  toFun := MulAction.toPerm
  map_one' := Equiv.ext <| one_smul α
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : α) u₂
#align mul_action.to_perm_hom MulAction.toPermHom
-/

#print AddAction.toPermHom /-
/-- Given an action of a additive group `α` on a set `β`, each `g : α` defines a permutation of
`β`. -/
@[simps]
def AddAction.toPermHom (α : Type _) [AddGroup α] [AddAction α β] : α →+ Additive (Equiv.Perm β)
    where
  toFun a := Additive.ofMul <| AddAction.toPerm a
  map_zero' := Equiv.ext <| zero_vadd α
  map_add' a₁ a₂ := Equiv.ext <| add_vadd a₁ a₂
#align add_action.to_perm_hom AddAction.toPermHom
-/

#print Equiv.Perm.applyMulAction /-
/-- The tautological action by `equiv.perm α` on `α`.

This generalizes `function.End.apply_mul_action`.-/
instance Equiv.Perm.applyMulAction (α : Type _) : MulAction (Equiv.Perm α) α
    where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align equiv.perm.apply_mul_action Equiv.Perm.applyMulAction
-/

#print Equiv.Perm.smul_def /-
@[simp]
protected theorem Equiv.Perm.smul_def {α : Type _} (f : Equiv.Perm α) (a : α) : f • a = f a :=
  rfl
#align equiv.perm.smul_def Equiv.Perm.smul_def
-/

#print Equiv.Perm.applyFaithfulSMul /-
/-- `equiv.perm.apply_mul_action` is faithful. -/
instance Equiv.Perm.applyFaithfulSMul (α : Type _) : FaithfulSMul (Equiv.Perm α) α :=
  ⟨fun x y => Equiv.ext⟩
#align equiv.perm.apply_has_faithful_smul Equiv.Perm.applyFaithfulSMul
-/

variable {α} {β}

/- warning: inv_smul_eq_iff -> inv_smul_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {a : α} {x : β} {y : β}, Iff (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) x) y) (Eq.{succ u2} β x (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) a y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {a : α} {x : β} {y : β}, Iff (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) x) y) (Eq.{succ u2} β x (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a y))
Case conversion may be inaccurate. Consider using '#align inv_smul_eq_iff inv_smul_eq_iffₓ'. -/
@[to_additive]
theorem inv_smul_eq_iff {a : α} {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  (MulAction.toPerm a).symm_apply_eq
#align inv_smul_eq_iff inv_smul_eq_iff

/- warning: eq_inv_smul_iff -> eq_inv_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {a : α} {x : β} {y : β}, Iff (Eq.{succ u2} β x (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) y)) (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) a x) y)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {a : α} {x : β} {y : β}, Iff (Eq.{succ u2} β x (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) y)) (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a x) y)
Case conversion may be inaccurate. Consider using '#align eq_inv_smul_iff eq_inv_smul_iffₓ'. -/
@[to_additive]
theorem eq_inv_smul_iff {a : α} {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  (MulAction.toPerm a).eq_symm_apply
#align eq_inv_smul_iff eq_inv_smul_iff

/- warning: smul_inv -> smul_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_3 : Group.{u2} β] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)))))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))))) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)] (c : α) (x : β), Eq.{succ u2} β (Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) c x)) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) c) (Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)) x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_3 : Group.{u2} β] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (MulAction.toSMul.{u2, u2} β β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)) (Monoid.toMulAction.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (MulAction.toSMul.{u2, u2} β β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)) (Monoid.toMulAction.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)))) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)] (c : α) (x : β), Eq.{succ u2} β (Inv.inv.{u2} β (InvOneClass.toInv.{u2} β (DivInvOneMonoid.toInvOneClass.{u2} β (DivisionMonoid.toDivInvOneMonoid.{u2} β (Group.toDivisionMonoid.{u2} β _inst_3)))) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) c x)) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) c) (Inv.inv.{u2} β (InvOneClass.toInv.{u2} β (DivInvOneMonoid.toInvOneClass.{u2} β (DivisionMonoid.toDivInvOneMonoid.{u2} β (Group.toDivisionMonoid.{u2} β _inst_3)))) x))
Case conversion may be inaccurate. Consider using '#align smul_inv smul_invₓ'. -/
theorem smul_inv [Group β] [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) :
    (c • x)⁻¹ = c⁻¹ • x⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, smul_mul_smul, mul_right_inv, mul_right_inv, one_smul]
#align smul_inv smul_inv

/- warning: smul_zpow -> smul_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_3 : Group.{u2} β] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)))))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))))) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)] (c : α) (x : β) (p : Int), Eq.{succ u2} β (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int (DivInvMonoid.Pow.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) c x) p) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c p) (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int (DivInvMonoid.Pow.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))) x p))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_3 : Group.{u2} β] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (MulAction.toSMul.{u2, u2} β β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)) (Monoid.toMulAction.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (MulAction.toSMul.{u2, u2} β β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)) (Monoid.toMulAction.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3)))) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)] (c : α) (x : β) (p : Int), Eq.{succ u2} β (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int (DivInvMonoid.Pow.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) c x) p) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) c p) (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int (DivInvMonoid.Pow.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))) x p))
Case conversion may be inaccurate. Consider using '#align smul_zpow smul_zpowₓ'. -/
theorem smul_zpow [Group β] [SMulCommClass α β β] [IsScalarTower α β β] (c : α) (x : β) (p : ℤ) :
    (c • x) ^ p = c ^ p • x ^ p := by cases p <;> simp [smul_pow, smul_inv]
#align smul_zpow smul_zpow

#print Commute.smul_right_iff /-
@[simp]
theorem Commute.smul_right_iff [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    (r : α) : Commute a (r • b) ↔ Commute a b :=
  ⟨fun h => inv_smul_smul r b ▸ h.smul_right r⁻¹, fun h => h.smul_right r⟩
#align commute.smul_right_iff Commute.smul_right_iff
-/

#print Commute.smul_left_iff /-
@[simp]
theorem Commute.smul_left_iff [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    (r : α) : Commute (r • a) b ↔ Commute a b := by
  rw [Commute.symm_iff, Commute.smul_right_iff, Commute.symm_iff]
#align commute.smul_left_iff Commute.smul_left_iff
-/

#print MulAction.bijective /-
@[to_additive]
protected theorem MulAction.bijective (g : α) : Bijective ((· • ·) g : β → β) :=
  (MulAction.toPerm g).Bijective
#align mul_action.bijective MulAction.bijective
-/

#print MulAction.injective /-
@[to_additive]
protected theorem MulAction.injective (g : α) : Injective ((· • ·) g : β → β) :=
  (MulAction.bijective g).Injective
#align mul_action.injective MulAction.injective
-/

#print MulAction.surjective /-
@[to_additive]
protected theorem MulAction.surjective (g : α) : Surjective ((· • ·) g : β → β) :=
  (MulAction.bijective g).Surjective
#align mul_action.surjective MulAction.surjective
-/

#print smul_left_cancel /-
@[to_additive]
theorem smul_left_cancel (g : α) {x y : β} (h : g • x = g • y) : x = y :=
  MulAction.injective g h
#align smul_left_cancel smul_left_cancel
-/

#print smul_left_cancel_iff /-
@[simp, to_additive]
theorem smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y :=
  (MulAction.injective g).eq_iff
#align smul_left_cancel_iff smul_left_cancel_iff
-/

/- warning: smul_eq_iff_eq_inv_smul -> smul_eq_iff_eq_inv_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (g : α) {x : β} {y : β}, Iff (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) g x) y) (Eq.{succ u2} β x (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) g) y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (g : α) {x : β} {y : β}, Iff (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) g x) y) (Eq.{succ u2} β x (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) g) y))
Case conversion may be inaccurate. Consider using '#align smul_eq_iff_eq_inv_smul smul_eq_iff_eq_inv_smulₓ'. -/
@[to_additive]
theorem smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g • x = y ↔ x = g⁻¹ • y :=
  (MulAction.toPerm g).apply_eq_iff_eq_symm_apply
#align smul_eq_iff_eq_inv_smul smul_eq_iff_eq_inv_smul

end Group

/- warning: cancel_monoid_with_zero.to_has_faithful_smul -> CancelMonoidWithZero.faithfulSMul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} α] [_inst_2 : Nontrivial.{u1} α], FaithfulSMul.{u1, u1} α α (Mul.toSMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} α] [_inst_2 : Nontrivial.{u1} α], FaithfulSMul.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (MonoidWithZero.toMonoid.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) (Monoid.toMulAction.{u1} α (MonoidWithZero.toMonoid.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align cancel_monoid_with_zero.to_has_faithful_smul CancelMonoidWithZero.faithfulSMulₓ'. -/
/-- `monoid.to_mul_action` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.faithfulSMul [CancelMonoidWithZero α] [Nontrivial α] :
    FaithfulSMul α α :=
  ⟨fun x y h => mul_left_injective₀ one_ne_zero (h 1)⟩
#align cancel_monoid_with_zero.to_has_faithful_smul CancelMonoidWithZero.faithfulSMul

section Gwz

variable [GroupWithZero α] [MulAction α β] {a : α}

/- warning: inv_smul_smul₀ -> inv_smul_smul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (x : β), Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) c) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) c x)) x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (forall (x : β), Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) c) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) c x)) x)
Case conversion may be inaccurate. Consider using '#align inv_smul_smul₀ inv_smul_smul₀ₓ'. -/
@[simp]
theorem inv_smul_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
  inv_smul_smul (Units.mk0 c hc) x
#align inv_smul_smul₀ inv_smul_smul₀

/- warning: smul_inv_smul₀ -> smul_inv_smul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (x : β), Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) c (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) c) x)) x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (forall (x : β), Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) c (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) c) x)) x)
Case conversion may be inaccurate. Consider using '#align smul_inv_smul₀ smul_inv_smul₀ₓ'. -/
@[simp]
theorem smul_inv_smul₀ {c : α} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
  smul_inv_smul (Units.mk0 c hc) x
#align smul_inv_smul₀ smul_inv_smul₀

/- warning: inv_smul_eq_iff₀ -> inv_smul_eq_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall {x : β} {y : β}, Iff (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) x) y) (Eq.{succ u2} β x (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) a y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (forall {x : β} {y : β}, Iff (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) a) x) y) (Eq.{succ u2} β x (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a y)))
Case conversion may be inaccurate. Consider using '#align inv_smul_eq_iff₀ inv_smul_eq_iff₀ₓ'. -/
theorem inv_smul_eq_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
  (MulAction.toPerm (Units.mk0 a ha)).symm_apply_eq
#align inv_smul_eq_iff₀ inv_smul_eq_iff₀

/- warning: eq_inv_smul_iff₀ -> eq_inv_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall {x : β} {y : β}, Iff (Eq.{succ u2} β x (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) y)) (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) a x) y))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (forall {x : β} {y : β}, Iff (Eq.{succ u2} β x (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) a) y)) (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a x) y))
Case conversion may be inaccurate. Consider using '#align eq_inv_smul_iff₀ eq_inv_smul_iff₀ₓ'. -/
theorem eq_inv_smul_iff₀ {a : α} (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
  (MulAction.toPerm (Units.mk0 a ha)).eq_symm_apply
#align eq_inv_smul_iff₀ eq_inv_smul_iff₀

/- warning: commute.smul_right_iff₀ -> Commute.smul_right_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] [_inst_3 : Mul.{u2} β] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β _inst_3)] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β _inst_3) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)] {a : β} {b : β} {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Iff (Commute.{u2} β _inst_3 a (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) c b)) (Commute.{u2} β _inst_3 a b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] [_inst_3 : Mul.{u2} β] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β _inst_3)] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β _inst_3) (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)] {a : β} {b : β} {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (Iff (Commute.{u2} β _inst_3 a (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) c b)) (Commute.{u2} β _inst_3 a b))
Case conversion may be inaccurate. Consider using '#align commute.smul_right_iff₀ Commute.smul_right_iff₀ₓ'. -/
@[simp]
theorem Commute.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β}
    {c : α} (hc : c ≠ 0) : Commute a (c • b) ↔ Commute a b :=
  Commute.smul_right_iff (Units.mk0 c hc)
#align commute.smul_right_iff₀ Commute.smul_right_iff₀

/- warning: commute.smul_left_iff₀ -> Commute.smul_left_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] [_inst_3 : Mul.{u2} β] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β _inst_3)] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β _inst_3) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)] {a : β} {b : β} {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Iff (Commute.{u2} β _inst_3 (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) c a) b) (Commute.{u2} β _inst_3 a b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] [_inst_3 : Mul.{u2} β] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β _inst_3)] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Mul.toSMul.{u2} β _inst_3) (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)] {a : β} {b : β} {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (Iff (Commute.{u2} β _inst_3 (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) c a) b) (Commute.{u2} β _inst_3 a b))
Case conversion may be inaccurate. Consider using '#align commute.smul_left_iff₀ Commute.smul_left_iff₀ₓ'. -/
@[simp]
theorem Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {a b : β} {c : α}
    (hc : c ≠ 0) : Commute (c • a) b ↔ Commute a b :=
  Commute.smul_left_iff (Units.mk0 c hc)
#align commute.smul_left_iff₀ Commute.smul_left_iff₀

/- warning: mul_action.bijective₀ -> MulAction.bijective₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Function.Bijective.{succ u2, succ u2} β β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (Function.Bijective.{succ u2, succ u2} β β ((fun (x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1633 : α) (x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1635 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1633 x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1635) a))
Case conversion may be inaccurate. Consider using '#align mul_action.bijective₀ MulAction.bijective₀ₓ'. -/
protected theorem MulAction.bijective₀ (ha : a ≠ 0) : Bijective ((· • ·) a : β → β) :=
  MulAction.bijective <| Units.mk0 a ha
#align mul_action.bijective₀ MulAction.bijective₀

/- warning: mul_action.injective₀ -> MulAction.injective₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Function.Injective.{succ u2, succ u2} β β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (Function.Injective.{succ u2, succ u2} β β ((fun (x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1684 : α) (x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1686 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1684 x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1686) a))
Case conversion may be inaccurate. Consider using '#align mul_action.injective₀ MulAction.injective₀ₓ'. -/
protected theorem MulAction.injective₀ (ha : a ≠ 0) : Injective ((· • ·) a : β → β) :=
  (MulAction.bijective₀ ha).Injective
#align mul_action.injective₀ MulAction.injective₀

/- warning: mul_action.surjective₀ -> MulAction.surjective₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Function.Surjective.{succ u2, succ u2} β β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (Function.Surjective.{succ u2, succ u2} β β ((fun (x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1734 : α) (x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1736 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1734 x._@.Mathlib.GroupTheory.GroupAction.Group._hyg.1736) a))
Case conversion may be inaccurate. Consider using '#align mul_action.surjective₀ MulAction.surjective₀ₓ'. -/
protected theorem MulAction.surjective₀ (ha : a ≠ 0) : Surjective ((· • ·) a : β → β) :=
  (MulAction.bijective₀ ha).Surjective
#align mul_action.surjective₀ MulAction.surjective₀

end Gwz

end MulAction

section DistribMulAction

section Group

variable [Group α] [AddMonoid β] [DistribMulAction α β]

variable (β)

/- warning: distrib_mul_action.to_add_equiv -> DistribMulAction.toAddEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (β : Type.{u2}) [_inst_1 : Group.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2], α -> (AddEquiv.{u2, u2} β β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)) (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} (β : Type.{u2}) [_inst_1 : Group.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2], α -> (AddEquiv.{u2, u2} β β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align distrib_mul_action.to_add_equiv DistribMulAction.toAddEquivₓ'. -/
/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `mul_action.to_perm`. -/
@[simps (config := { simpRhs := true })]
def DistribMulAction.toAddEquiv (x : α) : β ≃+ β :=
  { DistribMulAction.toAddMonoidHom β x, MulAction.toPermHom α β x with }
#align distrib_mul_action.to_add_equiv DistribMulAction.toAddEquiv

variable (α β)

/- warning: distrib_mul_action.to_add_aut -> DistribMulAction.toAddAut is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Group.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2], MonoidHom.{u1, u2} α (AddAut.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u2} (AddAut.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))) (DivInvMonoid.toMonoid.{u2} (AddAut.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))) (Group.toDivInvMonoid.{u2} (AddAut.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))) (AddAut.group.{u2} β (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))))))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Group.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2], MonoidHom.{u1, u2} α (AddAut.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u2} (AddAut.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))) (DivInvMonoid.toMonoid.{u2} (AddAut.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))) (Group.toDivInvMonoid.{u2} (AddAut.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))) (AddAut.group.{u2} β (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))))))
Case conversion may be inaccurate. Consider using '#align distrib_mul_action.to_add_aut DistribMulAction.toAddAutₓ'. -/
/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `mul_action.to_perm_hom`. -/
@[simps]
def DistribMulAction.toAddAut : α →* AddAut β
    where
  toFun := DistribMulAction.toAddEquiv β
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' a₁ a₂ := AddEquiv.ext (mul_smul _ _)
#align distrib_mul_action.to_add_aut DistribMulAction.toAddAut

variable {α β}

/- warning: smul_eq_zero_iff_eq -> smul_eq_zero_iff_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2] (a : α) {x : β}, Iff (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2 _inst_3))) a x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))))) (Eq.{succ u2} β x (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2] (a : α) {x : β}, Iff (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2 _inst_3)))) a x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2)))) (Eq.{succ u2} β x (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2))))
Case conversion may be inaccurate. Consider using '#align smul_eq_zero_iff_eq smul_eq_zero_iff_eqₓ'. -/
theorem smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← inv_smul_smul a x, h, smul_zero], fun h => h.symm ▸ smul_zero _⟩
#align smul_eq_zero_iff_eq smul_eq_zero_iff_eq

/- warning: smul_ne_zero_iff_ne -> smul_ne_zero_iff_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2] (a : α) {x : β}, Iff (Ne.{succ u2} β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2 _inst_3))) a x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))))) (Ne.{succ u2} β x (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2] (a : α) {x : β}, Iff (Ne.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2 _inst_3)))) a x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2)))) (Ne.{succ u2} β x (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2))))
Case conversion may be inaccurate. Consider using '#align smul_ne_zero_iff_ne smul_ne_zero_iff_neₓ'. -/
theorem smul_ne_zero_iff_ne (a : α) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
  not_congr <| smul_eq_zero_iff_eq a
#align smul_ne_zero_iff_ne smul_ne_zero_iff_ne

end Group

section Gwz

variable [GroupWithZero α] [AddMonoid β] [DistribMulAction α β]

/- warning: smul_eq_zero_iff_eq' -> smul_eq_zero_iff_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall {x : β}, Iff (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2 _inst_3))) a x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))))) (Eq.{succ u2} β x (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (forall {x : β}, Iff (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2 _inst_3)))) a x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2)))) (Eq.{succ u2} β x (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2)))))
Case conversion may be inaccurate. Consider using '#align smul_eq_zero_iff_eq' smul_eq_zero_iff_eq'ₓ'. -/
theorem smul_eq_zero_iff_eq' {a : α} (ha : a ≠ 0) {x : β} : a • x = 0 ↔ x = 0 :=
  show Units.mk0 a ha • x = 0 ↔ x = 0 from smul_eq_zero_iff_eq _
#align smul_eq_zero_iff_eq' smul_eq_zero_iff_eq'

/- warning: smul_ne_zero_iff_ne' -> smul_ne_zero_iff_ne' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall {x : β}, Iff (Ne.{succ u2} β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2 _inst_3))) a x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))))) (Ne.{succ u2} β x (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (forall {x : β}, Iff (Ne.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2 _inst_3)))) a x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2)))) (Ne.{succ u2} β x (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2)))))
Case conversion may be inaccurate. Consider using '#align smul_ne_zero_iff_ne' smul_ne_zero_iff_ne'ₓ'. -/
theorem smul_ne_zero_iff_ne' {a : α} (ha : a ≠ 0) {x : β} : a • x ≠ 0 ↔ x ≠ 0 :=
  show Units.mk0 a ha • x ≠ 0 ↔ x ≠ 0 from smul_ne_zero_iff_ne _
#align smul_ne_zero_iff_ne' smul_ne_zero_iff_ne'

end Gwz

end DistribMulAction

section MulDistribMulAction

variable [Group α] [Monoid β] [MulDistribMulAction α β]

variable (β)

/- warning: mul_distrib_mul_action.to_mul_equiv -> MulDistribMulAction.toMulEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (β : Type.{u2}) [_inst_1 : Group.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MulDistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2], α -> (MulEquiv.{u2, u2} β β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} (β : Type.{u2}) [_inst_1 : Group.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MulDistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2], α -> (MulEquiv.{u2, u2} β β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align mul_distrib_mul_action.to_mul_equiv MulDistribMulAction.toMulEquivₓ'. -/
/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `mul_action.to_perm`. -/
@[simps (config := { simpRhs := true })]
def MulDistribMulAction.toMulEquiv (x : α) : β ≃* β :=
  { MulDistribMulAction.toMonoidHom β x, MulAction.toPermHom α β x with }
#align mul_distrib_mul_action.to_mul_equiv MulDistribMulAction.toMulEquiv

variable (α β)

/- warning: mul_distrib_mul_action.to_mul_aut -> MulDistribMulAction.toMulAut is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Group.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MulDistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2], MonoidHom.{u1, u2} α (MulAut.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u2} (MulAut.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (DivInvMonoid.toMonoid.{u2} (MulAut.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (Group.toDivInvMonoid.{u2} (MulAut.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (MulAut.group.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))))))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Group.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MulDistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2], MonoidHom.{u1, u2} α (MulAut.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u2} (MulAut.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (DivInvMonoid.toMonoid.{u2} (MulAut.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (Group.toDivInvMonoid.{u2} (MulAut.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (MulAut.instGroupMulAut.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))))))
Case conversion may be inaccurate. Consider using '#align mul_distrib_mul_action.to_mul_aut MulDistribMulAction.toMulAutₓ'. -/
/-- Each element of the group defines an multiplicative monoid isomorphism.

This is a stronger version of `mul_action.to_perm_hom`. -/
@[simps]
def MulDistribMulAction.toMulAut : α →* MulAut β
    where
  toFun := MulDistribMulAction.toMulEquiv β
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' a₁ a₂ := MulEquiv.ext (mul_smul _ _)
#align mul_distrib_mul_action.to_mul_aut MulDistribMulAction.toMulAut

variable {α β}

end MulDistribMulAction

section Arrow

#print arrowAction /-
/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[to_additive arrowAddAction
      "If `G` acts on `A`, then it acts also on `A → B`, by\n`(g +ᵥ F) a = F (g⁻¹ +ᵥ a)`",
  simps]
def arrowAction {G A B : Type _} [DivisionMonoid G] [MulAction G A] : MulAction G (A → B)
    where
  smul g F a := F (g⁻¹ • a)
  one_smul := by
    intro
    simp only [inv_one, one_smul]
  mul_smul := by
    intros
    simp only [mul_smul, mul_inv_rev]
#align arrow_action arrowAction
-/

attribute [local instance] arrowAction

#print arrowMulDistribMulAction /-
/-- When `B` is a monoid, `arrow_action` is additionally a `mul_distrib_mul_action`. -/
def arrowMulDistribMulAction {G A B : Type _} [Group G] [MulAction G A] [Monoid B] :
    MulDistribMulAction G (A → B) where
  smul_one g := rfl
  smul_mul g f₁ f₂ := rfl
#align arrow_mul_distrib_mul_action arrowMulDistribMulAction
-/

attribute [local instance] arrowMulDistribMulAction

/- warning: mul_aut_arrow -> mulAutArrow is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {A : Type.{u2}} {H : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : MulAction.{u1, u2} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_3 : Monoid.{u3} H], MonoidHom.{u1, max u2 u3} G (MulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toHasMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{max u2 u3} (MulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toHasMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))) (DivInvMonoid.toMonoid.{max u2 u3} (MulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toHasMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))) (Group.toDivInvMonoid.{max u2 u3} (MulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toHasMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))) (MulAut.group.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toHasMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))))))
but is expected to have type
  forall {G : Type.{u1}} {A : Type.{u2}} {H : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : MulAction.{u1, u2} G A (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_3 : Monoid.{u3} H], MonoidHom.{u1, max u2 u3} G (MulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{max u2 u3} (MulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))) (DivInvMonoid.toMonoid.{max u2 u3} (MulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))) (Group.toDivInvMonoid.{max u2 u3} (MulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))) (MulAut.instGroupMulAut.{max u2 u3} (A -> H) (Pi.instMul.{u2, u3} A (fun (ᾰ : A) => H) (fun (i : A) => MulOneClass.toMul.{u3} H (Monoid.toMulOneClass.{u3} H _inst_3)))))))
Case conversion may be inaccurate. Consider using '#align mul_aut_arrow mulAutArrowₓ'. -/
/-- Given groups `G H` with `G` acting on `A`, `G` acts by
  multiplicative automorphisms on `A → H`. -/
@[simps]
def mulAutArrow {G A H} [Group G] [MulAction G A] [Monoid H] : G →* MulAut (A → H) :=
  MulDistribMulAction.toMulAut _ _
#align mul_aut_arrow mulAutArrow

end Arrow

namespace IsUnit

section MulAction

variable [Monoid α] [MulAction α β]

#print IsUnit.smul_left_cancel /-
@[to_additive]
theorem smul_left_cancel {a : α} (ha : IsUnit a) {x y : β} : a • x = a • y ↔ x = y :=
  let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u
#align is_unit.smul_left_cancel IsUnit.smul_left_cancel
-/

end MulAction

section DistribMulAction

variable [Monoid α] [AddMonoid β] [DistribMulAction α β]

/- warning: is_unit.smul_eq_zero -> IsUnit.smul_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 _inst_2] {u : α}, (IsUnit.{u1} α _inst_1 u) -> (forall {x : β}, Iff (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 _inst_2 _inst_3))) u x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))))) (Eq.{succ u2} β x (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_2)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddMonoid.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 _inst_2] {u : α}, (IsUnit.{u1} α _inst_1 u) -> (forall {x : β}, Iff (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_2) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β _inst_2) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 _inst_2 _inst_3)))) u x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2)))) (Eq.{succ u2} β x (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (AddMonoid.toZero.{u2} β _inst_2)))))
Case conversion may be inaccurate. Consider using '#align is_unit.smul_eq_zero IsUnit.smul_eq_zeroₓ'. -/
@[simp]
theorem smul_eq_zero {u : α} (hu : IsUnit u) {x : β} : u • x = 0 ↔ x = 0 :=
  (Exists.elim hu) fun u hu => hu ▸ show u • x = 0 ↔ x = 0 from smul_eq_zero_iff_eq u
#align is_unit.smul_eq_zero IsUnit.smul_eq_zero

end DistribMulAction

end IsUnit

section Smul

variable [Group α] [Monoid β]

/- warning: is_unit_smul_iff -> isUnit_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_3) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_3) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_3)] (g : α) (m : β), Iff (IsUnit.{u2} β _inst_2 (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_3) g m)) (IsUnit.{u2} β _inst_2 m)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] [_inst_4 : SMulCommClass.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_3) (MulAction.toSMul.{u2, u2} β β _inst_2 (Monoid.toMulAction.{u2} β _inst_2))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_3) (MulAction.toSMul.{u2, u2} β β _inst_2 (Monoid.toMulAction.{u2} β _inst_2)) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_3)] (g : α) (m : β), Iff (IsUnit.{u2} β _inst_2 (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_3)) g m)) (IsUnit.{u2} β _inst_2 m)
Case conversion may be inaccurate. Consider using '#align is_unit_smul_iff isUnit_smul_iffₓ'. -/
@[simp]
theorem isUnit_smul_iff [MulAction α β] [SMulCommClass α β β] [IsScalarTower α β β] (g : α)
    (m : β) : IsUnit (g • m) ↔ IsUnit m :=
  ⟨fun h => inv_smul_smul g m ▸ h.smul g⁻¹, IsUnit.smul g⟩
#align is_unit_smul_iff isUnit_smul_iff

/- warning: is_unit.smul_sub_iff_sub_inv_smul -> IsUnit.smul_sub_iff_sub_inv_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : AddGroup.{u2} β] [_inst_4 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4))) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4)))] [_inst_6 : SMulCommClass.{u1, u2, u2} α β β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4))) (Mul.toSMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)))] (r : α) (a : β), Iff (IsUnit.{u2} β _inst_2 (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4))) r (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)))))) a)) (IsUnit.{u2} β _inst_2 (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))))) (SMul.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) r) a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : AddGroup.{u2} β] [_inst_4 : DistribMulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))] [_inst_5 : IsScalarTower.{u1, u2, u2} α β β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4))) (MulAction.toSMul.{u2, u2} β β _inst_2 (Monoid.toMulAction.{u2} β _inst_2)) (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4)))] [_inst_6 : SMulCommClass.{u1, u2, u2} α β β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4))) (MulAction.toSMul.{u2, u2} β β _inst_2 (Monoid.toMulAction.{u2} β _inst_2))] (r : α) (a : β), Iff (IsUnit.{u2} β _inst_2 (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4)))) r (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (Monoid.toOne.{u2} β _inst_2)))) a)) (IsUnit.{u2} β _inst_2 (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (Monoid.toOne.{u2} β _inst_2))) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) (DistribMulAction.toDistribSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)) _inst_4)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) r) a)))
Case conversion may be inaccurate. Consider using '#align is_unit.smul_sub_iff_sub_inv_smul IsUnit.smul_sub_iff_sub_inv_smulₓ'. -/
theorem IsUnit.smul_sub_iff_sub_inv_smul [AddGroup β] [DistribMulAction α β] [IsScalarTower α β β]
    [SMulCommClass α β β] (r : α) (a : β) : IsUnit (r • 1 - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]
#align is_unit.smul_sub_iff_sub_inv_smul IsUnit.smul_sub_iff_sub_inv_smul

end Smul

