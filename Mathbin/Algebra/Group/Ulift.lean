/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.group.ulift
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Defs
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.GroupWithZero.InjSurj

/-!
# `ulift` instances for groups and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for group, monoid, semigroup and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We use `tactic.pi_instance_derive_field`, even though it wasn't intended for this purpose,
which seems to work fine.

We also provide `ulift.mul_equiv : ulift R ≃* R` (and its additive analogue).
-/


universe u v

variable {α : Type u} {β : Type _} {x y : ULift.{v} α}

namespace ULift

#print ULift.one /-
@[to_additive]
instance one [One α] : One (ULift α) :=
  ⟨⟨1⟩⟩
#align ulift.has_one ULift.one
-/

/- warning: ulift.one_down -> ULift.one_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α], Eq.{succ u1} α (ULift.down.{u2, u1} α (OfNat.ofNat.{max u1 u2} (ULift.{u2, u1} α) 1 (OfNat.mk.{max u1 u2} (ULift.{u2, u1} α) 1 (One.one.{max u1 u2} (ULift.{u2, u1} α) (ULift.one.{u1, u2} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : One.{u2} α], Eq.{succ u2} α (ULift.down.{u1, u2} α (OfNat.ofNat.{max u2 u1} (ULift.{u1, u2} α) 1 (One.toOfNat1.{max u2 u1} (ULift.{u1, u2} α) (ULift.one.{u2, u1} α _inst_1)))) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align ulift.one_down ULift.one_downₓ'. -/
@[simp, to_additive]
theorem one_down [One α] : (1 : ULift α).down = 1 :=
  rfl
#align ulift.one_down ULift.one_down

#print ULift.mul /-
@[to_additive]
instance mul [Mul α] : Mul (ULift α) :=
  ⟨fun f g => ⟨f.down * g.down⟩⟩
#align ulift.has_mul ULift.mul
-/

#print ULift.mul_down /-
@[simp, to_additive]
theorem mul_down [Mul α] : (x * y).down = x.down * y.down :=
  rfl
#align ulift.mul_down ULift.mul_down
-/

#print ULift.div /-
@[to_additive]
instance div [Div α] : Div (ULift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩
#align ulift.has_div ULift.div
-/

#print ULift.div_down /-
@[simp, to_additive]
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl
#align ulift.div_down ULift.div_down
-/

#print ULift.inv /-
@[to_additive]
instance inv [Inv α] : Inv (ULift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩
#align ulift.has_inv ULift.inv
-/

#print ULift.inv_down /-
@[simp, to_additive]
theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ :=
  rfl
#align ulift.inv_down ULift.inv_down
-/

/- warning: ulift.has_smul -> ULift.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSmul.{u1, u2} α β], HasSmul.{u1, max u2 u3} α (ULift.{u3, u2} β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β], SMul.{u1, max u2 u3} α (ULift.{u3, u2} β)
Case conversion may be inaccurate. Consider using '#align ulift.has_smul ULift.smulₓ'. -/
@[to_additive]
instance smul [HasSmul α β] : HasSmul α (ULift β) :=
  ⟨fun n x => up (n • x.down)⟩
#align ulift.has_smul ULift.smul

/- warning: ulift.smul_down -> ULift.smul_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : HasSmul.{u1, u3} α β] (a : α) (b : ULift.{u2, u3} β), Eq.{succ u3} β (ULift.down.{u2, u3} β (HasSmul.smul.{u1, max u3 u2} α (ULift.{u2, u3} β) (ULift.smul.{u1, u3, u2} α β _inst_1) a b)) (HasSmul.smul.{u1, u3} α β _inst_1 a (ULift.down.{u2, u3} β b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : α) (b : ULift.{u3, u1} β), Eq.{succ u1} β (ULift.down.{u3, u1} β (HSMul.hSMul.{u2, max u3 u1, max u3 u1} α (ULift.{u3, u1} β) (ULift.{u3, u1} β) (instHSMul.{u2, max u3 u1} α (ULift.{u3, u1} β) (ULift.smul.{u2, u1, u3} α β _inst_1)) a b)) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a (ULift.down.{u3, u1} β b))
Case conversion may be inaccurate. Consider using '#align ulift.smul_down ULift.smul_downₓ'. -/
@[simp, to_additive]
theorem smul_down [HasSmul α β] (a : α) (b : ULift.{v} β) : (a • b).down = a • b.down :=
  rfl
#align ulift.smul_down ULift.smul_down

#print ULift.pow /-
@[to_additive HasSmul, to_additive_reorder 1]
instance pow [Pow α β] : Pow (ULift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩
#align ulift.has_pow ULift.pow
-/

/- warning: ulift.pow_down -> ULift.pow_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : Pow.{u1, u3} α β] (a : ULift.{u2, u1} α) (b : β), Eq.{succ u1} α (ULift.down.{u2, u1} α (HPow.hPow.{max u1 u2, u3, max u1 u2} (ULift.{u2, u1} α) β (ULift.{u2, u1} α) (instHPow.{max u1 u2, u3} (ULift.{u2, u1} α) β (ULift.pow.{u1, u3, u2} α β _inst_1)) a b)) (HPow.hPow.{u1, u3, u1} α β α (instHPow.{u1, u3} α β _inst_1) (ULift.down.{u2, u1} α a) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : ULift.{u3, u2} α) (b : β), Eq.{succ u2} α (ULift.down.{u3, u2} α (HPow.hPow.{max u2 u3, u1, max u2 u3} (ULift.{u3, u2} α) β (ULift.{u3, u2} α) (instHPow.{max u2 u3, u1} (ULift.{u3, u2} α) β (ULift.pow.{u2, u1, u3} α β _inst_1)) a b)) (HPow.hPow.{u2, u1, u2} α β α (instHPow.{u2, u1} α β _inst_1) (ULift.down.{u3, u2} α a) b)
Case conversion may be inaccurate. Consider using '#align ulift.pow_down ULift.pow_downₓ'. -/
@[simp, to_additive smul_down, to_additive_reorder 1]
theorem pow_down [Pow α β] (a : ULift.{v} α) (b : β) : (a ^ b).down = a.down ^ b :=
  rfl
#align ulift.pow_down ULift.pow_down

#print ULift.MulEquiv.ulift /-
/-- The multiplicative equivalence between `ulift α` and `α`.
-/
@[to_additive "The additive equivalence between `ulift α` and `α`."]
def ULift.MulEquiv.ulift [Mul α] : ULift α ≃* α :=
  { Equiv.ulift with map_mul' := fun x y => rfl }
#align mul_equiv.ulift ULift.MulEquiv.ulift
-/

#print ULift.semigroup /-
@[to_additive]
instance semigroup [Semigroup α] : Semigroup (ULift α) :=
  (ULift.MulEquiv.ulift.Injective.Semigroup _) fun x y => rfl
#align ulift.semigroup ULift.semigroup
-/

#print ULift.commSemigroup /-
@[to_additive]
instance commSemigroup [CommSemigroup α] : CommSemigroup (ULift α) :=
  (Equiv.ulift.Injective.CommSemigroup _) fun x y => rfl
#align ulift.comm_semigroup ULift.commSemigroup
-/

#print ULift.mulOneClass /-
@[to_additive]
instance mulOneClass [MulOneClass α] : MulOneClass (ULift α) :=
  (Equiv.ulift.Injective.MulOneClass _ rfl) fun x y => rfl
#align ulift.mul_one_class ULift.mulOneClass
-/

#print ULift.mulZeroOneClass /-
instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass (ULift α) :=
  (Equiv.ulift.Injective.MulZeroOneClass _ rfl rfl) fun x y => rfl
#align ulift.mul_zero_one_class ULift.mulZeroOneClass
-/

#print ULift.monoid /-
@[to_additive]
instance monoid [Monoid α] : Monoid (ULift α) :=
  Equiv.ulift.Injective.Monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.monoid ULift.monoid
-/

#print ULift.addMonoidWithOne /-
instance addMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (ULift α) :=
  { ULift.one, ULift.addMonoid with
    natCast := fun n => ⟨n⟩
    nat_cast_zero := congr_arg ULift.up Nat.cast_zero
    nat_cast_succ := fun n => congr_arg ULift.up (Nat.cast_succ _) }
#align ulift.add_monoid_with_one ULift.addMonoidWithOne
-/

/- warning: ulift.nat_cast_down -> ULift.nat_cast_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] (n : Nat), Eq.{succ u1} α (ULift.down.{u2, u1} α ((fun (a : Type) (b : Type.{max u1 u2}) [self : HasLiftT.{1, succ (max u1 u2)} a b] => self.0) Nat (ULift.{u2, u1} α) (HasLiftT.mk.{1, succ (max u1 u2)} Nat (ULift.{u2, u1} α) (CoeTCₓ.coe.{1, succ (max u1 u2)} Nat (ULift.{u2, u1} α) (Nat.castCoe.{max u1 u2} (ULift.{u2, u1} α) (AddMonoidWithOne.toNatCast.{max u1 u2} (ULift.{u2, u1} α) (ULift.addMonoidWithOne.{u1, u2} α _inst_1))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α _inst_1)))) n)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : AddMonoidWithOne.{u2} α] (n : Nat), Eq.{succ u2} α (ULift.down.{u1, u2} α (Nat.cast.{max u2 u1} (ULift.{u1, u2} α) (AddMonoidWithOne.toNatCast.{max u2 u1} (ULift.{u1, u2} α) (ULift.addMonoidWithOne.{u2, u1} α _inst_1)) n)) (Nat.cast.{u2} α (AddMonoidWithOne.toNatCast.{u2} α _inst_1) n)
Case conversion may be inaccurate. Consider using '#align ulift.nat_cast_down ULift.nat_cast_downₓ'. -/
@[simp]
theorem nat_cast_down [AddMonoidWithOne α] (n : ℕ) : (n : ULift α).down = n :=
  rfl
#align ulift.nat_cast_down ULift.nat_cast_down

#print ULift.commMonoid /-
@[to_additive]
instance commMonoid [CommMonoid α] : CommMonoid (ULift α) :=
  Equiv.ulift.Injective.CommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_monoid ULift.commMonoid
-/

#print ULift.monoidWithZero /-
instance monoidWithZero [MonoidWithZero α] : MonoidWithZero (ULift α) :=
  Equiv.ulift.Injective.MonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.monoid_with_zero ULift.monoidWithZero
-/

#print ULift.commMonoidWithZero /-
instance commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α) :=
  Equiv.ulift.Injective.CommMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_monoid_with_zero ULift.commMonoidWithZero
-/

#print ULift.divInvMonoid /-
@[to_additive]
instance divInvMonoid [DivInvMonoid α] : DivInvMonoid (ULift α) :=
  Equiv.ulift.Injective.DivInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.div_inv_monoid ULift.divInvMonoid
-/

#print ULift.group /-
@[to_additive]
instance group [Group α] : Group (ULift α) :=
  Equiv.ulift.Injective.Group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.group ULift.group
-/

#print ULift.addGroupWithOne /-
instance addGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (ULift α) :=
  { ULift.addMonoidWithOne,
    ULift.addGroup with
    intCast := fun n => ⟨n⟩
    int_cast_of_nat := fun n => congr_arg ULift.up (Int.cast_of_nat _)
    int_cast_neg_succ_of_nat := fun n => congr_arg ULift.up (Int.cast_negSucc _) }
#align ulift.add_group_with_one ULift.addGroupWithOne
-/

/- warning: ulift.int_cast_down -> ULift.int_cast_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] (n : Int), Eq.{succ u1} α (ULift.down.{u2, u1} α ((fun (a : Type) (b : Type.{max u1 u2}) [self : HasLiftT.{1, succ (max u1 u2)} a b] => self.0) Int (ULift.{u2, u1} α) (HasLiftT.mk.{1, succ (max u1 u2)} Int (ULift.{u2, u1} α) (CoeTCₓ.coe.{1, succ (max u1 u2)} Int (ULift.{u2, u1} α) (Int.castCoe.{max u1 u2} (ULift.{u2, u1} α) (AddGroupWithOne.toHasIntCast.{max u1 u2} (ULift.{u2, u1} α) (ULift.addGroupWithOne.{u1, u2} α _inst_1))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) n)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : AddGroupWithOne.{u2} α] (n : Int), Eq.{succ u2} α (ULift.down.{u1, u2} α (Int.cast.{max u2 u1} (ULift.{u1, u2} α) (AddGroupWithOne.toIntCast.{max u2 u1} (ULift.{u1, u2} α) (ULift.addGroupWithOne.{u2, u1} α _inst_1)) n)) (Int.cast.{u2} α (AddGroupWithOne.toIntCast.{u2} α _inst_1) n)
Case conversion may be inaccurate. Consider using '#align ulift.int_cast_down ULift.int_cast_downₓ'. -/
@[simp]
theorem int_cast_down [AddGroupWithOne α] (n : ℤ) : (n : ULift α).down = n :=
  rfl
#align ulift.int_cast_down ULift.int_cast_down

#print ULift.commGroup /-
@[to_additive]
instance commGroup [CommGroup α] : CommGroup (ULift α) :=
  Equiv.ulift.Injective.CommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_group ULift.commGroup
-/

#print ULift.groupWithZero /-
instance groupWithZero [GroupWithZero α] : GroupWithZero (ULift α) :=
  Equiv.ulift.Injective.GroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.group_with_zero ULift.groupWithZero
-/

#print ULift.commGroupWithZero /-
instance commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α) :=
  Equiv.ulift.Injective.CommGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_group_with_zero ULift.commGroupWithZero
-/

#print ULift.leftCancelSemigroup /-
@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (ULift α) :=
  Equiv.ulift.Injective.LeftCancelSemigroup _ fun _ _ => rfl
#align ulift.left_cancel_semigroup ULift.leftCancelSemigroup
-/

#print ULift.rightCancelSemigroup /-
@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (ULift α) :=
  Equiv.ulift.Injective.RightCancelSemigroup _ fun _ _ => rfl
#align ulift.right_cancel_semigroup ULift.rightCancelSemigroup
-/

#print ULift.leftCancelMonoid /-
@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (ULift α) :=
  Equiv.ulift.Injective.LeftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.left_cancel_monoid ULift.leftCancelMonoid
-/

#print ULift.rightCancelMonoid /-
@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (ULift α) :=
  Equiv.ulift.Injective.RightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.right_cancel_monoid ULift.rightCancelMonoid
-/

#print ULift.cancelMonoid /-
@[to_additive AddCancelMonoid]
instance cancelMonoid [CancelMonoid α] : CancelMonoid (ULift α) :=
  Equiv.ulift.Injective.CancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.cancel_monoid ULift.cancelMonoid
-/

#print ULift.cancelCommMonoid /-
@[to_additive AddCancelMonoid]
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (ULift α) :=
  Equiv.ulift.Injective.CancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.cancel_comm_monoid ULift.cancelCommMonoid
-/

#print ULift.nontrivial /-
instance nontrivial [Nontrivial α] : Nontrivial (ULift α) :=
  Equiv.ulift.symm.Injective.Nontrivial
#align ulift.nontrivial ULift.nontrivial
-/

-- TODO we don't do `ordered_cancel_comm_monoid` or `ordered_comm_group`
-- We'd need to add instances for `ulift` in `order.basic`.
end ULift

