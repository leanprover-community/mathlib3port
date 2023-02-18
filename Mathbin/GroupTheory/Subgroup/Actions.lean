/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.subgroup.actions
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Actions by `subgroup`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are just copies of the definitions about `submonoid` starting from `submonoid.mul_action`.

## Tags
subgroup, subgroups

-/


namespace Subgroup

variable {G : Type _} [Group G]

variable {α β : Type _}

/-- The action by a subgroup is the action by the underlying group. -/
@[to_additive "The additive action by an add_subgroup is the action by the underlying\nadd_group. "]
instance [MulAction G α] (S : Subgroup G) : MulAction S α :=
  S.toSubmonoid.MulAction

/- warning: subgroup.smul_def -> Subgroup.smul_def is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {α : Type.{u2}} [_inst_2 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] {S : Subgroup.{u1} G _inst_1} (g : coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) (m : α), Eq.{succ u2} α (SMul.smul.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) α (MulAction.toHasSmul.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) α (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) (Subgroup.toGroup.{u1} G _inst_1 S))) (Subgroup.mulAction.{u1, u2} G _inst_1 α _inst_2 S)) g m) (SMul.smul.{u1, u2} G α (MulAction.toHasSmul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) G (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) G (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) G (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) G (coeSubtype.{succ u1} G (fun (x : G) => Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) x S))))) g) m)
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : Group.{u2} G] {α : Type.{u1}} [_inst_2 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))] {S : Subgroup.{u2} G _inst_1} (g : Subtype.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) x S)) (m : α), Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} (Subtype.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) x S)) α α (instHSMul.{u2, u1} (Subtype.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) x S)) α (Submonoid.smul.{u2, u1} G α (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (MulAction.toSMul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_2) (Subgroup.toSubmonoid.{u2} G _inst_1 S))) g m) (HSMul.hSMul.{u2, u1, u1} G α α (instHSMul.{u2, u1} G α (MulAction.toSMul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) _inst_2)) (Subtype.val.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Set.{u2} G) (Set.instMembershipSet.{u2} G) x (SetLike.coe.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1) S)) g) m)
Case conversion may be inaccurate. Consider using '#align subgroup.smul_def Subgroup.smul_defₓ'. -/
@[to_additive]
theorem smul_def [MulAction G α] {S : Subgroup G} (g : S) (m : α) : g • m = (g : G) • m :=
  rfl
#align subgroup.smul_def Subgroup.smul_def
#align add_subgroup.vadd_def AddSubgroup.vadd_def

/- warning: subgroup.smul_comm_class_left -> Subgroup.smulCommClass_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : MulAction.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_3 : SMul.{u2, u3} α β] [_inst_4 : SMulCommClass.{u1, u2, u3} G α β (MulAction.toHasSmul.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2) _inst_3] (S : Subgroup.{u1} G _inst_1), SMulCommClass.{u1, u2, u3} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) α β (MulAction.toHasSmul.{u1, u3} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) β (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) (Subgroup.toGroup.{u1} G _inst_1 S))) (Subgroup.mulAction.{u1, u3} G _inst_1 β _inst_2 S)) _inst_3
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : MulAction.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_3 : SMul.{u2, u3} α β] [_inst_4 : SMulCommClass.{u1, u2, u3} G α β (MulAction.toSMul.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2) _inst_3] (S : Subgroup.{u1} G _inst_1), SMulCommClass.{u1, u2, u3} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x S)) α β (Submonoid.smul.{u1, u3} G β (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulAction.toSMul.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2) (Subgroup.toSubmonoid.{u1} G _inst_1 S)) _inst_3
Case conversion may be inaccurate. Consider using '#align subgroup.smul_comm_class_left Subgroup.smulCommClass_leftₓ'. -/
@[to_additive]
instance smulCommClass_left [MulAction G β] [SMul α β] [SMulCommClass G α β] (S : Subgroup G) :
    SMulCommClass S α β :=
  S.toSubmonoid.smulCommClass_left
#align subgroup.smul_comm_class_left Subgroup.smulCommClass_left
#align add_subgroup.vadd_comm_class_left AddSubgroup.vaddCommClass_left

/- warning: subgroup.smul_comm_class_right -> Subgroup.smulCommClass_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : SMul.{u2, u3} α β] [_inst_3 : MulAction.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMulCommClass.{u2, u1, u3} α G β _inst_2 (MulAction.toHasSmul.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)] (S : Subgroup.{u1} G _inst_1), SMulCommClass.{u2, u1, u3} α (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) β _inst_2 (MulAction.toHasSmul.{u1, u3} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) β (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) S) (Subgroup.toGroup.{u1} G _inst_1 S))) (Subgroup.mulAction.{u1, u3} G _inst_1 β _inst_3 S))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {α : Type.{u2}} {β : Type.{u3}} [_inst_2 : SMul.{u2, u3} α β] [_inst_3 : MulAction.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] [_inst_4 : SMulCommClass.{u2, u1, u3} α G β _inst_2 (MulAction.toSMul.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3)] (S : Subgroup.{u1} G _inst_1), SMulCommClass.{u2, u1, u3} α (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x S)) β _inst_2 (Submonoid.smul.{u1, u3} G β (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulAction.toSMul.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_3) (Subgroup.toSubmonoid.{u1} G _inst_1 S))
Case conversion may be inaccurate. Consider using '#align subgroup.smul_comm_class_right Subgroup.smulCommClass_rightₓ'. -/
@[to_additive]
instance smulCommClass_right [SMul α β] [MulAction G β] [SMulCommClass α G β] (S : Subgroup G) :
    SMulCommClass α S β :=
  S.toSubmonoid.smulCommClass_right
#align subgroup.smul_comm_class_right Subgroup.smulCommClass_right
#align add_subgroup.vadd_comm_class_right AddSubgroup.vaddCommClass_right

/-- Note that this provides `is_scalar_tower S G G` which is needed by `smul_mul_assoc`. -/
instance [SMul α β] [MulAction G α] [MulAction G β] [IsScalarTower G α β] (S : Subgroup G) :
    IsScalarTower S α β :=
  S.toSubmonoid.IsScalarTower

instance [MulAction G α] [FaithfulSMul G α] (S : Subgroup G) : FaithfulSMul S α :=
  S.toSubmonoid.FaithfulSMul

/-- The action by a subgroup is the action by the underlying group. -/
instance [AddMonoid α] [DistribMulAction G α] (S : Subgroup G) : DistribMulAction S α :=
  S.toSubmonoid.DistribMulAction

/-- The action by a subgroup is the action by the underlying group. -/
instance [Monoid α] [MulDistribMulAction G α] (S : Subgroup G) : MulDistribMulAction S α :=
  S.toSubmonoid.MulDistribMulAction

/- warning: subgroup.center.smul_comm_class_left -> Subgroup.center.smulCommClass_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], SMulCommClass.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) G G (MulAction.toHasSmul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) G (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) (Subgroup.toGroup.{u1} G _inst_1 (Subgroup.center.{u1} G _inst_1)))) (Subgroup.mulAction.{u1, u1} G _inst_1 G (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.center.{u1} G _inst_1))) (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], SMulCommClass.{u1, u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Subgroup.center.{u1} G _inst_1))) G G (Submonoid.smul.{u1, u1} G G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (Subgroup.toSubmonoid.{u1} G _inst_1 (Subgroup.center.{u1} G _inst_1))) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align subgroup.center.smul_comm_class_left Subgroup.center.smulCommClass_leftₓ'. -/
/-- The center of a group acts commutatively on that group. -/
instance center.smulCommClass_left : SMulCommClass (center G) G G :=
  Submonoid.center.smulCommClass_left
#align subgroup.center.smul_comm_class_left Subgroup.center.smulCommClass_left

/- warning: subgroup.center.smul_comm_class_right -> Subgroup.center.smulCommClass_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], SMulCommClass.{u1, u1, u1} G (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) G (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (MulAction.toHasSmul.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) G (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Subgroup.center.{u1} G _inst_1)) (Subgroup.toGroup.{u1} G _inst_1 (Subgroup.center.{u1} G _inst_1)))) (Subgroup.mulAction.{u1, u1} G _inst_1 G (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Subgroup.center.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], SMulCommClass.{u1, u1, u1} G (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Subgroup.center.{u1} G _inst_1))) G (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (Submonoid.smul.{u1, u1} G G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (Subgroup.toSubmonoid.{u1} G _inst_1 (Subgroup.center.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.center.smul_comm_class_right Subgroup.center.smulCommClass_rightₓ'. -/
/-- The center of a group acts commutatively on that group. -/
instance center.smulCommClass_right : SMulCommClass G (center G) G :=
  Submonoid.center.smulCommClass_right
#align subgroup.center.smul_comm_class_right Subgroup.center.smulCommClass_right

end Subgroup

