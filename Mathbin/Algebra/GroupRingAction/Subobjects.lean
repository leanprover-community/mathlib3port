/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.group_ring_action.subobjects
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Instances of `mul_semiring_action` for subobjects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are defined in this file as `semiring`s are not available yet where `submonoid` and `subgroup`
are defined.

Instances for `subsemiring` and `subring` are provided next to the other scalar actions instances
for those subobjects.

-/


variable {M G R : Type _}

variable [Monoid M] [Group G] [Semiring R]

/- warning: submonoid.mul_semiring_action -> Submonoid.mulSemiringAction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : Semiring.{u2} R] [_inst_4 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_3] (H : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)), MulSemiringAction.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) H) R (Submonoid.toMonoid.{u1} M _inst_1 H) _inst_3
but is expected to have type
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : Semiring.{u2} R] [_inst_4 : MulSemiringAction.{u1, u2} M R _inst_1 _inst_3] (H : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)), MulSemiringAction.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x H)) R (Submonoid.toMonoid.{u1} M _inst_1 H) _inst_3
Case conversion may be inaccurate. Consider using '#align submonoid.mul_semiring_action Submonoid.mulSemiringActionₓ'. -/
/-- A stronger version of `submonoid.distrib_mul_action`. -/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) :
    MulSemiringAction H R :=
  { H.MulDistribMulAction, H.DistribMulAction with smul := (· • ·) }
#align submonoid.mul_semiring_action Submonoid.mulSemiringAction

/- warning: subgroup.mul_semiring_action -> Subgroup.mulSemiringAction is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {R : Type.{u2}} [_inst_2 : Group.{u1} G] [_inst_3 : Semiring.{u2} R] [_inst_4 : MulSemiringAction.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3] (H : Subgroup.{u1} G _inst_2), MulSemiringAction.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) H) R (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) H) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.setLike.{u1} G _inst_2)) H) (Subgroup.toGroup.{u1} G _inst_2 H))) _inst_3
but is expected to have type
  forall {G : Type.{u1}} {R : Type.{u2}} [_inst_2 : Group.{u1} G] [_inst_3 : Semiring.{u2} R] [_inst_4 : MulSemiringAction.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3] (H : Subgroup.{u1} G _inst_2), MulSemiringAction.{u1, u2} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_2) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_2)) x H)) R (Submonoid.toMonoid.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Subgroup.toSubmonoid.{u1} G _inst_2 H)) _inst_3
Case conversion may be inaccurate. Consider using '#align subgroup.mul_semiring_action Subgroup.mulSemiringActionₓ'. -/
/-- A stronger version of `subgroup.distrib_mul_action`. -/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) :
    MulSemiringAction H R :=
  H.toSubmonoid.MulSemiringAction
#align subgroup.mul_semiring_action Subgroup.mulSemiringAction

