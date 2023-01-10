/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.submonoid.center
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.GroupTheory.Subsemigroup.Center

/-!
# Centers of monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `submonoid.center`: the center of a monoid
* `add_submonoid.center`: the center of an additive monoid

We provide `subgroup.center`, `add_subgroup.center`, `subsemiring.center`, and `subring.center` in
other files.
-/


namespace Submonoid

section

variable (M : Type _) [Monoid M]

#print Submonoid.center /-
/-- The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a monoid `M` is the set of elements that commute with everything in\n`M`"]
def center : Submonoid M where
  carrier := Set.center M
  one_mem' := Set.one_mem_center M
  mul_mem' a b := Set.mul_mem_center
#align submonoid.center Submonoid.center
-/

/- warning: submonoid.coe_center -> Submonoid.coe_center is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (Submonoid.center.{u1} M _inst_1)) (Set.center.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.center.{u1} M _inst_1)) (Set.center.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_center Submonoid.coe_centerₓ'. -/
@[to_additive]
theorem coe_center : ↑(center M) = Set.center M :=
  rfl
#align submonoid.coe_center Submonoid.coe_center

/- warning: submonoid.center_to_subsemigroup -> Submonoid.center_toSubsemigroup is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Subsemigroup.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.toSubsemigroup.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Submonoid.center.{u1} M _inst_1)) (Subsemigroup.center.{u1} M (Monoid.toSemigroup.{u1} M _inst_1))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Subsemigroup.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.toSubsemigroup.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Submonoid.center.{u1} M _inst_1)) (Subsemigroup.center.{u1} M (Monoid.toSemigroup.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.center_to_subsemigroup Submonoid.center_toSubsemigroupₓ'. -/
@[simp]
theorem center_toSubsemigroup : (center M).toSubsemigroup = Subsemigroup.center M :=
  rfl
#align submonoid.center_to_subsemigroup Submonoid.center_toSubsemigroup

/- warning: add_submonoid.center_to_add_subsemigroup -> AddSubmonoid.center_toAddSubsemigroup is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_2 : AddMonoid.{u1} M], Eq.{succ u1} (AddSubsemigroup.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_2))) (AddSubmonoid.toAddSubsemigroup.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_2) (AddSubmonoid.center.{u1} M _inst_2)) (AddSubsemigroup.center.{u1} M (AddMonoid.toAddSemigroup.{u1} M _inst_2))
but is expected to have type
  forall (M : Type.{u1}) [_inst_2 : AddMonoid.{u1} M], Eq.{succ u1} (AddSubsemigroup.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_2))) (AddSubmonoid.toAddSubsemigroup.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_2) (AddSubmonoid.center.{u1} M _inst_2)) (AddSubsemigroup.center.{u1} M (AddMonoid.toAddSemigroup.{u1} M _inst_2))
Case conversion may be inaccurate. Consider using '#align add_submonoid.center_to_add_subsemigroup AddSubmonoid.center_toAddSubsemigroupₓ'. -/
theorem AddSubmonoid.center_toAddSubsemigroup (M) [AddMonoid M] :
    (AddSubmonoid.center M).toAddSubsemigroup = AddSubsemigroup.center M :=
  rfl
#align add_submonoid.center_to_add_subsemigroup AddSubmonoid.center_toAddSubsemigroup

attribute [to_additive AddSubmonoid.center_toAddSubsemigroup] Submonoid.center_toSubsemigroup

variable {M}

/- warning: submonoid.mem_center_iff -> Submonoid.mem_center_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {z : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) z (Submonoid.center.{u1} M _inst_1)) (forall (g : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) g z) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) z g))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {z : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) z (Submonoid.center.{u1} M _inst_1)) (forall (g : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) g z) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) z g))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_center_iff Submonoid.mem_center_iffₓ'. -/
@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align submonoid.mem_center_iff Submonoid.mem_center_iff

/- warning: submonoid.decidable_mem_center -> Submonoid.decidableMemCenter is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M) [_inst_2 : Decidable (forall (b : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) b a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b))], Decidable (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a (Submonoid.center.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M) [_inst_2 : Decidable (forall (b : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) b a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b))], Decidable (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a (Submonoid.center.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.decidable_mem_center Submonoid.decidableMemCenterₓ'. -/
@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ mem_center_iff
#align submonoid.decidable_mem_center Submonoid.decidableMemCenter

/-- The center of a monoid is commutative. -/
instance : CommMonoid (center M) :=
  { (center M).toMonoid with mul_comm := fun a b => Subtype.ext <| b.Prop _ }

/- warning: submonoid.center.smul_comm_class_left -> Submonoid.center.smulCommClass_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], SMulCommClass.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.center.{u1} M _inst_1)) M M (Submonoid.hasSmul.{u1, u1} M M (Monoid.toMulOneClass.{u1} M _inst_1) (Mul.toSMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.center.{u1} M _inst_1)) (Mul.toSMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], SMulCommClass.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.center.{u1} M _inst_1))) M M (Submonoid.instSMulSubtypeMemSubmonoidInstMembershipInstSetLikeSubmonoid.{u1, u1} M M (Monoid.toMulOneClass.{u1} M _inst_1) (MulAction.toSMul.{u1, u1} M M _inst_1 (Monoid.toMulAction.{u1} M _inst_1)) (Submonoid.center.{u1} M _inst_1)) (MulAction.toSMul.{u1, u1} M M _inst_1 (Monoid.toMulAction.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.center.smul_comm_class_left Submonoid.center.smulCommClass_leftₓ'. -/
/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smulCommClass_left : SMulCommClass (center M) M M
    where smul_comm m x y := (Commute.left_comm (m.Prop x) y).symm
#align submonoid.center.smul_comm_class_left Submonoid.center.smulCommClass_left

/- warning: submonoid.center.smul_comm_class_right -> Submonoid.center.smulCommClass_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], SMulCommClass.{u1, u1, u1} M (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.center.{u1} M _inst_1)) M (Mul.toSMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.hasSmul.{u1, u1} M M (Monoid.toMulOneClass.{u1} M _inst_1) (Mul.toSMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.center.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], SMulCommClass.{u1, u1, u1} M (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.center.{u1} M _inst_1))) M (MulAction.toSMul.{u1, u1} M M _inst_1 (Monoid.toMulAction.{u1} M _inst_1)) (Submonoid.instSMulSubtypeMemSubmonoidInstMembershipInstSetLikeSubmonoid.{u1, u1} M M (Monoid.toMulOneClass.{u1} M _inst_1) (MulAction.toSMul.{u1, u1} M M _inst_1 (Monoid.toMulAction.{u1} M _inst_1)) (Submonoid.center.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.center.smul_comm_class_right Submonoid.center.smulCommClass_rightₓ'. -/
/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smulCommClass_right : SMulCommClass M (center M) M :=
  SMulCommClass.symm _ _ _
#align submonoid.center.smul_comm_class_right Submonoid.center.smulCommClass_right

/-! Note that `smul_comm_class (center M) (center M) M` is already implied by
`submonoid.smul_comm_class_right` -/


example : SMulCommClass (center M) (center M) M := by infer_instance

end

section

variable (M : Type _) [CommMonoid M]

/- warning: submonoid.center_eq_top -> Submonoid.center_eq_top is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : CommMonoid.{u1} M], Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Submonoid.center.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : CommMonoid.{u1} M], Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Submonoid.center.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align submonoid.center_eq_top Submonoid.center_eq_topₓ'. -/
@[simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align submonoid.center_eq_top Submonoid.center_eq_top

end

end Submonoid

-- Guard against import creep
assert_not_exists finset

