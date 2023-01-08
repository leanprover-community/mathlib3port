/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux

! This file was ported from Lean 3 source module group_theory.subsemigroup.center
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Defs
import Mathbin.GroupTheory.Subsemigroup.Operations

/-!
# Centers of magmas and semigroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `set.center`: the center of a magma
* `subsemigroup.center`: the center of a semigroup
* `set.add_center`: the center of an additive magma
* `add_subsemigroup.center`: the center of an additive semigroup

We provide `submonoid.center`, `add_submonoid.center`, `subgroup.center`, `add_subgroup.center`,
`subsemiring.center`, and `subring.center` in other files.
-/


variable {M : Type _}

namespace Set

variable (M)

#print Set.center /-
/-- The center of a magma. -/
@[to_additive add_center " The center of an additive magma. "]
def center [Mul M] : Set M :=
  { z | ∀ m, m * z = z * m }
#align set.center Set.center
-/

#print Set.mem_center_iff /-
@[to_additive mem_add_center]
theorem mem_center_iff [Mul M] {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align set.mem_center_iff Set.mem_center_iff
-/

#print Set.decidableMemCenter /-
instance decidableMemCenter [Mul M] [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (mem_center_iff M)
#align set.decidable_mem_center Set.decidableMemCenter
-/

/- warning: set.one_mem_center -> Set.one_mem_center is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M], Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) (Set.center.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M], Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) (Set.center.{u1} M (MulOneClass.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align set.one_mem_center Set.one_mem_centerₓ'. -/
@[simp, to_additive zero_mem_add_center]
theorem one_mem_center [MulOneClass M] : (1 : M) ∈ Set.center M := by simp [mem_center_iff]
#align set.one_mem_center Set.one_mem_center

/- warning: set.zero_mem_center -> Set.zero_mem_center is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : MulZeroClass.{u1} M], Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (MulZeroClass.toHasZero.{u1} M _inst_1)))) (Set.center.{u1} M (MulZeroClass.toHasMul.{u1} M _inst_1))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : MulZeroClass.{u1} M], Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (MulZeroClass.toZero.{u1} M _inst_1))) (Set.center.{u1} M (MulZeroClass.toMul.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align set.zero_mem_center Set.zero_mem_centerₓ'. -/
@[simp]
theorem zero_mem_center [MulZeroClass M] : (0 : M) ∈ Set.center M := by simp [mem_center_iff]
#align set.zero_mem_center Set.zero_mem_center

variable {M}

/- warning: set.mul_mem_center -> Set.mul_mem_center is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Semigroup.{u1} M] {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.center.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b (Set.center.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) a b) (Set.center.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Semigroup.{u1} M] {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.center.{u1} M (Semigroup.toMul.{u1} M _inst_1))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b (Set.center.{u1} M (Semigroup.toMul.{u1} M _inst_1))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) a b) (Set.center.{u1} M (Semigroup.toMul.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.mul_mem_center Set.mul_mem_centerₓ'. -/
@[simp, to_additive add_mem_add_center]
theorem mul_mem_center [Semigroup M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a * b ∈ Set.center M := fun g => by rw [mul_assoc, ← hb g, ← mul_assoc, ha g, mul_assoc]
#align set.mul_mem_center Set.mul_mem_center

/- warning: set.inv_mem_center -> Set.inv_mem_center is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] {a : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.center.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (Inv.inv.{u1} M (DivInvMonoid.toHasInv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)) a) (Set.center.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] {a : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.center.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (Inv.inv.{u1} M (InvOneClass.toInv.{u1} M (DivInvOneMonoid.toInvOneClass.{u1} M (DivisionMonoid.toDivInvOneMonoid.{u1} M (Group.toDivisionMonoid.{u1} M _inst_1)))) a) (Set.center.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.inv_mem_center Set.inv_mem_centerₓ'. -/
@[simp, to_additive neg_mem_add_center]
theorem inv_mem_center [Group M] {a : M} (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := fun g => by
  rw [← inv_inj, mul_inv_rev, inv_inv, ← ha, mul_inv_rev, inv_inv]
#align set.inv_mem_center Set.inv_mem_center

/- warning: set.add_mem_center -> Set.add_mem_center is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Distrib.{u1} M] {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.center.{u1} M (Distrib.toHasMul.{u1} M _inst_1))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b (Set.center.{u1} M (Distrib.toHasMul.{u1} M _inst_1))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (Distrib.toHasAdd.{u1} M _inst_1)) a b) (Set.center.{u1} M (Distrib.toHasMul.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Distrib.{u1} M] {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.center.{u1} M (Distrib.toMul.{u1} M _inst_1))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b (Set.center.{u1} M (Distrib.toMul.{u1} M _inst_1))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (Distrib.toAdd.{u1} M _inst_1)) a b) (Set.center.{u1} M (Distrib.toMul.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.add_mem_center Set.add_mem_centerₓ'. -/
@[simp]
theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a + b ∈ Set.center M := fun c => by rw [add_mul, mul_add, ha c, hb c]
#align set.add_mem_center Set.add_mem_center

/- warning: set.neg_mem_center -> Set.neg_mem_center is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Ring.{u1} M] {a : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.center.{u1} M (Distrib.toHasMul.{u1} M (Ring.toDistrib.{u1} M _inst_1)))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (Neg.neg.{u1} M (SubNegMonoid.toHasNeg.{u1} M (AddGroup.toSubNegMonoid.{u1} M (AddGroupWithOne.toAddGroup.{u1} M (NonAssocRing.toAddGroupWithOne.{u1} M (Ring.toNonAssocRing.{u1} M _inst_1))))) a) (Set.center.{u1} M (Distrib.toHasMul.{u1} M (Ring.toDistrib.{u1} M _inst_1))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Ring.{u1} M] {a : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.center.{u1} M (NonUnitalNonAssocRing.toMul.{u1} M (NonAssocRing.toNonUnitalNonAssocRing.{u1} M (Ring.toNonAssocRing.{u1} M _inst_1))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (Neg.neg.{u1} M (Ring.toNeg.{u1} M _inst_1) a) (Set.center.{u1} M (NonUnitalNonAssocRing.toMul.{u1} M (NonAssocRing.toNonUnitalNonAssocRing.{u1} M (Ring.toNonAssocRing.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align set.neg_mem_center Set.neg_mem_centerₓ'. -/
@[simp]
theorem neg_mem_center [Ring M] {a : M} (ha : a ∈ Set.center M) : -a ∈ Set.center M := fun c => by
  rw [← neg_mul_comm, ha (-c), neg_mul_comm]
#align set.neg_mem_center Set.neg_mem_center

/- warning: set.subset_center_units -> Set.subset_center_units is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], HasSubset.Subset.{u1} (Set.{u1} (Units.{u1} M _inst_1)) (Set.hasSubset.{u1} (Units.{u1} M _inst_1)) (Set.preimage.{u1, u1} (Units.{u1} M _inst_1) M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1))))) (Set.center.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (Set.center.{u1} (Units.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], HasSubset.Subset.{u1} (Set.{u1} (Units.{u1} M _inst_1)) (Set.instHasSubsetSet_1.{u1} (Units.{u1} M _inst_1)) (Set.preimage.{u1, u1} (Units.{u1} M _inst_1) M (Units.val.{u1} M _inst_1) (Set.center.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (Set.center.{u1} (Units.{u1} M _inst_1) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_1) (Units.instMulOneClassUnits.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.subset_center_units Set.subset_center_unitsₓ'. -/
@[to_additive subset_add_center_add_units]
theorem subset_center_units [Monoid M] : (coe : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun a ha b => Units.ext <| ha _
#align set.subset_center_units Set.subset_center_units

/- warning: set.center_units_subset -> Set.center_units_subset is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : GroupWithZero.{u1} M], HasSubset.Subset.{u1} (Set.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))) (Set.hasSubset.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))) (Set.center.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (MulOneClass.toHasMul.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (Units.mulOneClass.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))) (Set.preimage.{u1, u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (coeBase.{succ u1, succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (Units.hasCoe.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))) (Set.center.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : GroupWithZero.{u1} M], HasSubset.Subset.{u1} (Set.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))) (Set.instHasSubsetSet_1.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))) (Set.center.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (MulOneClass.toMul.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (Units.instMulOneClassUnits.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))) (Set.preimage.{u1, u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (Units.val.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (Set.center.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.center_units_subset Set.center_units_subsetₓ'. -/
theorem center_units_subset [GroupWithZero M] : Set.center Mˣ ⊆ (coe : Mˣ → M) ⁻¹' center M :=
  fun a ha b => by
  obtain rfl | hb := eq_or_ne b 0
  · rw [zero_mul, mul_zero]
  · exact units.ext_iff.mp (ha (Units.mk0 _ hb))
#align set.center_units_subset Set.center_units_subset

/- warning: set.center_units_eq -> Set.center_units_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : GroupWithZero.{u1} M], Eq.{succ u1} (Set.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))) (Set.center.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (MulOneClass.toHasMul.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (Units.mulOneClass.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))) (Set.preimage.{u1, u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (coeBase.{succ u1, succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (Units.hasCoe.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))) (Set.center.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : GroupWithZero.{u1} M], Eq.{succ u1} (Set.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))) (Set.center.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (MulOneClass.toMul.{u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (Units.instMulOneClassUnits.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))) (Set.preimage.{u1, u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) M (Units.val.{u1} M (MonoidWithZero.toMonoid.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))) (Set.center.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.center_units_eq Set.center_units_eqₓ'. -/
/-- In a group with zero, the center of the units is the preimage of the center. -/
theorem center_units_eq [GroupWithZero M] : Set.center Mˣ = (coe : Mˣ → M) ⁻¹' center M :=
  Subset.antisymm center_units_subset subset_center_units
#align set.center_units_eq Set.center_units_eq

/- warning: set.inv_mem_center₀ -> Set.inv_mem_center₀ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : GroupWithZero.{u1} M] {a : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.center.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (Inv.inv.{u1} M (DivInvMonoid.toHasInv.{u1} M (GroupWithZero.toDivInvMonoid.{u1} M _inst_1)) a) (Set.center.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : GroupWithZero.{u1} M] {a : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.center.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (Inv.inv.{u1} M (GroupWithZero.toInv.{u1} M _inst_1) a) (Set.center.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.inv_mem_center₀ Set.inv_mem_center₀ₓ'. -/
@[simp]
theorem inv_mem_center₀ [GroupWithZero M] {a : M} (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M :=
  by
  obtain rfl | ha0 := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_center M
  rcases IsUnit.mk0 _ ha0 with ⟨a, rfl⟩
  rw [← Units.val_inv_eq_inv_val]
  exact center_units_subset (inv_mem_center (subset_center_units ha))
#align set.inv_mem_center₀ Set.inv_mem_center₀

/- warning: set.div_mem_center -> Set.div_mem_center is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.center.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b (Set.center.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) a b) (Set.center.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Group.{u1} M] {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.center.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b (Set.center.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))) a b) (Set.center.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.div_mem_center Set.div_mem_centerₓ'. -/
@[simp, to_additive sub_mem_add_center]
theorem div_mem_center [Group M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)
#align set.div_mem_center Set.div_mem_center

/- warning: set.div_mem_center₀ -> Set.div_mem_center₀ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : GroupWithZero.{u1} M] {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Set.center.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b (Set.center.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (GroupWithZero.toDivInvMonoid.{u1} M _inst_1))) a b) (Set.center.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : GroupWithZero.{u1} M] {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Set.center.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b (Set.center.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1)))))) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (GroupWithZero.toDiv.{u1} M _inst_1)) a b) (Set.center.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (GroupWithZero.toMonoidWithZero.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.div_mem_center₀ Set.div_mem_center₀ₓ'. -/
@[simp]
theorem div_mem_center₀ [GroupWithZero M] {a b : M} (ha : a ∈ Set.center M)
    (hb : b ∈ Set.center M) : a / b ∈ Set.center M :=
  by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center₀ hb)
#align set.div_mem_center₀ Set.div_mem_center₀

variable (M)

/- warning: set.center_eq_univ -> Set.center_eq_univ is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : CommSemigroup.{u1} M], Eq.{succ u1} (Set.{u1} M) (Set.center.{u1} M (Semigroup.toHasMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))) (Set.univ.{u1} M)
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : CommSemigroup.{u1} M], Eq.{succ u1} (Set.{u1} M) (Set.center.{u1} M (Semigroup.toMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))) (Set.univ.{u1} M)
Case conversion may be inaccurate. Consider using '#align set.center_eq_univ Set.center_eq_univₓ'. -/
@[simp, to_additive add_center_eq_univ]
theorem center_eq_univ [CommSemigroup M] : center M = Set.univ :=
  (Subset.antisymm (subset_univ _)) fun x _ y => mul_comm y x
#align set.center_eq_univ Set.center_eq_univ

end Set

namespace Subsemigroup

section

variable (M) [Semigroup M]

/- warning: subsemigroup.center -> Subsemigroup.center is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Semigroup.{u1} M], Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Semigroup.{u1} M], Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align subsemigroup.center Subsemigroup.centerₓ'. -/
/-- The center of a semigroup `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a semigroup `M` is the set of elements that commute with everything in\n`M`"]
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' a b := Set.mul_mem_center
#align subsemigroup.center Subsemigroup.center

/- warning: subsemigroup.coe_center clashes with [anonymous] -> [anonymous]
warning: subsemigroup.coe_center -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u_1}) [_inst_1 : Semigroup.{u_1} M], Eq.{max (succ u_1) 1} (Set.{u_1} M) ((fun (a : Type.{u_1}) (b : Sort.{max (succ u_1) 1}) [self : HasLiftT.{succ u_1, max (succ u_1) 1} a b] => self.0) (Subsemigroup.{u_1} M (Semigroup.toHasMul.{u_1} M _inst_1)) (Set.{u_1} M) (HasLiftT.mk.{succ u_1, max (succ u_1) 1} (Subsemigroup.{u_1} M (Semigroup.toHasMul.{u_1} M _inst_1)) (Set.{u_1} M) (CoeTCₓ.coe.{succ u_1, max (succ u_1) 1} (Subsemigroup.{u_1} M (Semigroup.toHasMul.{u_1} M _inst_1)) (Set.{u_1} M) (SetLike.Set.hasCoeT.{u_1, u_1} (Subsemigroup.{u_1} M (Semigroup.toHasMul.{u_1} M _inst_1)) M (Subsemigroup.setLike.{u_1} M (Semigroup.toHasMul.{u_1} M _inst_1))))) (Subsemigroup.center.{u_1} M _inst_1)) (Set.center.{u_1} M (Semigroup.toHasMul.{u_1} M _inst_1))
but is expected to have type
  forall {M : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> M -> _inst_1) -> Nat -> (List.{u} M) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align subsemigroup.coe_center [anonymous]ₓ'. -/
@[to_additive]
theorem [anonymous] : ↑(center M) = Set.center M :=
  rfl
#align subsemigroup.coe_center[anonymous]

variable {M}

/- warning: subsemigroup.mem_center_iff -> Subsemigroup.mem_center_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Semigroup.{u1} M] {z : M}, Iff (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) M (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))) z (Subsemigroup.center.{u1} M _inst_1)) (forall (g : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) g z) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) z g))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Semigroup.{u1} M] {z : M}, Iff (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1))) z (Subsemigroup.center.{u1} M _inst_1)) (forall (g : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) g z) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) z g))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_center_iff Subsemigroup.mem_center_iffₓ'. -/
@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align subsemigroup.mem_center_iff Subsemigroup.mem_center_iff

/- warning: subsemigroup.decidable_mem_center -> Subsemigroup.decidableMemCenter is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Semigroup.{u1} M] (a : M) [_inst_2 : Decidable (forall (b : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) b a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) a b))], Decidable (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) M (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_1))) a (Subsemigroup.center.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Semigroup.{u1} M] (a : M) [_inst_2 : Decidable (forall (b : M), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) b a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) a b))], Decidable (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1))) a (Subsemigroup.center.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align subsemigroup.decidable_mem_center Subsemigroup.decidableMemCenterₓ'. -/
@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ mem_center_iff
#align subsemigroup.decidable_mem_center Subsemigroup.decidableMemCenter

/-- The center of a semigroup is commutative. -/
@[to_additive "The center of an additive semigroup is commutative."]
instance : CommSemigroup (center M) :=
  { MulMemClass.toSemigroup (center M) with mul_comm := fun a b => Subtype.ext <| b.Prop _ }

end

section

variable (M) [CommSemigroup M]

/- warning: subsemigroup.center_eq_top -> Subsemigroup.center_eq_top is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : CommSemigroup.{u1} M], Eq.{succ u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))) (Subsemigroup.center.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1)) (Top.top.{u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))) (Subsemigroup.hasTop.{u1} M (Semigroup.toHasMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : CommSemigroup.{u1} M], Eq.{succ u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))) (Subsemigroup.center.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1)) (Top.top.{u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))) (Subsemigroup.instTopSubsemigroup.{u1} M (Semigroup.toMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align subsemigroup.center_eq_top Subsemigroup.center_eq_topₓ'. -/
@[to_additive, simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align subsemigroup.center_eq_top Subsemigroup.center_eq_top

end

end Subsemigroup

-- Guard against import creep
assert_not_exists finset

