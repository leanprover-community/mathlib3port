/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.set.intervals.iso_Ioo
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Monotone.Odd
import Mathbin.Tactic.FieldSimp

/-!
# Order isomorphism between a linear ordered field and `(-1, 1)`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide an order isomorphism `order_iso_Ioo_neg_one_one` between the open interval
`(-1, 1)` in a linear ordered field and the whole field.
-/


open Set

/- warning: order_iso_Ioo_neg_one_one -> orderIsoIooNegOneOne is a dubious translation:
lean 3 declaration is
  forall (k : Type.{u1}) [_inst_1 : LinearOrderedField.{u1} k], OrderIso.{u1, u1} k (coeSort.{succ u1, succ (succ u1)} (Set.{u1} k) Type.{u1} (Set.hasCoeToSort.{u1} k) (Set.Ioo.{u1} k (PartialOrder.toPreorder.{u1} k (OrderedAddCommGroup.toPartialOrder.{u1} k (StrictOrderedRing.toOrderedAddCommGroup.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1)))))) (Neg.neg.{u1} k (SubNegMonoid.toHasNeg.{u1} k (AddGroup.toSubNegMonoid.{u1} k (AddGroupWithOne.toAddGroup.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))))))) (OfNat.ofNat.{u1} k 1 (OfNat.mk.{u1} k 1 (One.one.{u1} k (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1)))))))))))) (OfNat.ofNat.{u1} k 1 (OfNat.mk.{u1} k 1 (One.one.{u1} k (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))))))))))) (Preorder.toLE.{u1} k (PartialOrder.toPreorder.{u1} k (OrderedAddCommGroup.toPartialOrder.{u1} k (StrictOrderedRing.toOrderedAddCommGroup.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))))) (Subtype.hasLe.{u1} k (Preorder.toLE.{u1} k (PartialOrder.toPreorder.{u1} k (OrderedAddCommGroup.toPartialOrder.{u1} k (StrictOrderedRing.toOrderedAddCommGroup.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))))) (fun (x : k) => Membership.Mem.{u1, u1} k (Set.{u1} k) (Set.hasMem.{u1} k) x (Set.Ioo.{u1} k (PartialOrder.toPreorder.{u1} k (OrderedAddCommGroup.toPartialOrder.{u1} k (StrictOrderedRing.toOrderedAddCommGroup.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1)))))) (Neg.neg.{u1} k (SubNegMonoid.toHasNeg.{u1} k (AddGroup.toSubNegMonoid.{u1} k (AddGroupWithOne.toAddGroup.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))))))) (OfNat.ofNat.{u1} k 1 (OfNat.mk.{u1} k 1 (One.one.{u1} k (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1)))))))))))) (OfNat.ofNat.{u1} k 1 (OfNat.mk.{u1} k 1 (One.one.{u1} k (AddMonoidWithOne.toOne.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))))))))))))
but is expected to have type
  forall (k : Type.{u1}) [_inst_1 : LinearOrderedField.{u1} k], OrderIso.{u1, u1} k (Set.Elem.{u1} k (Set.Ioo.{u1} k (PartialOrder.toPreorder.{u1} k (StrictOrderedRing.toPartialOrder.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))) (Neg.neg.{u1} k (Ring.toNeg.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))) (OfNat.ofNat.{u1} k 1 (One.toOfNat1.{u1} k (NonAssocRing.toOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))))))) (OfNat.ofNat.{u1} k 1 (One.toOfNat1.{u1} k (NonAssocRing.toOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1)))))))))) (Preorder.toLE.{u1} k (PartialOrder.toPreorder.{u1} k (StrictOrderedRing.toPartialOrder.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1)))))) (Subtype.le.{u1} k (Preorder.toLE.{u1} k (PartialOrder.toPreorder.{u1} k (StrictOrderedRing.toPartialOrder.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1)))))) (fun (x : k) => Membership.mem.{u1, u1} k (Set.{u1} k) (Set.instMembershipSet.{u1} k) x (Set.Ioo.{u1} k (PartialOrder.toPreorder.{u1} k (StrictOrderedRing.toPartialOrder.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))) (Neg.neg.{u1} k (Ring.toNeg.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))) (OfNat.ofNat.{u1} k 1 (One.toOfNat1.{u1} k (NonAssocRing.toOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1))))))))) (OfNat.ofNat.{u1} k 1 (One.toOfNat1.{u1} k (NonAssocRing.toOne.{u1} k (Ring.toNonAssocRing.{u1} k (StrictOrderedRing.toRing.{u1} k (LinearOrderedRing.toStrictOrderedRing.{u1} k (LinearOrderedCommRing.toLinearOrderedRing.{u1} k (LinearOrderedField.toLinearOrderedCommRing.{u1} k _inst_1)))))))))))
Case conversion may be inaccurate. Consider using '#align order_iso_Ioo_neg_one_one orderIsoIooNegOneOneₓ'. -/
/-- In a linear ordered field, the whole field is order isomorphic to the open interval `(-1, 1)`.
We consider the actual implementation to be a "black box", so it is irreducible.
-/
irreducible_def orderIsoIooNegOneOne (k : Type _) [LinearOrderedField k] : k ≃o Ioo (-1 : k) 1 :=
  by
  refine' StrictMono.orderIsoOfRightInverse _ _ (fun x => x / (1 - |x|)) _
  · refine' cod_restrict (fun x => x / (1 + |x|)) _ fun x => abs_lt.1 _
    have H : 0 < 1 + |x| := (abs_nonneg x).trans_lt (lt_one_add _)
    calc
      |x / (1 + |x|)| = |x| / (1 + |x|) := by rw [abs_div, abs_of_pos H]
      _ < 1 := (div_lt_one H).2 (lt_one_add _)
      
  · refine' (strictMono_of_odd_strictMonoOn_nonneg _ _).codRestrict _
    · intro x
      simp only [abs_neg, neg_div]
    · rintro x (hx : 0 ≤ x) y (hy : 0 ≤ y) hxy
      simp [abs_of_nonneg, mul_add, mul_comm x y, div_lt_div_iff, hx.trans_lt (lt_one_add _),
        hy.trans_lt (lt_one_add _), *]
  · refine' fun x => Subtype.ext _
    have : 0 < 1 - |(x : k)| := sub_pos.2 (abs_lt.2 x.2)
    field_simp [abs_div, this.ne', abs_of_pos this]
#align order_iso_Ioo_neg_one_one orderIsoIooNegOneOne

