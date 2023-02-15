/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.int.interval
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharZero.Lemmas
import Mathbin.Order.LocallyFinite
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals of integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves that `ℤ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Int

instance : LocallyFiniteOrder ℤ
    where
  finsetIcc a b :=
    (Finset.range (b + 1 - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIco a b := (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding a
  finsetIoc a b :=
    (Finset.range (b - a).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finsetIoo a b :=
    (Finset.range (b - a - 1).toNat).map <| Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)
  finset_mem_Icc a b x :=
    by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [lt_sub_iff_add_lt, Int.lt_add_one_iff, add_comm] at h
      exact ⟨Int.le.intro rfl, h⟩
    · rintro ⟨ha, hb⟩
      use (x - a).toNat
      rw [← lt_add_one_iff] at hb
      rw [to_nat_sub_of_le ha]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
  finset_mem_Ico a b x :=
    by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      exact ⟨Int.le.intro rfl, lt_sub_iff_add_lt'.mp h⟩
    · rintro ⟨ha, hb⟩
      use (x - a).toNat
      rw [to_nat_sub_of_le ha]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩
  finset_mem_Ioc a b x :=
    by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [← add_one_le_iff, le_sub_iff_add_le', add_comm _ (1 : ℤ), ← add_assoc] at h
      exact ⟨Int.le.intro rfl, h⟩
    · rintro ⟨ha, hb⟩
      use (x - (a + 1)).toNat
      rw [to_nat_sub_of_le ha, ← add_one_le_iff, sub_add, add_sub_cancel]
      exact ⟨sub_le_sub_right hb _, add_sub_cancel'_right _ _⟩
  finset_mem_Ioo a b x :=
    by
    simp_rw [mem_map, exists_prop, mem_range, Int.lt_toNat, Function.Embedding.trans_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    constructor
    · rintro ⟨a, h, rfl⟩
      rw [sub_sub, lt_sub_iff_add_lt'] at h
      exact ⟨Int.le.intro rfl, h⟩
    · rintro ⟨ha, hb⟩
      use (x - (a + 1)).toNat
      rw [to_nat_sub_of_le ha, sub_sub]
      exact ⟨sub_lt_sub_right hb _, add_sub_cancel'_right _ _⟩

namespace Int

variable (a b : ℤ)

/- warning: int.Icc_eq_finset_map -> Int.Icc_eq_finset_map is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} (Finset.{0} Int) (Finset.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b) (Finset.map.{0, 0} Nat Int (Function.Embedding.trans.{1, 1, 1} Nat Int Int (Nat.castEmbedding.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (NonAssocRing.toAddGroupWithOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (StrictOrderedSemiring.to_charZero.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (addLeftEmbedding.{0} Int (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Int (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Int (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) a)) (Finset.range (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) b (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) a))))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} (Finset.{0} Int) (Finset.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b) (Finset.map.{0, 0} Nat Int (Function.Embedding.trans.{1, 1, 1} Nat Int Int (Nat.castEmbedding.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (Ring.toAddGroupWithOne.{0} Int Int.instRingInt)) (StrictOrderedSemiring.to_charZero.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing))))) (addLeftEmbedding.{0} Int (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Int (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Int (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing))))))) a)) (Finset.range (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) b (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) a))))
Case conversion may be inaccurate. Consider using '#align int.Icc_eq_finset_map Int.Icc_eq_finset_mapₓ'. -/
theorem Icc_eq_finset_map :
    Icc a b =
      (Finset.range (b + 1 - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl
#align int.Icc_eq_finset_map Int.Icc_eq_finset_map

/- warning: int.Ico_eq_finset_map -> Int.Ico_eq_finset_map is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} (Finset.{0} Int) (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b) (Finset.map.{0, 0} Nat Int (Function.Embedding.trans.{1, 1, 1} Nat Int Int (Nat.castEmbedding.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (NonAssocRing.toAddGroupWithOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (StrictOrderedSemiring.to_charZero.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (addLeftEmbedding.{0} Int (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Int (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Int (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) a)) (Finset.range (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} (Finset.{0} Int) (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b) (Finset.map.{0, 0} Nat Int (Function.Embedding.trans.{1, 1, 1} Nat Int Int (Nat.castEmbedding.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (Ring.toAddGroupWithOne.{0} Int Int.instRingInt)) (StrictOrderedSemiring.to_charZero.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing))))) (addLeftEmbedding.{0} Int (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Int (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Int (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing))))))) a)) (Finset.range (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))))
Case conversion may be inaccurate. Consider using '#align int.Ico_eq_finset_map Int.Ico_eq_finset_mapₓ'. -/
theorem Ico_eq_finset_map :
    Ico a b = (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding a) :=
  rfl
#align int.Ico_eq_finset_map Int.Ico_eq_finset_map

/- warning: int.Ioc_eq_finset_map -> Int.Ioc_eq_finset_map is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} (Finset.{0} Int) (Finset.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b) (Finset.map.{0, 0} Nat Int (Function.Embedding.trans.{1, 1, 1} Nat Int Int (Nat.castEmbedding.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (NonAssocRing.toAddGroupWithOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (StrictOrderedSemiring.to_charZero.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (addLeftEmbedding.{0} Int (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Int (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Int (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) a (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))) (Finset.range (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} (Finset.{0} Int) (Finset.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b) (Finset.map.{0, 0} Nat Int (Function.Embedding.trans.{1, 1, 1} Nat Int Int (Nat.castEmbedding.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (Ring.toAddGroupWithOne.{0} Int Int.instRingInt)) (StrictOrderedSemiring.to_charZero.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing))))) (addLeftEmbedding.{0} Int (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Int (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Int (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing))))))) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) a (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))) (Finset.range (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))))
Case conversion may be inaccurate. Consider using '#align int.Ioc_eq_finset_map Int.Ioc_eq_finset_mapₓ'. -/
theorem Ioc_eq_finset_map :
    Ioc a b =
      (Finset.range (b - a).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl
#align int.Ioc_eq_finset_map Int.Ioc_eq_finset_map

/- warning: int.Ioo_eq_finset_map -> Int.Ioo_eq_finset_map is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} (Finset.{0} Int) (Finset.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b) (Finset.map.{0, 0} Nat Int (Function.Embedding.trans.{1, 1, 1} Nat Int Int (Nat.castEmbedding.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (NonAssocRing.toAddGroupWithOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (StrictOrderedSemiring.to_charZero.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (addLeftEmbedding.{0} Int (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Int (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Int (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) a (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))) (Finset.range (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} (Finset.{0} Int) (Finset.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b) (Finset.map.{0, 0} Nat Int (Function.Embedding.trans.{1, 1, 1} Nat Int Int (Nat.castEmbedding.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (Ring.toAddGroupWithOne.{0} Int Int.instRingInt)) (StrictOrderedSemiring.to_charZero.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing))))) (addLeftEmbedding.{0} Int (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Int (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Int (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing))))))) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) a (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))) (Finset.range (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))))
Case conversion may be inaccurate. Consider using '#align int.Ioo_eq_finset_map Int.Ioo_eq_finset_mapₓ'. -/
theorem Ioo_eq_finset_map :
    Ioo a b =
      (Finset.range (b - a - 1).toNat).map (Nat.castEmbedding.trans <| addLeftEmbedding (a + 1)) :=
  rfl
#align int.Ioo_eq_finset_map Int.Ioo_eq_finset_map

/- warning: int.card_Icc -> Int.card_Icc is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Finset.card.{0} Int (Finset.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) b (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) a))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Finset.card.{0} Int (Finset.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) b (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) a))
Case conversion may be inaccurate. Consider using '#align int.card_Icc Int.card_Iccₓ'. -/
@[simp]
theorem card_Icc : (Icc a b).card = (b + 1 - a).toNat :=
  by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]
#align int.card_Icc Int.card_Icc

/- warning: int.card_Ico -> Int.card_Ico is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Finset.card.{0} Int (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Finset.card.{0} Int (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.card_Ico Int.card_Icoₓ'. -/
@[simp]
theorem card_Ico : (Ico a b).card = (b - a).toNat :=
  by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]
#align int.card_Ico Int.card_Ico

/- warning: int.card_Ioc -> Int.card_Ioc is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Finset.card.{0} Int (Finset.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Finset.card.{0} Int (Finset.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.card_Ioc Int.card_Iocₓ'. -/
@[simp]
theorem card_Ioc : (Ioc a b).card = (b - a).toNat :=
  by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]
#align int.card_Ioc Int.card_Ioc

/- warning: int.card_Ioo -> Int.card_Ioo is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Finset.card.{0} Int (Finset.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Finset.card.{0} Int (Finset.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))
Case conversion may be inaccurate. Consider using '#align int.card_Ioo Int.card_Iooₓ'. -/
@[simp]
theorem card_Ioo : (Ioo a b).card = (b - a - 1).toNat :=
  by
  change (Finset.map _ _).card = _
  rw [Finset.card_map, Finset.card_range]
#align int.card_Ioo Int.card_Ioo

/- warning: int.card_Icc_of_le -> Int.card_Icc_of_le is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.hasLe a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) b (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) -> (Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Finset.card.{0} Int (Finset.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) b (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) a))
but is expected to have type
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.instLEInt a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) b (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) -> (Eq.{1} Int (Nat.cast.{0} Int Int.instNatCastInt (Finset.card.{0} Int (Finset.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) b (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) a))
Case conversion may be inaccurate. Consider using '#align int.card_Icc_of_le Int.card_Icc_of_leₓ'. -/
theorem card_Icc_of_le (h : a ≤ b + 1) : ((Icc a b).card : ℤ) = b + 1 - a := by
  rw [card_Icc, to_nat_sub_of_le h]
#align int.card_Icc_of_le Int.card_Icc_of_le

/- warning: int.card_Ico_of_le -> Int.card_Ico_of_le is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.hasLe a b) -> (Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Finset.card.{0} Int (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.instLEInt a b) -> (Eq.{1} Int (Nat.cast.{0} Int Int.instNatCastInt (Finset.card.{0} Int (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.card_Ico_of_le Int.card_Ico_of_leₓ'. -/
theorem card_Ico_of_le (h : a ≤ b) : ((Ico a b).card : ℤ) = b - a := by
  rw [card_Ico, to_nat_sub_of_le h]
#align int.card_Ico_of_le Int.card_Ico_of_le

/- warning: int.card_Ioc_of_le -> Int.card_Ioc_of_le is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.hasLe a b) -> (Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Finset.card.{0} Int (Finset.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.instLEInt a b) -> (Eq.{1} Int (Nat.cast.{0} Int Int.instNatCastInt (Finset.card.{0} Int (Finset.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.card_Ioc_of_le Int.card_Ioc_of_leₓ'. -/
theorem card_Ioc_of_le (h : a ≤ b) : ((Ioc a b).card : ℤ) = b - a := by
  rw [card_Ioc, to_nat_sub_of_le h]
#align int.card_Ioc_of_le Int.card_Ioc_of_le

/- warning: int.card_Ioo_of_lt -> Int.card_Ioo_of_lt is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (LT.lt.{0} Int Int.hasLt a b) -> (Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Finset.card.{0} Int (Finset.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))
but is expected to have type
  forall (a : Int) (b : Int), (LT.lt.{0} Int Int.instLTInt a b) -> (Eq.{1} Int (Nat.cast.{0} Int Int.instNatCastInt (Finset.card.{0} Int (Finset.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))
Case conversion may be inaccurate. Consider using '#align int.card_Ioo_of_lt Int.card_Ioo_of_ltₓ'. -/
theorem card_Ioo_of_lt (h : a < b) : ((Ioo a b).card : ℤ) = b - a - 1 := by
  rw [card_Ioo, sub_sub, to_nat_sub_of_le h]
#align int.card_Ioo_of_lt Int.card_Ioo_of_lt

/- warning: int.card_fintype_Icc -> Int.card_fintype_Icc is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} Int) Type (Set.hasCoeToSort.{0} Int) (Set.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) a b)) (Set.fintypeIcc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) b (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) a))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} Int (Set.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) a b)) (Set.fintypeIcc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) b (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) a))
Case conversion may be inaccurate. Consider using '#align int.card_fintype_Icc Int.card_fintype_Iccₓ'. -/
@[simp]
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = (b + 1 - a).toNat := by
  rw [← card_Icc, Fintype.card_ofFinset]
#align int.card_fintype_Icc Int.card_fintype_Icc

/- warning: int.card_fintype_Ico -> Int.card_fintype_Ico is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} Int) Type (Set.hasCoeToSort.{0} Int) (Set.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) a b)) (Set.fintypeIco.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} Int (Set.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) a b)) (Set.fintypeIco.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.card_fintype_Ico Int.card_fintype_Icoₓ'. -/
@[simp]
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = (b - a).toNat := by
  rw [← card_Ico, Fintype.card_ofFinset]
#align int.card_fintype_Ico Int.card_fintype_Ico

/- warning: int.card_fintype_Ioc -> Int.card_fintype_Ioc is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} Int) Type (Set.hasCoeToSort.{0} Int) (Set.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) a b)) (Set.fintypeIoc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} Int (Set.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) a b)) (Set.fintypeIoc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.card_fintype_Ioc Int.card_fintype_Iocₓ'. -/
@[simp]
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = (b - a).toNat := by
  rw [← card_Ioc, Fintype.card_ofFinset]
#align int.card_fintype_Ioc Int.card_fintype_Ioc

/- warning: int.card_fintype_Ioo -> Int.card_fintype_Ioo is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} Int) Type (Set.hasCoeToSort.{0} Int) (Set.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) a b)) (Set.fintypeIoo.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} Int (Set.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) a b)) (Set.fintypeIoo.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b)) (Int.toNat (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))
Case conversion may be inaccurate. Consider using '#align int.card_fintype_Ioo Int.card_fintype_Iooₓ'. -/
@[simp]
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = (b - a - 1).toNat := by
  rw [← card_Ioo, Fintype.card_ofFinset]
#align int.card_fintype_Ioo Int.card_fintype_Ioo

/- warning: int.card_fintype_Icc_of_le -> Int.card_fintype_Icc_of_le is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.hasLe a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) b (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) -> (Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} Int) Type (Set.hasCoeToSort.{0} Int) (Set.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) a b)) (Set.fintypeIcc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) b (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) a))
but is expected to have type
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.instLEInt a (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) b (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) -> (Eq.{1} Int (Nat.cast.{0} Int Int.instNatCastInt (Fintype.card.{0} (Set.Elem.{0} Int (Set.Icc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) a b)) (Set.fintypeIcc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) b (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) a))
Case conversion may be inaccurate. Consider using '#align int.card_fintype_Icc_of_le Int.card_fintype_Icc_of_leₓ'. -/
theorem card_fintype_Icc_of_le (h : a ≤ b + 1) : (Fintype.card (Set.Icc a b) : ℤ) = b + 1 - a := by
  rw [card_fintype_Icc, to_nat_sub_of_le h]
#align int.card_fintype_Icc_of_le Int.card_fintype_Icc_of_le

/- warning: int.card_fintype_Ico_of_le -> Int.card_fintype_Ico_of_le is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.hasLe a b) -> (Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} Int) Type (Set.hasCoeToSort.{0} Int) (Set.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) a b)) (Set.fintypeIco.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.instLEInt a b) -> (Eq.{1} Int (Nat.cast.{0} Int Int.instNatCastInt (Fintype.card.{0} (Set.Elem.{0} Int (Set.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) a b)) (Set.fintypeIco.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.card_fintype_Ico_of_le Int.card_fintype_Ico_of_leₓ'. -/
theorem card_fintype_Ico_of_le (h : a ≤ b) : (Fintype.card (Set.Ico a b) : ℤ) = b - a := by
  rw [card_fintype_Ico, to_nat_sub_of_le h]
#align int.card_fintype_Ico_of_le Int.card_fintype_Ico_of_le

/- warning: int.card_fintype_Ioc_of_le -> Int.card_fintype_Ioc_of_le is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.hasLe a b) -> (Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} Int) Type (Set.hasCoeToSort.{0} Int) (Set.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) a b)) (Set.fintypeIoc.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall (a : Int) (b : Int), (LE.le.{0} Int Int.instLEInt a b) -> (Eq.{1} Int (Nat.cast.{0} Int Int.instNatCastInt (Fintype.card.{0} (Set.Elem.{0} Int (Set.Ioc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) a b)) (Set.fintypeIoc.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.card_fintype_Ioc_of_le Int.card_fintype_Ioc_of_leₓ'. -/
theorem card_fintype_Ioc_of_le (h : a ≤ b) : (Fintype.card (Set.Ioc a b) : ℤ) = b - a := by
  rw [card_fintype_Ioc, to_nat_sub_of_le h]
#align int.card_fintype_Ioc_of_le Int.card_fintype_Ioc_of_le

/- warning: int.card_fintype_Ioo_of_lt -> Int.card_fintype_Ioo_of_lt is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (LT.lt.{0} Int Int.hasLt a b) -> (Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} Int) Type (Set.hasCoeToSort.{0} Int) (Set.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) a b)) (Set.fintypeIoo.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))
but is expected to have type
  forall (a : Int) (b : Int), (LT.lt.{0} Int Int.instLTInt a b) -> (Eq.{1} Int (Nat.cast.{0} Int Int.instNatCastInt (Fintype.card.{0} (Set.Elem.{0} Int (Set.Ioo.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) a b)) (Set.fintypeIoo.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing a b))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))
Case conversion may be inaccurate. Consider using '#align int.card_fintype_Ioo_of_lt Int.card_fintype_Ioo_of_ltₓ'. -/
theorem card_fintype_Ioo_of_lt (h : a < b) : (Fintype.card (Set.Ioo a b) : ℤ) = b - a - 1 := by
  rw [card_fintype_Ioo, sub_sub, to_nat_sub_of_le h]
#align int.card_fintype_Ioo_of_lt Int.card_fintype_Ioo_of_lt

/- warning: int.image_Ico_mod -> Int.image_Ico_emod is a dubious translation:
lean 3 declaration is
  forall (n : Int) (a : Int), (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a) -> (Eq.{1} (Finset.{0} Int) (Finset.image.{0, 0} Int Int (fun (a : Int) (b : Int) => Int.decidableEq a b) (fun (_x : Int) => HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.hasMod) _x a) (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder n (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) n a))) (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) Int.locallyFiniteOrder (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a))
but is expected to have type
  forall (n : Int) (a : Int), (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a) -> (Eq.{1} (Finset.{0} Int) (Finset.image.{0, 0} Int Int (fun (a : Int) (b : Int) => Int.instDecidableEqInt a b) (fun (_x : Int) => HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.instModInt_1) _x a) (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing n (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) n a))) (Finset.Ico.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) instLocallyFiniteOrderIntToPreorderToPartialOrderToStrictOrderedRingToLinearOrderedRingLinearOrderedCommRing (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a))
Case conversion may be inaccurate. Consider using '#align int.image_Ico_mod Int.image_Ico_emodₓ'. -/
theorem image_Ico_emod (n a : ℤ) (h : 0 ≤ a) : (Ico n (n + a)).image (· % a) = Ico 0 a :=
  by
  obtain rfl | ha := eq_or_lt_of_le h
  · simp
  ext i
  simp only [mem_image, exists_prop, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, h, rfl⟩
    exact ⟨mod_nonneg i (ne_of_gt ha), mod_lt_of_pos i ha⟩
  intro hia
  have hn := Int.emod_add_ediv n a
  obtain hi | hi := lt_or_le i (n % a)
  · refine' ⟨i + a * (n / a + 1), ⟨_, _⟩, _⟩
    · rw [add_comm (n / a), mul_add, mul_one, ← add_assoc]
      refine' hn.symm.le.trans (add_le_add_right _ _)
      simpa only [zero_add] using add_le_add hia.left (Int.emod_lt_of_pos n ha).le
    · refine' lt_of_lt_of_le (add_lt_add_right hi (a * (n / a + 1))) _
      rw [mul_add, mul_one, ← add_assoc, hn]
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hia.left hia.right]
  · refine' ⟨i + a * (n / a), ⟨_, _⟩, _⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
    · rw [add_comm n a]
      refine' add_lt_add_of_lt_of_le hia.right (le_trans _ hn.le)
      simp only [zero_le, le_add_iff_nonneg_left]
      exact Int.emod_nonneg n (ne_of_gt ha)
    · rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hia.left hia.right]
#align int.image_Ico_mod Int.image_Ico_emod

end Int

