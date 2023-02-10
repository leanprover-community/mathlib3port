/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.nat.interval
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals of naturals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves that `ℕ` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `ordered_group`, `canonically_ordered_monoid` or `succ_order`
and subsequently be moved upstream to `data.finset.locally_finite`.
-/


open Finset Nat

instance : LocallyFiniteOrder ℕ
    where
  finsetIcc a b := ⟨List.range' a (b + 1 - a), List.nodup_range' _ _⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range' _ _⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range' _ _⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range' _ _⟩
  finset_mem_Icc a b x :=
    by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range']
    cases le_or_lt a b
    · rw [add_tsub_cancel_of_le (Nat.lt_succ_of_le h).le, Nat.lt_succ_iff]
    · rw [tsub_eq_zero_iff_le.2 (succ_le_of_lt h), add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)
  finset_mem_Ico a b x :=
    by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range']
    cases le_or_lt a b
    · rw [add_tsub_cancel_of_le h]
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2.le)
  finset_mem_Ioc a b x :=
    by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range']
    cases le_or_lt a b
    · rw [← succ_sub_succ, add_tsub_cancel_of_le (succ_le_succ h), Nat.lt_succ_iff, Nat.succ_le_iff]
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.le.trans hx.2)
  finset_mem_Ioo a b x :=
    by
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range', ← tsub_add_eq_tsub_tsub]
    cases le_or_lt (a + 1) b
    · rw [add_tsub_cancel_of_le h, Nat.succ_le_iff]
    · rw [tsub_eq_zero_iff_le.2 h.le, add_zero]
      exact iff_of_false (fun hx => hx.2.not_le hx.1) fun hx => h.not_le (hx.1.trans hx.2)

variable (a b c : ℕ)

namespace Nat

#print Nat.Icc_eq_range' /-
theorem Icc_eq_range' : Icc a b = ⟨List.range' a (b + 1 - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Icc_eq_range' Nat.Icc_eq_range'
-/

#print Nat.Ico_eq_range' /-
theorem Ico_eq_range' : Ico a b = ⟨List.range' a (b - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ico_eq_range' Nat.Ico_eq_range'
-/

#print Nat.Ioc_eq_range' /-
theorem Ioc_eq_range' : Ioc a b = ⟨List.range' (a + 1) (b - a), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ioc_eq_range' Nat.Ioc_eq_range'
-/

#print Nat.Ioo_eq_range' /-
theorem Ioo_eq_range' : Ioo a b = ⟨List.range' (a + 1) (b - a - 1), List.nodup_range' _ _⟩ :=
  rfl
#align nat.Ioo_eq_range' Nat.Ioo_eq_range'
-/

#print Nat.Iio_eq_range /-
theorem Iio_eq_range : Iio = range := by
  ext (b x)
  rw [mem_Iio, mem_range]
#align nat.Iio_eq_range Nat.Iio_eq_range
-/

#print Nat.Ico_zero_eq_range /-
@[simp]
theorem Ico_zero_eq_range : Ico 0 = range := by rw [← bot_eq_zero, ← Iio_eq_Ico, Iio_eq_range]
#align nat.Ico_zero_eq_range Nat.Ico_zero_eq_range
-/

#print Finset.range_eq_Ico /-
theorem Finset.range_eq_Ico : range = Ico 0 :=
  Ico_zero_eq_range.symm
#align finset.range_eq_Ico Finset.range_eq_Ico
-/

#print Nat.card_Icc /-
@[simp]
theorem card_Icc : (Icc a b).card = b + 1 - a :=
  List.length_range' _ _
#align nat.card_Icc Nat.card_Icc
-/

#print Nat.card_Ico /-
@[simp]
theorem card_Ico : (Ico a b).card = b - a :=
  List.length_range' _ _
#align nat.card_Ico Nat.card_Ico
-/

#print Nat.card_Ioc /-
@[simp]
theorem card_Ioc : (Ioc a b).card = b - a :=
  List.length_range' _ _
#align nat.card_Ioc Nat.card_Ioc
-/

#print Nat.card_Ioo /-
@[simp]
theorem card_Ioo : (Ioo a b).card = b - a - 1 :=
  List.length_range' _ _
#align nat.card_Ioo Nat.card_Ioo
-/

#print Nat.card_Iic /-
@[simp]
theorem card_Iic : (Iic b).card = b + 1 := by rw [Iic_eq_Icc, card_Icc, bot_eq_zero, tsub_zero]
#align nat.card_Iic Nat.card_Iic
-/

#print Nat.card_Iio /-
@[simp]
theorem card_Iio : (Iio b).card = b := by rw [Iio_eq_Ico, card_Ico, bot_eq_zero, tsub_zero]
#align nat.card_Iio Nat.card_Iio
-/

#print Nat.card_fintypeIcc /-
@[simp]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [Fintype.card_ofFinset, card_Icc]
#align nat.card_fintype_Icc Nat.card_fintypeIcc
-/

#print Nat.card_fintypeIco /-
@[simp]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by
  rw [Fintype.card_ofFinset, card_Ico]
#align nat.card_fintype_Ico Nat.card_fintypeIco
-/

#print Nat.card_fintypeIoc /-
@[simp]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [Fintype.card_ofFinset, card_Ioc]
#align nat.card_fintype_Ioc Nat.card_fintypeIoc
-/

#print Nat.card_fintypeIoo /-
@[simp]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [Fintype.card_ofFinset, card_Ioo]
#align nat.card_fintype_Ioo Nat.card_fintypeIoo
-/

#print Nat.card_fintypeIic /-
@[simp]
theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_ofFinset, card_Iic]
#align nat.card_fintype_Iic Nat.card_fintypeIic
-/

#print Nat.card_fintypeIio /-
@[simp]
theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by rw [Fintype.card_ofFinset, card_Iio]
#align nat.card_fintype_Iio Nat.card_fintypeIio
-/

#print Nat.Icc_succ_left /-
-- TODO@Yaël: Generalize all the following lemmas to `succ_order`
theorem Icc_succ_left : Icc a.succ b = Ioc a b :=
  by
  ext x
  rw [mem_Icc, mem_Ioc, succ_le_iff]
#align nat.Icc_succ_left Nat.Icc_succ_left
-/

#print Nat.Ico_succ_right /-
theorem Ico_succ_right : Ico a b.succ = Icc a b :=
  by
  ext x
  rw [mem_Ico, mem_Icc, lt_succ_iff]
#align nat.Ico_succ_right Nat.Ico_succ_right
-/

#print Nat.Ico_succ_left /-
theorem Ico_succ_left : Ico a.succ b = Ioo a b :=
  by
  ext x
  rw [mem_Ico, mem_Ioo, succ_le_iff]
#align nat.Ico_succ_left Nat.Ico_succ_left
-/

#print Nat.Icc_pred_right /-
theorem Icc_pred_right {b : ℕ} (h : 0 < b) : Icc a (b - 1) = Ico a b :=
  by
  ext x
  rw [mem_Icc, mem_Ico, lt_iff_le_pred h]
#align nat.Icc_pred_right Nat.Icc_pred_right
-/

#print Nat.Ico_succ_succ /-
theorem Ico_succ_succ : Ico a.succ b.succ = Ioc a b :=
  by
  ext x
  rw [mem_Ico, mem_Ioc, succ_le_iff, lt_succ_iff]
#align nat.Ico_succ_succ Nat.Ico_succ_succ
-/

#print Nat.Ico_succ_singleton /-
@[simp]
theorem Ico_succ_singleton : Ico a (a + 1) = {a} := by rw [Ico_succ_right, Icc_self]
#align nat.Ico_succ_singleton Nat.Ico_succ_singleton
-/

#print Nat.Ico_pred_singleton /-
@[simp]
theorem Ico_pred_singleton {a : ℕ} (h : 0 < a) : Ico (a - 1) a = {a - 1} := by
  rw [← Icc_pred_right _ h, Icc_self]
#align nat.Ico_pred_singleton Nat.Ico_pred_singleton
-/

#print Nat.Ioc_succ_singleton /-
@[simp]
theorem Ioc_succ_singleton : Ioc b (b + 1) = {b + 1} := by rw [← Nat.Icc_succ_left, Icc_self]
#align nat.Ioc_succ_singleton Nat.Ioc_succ_singleton
-/

variable {a b c}

/- warning: nat.Ico_succ_right_eq_insert_Ico -> Nat.Ico_succ_right_eq_insert_Ico is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat}, (LE.le.{0} Nat Nat.hasLe a b) -> (Eq.{1} (Finset.{0} Nat) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) b (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.hasInsert.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) b (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b)))
but is expected to have type
  forall {a : Nat} {b : Nat}, (LE.le.{0} Nat instLENat a b) -> (Eq.{1} (Finset.{0} Nat) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) b (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.instInsertFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) b (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b)))
Case conversion may be inaccurate. Consider using '#align nat.Ico_succ_right_eq_insert_Ico Nat.Ico_succ_right_eq_insert_Icoₓ'. -/
theorem Ico_succ_right_eq_insert_Ico (h : a ≤ b) : Ico a (b + 1) = insert b (Ico a b) := by
  rw [Ico_succ_right, ← Ico_insert_right h]
#align nat.Ico_succ_right_eq_insert_Ico Nat.Ico_succ_right_eq_insert_Ico

/- warning: nat.Ico_insert_succ_left -> Nat.Ico_insert_succ_left is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat}, (LT.lt.{0} Nat Nat.hasLt a b) -> (Eq.{1} (Finset.{0} Nat) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.hasInsert.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) a (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (Nat.succ a) b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b))
but is expected to have type
  forall {a : Nat} {b : Nat}, (LT.lt.{0} Nat instLTNat a b) -> (Eq.{1} (Finset.{0} Nat) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.instInsertFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) a (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Nat.succ a) b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b))
Case conversion may be inaccurate. Consider using '#align nat.Ico_insert_succ_left Nat.Ico_insert_succ_leftₓ'. -/
theorem Ico_insert_succ_left (h : a < b) : insert a (Ico a.succ b) = Ico a b := by
  rw [Ico_succ_left, ← Ioo_insert_left h]
#align nat.Ico_insert_succ_left Nat.Ico_insert_succ_left

/- warning: nat.image_sub_const_Ico -> Nat.image_sub_const_Ico is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat} {c : Nat}, (LE.le.{0} Nat Nat.hasLe c a) -> (Eq.{1} (Finset.{0} Nat) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (fun (x : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) x c) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) a c) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) b c)))
but is expected to have type
  forall {a : Nat} {b : Nat} {c : Nat}, (LE.le.{0} Nat instLENat c a) -> (Eq.{1} (Finset.{0} Nat) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (fun (x : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) x c) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) a c) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) b c)))
Case conversion may be inaccurate. Consider using '#align nat.image_sub_const_Ico Nat.image_sub_const_Icoₓ'. -/
theorem image_sub_const_Ico (h : c ≤ a) : ((Ico a b).image fun x => x - c) = Ico (a - c) (b - c) :=
  by
  ext x
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ico] at hx⊢
    exact ⟨tsub_le_tsub_right hx.1 _, tsub_lt_tsub_right_of_le (h.trans hx.1) hx.2⟩
  · rintro h
    refine' ⟨x + c, _, add_tsub_cancel_right _ _⟩
    rw [mem_Ico] at h⊢
    exact ⟨tsub_le_iff_right.1 h.1, lt_tsub_iff_right.1 h.2⟩
#align nat.image_sub_const_Ico Nat.image_sub_const_Ico

/- warning: nat.Ico_image_const_sub_eq_Ico -> Nat.Ico_image_const_sub_eq_Ico is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat} {c : Nat}, (LE.le.{0} Nat Nat.hasLe a c) -> (Eq.{1} (Finset.{0} Nat) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (fun (x : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) c x) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) c (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) b) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) c (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a)))
but is expected to have type
  forall {a : Nat} {b : Nat} {c : Nat}, (LE.le.{0} Nat instLENat a c) -> (Eq.{1} (Finset.{0} Nat) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (fun (x : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) c x) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) c (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) b) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) c (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a)))
Case conversion may be inaccurate. Consider using '#align nat.Ico_image_const_sub_eq_Ico Nat.Ico_image_const_sub_eq_Icoₓ'. -/
theorem Ico_image_const_sub_eq_Ico (hac : a ≤ c) :
    ((Ico a b).image fun x => c - x) = Ico (c + 1 - b) (c + 1 - a) :=
  by
  ext x
  rw [mem_image, mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ico] at hx
    refine'
      ⟨_,
        ((tsub_le_tsub_iff_left hac).2 hx.1).trans_lt
          ((tsub_lt_tsub_iff_right hac).2 (Nat.lt_succ_self _))⟩
    cases lt_or_le c b
    · rw [tsub_eq_zero_iff_le.mpr (succ_le_of_lt h)]
      exact zero_le _
    · rw [← succ_sub_succ c]
      exact (tsub_le_tsub_iff_left (succ_le_succ <| hx.2.le.trans h)).2 hx.2
  · rintro ⟨hb, ha⟩
    rw [lt_tsub_iff_left, lt_succ_iff] at ha
    have hx : x ≤ c := (Nat.le_add_left _ _).trans ha
    refine' ⟨c - x, _, tsub_tsub_cancel_of_le hx⟩
    · rw [mem_Ico]
      exact
        ⟨le_tsub_of_add_le_right ha,
          (tsub_lt_iff_left hx).2 <| succ_le_iff.1 <| tsub_le_iff_right.1 hb⟩
#align nat.Ico_image_const_sub_eq_Ico Nat.Ico_image_const_sub_eq_Ico

/- warning: nat.Ico_succ_left_eq_erase_Ico -> Nat.Ico_succ_left_eq_erase_Ico is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat}, Eq.{1} (Finset.{0} Nat) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (Nat.succ a) b) (Finset.erase.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder a b) a)
but is expected to have type
  forall {a : Nat} {b : Nat}, Eq.{1} (Finset.{0} Nat) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Nat.succ a) b) (Finset.erase.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring a b) a)
Case conversion may be inaccurate. Consider using '#align nat.Ico_succ_left_eq_erase_Ico Nat.Ico_succ_left_eq_erase_Icoₓ'. -/
theorem Ico_succ_left_eq_erase_Ico : Ico a.succ b = erase (Ico a b) a :=
  by
  ext x
  rw [Ico_succ_left, mem_erase, mem_Ico, mem_Ioo, ← and_assoc', ne_comm, and_comm' (a ≠ x),
    lt_iff_le_and_ne]
#align nat.Ico_succ_left_eq_erase_Ico Nat.Ico_succ_left_eq_erase_Ico

#print Nat.mod_injOn_Ico /-
theorem mod_injOn_Ico (n a : ℕ) : Set.InjOn (· % a) (Finset.Ico n (n + a)) :=
  by
  induction' n with n ih
  · simp only [zero_add, nat_zero_eq_zero, Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [Finset.mem_range, Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
  rw [Ico_succ_left_eq_erase_Ico, succ_add, Ico_succ_right_eq_insert_Ico le_self_add]
  rintro k hk l hl (hkl : k % a = l % a)
  have ha : 0 < a := by
    by_contra ha
    simp only [not_lt, nonpos_iff_eq_zero] at ha
    simpa [ha] using hk
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hk hl
  rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
  · rfl
  · rw [add_mod_right] at hkl
    refine' (hln <| ih hl _ hkl.symm).elim
    simp only [lt_add_iff_pos_right, Set.left_mem_Ico, Finset.coe_Ico, ha]
  · rw [add_mod_right] at hkl
    suffices k = n by contradiction
    refine' ih hk _ hkl
    simp only [lt_add_iff_pos_right, Set.left_mem_Ico, Finset.coe_Ico, ha]
  · refine' ih _ _ hkl <;> simp only [Finset.mem_coe, hk, hl]
#align nat.mod_inj_on_Ico Nat.mod_injOn_Ico
-/

/- warning: nat.image_Ico_mod -> Nat.image_Ico_mod is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (a : Nat), Eq.{1} (Finset.{0} Nat) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (fun (_x : Nat) => HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) _x a) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n a))) (Finset.range a)
but is expected to have type
  forall (n : Nat) (a : Nat), Eq.{1} (Finset.{0} Nat) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (fun (_x : Nat) => HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) _x a) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n a))) (Finset.range a)
Case conversion may be inaccurate. Consider using '#align nat.image_Ico_mod Nat.image_Ico_modₓ'. -/
/-- Note that while this lemma cannot be easily generalized to a type class, it holds for ℤ as
well. See `int.image_Ico_mod` for the ℤ version. -/
theorem image_Ico_mod (n a : ℕ) : (Ico n (n + a)).image (· % a) = range a :=
  by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zero, Ico_self, image_empty]
  ext i
  simp only [mem_image, exists_prop, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, h, rfl⟩
    exact mod_lt i ha.bot_lt
  intro hia
  have hn := Nat.mod_add_div n a
  obtain hi | hi := lt_or_le i (n % a)
  · refine' ⟨i + a * (n / a + 1), ⟨_, _⟩, _⟩
    · rw [add_comm (n / a), mul_add, mul_one, ← add_assoc]
      refine' hn.symm.le.trans (add_le_add_right _ _)
      simpa only [zero_add] using add_le_add (zero_le i) (Nat.mod_lt n ha.bot_lt).le
    · refine' lt_of_lt_of_le (add_lt_add_right hi (a * (n / a + 1))) _
      rw [mul_add, mul_one, ← add_assoc, hn]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
  · refine' ⟨i + a * (n / a), ⟨_, _⟩, _⟩
    · exact hn.symm.le.trans (add_le_add_right hi _)
    · rw [add_comm n a]
      refine' add_lt_add_of_lt_of_le hia (le_trans _ hn.le)
      simp only [zero_le, le_add_iff_nonneg_left]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
#align nat.image_Ico_mod Nat.image_Ico_mod

section Multiset

open Multiset

#print Nat.multiset_Ico_map_mod /-
theorem multiset_Ico_map_mod (n a : ℕ) : (Multiset.Ico n (n + a)).map (· % a) = range a :=
  by
  convert congr_arg Finset.val (image_Ico_mod n a)
  refine' ((nodup_map_iff_inj_on (Finset.Ico _ _).Nodup).2 <| _).dedup.symm
  exact mod_inj_on_Ico _ _
#align nat.multiset_Ico_map_mod Nat.multiset_Ico_map_mod
-/

end Multiset

end Nat

namespace Finset

/- warning: finset.range_image_pred_top_sub -> Finset.range_image_pred_top_sub is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (Finset.{0} Nat) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (fun (j : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) j) (Finset.range n)) (Finset.range n)
but is expected to have type
  forall (n : Nat), Eq.{1} (Finset.{0} Nat) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (fun (j : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) j) (Finset.range n)) (Finset.range n)
Case conversion may be inaccurate. Consider using '#align finset.range_image_pred_top_sub Finset.range_image_pred_top_subₓ'. -/
theorem range_image_pred_top_sub (n : ℕ) :
    ((Finset.range n).image fun j => n - 1 - j) = Finset.range n :=
  by
  cases n
  · rw [range_zero, image_empty]
  · rw [Finset.range_eq_Ico, Nat.Ico_image_const_sub_eq_Ico (zero_le _)]
    simp_rw [succ_sub_succ, tsub_zero, tsub_self]
#align finset.range_image_pred_top_sub Finset.range_image_pred_top_sub

/- warning: finset.range_add_eq_union -> Finset.range_add_eq_union is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (b : Nat), Eq.{1} (Finset.{0} Nat) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Union.union.{0} (Finset.{0} Nat) (Finset.hasUnion.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) (Finset.range a) (Finset.map.{0, 0} Nat Nat (addLeftEmbedding.{0} Nat (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Nat (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) a) (Finset.range b)))
but is expected to have type
  forall (a : Nat) (b : Nat), Eq.{1} (Finset.{0} Nat) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (Union.union.{0} (Finset.{0} Nat) (Finset.instUnionFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) (Finset.range a) (Finset.map.{0, 0} Nat Nat (addLeftEmbedding.{0} Nat (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Nat (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) a) (Finset.range b)))
Case conversion may be inaccurate. Consider using '#align finset.range_add_eq_union Finset.range_add_eq_unionₓ'. -/
theorem range_add_eq_union : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) :=
  by
  rw [Finset.range_eq_Ico, map_eq_image]
  convert (Ico_union_Ico_eq_Ico a.zero_le le_self_add).symm
  exact image_add_left_Ico _ _ _
#align finset.range_add_eq_union Finset.range_add_eq_union

end Finset

section Induction

variable {P : ℕ → Prop} (h : ∀ n, P (n + 1) → P n)

include h

#print Nat.decreasing_induction_of_not_bddAbove /-
theorem Nat.decreasing_induction_of_not_bddAbove (hP : ¬BddAbove { x | P x }) (n : ℕ) : P n :=
  let ⟨m, hm, hl⟩ := not_bddAbove_iff.1 hP n
  decreasingInduction h hl.le hm
#align nat.decreasing_induction_of_not_bdd_above Nat.decreasing_induction_of_not_bddAbove
-/

#print Nat.decreasing_induction_of_infinite /-
theorem Nat.decreasing_induction_of_infinite (hP : { x | P x }.Infinite) (n : ℕ) : P n :=
  Nat.decreasing_induction_of_not_bddAbove h (mt BddAbove.finite hP) n
#align nat.decreasing_induction_of_infinite Nat.decreasing_induction_of_infinite
-/

#print Nat.cauchy_induction' /-
theorem Nat.cauchy_induction' (seed : ℕ) (hs : P seed) (hi : ∀ x, seed ≤ x → P x → ∃ y, x < y ∧ P y)
    (n : ℕ) : P n := by
  apply Nat.decreasing_induction_of_infinite h fun hf => _
  obtain ⟨m, hP, hm⟩ := hf.exists_maximal_wrt id _ ⟨seed, hs⟩
  obtain ⟨y, hl, hy⟩ := hi m (le_of_not_lt fun hl => hl.Ne <| hm seed hs hl.le) hP
  exact hl.ne (hm y hy hl.le)
#align nat.cauchy_induction' Nat.cauchy_induction'
-/

#print Nat.cauchy_induction /-
theorem Nat.cauchy_induction (seed : ℕ) (hs : P seed) (f : ℕ → ℕ)
    (hf : ∀ x, seed ≤ x → P x → x < f x ∧ P (f x)) (n : ℕ) : P n :=
  seed.cauchy_induction' h hs (fun x hl hx => ⟨f x, hf x hl hx⟩) n
#align nat.cauchy_induction Nat.cauchy_induction
-/

#print Nat.cauchy_induction_mul /-
theorem Nat.cauchy_induction_mul (k seed : ℕ) (hk : 1 < k) (hs : P seed.succ)
    (hm : ∀ x, seed < x → P x → P (k * x)) (n : ℕ) : P n :=
  by
  apply Nat.cauchy_induction h _ hs ((· * ·) k) fun x hl hP => ⟨_, hm x hl hP⟩
  convert (mul_lt_mul_right <| seed.succ_pos.trans_le hl).2 hk
  rw [one_mul]
#align nat.cauchy_induction_mul Nat.cauchy_induction_mul
-/

#print Nat.cauchy_induction_two_mul /-
theorem Nat.cauchy_induction_two_mul (seed : ℕ) (hs : P seed.succ)
    (hm : ∀ x, seed < x → P x → P (2 * x)) (n : ℕ) : P n :=
  Nat.cauchy_induction_mul h 2 seed one_lt_two hs hm n
#align nat.cauchy_induction_two_mul Nat.cauchy_induction_two_mul
-/

end Induction

