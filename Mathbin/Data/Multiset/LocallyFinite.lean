/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.multiset.locally_finite
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.LocallyFinite

/-!
# Intervals as multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides basic results about all the `multiset.Ixx`, which are defined in
`order.locally_finite`.

Note that intervals of multisets themselves (`multiset.locally_finite_order`) are defined elsewhere.
-/


variable {α : Type _}

namespace Multiset

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] {a b c : α}

#print Multiset.nodup_Icc /-
theorem nodup_Icc : (Icc a b).Nodup :=
  Finset.nodup _
#align multiset.nodup_Icc Multiset.nodup_Icc
-/

#print Multiset.nodup_Ico /-
theorem nodup_Ico : (Ico a b).Nodup :=
  Finset.nodup _
#align multiset.nodup_Ico Multiset.nodup_Ico
-/

#print Multiset.nodup_Ioc /-
theorem nodup_Ioc : (Ioc a b).Nodup :=
  Finset.nodup _
#align multiset.nodup_Ioc Multiset.nodup_Ioc
-/

#print Multiset.nodup_Ioo /-
theorem nodup_Ioo : (Ioo a b).Nodup :=
  Finset.nodup _
#align multiset.nodup_Ioo Multiset.nodup_Ioo
-/

#print Multiset.Icc_eq_zero_iff /-
@[simp]
theorem Icc_eq_zero_iff : Icc a b = 0 ↔ ¬a ≤ b := by
  rw [Icc, Finset.val_eq_zero, Finset.Icc_eq_empty_iff]
#align multiset.Icc_eq_zero_iff Multiset.Icc_eq_zero_iff
-/

#print Multiset.Ico_eq_zero_iff /-
@[simp]
theorem Ico_eq_zero_iff : Ico a b = 0 ↔ ¬a < b := by
  rw [Ico, Finset.val_eq_zero, Finset.Ico_eq_empty_iff]
#align multiset.Ico_eq_zero_iff Multiset.Ico_eq_zero_iff
-/

#print Multiset.Ioc_eq_zero_iff /-
@[simp]
theorem Ioc_eq_zero_iff : Ioc a b = 0 ↔ ¬a < b := by
  rw [Ioc, Finset.val_eq_zero, Finset.Ioc_eq_empty_iff]
#align multiset.Ioc_eq_zero_iff Multiset.Ioc_eq_zero_iff
-/

#print Multiset.Ioo_eq_zero_iff /-
@[simp]
theorem Ioo_eq_zero_iff [DenselyOrdered α] : Ioo a b = 0 ↔ ¬a < b := by
  rw [Ioo, Finset.val_eq_zero, Finset.Ioo_eq_empty_iff]
#align multiset.Ioo_eq_zero_iff Multiset.Ioo_eq_zero_iff
-/

alias Icc_eq_zero_iff ↔ _ Icc_eq_zero
#align multiset.Icc_eq_zero Multiset.Icc_eq_zero

alias Ico_eq_zero_iff ↔ _ Ico_eq_zero
#align multiset.Ico_eq_zero Multiset.Ico_eq_zero

alias Ioc_eq_zero_iff ↔ _ Ioc_eq_zero
#align multiset.Ioc_eq_zero Multiset.Ioc_eq_zero

#print Multiset.Ioo_eq_zero /-
@[simp]
theorem Ioo_eq_zero (h : ¬a < b) : Ioo a b = 0 :=
  eq_zero_iff_forall_not_mem.2 fun x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)
#align multiset.Ioo_eq_zero Multiset.Ioo_eq_zero
-/

#print Multiset.Icc_eq_zero_of_lt /-
@[simp]
theorem Icc_eq_zero_of_lt (h : b < a) : Icc a b = 0 :=
  Icc_eq_zero h.not_le
#align multiset.Icc_eq_zero_of_lt Multiset.Icc_eq_zero_of_lt
-/

#print Multiset.Ico_eq_zero_of_le /-
@[simp]
theorem Ico_eq_zero_of_le (h : b ≤ a) : Ico a b = 0 :=
  Ico_eq_zero h.not_lt
#align multiset.Ico_eq_zero_of_le Multiset.Ico_eq_zero_of_le
-/

#print Multiset.Ioc_eq_zero_of_le /-
@[simp]
theorem Ioc_eq_zero_of_le (h : b ≤ a) : Ioc a b = 0 :=
  Ioc_eq_zero h.not_lt
#align multiset.Ioc_eq_zero_of_le Multiset.Ioc_eq_zero_of_le
-/

#print Multiset.Ioo_eq_zero_of_le /-
@[simp]
theorem Ioo_eq_zero_of_le (h : b ≤ a) : Ioo a b = 0 :=
  Ioo_eq_zero h.not_lt
#align multiset.Ioo_eq_zero_of_le Multiset.Ioo_eq_zero_of_le
-/

variable (a)

#print Multiset.Ico_self /-
@[simp]
theorem Ico_self : Ico a a = 0 := by rw [Ico, Finset.Ico_self, Finset.empty_val]
#align multiset.Ico_self Multiset.Ico_self
-/

#print Multiset.Ioc_self /-
@[simp]
theorem Ioc_self : Ioc a a = 0 := by rw [Ioc, Finset.Ioc_self, Finset.empty_val]
#align multiset.Ioc_self Multiset.Ioc_self
-/

#print Multiset.Ioo_self /-
@[simp]
theorem Ioo_self : Ioo a a = 0 := by rw [Ioo, Finset.Ioo_self, Finset.empty_val]
#align multiset.Ioo_self Multiset.Ioo_self
-/

variable {a b c}

#print Multiset.left_mem_Icc /-
theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b :=
  Finset.left_mem_Icc
#align multiset.left_mem_Icc Multiset.left_mem_Icc
-/

#print Multiset.left_mem_Ico /-
theorem left_mem_Ico : a ∈ Ico a b ↔ a < b :=
  Finset.left_mem_Ico
#align multiset.left_mem_Ico Multiset.left_mem_Ico
-/

#print Multiset.right_mem_Icc /-
theorem right_mem_Icc : b ∈ Icc a b ↔ a ≤ b :=
  Finset.right_mem_Icc
#align multiset.right_mem_Icc Multiset.right_mem_Icc
-/

#print Multiset.right_mem_Ioc /-
theorem right_mem_Ioc : b ∈ Ioc a b ↔ a < b :=
  Finset.right_mem_Ioc
#align multiset.right_mem_Ioc Multiset.right_mem_Ioc
-/

#print Multiset.left_not_mem_Ioc /-
@[simp]
theorem left_not_mem_Ioc : a ∉ Ioc a b :=
  Finset.left_not_mem_Ioc
#align multiset.left_not_mem_Ioc Multiset.left_not_mem_Ioc
-/

#print Multiset.left_not_mem_Ioo /-
@[simp]
theorem left_not_mem_Ioo : a ∉ Ioo a b :=
  Finset.left_not_mem_Ioo
#align multiset.left_not_mem_Ioo Multiset.left_not_mem_Ioo
-/

#print Multiset.right_not_mem_Ico /-
@[simp]
theorem right_not_mem_Ico : b ∉ Ico a b :=
  Finset.right_not_mem_Ico
#align multiset.right_not_mem_Ico Multiset.right_not_mem_Ico
-/

#print Multiset.right_not_mem_Ioo /-
@[simp]
theorem right_not_mem_Ioo : b ∉ Ioo a b :=
  Finset.right_not_mem_Ioo
#align multiset.right_not_mem_Ioo Multiset.right_not_mem_Ioo
-/

#print Multiset.Ico_filter_lt_of_le_left /-
theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    ((Ico a b).filterₓ fun x => x < c) = ∅ :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_left hca]
  rfl
#align multiset.Ico_filter_lt_of_le_left Multiset.Ico_filter_lt_of_le_left
-/

#print Multiset.Ico_filter_lt_of_right_le /-
theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    ((Ico a b).filterₓ fun x => x < c) = Ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_right_le hbc]
#align multiset.Ico_filter_lt_of_right_le Multiset.Ico_filter_lt_of_right_le
-/

#print Multiset.Ico_filter_lt_of_le_right /-
theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    ((Ico a b).filterₓ fun x => x < c) = Ico a c :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_right hcb]
  rfl
#align multiset.Ico_filter_lt_of_le_right Multiset.Ico_filter_lt_of_le_right
-/

#print Multiset.Ico_filter_le_of_le_left /-
theorem Ico_filter_le_of_le_left [DecidablePred ((· ≤ ·) c)] (hca : c ≤ a) :
    ((Ico a b).filterₓ fun x => c ≤ x) = Ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_le_left hca]
#align multiset.Ico_filter_le_of_le_left Multiset.Ico_filter_le_of_le_left
-/

#print Multiset.Ico_filter_le_of_right_le /-
theorem Ico_filter_le_of_right_le [DecidablePred ((· ≤ ·) b)] :
    ((Ico a b).filterₓ fun x => b ≤ x) = ∅ :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_right_le]
  rfl
#align multiset.Ico_filter_le_of_right_le Multiset.Ico_filter_le_of_right_le
-/

#print Multiset.Ico_filter_le_of_left_le /-
theorem Ico_filter_le_of_left_le [DecidablePred ((· ≤ ·) c)] (hac : a ≤ c) :
    ((Ico a b).filterₓ fun x => c ≤ x) = Ico c b :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_left_le hac]
  rfl
#align multiset.Ico_filter_le_of_left_le Multiset.Ico_filter_le_of_left_le
-/

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b : α}

#print Multiset.Icc_self /-
@[simp]
theorem Icc_self (a : α) : Icc a a = {a} := by rw [Icc, Finset.Icc_self, Finset.singleton_val]
#align multiset.Icc_self Multiset.Icc_self
-/

#print Multiset.Ico_cons_right /-
theorem Ico_cons_right (h : a ≤ b) : b ::ₘ Ico a b = Icc a b := by
  classical
    rw [Ico, ← Finset.insert_val_of_not_mem right_not_mem_Ico, Finset.Ico_insert_right h]
    rfl
#align multiset.Ico_cons_right Multiset.Ico_cons_right
-/

#print Multiset.Ioo_cons_left /-
theorem Ioo_cons_left (h : a < b) : a ::ₘ Ioo a b = Ico a b := by
  classical
    rw [Ioo, ← Finset.insert_val_of_not_mem left_not_mem_Ioo, Finset.Ioo_insert_left h]
    rfl
#align multiset.Ioo_cons_left Multiset.Ioo_cons_left
-/

#print Multiset.Ico_disjoint_Ico /-
theorem Ico_disjoint_Ico {a b c d : α} (h : b ≤ c) : (Ico a b).Disjoint (Ico c d) :=
  fun x hab hbc => by
  rw [mem_Ico] at hab hbc
  exact hab.2.not_le (h.trans hbc.1)
#align multiset.Ico_disjoint_Ico Multiset.Ico_disjoint_Ico
-/

#print Multiset.Ico_inter_Ico_of_le /-
@[simp]
theorem Ico_inter_Ico_of_le [DecidableEq α] {a b c d : α} (h : b ≤ c) : Ico a b ∩ Ico c d = 0 :=
  Multiset.inter_eq_zero_iff_disjoint.2 <| Ico_disjoint_Ico h
#align multiset.Ico_inter_Ico_of_le Multiset.Ico_inter_Ico_of_le
-/

#print Multiset.Ico_filter_le_left /-
theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    ((Ico a b).filterₓ fun x => x ≤ a) = {a} :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_left hab]
  rfl
#align multiset.Ico_filter_le_left Multiset.Ico_filter_le_left
-/

/- warning: multiset.card_Ico_eq_card_Icc_sub_one -> Multiset.card_Ico_eq_card_Icc_sub_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (HSub.hSub.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (instHSub.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) instSubNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align multiset.card_Ico_eq_card_Icc_sub_one Multiset.card_Ico_eq_card_Icc_sub_oneₓ'. -/
theorem card_Ico_eq_card_Icc_sub_one (a b : α) : (Ico a b).card = (Icc a b).card - 1 :=
  Finset.card_Ico_eq_card_Icc_sub_one _ _
#align multiset.card_Ico_eq_card_Icc_sub_one Multiset.card_Ico_eq_card_Icc_sub_one

/- warning: multiset.card_Ioc_eq_card_Icc_sub_one -> Multiset.card_Ioc_eq_card_Icc_sub_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (HSub.hSub.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (instHSub.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) instSubNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align multiset.card_Ioc_eq_card_Icc_sub_one Multiset.card_Ioc_eq_card_Icc_sub_oneₓ'. -/
theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : (Ioc a b).card = (Icc a b).card - 1 :=
  Finset.card_Ioc_eq_card_Icc_sub_one _ _
#align multiset.card_Ioc_eq_card_Icc_sub_one Multiset.card_Ioc_eq_card_Icc_sub_one

/- warning: multiset.card_Ioo_eq_card_Ico_sub_one -> Multiset.card_Ioo_eq_card_Ico_sub_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (HSub.hSub.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (instHSub.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) instSubNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align multiset.card_Ioo_eq_card_Ico_sub_one Multiset.card_Ioo_eq_card_Ico_sub_oneₓ'. -/
theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : (Ioo a b).card = (Ico a b).card - 1 :=
  Finset.card_Ioo_eq_card_Ico_sub_one _ _
#align multiset.card_Ioo_eq_card_Ico_sub_one Multiset.card_Ioo_eq_card_Ico_sub_one

/- warning: multiset.card_Ioo_eq_card_Icc_sub_two -> Multiset.card_Ioo_eq_card_Icc_sub_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α), Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (a : α) (b : α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (HSub.hSub.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (instHSub.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) instSubNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a b)) 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align multiset.card_Ioo_eq_card_Icc_sub_two Multiset.card_Ioo_eq_card_Icc_sub_twoₓ'. -/
theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : (Ioo a b).card = (Icc a b).card - 2 :=
  Finset.card_Ioo_eq_card_Icc_sub_two _ _
#align multiset.card_Ioo_eq_card_Icc_sub_two Multiset.card_Ioo_eq_card_Icc_sub_two

end PartialOrder

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a b c d : α}

#print Multiset.Ico_subset_Ico_iff /-
theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  Finset.Ico_subset_Ico_iff h
#align multiset.Ico_subset_Ico_iff Multiset.Ico_subset_Ico_iff
-/

#print Multiset.Ico_add_Ico_eq_Ico /-
theorem Ico_add_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) : Ico a b + Ico b c = Ico a c :=
  by
  rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl), Ico, Ico, Ico, ← Finset.union_val,
    Finset.Ico_union_Ico_eq_Ico hab hbc]
#align multiset.Ico_add_Ico_eq_Ico Multiset.Ico_add_Ico_eq_Ico
-/

/- warning: multiset.Ico_inter_Ico -> Multiset.Ico_inter_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] {a : α} {b : α} {c : α} {d : α}, Eq.{succ u1} (Multiset.{u1} α) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.hasInter.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 c d)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 (LinearOrder.max.{u1} α _inst_1 a c) (LinearOrder.min.{u1} α _inst_1 b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] {a : α} {b : α} {c : α} {d : α}, Eq.{succ u1} (Multiset.{u1} α) (Inter.inter.{u1} (Multiset.{u1} α) (Multiset.instInterMultiset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 c d)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a c) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align multiset.Ico_inter_Ico Multiset.Ico_inter_Icoₓ'. -/
theorem Ico_inter_Ico : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [Ico, Ico, Ico, ← Finset.inter_val, Finset.Ico_inter_Ico]
#align multiset.Ico_inter_Ico Multiset.Ico_inter_Ico

#print Multiset.Ico_filter_lt /-
@[simp]
theorem Ico_filter_lt (a b c : α) : ((Ico a b).filterₓ fun x => x < c) = Ico a (min b c) := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_lt]
#align multiset.Ico_filter_lt Multiset.Ico_filter_lt
-/

#print Multiset.Ico_filter_le /-
@[simp]
theorem Ico_filter_le (a b c : α) : ((Ico a b).filterₓ fun x => c ≤ x) = Ico (max a c) b := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_le]
#align multiset.Ico_filter_le Multiset.Ico_filter_le
-/

/- warning: multiset.Ico_sub_Ico_left -> Multiset.Ico_sub_Ico_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.hasSub.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b))) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a c)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 (LinearOrder.max.{u1} α _inst_1 a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b))) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a c)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a c) b)
Case conversion may be inaccurate. Consider using '#align multiset.Ico_sub_Ico_left Multiset.Ico_sub_Ico_leftₓ'. -/
@[simp]
theorem Ico_sub_Ico_left (a b c : α) : Ico a b - Ico a c = Ico (max a c) b := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_diff_Ico_left]
#align multiset.Ico_sub_Ico_left Multiset.Ico_sub_Ico_left

/- warning: multiset.Ico_sub_Ico_right -> Multiset.Ico_sub_Ico_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.hasSub.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b))) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a b) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 c b)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 a (LinearOrder.min.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (HSub.hSub.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHSub.{u1} (Multiset.{u1} α) (Multiset.instSubMultiset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b))) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a b) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 c b)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 a (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align multiset.Ico_sub_Ico_right Multiset.Ico_sub_Ico_rightₓ'. -/
@[simp]
theorem Ico_sub_Ico_right (a b c : α) : Ico a b - Ico c b = Ico a (min b c) := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_diff_Ico_right]
#align multiset.Ico_sub_Ico_right Multiset.Ico_sub_Ico_right

end LinearOrder

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]

/- warning: multiset.map_add_left_Icc -> Multiset.map_add_left_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α ((fun (x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2600 : α) (x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2602 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2600 x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2602) c) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_left_Icc Multiset.map_add_left_Iccₓ'. -/
theorem map_add_left_Icc (a b c : α) : (Icc a b).map ((· + ·) c) = Icc (c + a) (c + b) := by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Icc Multiset.map_add_left_Icc

/- warning: multiset.map_add_left_Ico -> Multiset.map_add_left_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α ((fun (x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2705 : α) (x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2707 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2705 x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2707) c) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_left_Ico Multiset.map_add_left_Icoₓ'. -/
theorem map_add_left_Ico (a b c : α) : (Ico a b).map ((· + ·) c) = Ico (c + a) (c + b) := by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ico Multiset.map_add_left_Ico

/- warning: multiset.map_add_left_Ioc -> Multiset.map_add_left_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α ((fun (x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2810 : α) (x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2812 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2810 x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2812) c) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_left_Ioc Multiset.map_add_left_Iocₓ'. -/
theorem map_add_left_Ioc (a b c : α) : (Ioc a b).map ((· + ·) c) = Ioc (c + a) (c + b) := by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ioc Multiset.map_add_left_Ioc

/- warning: multiset.map_add_left_Ioo -> Multiset.map_add_left_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α ((fun (x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2915 : α) (x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2917 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2915 x._@.Mathlib.Data.Multiset.LocallyFinite._hyg.2917) c) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c a) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) c b))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_left_Ioo Multiset.map_add_left_Iooₓ'. -/
theorem map_add_left_Ioo (a b c : α) : (Ioo a b).map ((· + ·) c) = Ioo (c + a) (c + b) := by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ioo Multiset.map_add_left_Ioo

/- warning: multiset.map_add_right_Icc -> Multiset.map_add_right_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x c) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x c) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_right_Icc Multiset.map_add_right_Iccₓ'. -/
theorem map_add_right_Icc (a b c : α) : ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c) :=
  by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _
#align multiset.map_add_right_Icc Multiset.map_add_right_Icc

/- warning: multiset.map_add_right_Ico -> Multiset.map_add_right_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x c) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x c) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ico.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_right_Ico Multiset.map_add_right_Icoₓ'. -/
theorem map_add_right_Ico (a b c : α) : ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c) :=
  by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _
#align multiset.map_add_right_Ico Multiset.map_add_right_Ico

/- warning: multiset.map_add_right_Ioc -> Multiset.map_add_right_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x c) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x c) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_right_Ioc Multiset.map_add_right_Iocₓ'. -/
theorem map_add_right_Ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c) :=
  by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _
#align multiset.map_add_right_Ioc Multiset.map_add_right_Ioc

/- warning: multiset.map_add_right_Ioo -> Multiset.map_add_right_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x c) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelAddCommMonoid.{u1} α] [_inst_2 : ExistsAddOfLE.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1)))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1))] (a : α) (b : α) (c : α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u1, u1} α α (fun (x : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) x c) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 a b)) (Multiset.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α _inst_1)) _inst_3 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddRightCancelMonoid.toAddMonoid.{u1} α (AddCancelMonoid.toAddRightCancelMonoid.{u1} α (AddCancelCommMonoid.toAddCancelMonoid.{u1} α (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} α _inst_1))))))) b c))
Case conversion may be inaccurate. Consider using '#align multiset.map_add_right_Ioo Multiset.map_add_right_Iooₓ'. -/
theorem map_add_right_Ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c) :=
  by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _
#align multiset.map_add_right_Ioo Multiset.map_add_right_Ioo

end OrderedCancelAddCommMonoid

end Multiset

