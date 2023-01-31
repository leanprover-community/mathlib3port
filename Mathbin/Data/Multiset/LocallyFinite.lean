/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.multiset.locally_finite
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.LocallyFinite

/-!
# Intervals as multisets

This file provides basic results about all the `multiset.Ixx`, which are defined in
`order.locally_finite`.

Note that intervals of multisets themselves (`multiset.locally_finite_order`) are defined elsewhere.
-/


variable {α : Type _}

namespace Multiset

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] {a b c : α}

theorem nodup_icc : (Icc a b).Nodup :=
  Finset.nodup _
#align multiset.nodup_Icc Multiset.nodup_icc

theorem nodup_ico : (Ico a b).Nodup :=
  Finset.nodup _
#align multiset.nodup_Ico Multiset.nodup_ico

theorem nodup_ioc : (Ioc a b).Nodup :=
  Finset.nodup _
#align multiset.nodup_Ioc Multiset.nodup_ioc

theorem nodup_ioo : (Ioo a b).Nodup :=
  Finset.nodup _
#align multiset.nodup_Ioo Multiset.nodup_ioo

@[simp]
theorem icc_eq_zero_iff : Icc a b = 0 ↔ ¬a ≤ b := by
  rw [Icc, Finset.val_eq_zero, Finset.Icc_eq_empty_iff]
#align multiset.Icc_eq_zero_iff Multiset.icc_eq_zero_iff

@[simp]
theorem ico_eq_zero_iff : Ico a b = 0 ↔ ¬a < b := by
  rw [Ico, Finset.val_eq_zero, Finset.Ico_eq_empty_iff]
#align multiset.Ico_eq_zero_iff Multiset.ico_eq_zero_iff

@[simp]
theorem ioc_eq_zero_iff : Ioc a b = 0 ↔ ¬a < b := by
  rw [Ioc, Finset.val_eq_zero, Finset.Ioc_eq_empty_iff]
#align multiset.Ioc_eq_zero_iff Multiset.ioc_eq_zero_iff

@[simp]
theorem ioo_eq_zero_iff [DenselyOrdered α] : Ioo a b = 0 ↔ ¬a < b := by
  rw [Ioo, Finset.val_eq_zero, Finset.Ioo_eq_empty_iff]
#align multiset.Ioo_eq_zero_iff Multiset.ioo_eq_zero_iff

alias Icc_eq_zero_iff ↔ _ Icc_eq_zero
#align multiset.Icc_eq_zero Multiset.icc_eq_zero

alias Ico_eq_zero_iff ↔ _ Ico_eq_zero
#align multiset.Ico_eq_zero Multiset.ico_eq_zero

alias Ioc_eq_zero_iff ↔ _ Ioc_eq_zero
#align multiset.Ioc_eq_zero Multiset.ioc_eq_zero

@[simp]
theorem ioo_eq_zero (h : ¬a < b) : Ioo a b = 0 :=
  eq_zero_iff_forall_not_mem.2 fun x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)
#align multiset.Ioo_eq_zero Multiset.ioo_eq_zero

@[simp]
theorem icc_eq_zero_of_lt (h : b < a) : Icc a b = 0 :=
  icc_eq_zero h.not_le
#align multiset.Icc_eq_zero_of_lt Multiset.icc_eq_zero_of_lt

@[simp]
theorem ico_eq_zero_of_le (h : b ≤ a) : Ico a b = 0 :=
  ico_eq_zero h.not_lt
#align multiset.Ico_eq_zero_of_le Multiset.ico_eq_zero_of_le

@[simp]
theorem ioc_eq_zero_of_le (h : b ≤ a) : Ioc a b = 0 :=
  ioc_eq_zero h.not_lt
#align multiset.Ioc_eq_zero_of_le Multiset.ioc_eq_zero_of_le

@[simp]
theorem ioo_eq_zero_of_le (h : b ≤ a) : Ioo a b = 0 :=
  ioo_eq_zero h.not_lt
#align multiset.Ioo_eq_zero_of_le Multiset.ioo_eq_zero_of_le

variable (a)

@[simp]
theorem ico_self : Ico a a = 0 := by rw [Ico, Finset.Ico_self, Finset.empty_val]
#align multiset.Ico_self Multiset.ico_self

@[simp]
theorem ioc_self : Ioc a a = 0 := by rw [Ioc, Finset.Ioc_self, Finset.empty_val]
#align multiset.Ioc_self Multiset.ioc_self

@[simp]
theorem ioo_self : Ioo a a = 0 := by rw [Ioo, Finset.Ioo_self, Finset.empty_val]
#align multiset.Ioo_self Multiset.ioo_self

variable {a b c}

theorem left_mem_icc : a ∈ Icc a b ↔ a ≤ b :=
  Finset.left_mem_Icc
#align multiset.left_mem_Icc Multiset.left_mem_icc

theorem left_mem_ico : a ∈ Ico a b ↔ a < b :=
  Finset.left_mem_Ico
#align multiset.left_mem_Ico Multiset.left_mem_ico

theorem right_mem_icc : b ∈ Icc a b ↔ a ≤ b :=
  Finset.right_mem_Icc
#align multiset.right_mem_Icc Multiset.right_mem_icc

theorem right_mem_ioc : b ∈ Ioc a b ↔ a < b :=
  Finset.right_mem_Ioc
#align multiset.right_mem_Ioc Multiset.right_mem_ioc

@[simp]
theorem left_not_mem_ioc : a ∉ Ioc a b :=
  Finset.left_not_mem_Ioc
#align multiset.left_not_mem_Ioc Multiset.left_not_mem_ioc

@[simp]
theorem left_not_mem_ioo : a ∉ Ioo a b :=
  Finset.left_not_mem_Ioo
#align multiset.left_not_mem_Ioo Multiset.left_not_mem_ioo

@[simp]
theorem right_not_mem_ico : b ∉ Ico a b :=
  Finset.right_not_mem_Ico
#align multiset.right_not_mem_Ico Multiset.right_not_mem_ico

@[simp]
theorem right_not_mem_ioo : b ∉ Ioo a b :=
  Finset.right_not_mem_Ioo
#align multiset.right_not_mem_Ioo Multiset.right_not_mem_ioo

theorem ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    ((Ico a b).filter fun x => x < c) = ∅ :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_left hca]
  rfl
#align multiset.Ico_filter_lt_of_le_left Multiset.ico_filter_lt_of_le_left

theorem ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    ((Ico a b).filter fun x => x < c) = Ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_right_le hbc]
#align multiset.Ico_filter_lt_of_right_le Multiset.ico_filter_lt_of_right_le

theorem ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    ((Ico a b).filter fun x => x < c) = Ico a c :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_right hcb]
  rfl
#align multiset.Ico_filter_lt_of_le_right Multiset.ico_filter_lt_of_le_right

theorem ico_filter_le_of_le_left [DecidablePred ((· ≤ ·) c)] (hca : c ≤ a) :
    ((Ico a b).filter fun x => c ≤ x) = Ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_le_left hca]
#align multiset.Ico_filter_le_of_le_left Multiset.ico_filter_le_of_le_left

theorem ico_filter_le_of_right_le [DecidablePred ((· ≤ ·) b)] :
    ((Ico a b).filter fun x => b ≤ x) = ∅ :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_right_le]
  rfl
#align multiset.Ico_filter_le_of_right_le Multiset.ico_filter_le_of_right_le

theorem ico_filter_le_of_left_le [DecidablePred ((· ≤ ·) c)] (hac : a ≤ c) :
    ((Ico a b).filter fun x => c ≤ x) = Ico c b :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_left_le hac]
  rfl
#align multiset.Ico_filter_le_of_left_le Multiset.ico_filter_le_of_left_le

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b : α}

@[simp]
theorem icc_self (a : α) : Icc a a = {a} := by rw [Icc, Finset.Icc_self, Finset.singleton_val]
#align multiset.Icc_self Multiset.icc_self

theorem ico_cons_right (h : a ≤ b) : b ::ₘ Ico a b = Icc a b := by
  classical
    rw [Ico, ← Finset.insert_val_of_not_mem right_not_mem_Ico, Finset.Ico_insert_right h]
    rfl
#align multiset.Ico_cons_right Multiset.ico_cons_right

theorem ioo_cons_left (h : a < b) : a ::ₘ Ioo a b = Ico a b := by
  classical
    rw [Ioo, ← Finset.insert_val_of_not_mem left_not_mem_Ioo, Finset.Ioo_insert_left h]
    rfl
#align multiset.Ioo_cons_left Multiset.ioo_cons_left

theorem ico_disjoint_ico {a b c d : α} (h : b ≤ c) : (Ico a b).Disjoint (Ico c d) :=
  fun x hab hbc => by
  rw [mem_Ico] at hab hbc
  exact hab.2.not_le (h.trans hbc.1)
#align multiset.Ico_disjoint_Ico Multiset.ico_disjoint_ico

@[simp]
theorem ico_inter_ico_of_le [DecidableEq α] {a b c d : α} (h : b ≤ c) : Ico a b ∩ Ico c d = 0 :=
  Multiset.inter_eq_zero_iff_disjoint.2 <| ico_disjoint_ico h
#align multiset.Ico_inter_Ico_of_le Multiset.ico_inter_ico_of_le

theorem ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    ((Ico a b).filter fun x => x ≤ a) = {a} :=
  by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_left hab]
  rfl
#align multiset.Ico_filter_le_left Multiset.ico_filter_le_left

theorem card_ico_eq_card_icc_sub_one (a b : α) : (Ico a b).card = (Icc a b).card - 1 :=
  Finset.card_Ico_eq_card_Icc_sub_one _ _
#align multiset.card_Ico_eq_card_Icc_sub_one Multiset.card_ico_eq_card_icc_sub_one

theorem card_ioc_eq_card_icc_sub_one (a b : α) : (Ioc a b).card = (Icc a b).card - 1 :=
  Finset.card_Ioc_eq_card_Icc_sub_one _ _
#align multiset.card_Ioc_eq_card_Icc_sub_one Multiset.card_ioc_eq_card_icc_sub_one

theorem card_ioo_eq_card_ico_sub_one (a b : α) : (Ioo a b).card = (Ico a b).card - 1 :=
  Finset.card_Ioo_eq_card_Ico_sub_one _ _
#align multiset.card_Ioo_eq_card_Ico_sub_one Multiset.card_ioo_eq_card_ico_sub_one

theorem card_ioo_eq_card_icc_sub_two (a b : α) : (Ioo a b).card = (Icc a b).card - 2 :=
  Finset.card_Ioo_eq_card_Icc_sub_two _ _
#align multiset.card_Ioo_eq_card_Icc_sub_two Multiset.card_ioo_eq_card_icc_sub_two

end PartialOrder

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a b c d : α}

theorem ico_subset_ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  Finset.Ico_subset_Ico_iff h
#align multiset.Ico_subset_Ico_iff Multiset.ico_subset_ico_iff

theorem ico_add_ico_eq_ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) : Ico a b + Ico b c = Ico a c :=
  by
  rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl), Ico, Ico, Ico, ← Finset.union_val,
    Finset.Ico_union_Ico_eq_Ico hab hbc]
#align multiset.Ico_add_Ico_eq_Ico Multiset.ico_add_ico_eq_ico

theorem ico_inter_ico : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [Ico, Ico, Ico, ← Finset.inter_val, Finset.Ico_inter_Ico]
#align multiset.Ico_inter_Ico Multiset.ico_inter_ico

@[simp]
theorem ico_filter_lt (a b c : α) : ((Ico a b).filter fun x => x < c) = Ico a (min b c) := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_lt]
#align multiset.Ico_filter_lt Multiset.ico_filter_lt

@[simp]
theorem ico_filter_le (a b c : α) : ((Ico a b).filter fun x => c ≤ x) = Ico (max a c) b := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_le]
#align multiset.Ico_filter_le Multiset.ico_filter_le

@[simp]
theorem ico_sub_ico_left (a b c : α) : Ico a b - Ico a c = Ico (max a c) b := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_diff_Ico_left]
#align multiset.Ico_sub_Ico_left Multiset.ico_sub_ico_left

@[simp]
theorem ico_sub_ico_right (a b c : α) : Ico a b - Ico c b = Ico a (min b c) := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_diff_Ico_right]
#align multiset.Ico_sub_Ico_right Multiset.ico_sub_ico_right

end LinearOrder

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]

theorem map_add_left_icc (a b c : α) : (Icc a b).map ((· + ·) c) = Icc (c + a) (c + b) := by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Icc Multiset.map_add_left_icc

theorem map_add_left_ico (a b c : α) : (Ico a b).map ((· + ·) c) = Ico (c + a) (c + b) := by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ico Multiset.map_add_left_ico

theorem map_add_left_ioc (a b c : α) : (Ioc a b).map ((· + ·) c) = Ioc (c + a) (c + b) := by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ioc Multiset.map_add_left_ioc

theorem map_add_left_ioo (a b c : α) : (Ioo a b).map ((· + ·) c) = Ioo (c + a) (c + b) := by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
#align multiset.map_add_left_Ioo Multiset.map_add_left_ioo

theorem map_add_right_icc (a b c : α) : ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c) :=
  by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _
#align multiset.map_add_right_Icc Multiset.map_add_right_icc

theorem map_add_right_ico (a b c : α) : ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c) :=
  by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _
#align multiset.map_add_right_Ico Multiset.map_add_right_ico

theorem map_add_right_ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c) :=
  by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _
#align multiset.map_add_right_Ioc Multiset.map_add_right_ioc

theorem map_add_right_ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c) :=
  by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _
#align multiset.map_add_right_Ioo Multiset.map_add_right_ioo

end OrderedCancelAddCommMonoid

end Multiset

