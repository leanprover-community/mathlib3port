/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Algebra.Order.Group.Abs

/-! ### Lemmas about arithmetic operations and intervals. -/


variable {α : Type _}

namespace Set

section OrderedCommGroup

variable [OrderedCommGroup α] {a b c d : α}

/-! `inv_mem_Ixx_iff`, `sub_mem_Ixx_iff` -/


@[to_additive]
theorem inv_mem_Icc_iff : a⁻¹ ∈ Set.IccCat c d ↔ a ∈ Set.IccCat d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_le' le_inv'

@[to_additive]
theorem inv_mem_Ico_iff : a⁻¹ ∈ Set.IcoCat c d ↔ a ∈ Set.IocCat d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_lt' le_inv'

@[to_additive]
theorem inv_mem_Ioc_iff : a⁻¹ ∈ Set.IocCat c d ↔ a ∈ Set.IcoCat d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_le' lt_inv'

@[to_additive]
theorem inv_mem_Ioo_iff : a⁻¹ ∈ Set.IooCat c d ↔ a ∈ Set.IooCat d⁻¹ c⁻¹ :=
  (and_comm' _ _).trans <| and_congr inv_lt' lt_inv'

end OrderedCommGroup

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] {a b c d : α}

/-! `add_mem_Ixx_iff_left` -/


theorem add_mem_Icc_iff_left : a + b ∈ Set.IccCat c d ↔ a ∈ Set.IccCat (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm

theorem add_mem_Ico_iff_left : a + b ∈ Set.IcoCat c d ↔ a ∈ Set.IcoCat (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm

theorem add_mem_Ioc_iff_left : a + b ∈ Set.IocCat c d ↔ a ∈ Set.IocCat (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm

theorem add_mem_Ioo_iff_left : a + b ∈ Set.IooCat c d ↔ a ∈ Set.IooCat (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm

/-! `add_mem_Ixx_iff_right` -/


theorem add_mem_Icc_iff_right : a + b ∈ Set.IccCat c d ↔ b ∈ Set.IccCat (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm

theorem add_mem_Ico_iff_right : a + b ∈ Set.IcoCat c d ↔ b ∈ Set.IcoCat (c - a) (d - a) :=
  (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm

theorem add_mem_Ioc_iff_right : a + b ∈ Set.IocCat c d ↔ b ∈ Set.IocCat (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm

theorem add_mem_Ioo_iff_right : a + b ∈ Set.IooCat c d ↔ b ∈ Set.IooCat (c - a) (d - a) :=
  (and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm

/-! `sub_mem_Ixx_iff_left` -/


theorem sub_mem_Icc_iff_left : a - b ∈ Set.IccCat c d ↔ a ∈ Set.IccCat (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_le_iff_le_add

theorem sub_mem_Ico_iff_left : a - b ∈ Set.IcoCat c d ↔ a ∈ Set.IcoCat (c + b) (d + b) :=
  and_congr le_sub_iff_add_le sub_lt_iff_lt_add

theorem sub_mem_Ioc_iff_left : a - b ∈ Set.IocCat c d ↔ a ∈ Set.IocCat (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_le_iff_le_add

theorem sub_mem_Ioo_iff_left : a - b ∈ Set.IooCat c d ↔ a ∈ Set.IooCat (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add

/-! `sub_mem_Ixx_iff_right` -/


theorem sub_mem_Icc_iff_right : a - b ∈ Set.IccCat c d ↔ b ∈ Set.IccCat (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_le_comm le_sub_comm

theorem sub_mem_Ico_iff_right : a - b ∈ Set.IcoCat c d ↔ b ∈ Set.IocCat (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_lt_comm le_sub_comm

theorem sub_mem_Ioc_iff_right : a - b ∈ Set.IocCat c d ↔ b ∈ Set.IcoCat (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_le_comm lt_sub_comm

theorem sub_mem_Ioo_iff_right : a - b ∈ Set.IooCat c d ↔ b ∈ Set.IooCat (a - d) (a - c) :=
  (and_comm' _ _).trans <| and_congr sub_lt_comm lt_sub_comm

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
theorem mem_Icc_iff_abs_le {R : Type _} [LinearOrderedAddCommGroup R] {x y z : R} :
    |x - y| ≤ z ↔ y ∈ IccCat (x - z) (x + z) :=
  abs_le.trans <| (and_comm' _ _).trans <| and_congr sub_le_comm neg_le_sub_iff_le_add

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
theorem nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
    Nonempty ↥(IcoCat x (x + dx) \ IcoCat y (y + dy)) := by
  cases' lt_or_le x y with h' h'
  · use x
    simp [*, not_le.2 h']
    
  · use max x (x + dy)
    simp [*, le_refl]
    

end LinearOrderedAddCommGroup

end Set

