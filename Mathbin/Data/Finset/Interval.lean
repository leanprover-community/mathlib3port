/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Data.Finset.LocallyFinite

#align_import data.finset.interval from "leanprover-community/mathlib"@"d64d67d000b974f0d86a2be7918cf800be6271c8"

/-!
# Intervals of finsets as finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `finset α` and calculates the cardinality
of finite intervals of finsets.

If `s t : finset α`, then `finset.Icc s t` is the finset of finsets which include `s` and are
included in `t`. For example,
`finset.Icc {0, 1} {0, 1, 2, 3} = {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}}`
and
`finset.Icc {0, 1, 2} {0, 1, 3} = {}`.
-/


variable {α : Type _}

namespace Finset

variable [DecidableEq α] (s t : Finset α)

instance : LocallyFiniteOrder (Finset α)
    where
  finsetIcc s t := t.powerset.filterₓ ((· ⊆ ·) s)
  finsetIco s t := t.ssubsets.filterₓ ((· ⊆ ·) s)
  finsetIoc s t := t.powerset.filterₓ ((· ⊂ ·) s)
  finsetIoo s t := t.ssubsets.filterₓ ((· ⊂ ·) s)
  finset_mem_Icc s t u := by rw [mem_filter, mem_powerset]; exact and_comm' _ _
  finset_mem_Ico s t u := by rw [mem_filter, mem_ssubsets]; exact and_comm' _ _
  finset_mem_Ioc s t u := by rw [mem_filter, mem_powerset]; exact and_comm' _ _
  finset_mem_Ioo s t u := by rw [mem_filter, mem_ssubsets]; exact and_comm' _ _

#print Finset.Icc_eq_filter_powerset /-
theorem Icc_eq_filter_powerset : Icc s t = t.powerset.filterₓ ((· ⊆ ·) s) :=
  rfl
#align finset.Icc_eq_filter_powerset Finset.Icc_eq_filter_powerset
-/

#print Finset.Ico_eq_filter_ssubsets /-
theorem Ico_eq_filter_ssubsets : Ico s t = t.ssubsets.filterₓ ((· ⊆ ·) s) :=
  rfl
#align finset.Ico_eq_filter_ssubsets Finset.Ico_eq_filter_ssubsets
-/

#print Finset.Ioc_eq_filter_powerset /-
theorem Ioc_eq_filter_powerset : Ioc s t = t.powerset.filterₓ ((· ⊂ ·) s) :=
  rfl
#align finset.Ioc_eq_filter_powerset Finset.Ioc_eq_filter_powerset
-/

#print Finset.Ioo_eq_filter_ssubsets /-
theorem Ioo_eq_filter_ssubsets : Ioo s t = t.ssubsets.filterₓ ((· ⊂ ·) s) :=
  rfl
#align finset.Ioo_eq_filter_ssubsets Finset.Ioo_eq_filter_ssubsets
-/

#print Finset.Iic_eq_powerset /-
theorem Iic_eq_powerset : Iic s = s.powerset :=
  filter_true_of_mem fun t _ => empty_subset t
#align finset.Iic_eq_powerset Finset.Iic_eq_powerset
-/

#print Finset.Iio_eq_ssubsets /-
theorem Iio_eq_ssubsets : Iio s = s.ssubsets :=
  filter_true_of_mem fun t _ => empty_subset t
#align finset.Iio_eq_ssubsets Finset.Iio_eq_ssubsets
-/

variable {s t}

#print Finset.Icc_eq_image_powerset /-
theorem Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).powerset.image ((· ∪ ·) s) :=
  by
  ext u
  simp_rw [mem_Icc, mem_image, exists_prop, mem_powerset]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_le_sdiff_right ht, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, union_subset h <| hv.trans <| sdiff_subset _ _⟩
#align finset.Icc_eq_image_powerset Finset.Icc_eq_image_powerset
-/

#print Finset.Ico_eq_image_ssubsets /-
theorem Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.image ((· ∪ ·) s) :=
  by
  ext u
  simp_rw [mem_Ico, mem_image, exists_prop, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩
#align finset.Ico_eq_image_ssubsets Finset.Ico_eq_image_ssubsets
-/

#print Finset.card_Icc_finset /-
/-- Cardinality of a non-empty `Icc` of finsets. -/
theorem card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) :=
  by
  rw [← card_sdiff h, ← card_powerset, Icc_eq_image_powerset h, Finset.card_image_iff]
  rintro u hu v hv (huv : s ⊔ u = s ⊔ v)
  rw [mem_coe, mem_powerset] at hu hv
  rw [← (disjoint_sdiff.mono_right hu : Disjoint s u).sup_sdiff_cancel_left, ←
    (disjoint_sdiff.mono_right hv : Disjoint s v).sup_sdiff_cancel_left, huv]
#align finset.card_Icc_finset Finset.card_Icc_finset
-/

#print Finset.card_Ico_finset /-
/-- Cardinality of an `Ico` of finsets. -/
theorem card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc_finset h]
#align finset.card_Ico_finset Finset.card_Ico_finset
-/

#print Finset.card_Ioc_finset /-
/-- Cardinality of an `Ioc` of finsets. -/
theorem card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc_finset h]
#align finset.card_Ioc_finset Finset.card_Ioc_finset
-/

#print Finset.card_Ioo_finset /-
/-- Cardinality of an `Ioo` of finsets. -/
theorem card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc_finset h]
#align finset.card_Ioo_finset Finset.card_Ioo_finset
-/

#print Finset.card_Iic_finset /-
/-- Cardinality of an `Iic` of finsets. -/
theorem card_Iic_finset : (Iic s).card = 2 ^ s.card := by rw [Iic_eq_powerset, card_powerset]
#align finset.card_Iic_finset Finset.card_Iic_finset
-/

#print Finset.card_Iio_finset /-
/-- Cardinality of an `Iio` of finsets. -/
theorem card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 := by
  rw [Iio_eq_ssubsets, ssubsets, card_erase_of_mem (mem_powerset_self _), card_powerset]
#align finset.card_Iio_finset Finset.card_Iio_finset
-/

end Finset

