import Mathbin.Data.Finset.LocallyFinite

/-!
# Intervals of finsets as finsets

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

-- failed to format: format: uncaught backtrack exception
instance
  : LocallyFiniteOrder ( Finset α )
  where
    finsetIcc s t := t.powerset.filter ( ( · ⊆ · ) s )
      finsetIco s t := t.ssubsets.filter ( ( · ⊆ · ) s )
      finsetIoc s t := t.powerset.filter ( ( · ⊂ · ) s )
      finsetIoo s t := t.ssubsets.filter ( ( · ⊂ · ) s )
      finset_mem_Icc s t u := by rw [ mem_filter , mem_powerset ] exact and_comm _ _
      finset_mem_Ico s t u := by rw [ mem_filter , mem_ssubsets ] exact and_comm _ _
      finset_mem_Ioc s t u := by rw [ mem_filter , mem_powerset ] exact and_comm _ _
      finset_mem_Ioo s t u := by rw [ mem_filter , mem_ssubsets ] exact and_comm _ _

theorem Icc_eq_filter_powerset : Icc s t = t.powerset.filter ((· ⊆ ·) s) :=
  rfl

theorem Ico_eq_filter_ssubsets : Ico s t = t.ssubsets.filter ((· ⊆ ·) s) :=
  rfl

theorem Ioc_eq_filter_powerset : Ioc s t = t.powerset.filter ((· ⊂ ·) s) :=
  rfl

theorem Ioo_eq_filter_ssubsets : Ioo s t = t.ssubsets.filter ((· ⊂ ·) s) :=
  rfl

theorem Iic_eq_powerset : Iic s = s.powerset :=
  filter_true_of_mem $ fun t _ => empty_subset t

theorem Iio_eq_ssubsets : Iio s = s.ssubsets :=
  filter_true_of_mem $ fun t _ => empty_subset t

variable {s t}

theorem Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).Powerset.Image ((· ∪ ·) s) := by
  ext u
  simp_rw [mem_Icc, mem_image, exists_prop, mem_powerset]
  constructor
  ·
    rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_le_sdiff_right ht, sup_sdiff_cancel_right hs⟩
  ·
    rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, union_subset h $ hv.trans $ sdiff_subset _ _⟩

theorem Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.Image ((· ∪ ·) s) := by
  ext u
  simp_rw [mem_Ico, mem_image, exists_prop, mem_ssubsets]
  constructor
  ·
    rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  ·
    rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩

/--  Cardinality of a non-empty `Icc` of finsets. -/
theorem card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) := by
  rw [← card_sdiff h, ← card_powerset, Icc_eq_image_powerset h, Finset.card_image_eq_iff_inj_on]
  rintro u hu v hv (huv : s⊔u = s⊔v)
  rw [mem_coe, mem_powerset] at hu hv
  rw [← (disjoint_sdiff.mono_right hu : Disjoint s u).sup_sdiff_cancel_left, ←
    (disjoint_sdiff.mono_right hv : Disjoint s v).sup_sdiff_cancel_left, huv]

/--  Cardinality of an `Ico` of finsets. -/
theorem card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one (le_iff_subset.2 h), card_Icc_finset h]

/--  Cardinality of an `Ioc` of finsets. -/
theorem card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one (le_iff_subset.2 h), card_Icc_finset h]

/--  Cardinality of an `Ioo` of finsets. -/
theorem card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two (le_iff_subset.2 h), card_Icc_finset h]

end Finset

