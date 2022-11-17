/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Card
import Mathbin.Data.Fintype.Basic

/-!
# Down-compressions

This file defines down-compression.

Down-compressing `𝒜 : finset (finset α)` along `a : α` means removing `a` from the elements of `𝒜`,
when the resulting set is not already in `𝒜`.

## Main declarations

* `finset.non_member_subfamily`: `𝒜.non_member_subfamily a` is the subfamily of sets not containing
  `a`.
* `finset.member_subfamily`: `𝒜.member_subfamily a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `down.compression`: Down-compression.

## Notation

`𝓓 a 𝒜` is notation for `down.compress a 𝒜` in locale `set_family`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/


variable {α : Type _} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s : Finset α} {a : α}

namespace Finset

/-- Elements of `𝒜` that do not contain `a`. -/
def nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter $ fun s => a ∉ s
#align finset.non_member_subfamily Finset.nonMemberSubfamily

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
def memberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter $ fun s => a ∈ s).image $ fun s => erase s a
#align finset.member_subfamily Finset.memberSubfamily

@[simp]
theorem mem_non_member_subfamily : s ∈ 𝒜.nonMemberSubfamily a ↔ s ∈ 𝒜 ∧ a ∉ s :=
  mem_filter
#align finset.mem_non_member_subfamily Finset.mem_non_member_subfamily

@[simp]
theorem mem_member_subfamily : s ∈ 𝒜.memberSubfamily a ↔ insert a s ∈ 𝒜 ∧ a ∉ s := by
  simp_rw [member_subfamily, mem_image, mem_filter]
  refine' ⟨_, fun h => ⟨insert a s, ⟨h.1, mem_insert_self _ _⟩, erase_insert h.2⟩⟩
  rintro ⟨s, hs, rfl⟩
  rw [insert_erase hs.2]
  exact ⟨hs.1, not_mem_erase _ _⟩
#align finset.mem_member_subfamily Finset.mem_member_subfamily

theorem non_member_subfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∩ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∩ ℬ.nonMemberSubfamily a :=
  filter_inter_distrib _ _ _
#align finset.non_member_subfamily_inter Finset.non_member_subfamily_inter

theorem member_subfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∩ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∩ ℬ.memberSubfamily a := by
  unfold member_subfamily
  rw [filter_inter_distrib, image_inter_of_inj_on _ _ ((erase_inj_on' _).mono _)]
  rw [← coe_union, ← filter_union, coe_filter]
  exact Set.inter_subset_right _ _
#align finset.member_subfamily_inter Finset.member_subfamily_inter

theorem non_member_subfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∪ ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a ∪ ℬ.nonMemberSubfamily a :=
  filter_union _ _ _
#align finset.non_member_subfamily_union Finset.non_member_subfamily_union

theorem member_subfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ∪ ℬ).memberSubfamily a = 𝒜.memberSubfamily a ∪ ℬ.memberSubfamily a := by
  simp_rw [member_subfamily, filter_union, image_union]
#align finset.member_subfamily_union Finset.member_subfamily_union

theorem card_member_subfamily_add_card_non_member_subfamily (a : α) (𝒜 : Finset (Finset α)) :
    (𝒜.memberSubfamily a).card + (𝒜.nonMemberSubfamily a).card = 𝒜.card := by
  rw [member_subfamily, non_member_subfamily, card_image_of_inj_on, filter_card_add_filter_neg_card_eq_card]
  exact (erase_inj_on' _).mono fun s hs => (mem_filter.1 hs).2
#align
  finset.card_member_subfamily_add_card_non_member_subfamily Finset.card_member_subfamily_add_card_non_member_subfamily

theorem member_subfamily_union_non_member_subfamily (a : α) (𝒜 : Finset (Finset α)) :
    𝒜.memberSubfamily a ∪ 𝒜.nonMemberSubfamily a = 𝒜.image fun s => s.erase a := by
  ext s
  simp only [mem_union, mem_member_subfamily, mem_non_member_subfamily, mem_image, exists_prop]
  constructor
  · rintro (h | h)
    · exact ⟨_, h.1, erase_insert h.2⟩
      
    · exact ⟨_, h.1, erase_eq_of_not_mem h.2⟩
      
    
  · rintro ⟨s, hs, rfl⟩
    by_cases ha:a ∈ s
    · exact Or.inl ⟨by rwa [insert_erase ha], not_mem_erase _ _⟩
      
    · exact Or.inr ⟨by rwa [erase_eq_of_not_mem ha], not_mem_erase _ _⟩
      
    
#align finset.member_subfamily_union_non_member_subfamily Finset.member_subfamily_union_non_member_subfamily

@[simp]
theorem member_subfamily_member_subfamily : (𝒜.memberSubfamily a).memberSubfamily a = ∅ := by
  ext
  simp
#align finset.member_subfamily_member_subfamily Finset.member_subfamily_member_subfamily

@[simp]
theorem member_subfamily_non_member_subfamily : (𝒜.nonMemberSubfamily a).memberSubfamily a = ∅ := by
  ext
  simp
#align finset.member_subfamily_non_member_subfamily Finset.member_subfamily_non_member_subfamily

@[simp]
theorem non_member_subfamily_member_subfamily : (𝒜.memberSubfamily a).nonMemberSubfamily a = 𝒜.memberSubfamily a := by
  ext
  simp
#align finset.non_member_subfamily_member_subfamily Finset.non_member_subfamily_member_subfamily

@[simp]
theorem non_member_subfamily_non_member_subfamily :
    (𝒜.nonMemberSubfamily a).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a := by
  ext
  simp
#align finset.non_member_subfamily_non_member_subfamily Finset.non_member_subfamily_non_member_subfamily

end Finset

open Finset

-- The namespace is here to distinguish from other compressions.
namespace Down

/-- `a`-down-compressing `𝒜` means removing `a` from the elements of `𝒜` that contain it, when the
resulting finset is not already in `𝒜`. -/
def compression (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter $ fun s => erase s a ∈ 𝒜).disjUnion ((𝒜.image $ fun s => erase s a).filter $ fun s => s ∉ 𝒜) $
    disjoint_left.2 $ fun s h₁ h₂ => (mem_filter.1 h₂).2 (mem_filter.1 h₁).1
#align down.compression Down.compression

-- mathport name: down.compression
scoped[FinsetFamily] notation "𝓓 " => Down.compression

/-- `a` is in the down-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
theorem mem_compression : s ∈ 𝓓 a 𝒜 ↔ s ∈ 𝒜 ∧ s.erase a ∈ 𝒜 ∨ s ∉ 𝒜 ∧ insert a s ∈ 𝒜 := by
  simp_rw [compression, mem_disj_union, mem_filter, mem_image, and_comm' (s ∉ 𝒜)]
  refine'
    or_congr_right
      (and_congr_left $ fun hs => ⟨_, fun h => ⟨_, h, erase_insert $ insert_ne_self.1 $ ne_of_mem_of_not_mem h hs⟩⟩)
  rintro ⟨t, ht, rfl⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm)]
#align down.mem_compression Down.mem_compression

theorem erase_mem_compression (hs : s ∈ 𝒜) : s.erase a ∈ 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem, and_self_iff]
  refine' (em _).imp_right fun h => ⟨h, _⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem hs h).symm)]
#align down.erase_mem_compression Down.erase_mem_compression

-- This is a special case of `erase_mem_compression` once we have `compression_idem`.
theorem erase_mem_compression_of_mem_compression : s ∈ 𝓓 a 𝒜 → s.erase a ∈ 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem]
  refine' Or.imp (fun h => ⟨h.2, h.2⟩) fun h => _
  rwa [erase_eq_of_not_mem (insert_ne_self.1 $ ne_of_mem_of_not_mem h.2 h.1)]
#align down.erase_mem_compression_of_mem_compression Down.erase_mem_compression_of_mem_compression

theorem mem_compression_of_insert_mem_compression (h : insert a s ∈ 𝓓 a 𝒜) : s ∈ 𝓓 a 𝒜 := by
  by_cases ha:a ∈ s
  · rwa [insert_eq_of_mem ha] at h
    
  · rw [← erase_insert ha]
    exact erase_mem_compression_of_mem_compression h
    
#align down.mem_compression_of_insert_mem_compression Down.mem_compression_of_insert_mem_compression

/-- Down-compressing a family is idempotent. -/
@[simp]
theorem compression_idem (a : α) (𝒜 : Finset (Finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜 := by
  ext s
  refine' mem_compression.trans ⟨_, fun h => Or.inl ⟨h, erase_mem_compression_of_mem_compression h⟩⟩
  rintro (h | h)
  · exact h.1
    
  · cases h.1 (mem_compression_of_insert_mem_compression h.2)
    
#align down.compression_idem Down.compression_idem

/-- Down-compressing a family doesn't change its size. -/
@[simp]
theorem card_compression (a : α) (𝒜 : Finset (Finset α)) : (𝓓 a 𝒜).card = 𝒜.card := by
  rw [compression, card_disj_union, image_filter, card_image_of_inj_on ((erase_inj_on' _).mono $ fun s hs => _), ←
    card_disjoint_union, filter_union_filter_neg_eq]
  · exact disjoint_filter_filter_neg _ _ _
    
  rw [mem_coe, mem_filter] at hs
  exact not_imp_comm.1 erase_eq_of_not_mem (ne_of_mem_of_not_mem hs.1 hs.2).symm
#align down.card_compression Down.card_compression

end Down

