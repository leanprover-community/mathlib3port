/-
Copyright (c) 2023 Yaël Dillies, Vladimir Ivanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Ivanov
-/
import Data.Finset.Sups

#align_import combinatorics.set_family.ahlswede_zhang from "leanprover-community/mathlib"@"8818fdefc78642a7e6afcd20be5c184f3c7d9699"

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between the size of the
"truncated unions"  of a set family. It sharpens the Lubell-Yamamoto-Meshalkin inequality
`finset.sum_card_slice_div_choose_le_one`, by making explicit the correction term.

For a set family `𝒜`, the Ahlswede-Zhang identity states that the sum of
`|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|)` is exactly `1`.

## Main declarations

* `finset.truncated_sup`: `s.truncated_sup a` is the supremum of all `b ≤ a` in `𝒜` if there are
  some, or `⊤` if there are none.
* `finset.truncated_inf` `s.truncated_inf a` is the infimum of all `b ≥ a` in `𝒜` if there are
  some, or `⊥` if there are none.

## References

* [R. Ahlswede, Z. Zhang, *An identity in combinatorial extremal theory*](https://doi.org/10.1016/0001-8708(90)90023-G)
* [D. T. Tru, *An AZ-style identity and Bollobás deficiency*](https://doi.org/10.1016/j.jcta.2007.03.005)
-/


open scoped FinsetFamily

namespace Finset

variable {α β : Type _}

/-! ### Truncated supremum, truncated infimum -/


section SemilatticeSup

variable [SemilatticeSup α] [OrderTop α] [@DecidableRel α (· ≤ ·)] [SemilatticeSup β]
  [BoundedOrder β] [@DecidableRel β (· ≤ ·)] {s t : Finset α} {a b : α}

private theorem sup_aux : a ∈ lowerClosure (s : Set α) → (s.filterₓ fun b => a ≤ b).Nonempty :=
  fun ⟨b, hb, hab⟩ => ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

#print Finset.truncatedSup /-
/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊤`. -/
def truncatedSup (s : Finset α) (a : α) : α :=
  if h : a ∈ lowerClosure (s : Set α) then (s.filterₓ fun b => a ≤ b).sup' (sup_aux h) id else ⊤
#align finset.truncated_sup Finset.truncatedSup
-/

#print Finset.truncatedSup_of_mem /-
theorem truncatedSup_of_mem (h : a ∈ lowerClosure (s : Set α)) :
    truncatedSup s a = (s.filterₓ fun b => a ≤ b).sup' (sup_aux h) id :=
  dif_pos h
#align finset.truncated_sup_of_mem Finset.truncatedSup_of_mem
-/

#print Finset.truncatedSup_of_not_mem /-
theorem truncatedSup_of_not_mem (h : a ∉ lowerClosure (s : Set α)) : truncatedSup s a = ⊤ :=
  dif_neg h
#align finset.truncated_sup_of_not_mem Finset.truncatedSup_of_not_mem
-/

#print Finset.truncatedSup_empty /-
@[simp]
theorem truncatedSup_empty (a : α) : truncatedSup ∅ a = ⊤ :=
  truncatedSup_of_not_mem <| by simp
#align finset.truncated_sup_empty Finset.truncatedSup_empty
-/

#print Finset.le_truncatedSup /-
theorem le_truncatedSup : a ≤ truncatedSup s a :=
  by
  rw [truncated_sup]
  split_ifs
  · obtain ⟨ℬ, hb, h⟩ := h
    exact h.trans (le_sup' _ <| mem_filter.2 ⟨hb, h⟩)
  · exact le_top
#align finset.le_truncated_sup Finset.le_truncatedSup
-/

#print Finset.map_truncatedSup /-
theorem map_truncatedSup (e : α ≃o β) (s : Finset α) (a : α) :
    e (truncatedSup s a) = truncatedSup (s.map e.toEquiv.toEmbedding) (e a) :=
  by
  have :
    e a ∈ lowerClosure (s.map e.to_equiv.to_embedding : Set β) ↔ a ∈ lowerClosure (s : Set α) := by
    simp
  simp_rw [truncated_sup, apply_dite e, map_finset_sup', map_top, this]
  congr with h
  simp only [filter_map, Function.comp, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id.def]
  rw [sup'_map]
  -- TODO: Why can't `simp` use `finset.sup'_map`?
  simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
#align finset.map_truncated_sup Finset.map_truncatedSup
-/

variable [DecidableEq α]

private theorem lower_aux :
    a ∈ lowerClosure (↑(s ∪ t) : Set α) ↔
      a ∈ lowerClosure (s : Set α) ∨ a ∈ lowerClosure (t : Set α) :=
  by rw [coe_union, lowerClosure_union, LowerSet.mem_sup_iff]

#print Finset.truncatedSup_union /-
theorem truncatedSup_union (hs : a ∈ lowerClosure (s : Set α)) (ht : a ∈ lowerClosure (t : Set α)) :
    truncatedSup (s ∪ t) a = truncatedSup s a ⊔ truncatedSup t a := by
  simpa only [truncated_sup_of_mem, hs, ht, lower_aux.2 (Or.inl hs), filter_union] using
    sup'_union _ _ _
#align finset.truncated_sup_union Finset.truncatedSup_union
-/

#print Finset.truncatedSup_union_left /-
theorem truncatedSup_union_left (hs : a ∈ lowerClosure (s : Set α))
    (ht : a ∉ lowerClosure (t : Set α)) : truncatedSup (s ∪ t) a = truncatedSup s a :=
  by
  simp only [mem_lowerClosure, mem_coe, exists_prop, not_exists, not_and] at ht
  simp only [truncated_sup_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    lower_aux.2 (Or.inl hs), ht]
#align finset.truncated_sup_union_left Finset.truncatedSup_union_left
-/

#print Finset.truncatedSup_union_right /-
theorem truncatedSup_union_right (hs : a ∉ lowerClosure (s : Set α))
    (ht : a ∈ lowerClosure (t : Set α)) : truncatedSup (s ∪ t) a = truncatedSup t a := by
  rw [union_comm, truncated_sup_union_left ht hs]
#align finset.truncated_sup_union_right Finset.truncatedSup_union_right
-/

#print Finset.truncatedSup_union_of_not_mem /-
theorem truncatedSup_union_of_not_mem (hs : a ∉ lowerClosure (s : Set α))
    (ht : a ∉ lowerClosure (t : Set α)) : truncatedSup (s ∪ t) a = ⊤ :=
  truncatedSup_of_not_mem fun h => (lower_aux.1 h).elim hs ht
#align finset.truncated_sup_union_of_not_mem Finset.truncatedSup_union_of_not_mem
-/

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α] [BoundedOrder α] [@DecidableRel α (· ≤ ·)] [SemilatticeInf β]
  [BoundedOrder β] [@DecidableRel β (· ≤ ·)] {s t : Finset α} {a : α}

private theorem inf_aux : a ∈ upperClosure (s : Set α) → (s.filterₓ fun b => b ≤ a).Nonempty :=
  fun ⟨b, hb, hab⟩ => ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

#print Finset.truncatedInf /-
/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
def truncatedInf (s : Finset α) (a : α) : α :=
  if h : a ∈ upperClosure (s : Set α) then (s.filterₓ fun b => b ≤ a).inf' (inf_aux h) id else ⊥
#align finset.truncated_inf Finset.truncatedInf
-/

#print Finset.truncatedInf_of_mem /-
theorem truncatedInf_of_mem (h : a ∈ upperClosure (s : Set α)) :
    truncatedInf s a = (s.filterₓ fun b => b ≤ a).inf' (inf_aux h) id :=
  dif_pos h
#align finset.truncated_inf_of_mem Finset.truncatedInf_of_mem
-/

#print Finset.truncatedInf_of_not_mem /-
theorem truncatedInf_of_not_mem (h : a ∉ upperClosure (s : Set α)) : truncatedInf s a = ⊥ :=
  dif_neg h
#align finset.truncated_inf_of_not_mem Finset.truncatedInf_of_not_mem
-/

#print Finset.truncatedInf_le /-
theorem truncatedInf_le (s : Finset α) (a : α) : truncatedInf s a ≤ a :=
  by
  unfold truncated_inf
  split_ifs
  · obtain ⟨ℬ, hb, h⟩ := h
    exact (inf'_le _ <| mem_filter.2 ⟨hb, h⟩).trans h
  · exact bot_le
#align finset.truncated_inf_le Finset.truncatedInf_le
-/

#print Finset.truncatedInf_empty /-
@[simp]
theorem truncatedInf_empty (a : α) : truncatedInf ∅ a = ⊥ :=
  truncatedInf_of_not_mem <| by simp
#align finset.truncated_inf_empty Finset.truncatedInf_empty
-/

#print Finset.map_truncatedInf /-
theorem map_truncatedInf (e : α ≃o β) (s : Finset α) (a : α) :
    e (truncatedInf s a) = truncatedInf (s.map e.toEquiv.toEmbedding) (e a) :=
  by
  have :
    e a ∈ upperClosure (s.map e.to_equiv.to_embedding : Set β) ↔ a ∈ upperClosure (s : Set α) := by
    simp
  simp_rw [truncated_inf, apply_dite e, map_finset_inf', map_bot, this]
  congr with h
  simp only [filter_map, Function.comp, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id.def]
  rw [inf'_map]
  -- TODO: Why can't `simp` use `finset.inf'_map`?
  simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv]
#align finset.map_truncated_inf Finset.map_truncatedInf
-/

variable [DecidableEq α]

private theorem upper_aux :
    a ∈ upperClosure (↑(s ∪ t) : Set α) ↔
      a ∈ upperClosure (s : Set α) ∨ a ∈ upperClosure (t : Set α) :=
  by rw [coe_union, upperClosure_union, UpperSet.mem_inf_iff]

#print Finset.truncatedInf_union /-
theorem truncatedInf_union (hs : a ∈ upperClosure (s : Set α)) (ht : a ∈ upperClosure (t : Set α)) :
    truncatedInf (s ∪ t) a = truncatedInf s a ⊓ truncatedInf t a := by
  simpa only [truncated_inf_of_mem, hs, ht, upper_aux.2 (Or.inl hs), filter_union] using
    inf'_union _ _ _
#align finset.truncated_inf_union Finset.truncatedInf_union
-/

#print Finset.truncatedInf_union_left /-
theorem truncatedInf_union_left (hs : a ∈ upperClosure (s : Set α))
    (ht : a ∉ upperClosure (t : Set α)) : truncatedInf (s ∪ t) a = truncatedInf s a :=
  by
  simp only [mem_upperClosure, mem_coe, exists_prop, not_exists, not_and] at ht
  simp only [truncated_inf_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    upper_aux.2 (Or.inl hs), ht]
#align finset.truncated_inf_union_left Finset.truncatedInf_union_left
-/

#print Finset.truncatedInf_union_right /-
theorem truncatedInf_union_right (hs : a ∉ upperClosure (s : Set α))
    (ht : a ∈ upperClosure (t : Set α)) : truncatedInf (s ∪ t) a = truncatedInf t a := by
  rw [union_comm, truncated_inf_union_left ht hs]
#align finset.truncated_inf_union_right Finset.truncatedInf_union_right
-/

#print Finset.truncatedInf_union_of_not_mem /-
theorem truncatedInf_union_of_not_mem (hs : a ∉ upperClosure (s : Set α))
    (ht : a ∉ upperClosure (t : Set α)) : truncatedInf (s ∪ t) a = ⊥ :=
  truncatedInf_of_not_mem <| by rw [coe_union, upperClosure_union]; exact fun h => h.elim hs ht
#align finset.truncated_inf_union_of_not_mem Finset.truncatedInf_union_of_not_mem
-/

end SemilatticeInf

section DistribLattice

variable [DistribLattice α] [BoundedOrder α] [DecidableEq α] [@DecidableRel α (· ≤ ·)]
  {s t : Finset α} {a : α}

private theorem infs_aux :
    a ∈ lowerClosure (↑(s ⊼ t) : Set α) ↔ a ∈ lowerClosure (s : Set α) ⊓ lowerClosure t := by
  rw [coe_infs, lowerClosure_infs, LowerSet.mem_inf_iff]

private theorem sups_aux :
    a ∈ upperClosure (↑(s ⊻ t) : Set α) ↔ a ∈ upperClosure (s : Set α) ⊔ upperClosure t := by
  rw [coe_sups, upperClosure_sups, UpperSet.mem_sup_iff]

#print Finset.truncatedSup_infs /-
theorem truncatedSup_infs (hs : a ∈ lowerClosure (s : Set α)) (ht : a ∈ lowerClosure (t : Set α)) :
    truncatedSup (s ⊼ t) a = truncatedSup s a ⊓ truncatedSup t a :=
  by
  simp only [truncated_sup_of_mem, hs, ht, infs_aux.2 ⟨hs, ht⟩, sup'_inf_sup', filter_infs_ge]
  simp_rw [← image_inf_product]
  rw [sup'_image]
  rfl
#align finset.truncated_sup_infs Finset.truncatedSup_infs
-/

#print Finset.truncatedInf_sups /-
theorem truncatedInf_sups (hs : a ∈ upperClosure (s : Set α)) (ht : a ∈ upperClosure (t : Set α)) :
    truncatedInf (s ⊻ t) a = truncatedInf s a ⊔ truncatedInf t a :=
  by
  simp only [truncated_inf_of_mem, hs, ht, sups_aux.2 ⟨hs, ht⟩, inf'_sup_inf', filter_sups_le]
  simp_rw [← image_sup_product]
  rw [inf'_image]
  rfl
#align finset.truncated_inf_sups Finset.truncatedInf_sups
-/

#print Finset.truncatedSup_infs_of_not_mem /-
theorem truncatedSup_infs_of_not_mem (ha : a ∉ lowerClosure (s : Set α) ⊓ lowerClosure t) :
    truncatedSup (s ⊼ t) a = ⊤ :=
  truncatedSup_of_not_mem <| by rwa [coe_infs, lowerClosure_infs]
#align finset.truncated_sup_infs_of_not_mem Finset.truncatedSup_infs_of_not_mem
-/

#print Finset.truncatedInf_sups_of_not_mem /-
theorem truncatedInf_sups_of_not_mem (ha : a ∉ upperClosure (s : Set α) ⊔ upperClosure t) :
    truncatedInf (s ⊻ t) a = ⊥ :=
  truncatedInf_of_not_mem <| by rwa [coe_sups, upperClosure_sups]
#align finset.truncated_inf_sups_of_not_mem Finset.truncatedInf_sups_of_not_mem
-/

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra α] [@DecidableRel α (· ≤ ·)] {s : Finset α} {a : α}

#print Finset.compl_truncatedSup /-
@[simp]
theorem compl_truncatedSup (s : Finset α) (a : α) :
    truncatedSup s aᶜ = truncatedInf (s.map ⟨compl, compl_injective⟩) (aᶜ) :=
  map_truncatedSup (OrderIso.compl α) _ _
#align finset.compl_truncated_sup Finset.compl_truncatedSup
-/

#print Finset.compl_truncatedInf /-
@[simp]
theorem compl_truncatedInf (s : Finset α) (a : α) :
    truncatedInf s aᶜ = truncatedSup (s.map ⟨compl, compl_injective⟩) (aᶜ) :=
  map_truncatedInf (OrderIso.compl α) _ _
#align finset.compl_truncated_inf Finset.compl_truncatedInf
-/

end BooleanAlgebra

variable [DecidableEq α] [Fintype α]

#print Finset.card_truncatedSup_union_add_card_truncatedSup_infs /-
theorem card_truncatedSup_union_add_card_truncatedSup_infs (𝒜 ℬ : Finset (Finset α))
    (s : Finset α) :
    (truncatedSup (𝒜 ∪ ℬ) s).card + (truncatedSup (𝒜 ⊼ ℬ) s).card =
      (truncatedSup 𝒜 s).card + (truncatedSup ℬ s).card :=
  by
  by_cases h𝒜 : s ∈ lowerClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s ∈ lowerClosure (ℬ : Set <| Finset α)
  · rw [truncated_sup_union h𝒜 hℬ, truncated_sup_infs h𝒜 hℬ]
    exact card_union_add_card_inter _ _
  ·
    rw [truncated_sup_union_left h𝒜 hℬ, truncated_sup_of_not_mem hℬ,
      truncated_sup_infs_of_not_mem fun h => hℬ h.2]
  ·
    rw [truncated_sup_union_right h𝒜 hℬ, truncated_sup_of_not_mem h𝒜,
      truncated_sup_infs_of_not_mem fun h => h𝒜 h.1, add_comm]
  ·
    rw [truncated_sup_of_not_mem h𝒜, truncated_sup_of_not_mem hℬ,
      truncated_sup_union_of_not_mem h𝒜 hℬ, truncated_sup_infs_of_not_mem fun h => h𝒜 h.1]
#align finset.card_truncated_sup_union_add_card_truncated_sup_infs Finset.card_truncatedSup_union_add_card_truncatedSup_infs
-/

end Finset

