/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Data.Multiset.Sum
import Data.Finset.Card

#align_import data.finset.sum from "leanprover-community/mathlib"@"48a058d7e39a80ed56858505719a0b2197900999"

/-!
# Disjoint sum of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the disjoint sum of two finsets as `finset (α ⊕ β)`. Beware not to confuse with
the `finset.sum` operation which computes the additive sum.

## Main declarations

* `finset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/


open Function Multiset Sum

namespace Finset

variable {α β : Type _} (s : Finset α) (t : Finset β)

#print Finset.disjSum /-
/-- Disjoint sum of finsets. -/
def disjSum : Finset (Sum α β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩
#align finset.disj_sum Finset.disjSum
-/

#print Finset.val_disjSum /-
@[simp]
theorem val_disjSum : (s.disjSum t).1 = s.1.disjSum t.1 :=
  rfl
#align finset.val_disj_sum Finset.val_disjSum
-/

#print Finset.empty_disjSum /-
@[simp]
theorem empty_disjSum : (∅ : Finset α).disjSum t = t.map Embedding.inr :=
  val_inj.1 <| Multiset.zero_disjSum _
#align finset.empty_disj_sum Finset.empty_disjSum
-/

#print Finset.disjSum_empty /-
@[simp]
theorem disjSum_empty : s.disjSum (∅ : Finset β) = s.map Embedding.inl :=
  val_inj.1 <| Multiset.disjSum_zero _
#align finset.disj_sum_empty Finset.disjSum_empty
-/

#print Finset.card_disjSum /-
@[simp]
theorem card_disjSum : (s.disjSum t).card = s.card + t.card :=
  Multiset.card_disjSum _ _
#align finset.card_disj_sum Finset.card_disjSum
-/

#print Finset.disjoint_map_inl_map_inr /-
theorem disjoint_map_inl_map_inr : Disjoint (s.map Embedding.inl) (t.map Embedding.inr) := by
  simp_rw [disjoint_left, mem_map]; rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩
#align finset.disjoint_map_inl_map_inr Finset.disjoint_map_inl_map_inr
-/

#print Finset.map_inl_disjUnion_map_inr /-
@[simp]
theorem map_inl_disjUnion_map_inr :
    (s.map Embedding.inl).disjUnion (t.map Embedding.inr) (disjoint_map_inl_map_inr _ _) =
      s.disjSum t :=
  rfl
#align finset.map_inl_disj_union_map_inr Finset.map_inl_disjUnion_map_inr
-/

variable {s t} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} {a : α} {b : β} {x : Sum α β}

#print Finset.mem_disjSum /-
theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
  Multiset.mem_disjSum
#align finset.mem_disj_sum Finset.mem_disjSum
-/

#print Finset.inl_mem_disjSum /-
@[simp]
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s :=
  inl_mem_disjSum
#align finset.inl_mem_disj_sum Finset.inl_mem_disjSum
-/

#print Finset.inr_mem_disjSum /-
@[simp]
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t :=
  inr_mem_disjSum
#align finset.inr_mem_disj_sum Finset.inr_mem_disjSum
-/

#print Finset.disjSum_eq_empty /-
@[simp]
theorem disjSum_eq_empty : s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅ := by simp [ext_iff]
#align finset.disj_sum_eq_empty Finset.disjSum_eq_empty
-/

#print Finset.disjSum_mono /-
theorem disjSum_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.disjSum t₁ ⊆ s₂.disjSum t₂ :=
  val_le_iff.1 <| disjSum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)
#align finset.disj_sum_mono Finset.disjSum_mono
-/

#print Finset.disjSum_mono_left /-
theorem disjSum_mono_left (t : Finset β) : Monotone fun s : Finset α => s.disjSum t :=
  fun s₁ s₂ hs => disjSum_mono hs Subset.rfl
#align finset.disj_sum_mono_left Finset.disjSum_mono_left
-/

#print Finset.disjSum_mono_right /-
theorem disjSum_mono_right (s : Finset α) : Monotone (s.disjSum : Finset β → Finset (Sum α β)) :=
  fun t₁ t₂ => disjSum_mono Subset.rfl
#align finset.disj_sum_mono_right Finset.disjSum_mono_right
-/

#print Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset /-
theorem disjSum_ssubset_disjSum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ ⊆ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)
#align finset.disj_sum_ssubset_disj_sum_of_ssubset_of_subset Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset
-/

#print Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset /-
theorem disjSum_ssubset_disjSum_of_subset_of_ssubset (hs : s₁ ⊆ s₂) (ht : t₁ ⊂ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)
#align finset.disj_sum_ssubset_disj_sum_of_subset_of_ssubset Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset
-/

#print Finset.disjSum_strictMono_left /-
theorem disjSum_strictMono_left (t : Finset β) : StrictMono fun s : Finset α => s.disjSum t :=
  fun s₁ s₂ hs => disjSum_ssubset_disjSum_of_ssubset_of_subset hs Subset.rfl
#align finset.disj_sum_strict_mono_left Finset.disjSum_strictMono_left
-/

#print Finset.disj_sum_strictMono_right /-
theorem disj_sum_strictMono_right (s : Finset α) :
    StrictMono (s.disjSum : Finset β → Finset (Sum α β)) := fun s₁ s₂ =>
  disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl
#align finset.disj_sum_strict_mono_right Finset.disj_sum_strictMono_right
-/

end Finset

