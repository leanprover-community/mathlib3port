/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Data.SetLike.Basic
import Data.Set.Intervals.OrdConnected
import Data.Set.Intervals.OrderIso
import Tactic.ByContra

#align_import order.upper_lower.basic from "leanprover-community/mathlib"@"c0c52abb75074ed8b73a948341f50521fbf43b4c"

/-!
# Up-sets and down-sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines upper and lower sets in an order.

## Main declarations

* `is_upper_set`: Predicate for a set to be an upper set. This means every element greater than a
  member of the set is in the set itself.
* `is_lower_set`: Predicate for a set to be a lower set. This means every element less than a member
  of the set is in the set itself.
* `upper_set`: The type of upper sets.
* `lower_set`: The type of lower sets.
* `upper_closure`: The greatest upper set containing a set.
* `lower_closure`: The least lower set containing a set.
* `upper_set.Ici`: Principal upper set. `set.Ici` as an upper set.
* `upper_set.Ioi`: Strict principal upper set. `set.Ioi` as an upper set.
* `lower_set.Iic`: Principal lower set. `set.Iic` as an lower set.
* `lower_set.Iio`: Strict principal lower set. `set.Iio` as an lower set.

## Notation

`×ˢ` is notation for `upper_set.prod`/`lower_set.prod`.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `filter`.

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/


open OrderDual Set

variable {α β γ : Type _} {ι : Sort _} {κ : ι → Sort _}

/-! ### Unbundled upper/lower sets -/


section LE

variable [LE α] [LE β] {s t : Set α}

#print IsUpperSet /-
/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
def IsUpperSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s
#align is_upper_set IsUpperSet
-/

#print IsLowerSet /-
/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
def IsLowerSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s
#align is_lower_set IsLowerSet
-/

#print isUpperSet_empty /-
theorem isUpperSet_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id
#align is_upper_set_empty isUpperSet_empty
-/

#print isLowerSet_empty /-
theorem isLowerSet_empty : IsLowerSet (∅ : Set α) := fun _ _ _ => id
#align is_lower_set_empty isLowerSet_empty
-/

#print isUpperSet_univ /-
theorem isUpperSet_univ : IsUpperSet (univ : Set α) := fun _ _ _ => id
#align is_upper_set_univ isUpperSet_univ
-/

#print isLowerSet_univ /-
theorem isLowerSet_univ : IsLowerSet (univ : Set α) := fun _ _ _ => id
#align is_lower_set_univ isLowerSet_univ
-/

#print IsUpperSet.compl /-
theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet (sᶜ) := fun a b h hb ha => hb <| hs h ha
#align is_upper_set.compl IsUpperSet.compl
-/

#print IsLowerSet.compl /-
theorem IsLowerSet.compl (hs : IsLowerSet s) : IsUpperSet (sᶜ) := fun a b h hb ha => hb <| hs h ha
#align is_lower_set.compl IsLowerSet.compl
-/

#print isUpperSet_compl /-
@[simp]
theorem isUpperSet_compl : IsUpperSet (sᶜ) ↔ IsLowerSet s :=
  ⟨fun h => by convert h.compl; rw [compl_compl], IsLowerSet.compl⟩
#align is_upper_set_compl isUpperSet_compl
-/

#print isLowerSet_compl /-
@[simp]
theorem isLowerSet_compl : IsLowerSet (sᶜ) ↔ IsUpperSet s :=
  ⟨fun h => by convert h.compl; rw [compl_compl], IsUpperSet.compl⟩
#align is_lower_set_compl isLowerSet_compl
-/

#print IsUpperSet.union /-
theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∪ t) :=
  fun a b h => Or.imp (hs h) (ht h)
#align is_upper_set.union IsUpperSet.union
-/

#print IsLowerSet.union /-
theorem IsLowerSet.union (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∪ t) :=
  fun a b h => Or.imp (hs h) (ht h)
#align is_lower_set.union IsLowerSet.union
-/

#print IsUpperSet.inter /-
theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∩ t) :=
  fun a b h => And.imp (hs h) (ht h)
#align is_upper_set.inter IsUpperSet.inter
-/

#print IsLowerSet.inter /-
theorem IsLowerSet.inter (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∩ t) :=
  fun a b h => And.imp (hs h) (ht h)
#align is_lower_set.inter IsLowerSet.inter
-/

#print isUpperSet_iUnion /-
theorem isUpperSet_iUnion {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) :=
  fun a b h => Exists₂.imp <| forall_range_iff.2 fun i => hf i h
#align is_upper_set_Union isUpperSet_iUnion
-/

#print isLowerSet_iUnion /-
theorem isLowerSet_iUnion {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋃ i, f i) :=
  fun a b h => Exists₂.imp <| forall_range_iff.2 fun i => hf i h
#align is_lower_set_Union isLowerSet_iUnion
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print isUpperSet_iUnion₂ /-
theorem isUpperSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋃ (i) (j), f i j) :=
  isUpperSet_iUnion fun i => isUpperSet_iUnion <| hf i
#align is_upper_set_Union₂ isUpperSet_iUnion₂
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print isLowerSet_iUnion₂ /-
theorem isLowerSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) :
    IsLowerSet (⋃ (i) (j), f i j) :=
  isLowerSet_iUnion fun i => isLowerSet_iUnion <| hf i
#align is_lower_set_Union₂ isLowerSet_iUnion₂
-/

#print isUpperSet_sUnion /-
theorem isUpperSet_sUnion {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋃₀ S) :=
  fun a b h => Exists₂.imp fun s hs => hf s hs h
#align is_upper_set_sUnion isUpperSet_sUnion
-/

#print isLowerSet_sUnion /-
theorem isLowerSet_sUnion {S : Set (Set α)} (hf : ∀ s ∈ S, IsLowerSet s) : IsLowerSet (⋃₀ S) :=
  fun a b h => Exists₂.imp fun s hs => hf s hs h
#align is_lower_set_sUnion isLowerSet_sUnion
-/

#print isUpperSet_iInter /-
theorem isUpperSet_iInter {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) :=
  fun a b h => forall₂_imp <| forall_range_iff.2 fun i => hf i h
#align is_upper_set_Inter isUpperSet_iInter
-/

#print isLowerSet_iInter /-
theorem isLowerSet_iInter {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋂ i, f i) :=
  fun a b h => forall₂_imp <| forall_range_iff.2 fun i => hf i h
#align is_lower_set_Inter isLowerSet_iInter
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print isUpperSet_iInter₂ /-
theorem isUpperSet_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋂ (i) (j), f i j) :=
  isUpperSet_iInter fun i => isUpperSet_iInter <| hf i
#align is_upper_set_Inter₂ isUpperSet_iInter₂
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print isLowerSet_iInter₂ /-
theorem isLowerSet_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) :
    IsLowerSet (⋂ (i) (j), f i j) :=
  isLowerSet_iInter fun i => isLowerSet_iInter <| hf i
#align is_lower_set_Inter₂ isLowerSet_iInter₂
-/

#print isUpperSet_sInter /-
theorem isUpperSet_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋂₀ S) :=
  fun a b h => forall₂_imp fun s hs => hf s hs h
#align is_upper_set_sInter isUpperSet_sInter
-/

#print isLowerSet_sInter /-
theorem isLowerSet_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsLowerSet s) : IsLowerSet (⋂₀ S) :=
  fun a b h => forall₂_imp fun s hs => hf s hs h
#align is_lower_set_sInter isLowerSet_sInter
-/

#print isLowerSet_preimage_ofDual_iff /-
@[simp]
theorem isLowerSet_preimage_ofDual_iff : IsLowerSet (ofDual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl
#align is_lower_set_preimage_of_dual_iff isLowerSet_preimage_ofDual_iff
-/

#print isUpperSet_preimage_ofDual_iff /-
@[simp]
theorem isUpperSet_preimage_ofDual_iff : IsUpperSet (ofDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl
#align is_upper_set_preimage_of_dual_iff isUpperSet_preimage_ofDual_iff
-/

#print isLowerSet_preimage_toDual_iff /-
@[simp]
theorem isLowerSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsLowerSet (toDual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl
#align is_lower_set_preimage_to_dual_iff isLowerSet_preimage_toDual_iff
-/

#print isUpperSet_preimage_toDual_iff /-
@[simp]
theorem isUpperSet_preimage_toDual_iff {s : Set αᵒᵈ} : IsUpperSet (toDual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl
#align is_upper_set_preimage_to_dual_iff isUpperSet_preimage_toDual_iff
-/

alias ⟨_, IsUpperSet.toDual⟩ := isLowerSet_preimage_ofDual_iff
#align is_upper_set.to_dual IsUpperSet.toDual

alias ⟨_, IsLowerSet.toDual⟩ := isUpperSet_preimage_ofDual_iff
#align is_lower_set.to_dual IsLowerSet.toDual

alias ⟨_, IsUpperSet.ofDual⟩ := isLowerSet_preimage_toDual_iff
#align is_upper_set.of_dual IsUpperSet.ofDual

alias ⟨_, IsLowerSet.ofDual⟩ := isUpperSet_preimage_toDual_iff
#align is_lower_set.of_dual IsLowerSet.ofDual

end LE

section Preorder

variable [Preorder α] [Preorder β] {s : Set α} {p : α → Prop} (a : α)

#print isUpperSet_Ici /-
theorem isUpperSet_Ici : IsUpperSet (Ici a) := fun _ _ => ge_trans
#align is_upper_set_Ici isUpperSet_Ici
-/

#print isLowerSet_Iic /-
theorem isLowerSet_Iic : IsLowerSet (Iic a) := fun _ _ => le_trans
#align is_lower_set_Iic isLowerSet_Iic
-/

#print isUpperSet_Ioi /-
theorem isUpperSet_Ioi : IsUpperSet (Ioi a) := fun _ _ => flip lt_of_lt_of_le
#align is_upper_set_Ioi isUpperSet_Ioi
-/

#print isLowerSet_Iio /-
theorem isLowerSet_Iio : IsLowerSet (Iio a) := fun _ _ => lt_of_le_of_lt
#align is_lower_set_Iio isLowerSet_Iio
-/

#print isUpperSet_iff_Ici_subset /-
theorem isUpperSet_iff_Ici_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ici a ⊆ s := by
  simp [IsUpperSet, subset_def, @forall_swap (_ ∈ s)]
#align is_upper_set_iff_Ici_subset isUpperSet_iff_Ici_subset
-/

#print isLowerSet_iff_Iic_subset /-
theorem isLowerSet_iff_Iic_subset : IsLowerSet s ↔ ∀ ⦃a⦄, a ∈ s → Iic a ⊆ s := by
  simp [IsLowerSet, subset_def, @forall_swap (_ ∈ s)]
#align is_lower_set_iff_Iic_subset isLowerSet_iff_Iic_subset
-/

alias ⟨IsUpperSet.Ici_subset, _⟩ := isUpperSet_iff_Ici_subset
#align is_upper_set.Ici_subset IsUpperSet.Ici_subset

alias ⟨IsLowerSet.Iic_subset, _⟩ := isLowerSet_iff_Iic_subset
#align is_lower_set.Iic_subset IsLowerSet.Iic_subset

#print IsUpperSet.ordConnected /-
theorem IsUpperSet.ordConnected (h : IsUpperSet s) : s.OrdConnected :=
  ⟨fun a ha b _ => Icc_subset_Ici_self.trans <| h.Ici_subset ha⟩
#align is_upper_set.ord_connected IsUpperSet.ordConnected
-/

#print IsLowerSet.ordConnected /-
theorem IsLowerSet.ordConnected (h : IsLowerSet s) : s.OrdConnected :=
  ⟨fun a _ b hb => Icc_subset_Iic_self.trans <| h.Iic_subset hb⟩
#align is_lower_set.ord_connected IsLowerSet.ordConnected
-/

#print IsUpperSet.preimage /-
theorem IsUpperSet.preimage (hs : IsUpperSet s) {f : β → α} (hf : Monotone f) :
    IsUpperSet (f ⁻¹' s : Set β) := fun x y hxy => hs <| hf hxy
#align is_upper_set.preimage IsUpperSet.preimage
-/

#print IsLowerSet.preimage /-
theorem IsLowerSet.preimage (hs : IsLowerSet s) {f : β → α} (hf : Monotone f) :
    IsLowerSet (f ⁻¹' s : Set β) := fun x y hxy => hs <| hf hxy
#align is_lower_set.preimage IsLowerSet.preimage
-/

#print IsUpperSet.image /-
theorem IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : IsUpperSet (f '' s : Set β) :=
  by
  change IsUpperSet ((f : α ≃ β) '' s); rw [Set.image_equiv_eq_preimage_symm]
  exact hs.preimage f.symm.monotone
#align is_upper_set.image IsUpperSet.image
-/

#print IsLowerSet.image /-
theorem IsLowerSet.image (hs : IsLowerSet s) (f : α ≃o β) : IsLowerSet (f '' s : Set β) :=
  by
  change IsLowerSet ((f : α ≃ β) '' s); rw [Set.image_equiv_eq_preimage_symm]
  exact hs.preimage f.symm.monotone
#align is_lower_set.image IsLowerSet.image
-/

#print Set.monotone_mem /-
@[simp]
theorem Set.monotone_mem : Monotone (· ∈ s) ↔ IsUpperSet s :=
  Iff.rfl
#align set.monotone_mem Set.monotone_mem
-/

#print Set.antitone_mem /-
@[simp]
theorem Set.antitone_mem : Antitone (· ∈ s) ↔ IsLowerSet s :=
  forall_swap
#align set.antitone_mem Set.antitone_mem
-/

#print isUpperSet_setOf /-
@[simp]
theorem isUpperSet_setOf : IsUpperSet {a | p a} ↔ Monotone p :=
  Iff.rfl
#align is_upper_set_set_of isUpperSet_setOf
-/

#print isLowerSet_setOf /-
@[simp]
theorem isLowerSet_setOf : IsLowerSet {a | p a} ↔ Antitone p :=
  forall_swap
#align is_lower_set_set_of isLowerSet_setOf
-/

section OrderTop

variable [OrderTop α]

#print IsLowerSet.top_mem /-
theorem IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun a => hs le_top h, fun h => h.symm ▸ mem_univ _⟩
#align is_lower_set.top_mem IsLowerSet.top_mem
-/

#print IsUpperSet.top_mem /-
theorem IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨a, ha⟩ => hs le_top ha⟩
#align is_upper_set.top_mem IsUpperSet.top_mem
-/

#print IsUpperSet.not_top_mem /-
theorem IsUpperSet.not_top_mem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.Not.trans not_nonempty_iff_eq_empty
#align is_upper_set.not_top_mem IsUpperSet.not_top_mem
-/

end OrderTop

section OrderBot

variable [OrderBot α]

#print IsUpperSet.bot_mem /-
theorem IsUpperSet.bot_mem (hs : IsUpperSet s) : ⊥ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun a => hs bot_le h, fun h => h.symm ▸ mem_univ _⟩
#align is_upper_set.bot_mem IsUpperSet.bot_mem
-/

#print IsLowerSet.bot_mem /-
theorem IsLowerSet.bot_mem (hs : IsLowerSet s) : ⊥ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨a, ha⟩ => hs bot_le ha⟩
#align is_lower_set.bot_mem IsLowerSet.bot_mem
-/

#print IsLowerSet.not_bot_mem /-
theorem IsLowerSet.not_bot_mem (hs : IsLowerSet s) : ⊥ ∉ s ↔ s = ∅ :=
  hs.bot_mem.Not.trans not_nonempty_iff_eq_empty
#align is_lower_set.not_bot_mem IsLowerSet.not_bot_mem
-/

end OrderBot

section NoMaxOrder

variable [NoMaxOrder α] (a)

#print IsUpperSet.not_bddAbove /-
theorem IsUpperSet.not_bddAbove (hs : IsUpperSet s) : s.Nonempty → ¬BddAbove s :=
  by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_le (hb <| hs ((hb ha).trans hc.le) ha)
#align is_upper_set.not_bdd_above IsUpperSet.not_bddAbove
-/

#print not_bddAbove_Ici /-
theorem not_bddAbove_Ici : ¬BddAbove (Ici a) :=
  (isUpperSet_Ici _).not_bddAbove nonempty_Ici
#align not_bdd_above_Ici not_bddAbove_Ici
-/

#print not_bddAbove_Ioi /-
theorem not_bddAbove_Ioi : ¬BddAbove (Ioi a) :=
  (isUpperSet_Ioi _).not_bddAbove nonempty_Ioi
#align not_bdd_above_Ioi not_bddAbove_Ioi
-/

end NoMaxOrder

section NoMinOrder

variable [NoMinOrder α] (a)

#print IsLowerSet.not_bddBelow /-
theorem IsLowerSet.not_bddBelow (hs : IsLowerSet s) : s.Nonempty → ¬BddBelow s :=
  by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_lt b
  exact hc.not_le (hb <| hs (hc.le.trans <| hb ha) ha)
#align is_lower_set.not_bdd_below IsLowerSet.not_bddBelow
-/

#print not_bddBelow_Iic /-
theorem not_bddBelow_Iic : ¬BddBelow (Iic a) :=
  (isLowerSet_Iic _).not_bddBelow nonempty_Iic
#align not_bdd_below_Iic not_bddBelow_Iic
-/

#print not_bddBelow_Iio /-
theorem not_bddBelow_Iio : ¬BddBelow (Iio a) :=
  (isLowerSet_Iio _).not_bddBelow nonempty_Iio
#align not_bdd_below_Iio not_bddBelow_Iio
-/

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α}

#print isUpperSet_iff_forall_lt /-
theorem isUpperSet_iff_forall_lt : IsUpperSet s ↔ ∀ ⦃a b : α⦄, a < b → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]
#align is_upper_set_iff_forall_lt isUpperSet_iff_forall_lt
-/

#print isLowerSet_iff_forall_lt /-
theorem isLowerSet_iff_forall_lt : IsLowerSet s ↔ ∀ ⦃a b : α⦄, b < a → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]
#align is_lower_set_iff_forall_lt isLowerSet_iff_forall_lt
-/

#print isUpperSet_iff_Ioi_subset /-
theorem isUpperSet_iff_Ioi_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → Ioi a ⊆ s := by
  simp [isUpperSet_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]
#align is_upper_set_iff_Ioi_subset isUpperSet_iff_Ioi_subset
-/

#print isLowerSet_iff_Iio_subset /-
theorem isLowerSet_iff_Iio_subset : IsLowerSet s ↔ ∀ ⦃a⦄, a ∈ s → Iio a ⊆ s := by
  simp [isLowerSet_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]
#align is_lower_set_iff_Iio_subset isLowerSet_iff_Iio_subset
-/

alias ⟨IsUpperSet.Ioi_subset, _⟩ := isUpperSet_iff_Ioi_subset
#align is_upper_set.Ioi_subset IsUpperSet.Ioi_subset

alias ⟨IsLowerSet.Iio_subset, _⟩ := isLowerSet_iff_Iio_subset
#align is_lower_set.Iio_subset IsLowerSet.Iio_subset

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s t : Set α}

#print IsUpperSet.total /-
theorem IsUpperSet.total (hs : IsUpperSet s) (ht : IsUpperSet t) : s ⊆ t ∨ t ⊆ s :=
  by
  by_contra' h
  simp_rw [Set.not_subset] at h 
  obtain ⟨⟨a, has, hat⟩, b, hbt, hbs⟩ := h
  obtain hab | hba := le_total a b
  · exact hbs (hs hab has)
  · exact hat (ht hba hbt)
#align is_upper_set.total IsUpperSet.total
-/

#print IsLowerSet.total /-
theorem IsLowerSet.total (hs : IsLowerSet s) (ht : IsLowerSet t) : s ⊆ t ∨ t ⊆ s :=
  hs.toDual.Total ht.toDual
#align is_lower_set.total IsLowerSet.total
-/

end LinearOrder

/-! ### Bundled upper/lower sets -/


section LE

variable [LE α]

#print UpperSet /-
/-- The type of upper sets of an order. -/
structure UpperSet (α : Type _) [LE α] where
  carrier : Set α
  upper' : IsUpperSet carrier
#align upper_set UpperSet
-/

#print LowerSet /-
/-- The type of lower sets of an order. -/
structure LowerSet (α : Type _) [LE α] where
  carrier : Set α
  lower' : IsLowerSet carrier
#align lower_set LowerSet
-/

namespace UpperSet

instance : SetLike (UpperSet α) α where
  coe := UpperSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

#print UpperSet.ext /-
@[ext]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'
#align upper_set.ext UpperSet.ext
-/

#print UpperSet.carrier_eq_coe /-
@[simp]
theorem carrier_eq_coe (s : UpperSet α) : s.carrier = s :=
  rfl
#align upper_set.carrier_eq_coe UpperSet.carrier_eq_coe
-/

#print UpperSet.upper /-
protected theorem upper (s : UpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'
#align upper_set.upper UpperSet.upper
-/

#print UpperSet.mem_mk /-
@[simp]
theorem mem_mk (carrier : Set α) (upper') {a : α} : a ∈ mk carrier upper' ↔ a ∈ carrier :=
  Iff.rfl
#align upper_set.mem_mk UpperSet.mem_mk
-/

end UpperSet

namespace LowerSet

instance : SetLike (LowerSet α) α where
  coe := LowerSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

#print LowerSet.ext /-
@[ext]
theorem ext {s t : LowerSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'
#align lower_set.ext LowerSet.ext
-/

#print LowerSet.carrier_eq_coe /-
@[simp]
theorem carrier_eq_coe (s : LowerSet α) : s.carrier = s :=
  rfl
#align lower_set.carrier_eq_coe LowerSet.carrier_eq_coe
-/

#print LowerSet.lower /-
protected theorem lower (s : LowerSet α) : IsLowerSet (s : Set α) :=
  s.lower'
#align lower_set.lower LowerSet.lower
-/

#print LowerSet.mem_mk /-
@[simp]
theorem mem_mk (carrier : Set α) (lower') {a : α} : a ∈ mk carrier lower' ↔ a ∈ carrier :=
  Iff.rfl
#align lower_set.mem_mk LowerSet.mem_mk
-/

end LowerSet

/-! #### Order -/


namespace UpperSet

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

instance : Sup (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

instance : Inf (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

instance : Top (UpperSet α) :=
  ⟨⟨∅, isUpperSet_empty⟩⟩

instance : Bot (UpperSet α) :=
  ⟨⟨univ, isUpperSet_univ⟩⟩

instance : SupSet (UpperSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isUpperSet_iInter₂ fun s _ => s.upper⟩⟩

instance : InfSet (UpperSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isUpperSet_iUnion₂ fun s _ => s.upper⟩⟩

instance : CompleteDistribLattice (UpperSet α) :=
  (toDual.Injective.comp <| SetLike.coe_injective).CompleteDistribLattice _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

#print UpperSet.coe_subset_coe /-
@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ t ≤ s :=
  Iff.rfl
#align upper_set.coe_subset_coe UpperSet.coe_subset_coe
-/

#print UpperSet.coe_top /-
@[simp, norm_cast]
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl
#align upper_set.coe_top UpperSet.coe_top
-/

#print UpperSet.coe_bot /-
@[simp, norm_cast]
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl
#align upper_set.coe_bot UpperSet.coe_bot
-/

#print UpperSet.coe_eq_univ /-
@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊥ := by simp [SetLike.ext'_iff]
#align upper_set.coe_eq_univ UpperSet.coe_eq_univ
-/

#print UpperSet.coe_eq_empty /-
@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤ := by simp [SetLike.ext'_iff]
#align upper_set.coe_eq_empty UpperSet.coe_eq_empty
-/

#print UpperSet.coe_sup /-
@[simp, norm_cast]
theorem coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = s ∩ t :=
  rfl
#align upper_set.coe_sup UpperSet.coe_sup
-/

#print UpperSet.coe_inf /-
@[simp, norm_cast]
theorem coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = s ∪ t :=
  rfl
#align upper_set.coe_inf UpperSet.coe_inf
-/

#print UpperSet.coe_sSup /-
@[simp, norm_cast]
theorem coe_sSup (S : Set (UpperSet α)) : (↑(sSup S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl
#align upper_set.coe_Sup UpperSet.coe_sSup
-/

#print UpperSet.coe_sInf /-
@[simp, norm_cast]
theorem coe_sInf (S : Set (UpperSet α)) : (↑(sInf S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl
#align upper_set.coe_Inf UpperSet.coe_sInf
-/

#print UpperSet.coe_iSup /-
@[simp, norm_cast]
theorem coe_iSup (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by simp [iSup]
#align upper_set.coe_supr UpperSet.coe_iSup
-/

#print UpperSet.coe_iInf /-
@[simp, norm_cast]
theorem coe_iInf (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [iInf]
#align upper_set.coe_infi UpperSet.coe_iInf
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print UpperSet.coe_iSup₂ /-
@[simp, norm_cast]
theorem coe_iSup₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j :=
  by simp_rw [coe_supr]
#align upper_set.coe_supr₂ UpperSet.coe_iSup₂
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print UpperSet.coe_iInf₂ /-
@[simp, norm_cast]
theorem coe_iInf₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j :=
  by simp_rw [coe_infi]
#align upper_set.coe_infi₂ UpperSet.coe_iInf₂
-/

#print UpperSet.not_mem_top /-
@[simp]
theorem not_mem_top : a ∉ (⊤ : UpperSet α) :=
  id
#align upper_set.not_mem_top UpperSet.not_mem_top
-/

#print UpperSet.mem_bot /-
@[simp]
theorem mem_bot : a ∈ (⊥ : UpperSet α) :=
  trivial
#align upper_set.mem_bot UpperSet.mem_bot
-/

#print UpperSet.mem_sup_iff /-
@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl
#align upper_set.mem_sup_iff UpperSet.mem_sup_iff
-/

#print UpperSet.mem_inf_iff /-
@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl
#align upper_set.mem_inf_iff UpperSet.mem_inf_iff
-/

#print UpperSet.mem_sSup_iff /-
@[simp]
theorem mem_sSup_iff : a ∈ sSup S ↔ ∀ s ∈ S, a ∈ s :=
  mem_iInter₂
#align upper_set.mem_Sup_iff UpperSet.mem_sSup_iff
-/

#print UpperSet.mem_sInf_iff /-
@[simp]
theorem mem_sInf_iff : a ∈ sInf S ↔ ∃ s ∈ S, a ∈ s :=
  mem_iUnion₂
#align upper_set.mem_Inf_iff UpperSet.mem_sInf_iff
-/

#print UpperSet.mem_iSup_iff /-
@[simp]
theorem mem_iSup_iff {f : ι → UpperSet α} : (a ∈ ⨆ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_supr]; exact mem_Inter
#align upper_set.mem_supr_iff UpperSet.mem_iSup_iff
-/

#print UpperSet.mem_iInf_iff /-
@[simp]
theorem mem_iInf_iff {f : ι → UpperSet α} : (a ∈ ⨅ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_infi]; exact mem_Union
#align upper_set.mem_infi_iff UpperSet.mem_iInf_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print UpperSet.mem_iSup₂_iff /-
@[simp]
theorem mem_iSup₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_supr_iff]
#align upper_set.mem_supr₂_iff UpperSet.mem_iSup₂_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print UpperSet.mem_iInf₂_iff /-
@[simp]
theorem mem_iInf₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_infi_iff]
#align upper_set.mem_infi₂_iff UpperSet.mem_iInf₂_iff
-/

#print UpperSet.codisjoint_coe /-
@[simp, norm_cast]
theorem codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]
#align upper_set.codisjoint_coe UpperSet.codisjoint_coe
-/

end UpperSet

namespace LowerSet

variable {S : Set (LowerSet α)} {s t : LowerSet α} {a : α}

instance : Sup (LowerSet α) :=
  ⟨fun s t => ⟨s ∪ t, fun a b h => Or.imp (s.lower h) (t.lower h)⟩⟩

instance : Inf (LowerSet α) :=
  ⟨fun s t => ⟨s ∩ t, fun a b h => And.imp (s.lower h) (t.lower h)⟩⟩

instance : Top (LowerSet α) :=
  ⟨⟨univ, fun a b h => id⟩⟩

instance : Bot (LowerSet α) :=
  ⟨⟨∅, fun a b h => id⟩⟩

instance : SupSet (LowerSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isLowerSet_iUnion₂ fun s _ => s.lower⟩⟩

instance : InfSet (LowerSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isLowerSet_iInter₂ fun s _ => s.lower⟩⟩

instance : CompleteDistribLattice (LowerSet α) :=
  SetLike.coe_injective.CompleteDistribLattice _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl

instance : Inhabited (LowerSet α) :=
  ⟨⊥⟩

#print LowerSet.coe_subset_coe /-
@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  Iff.rfl
#align lower_set.coe_subset_coe LowerSet.coe_subset_coe
-/

#print LowerSet.coe_top /-
@[simp, norm_cast]
theorem coe_top : ((⊤ : LowerSet α) : Set α) = univ :=
  rfl
#align lower_set.coe_top LowerSet.coe_top
-/

#print LowerSet.coe_bot /-
@[simp, norm_cast]
theorem coe_bot : ((⊥ : LowerSet α) : Set α) = ∅ :=
  rfl
#align lower_set.coe_bot LowerSet.coe_bot
-/

#print LowerSet.coe_eq_univ /-
@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊤ := by simp [SetLike.ext'_iff]
#align lower_set.coe_eq_univ LowerSet.coe_eq_univ
-/

#print LowerSet.coe_eq_empty /-
@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊥ := by simp [SetLike.ext'_iff]
#align lower_set.coe_eq_empty LowerSet.coe_eq_empty
-/

#print LowerSet.coe_sup /-
@[simp, norm_cast]
theorem coe_sup (s t : LowerSet α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align lower_set.coe_sup LowerSet.coe_sup
-/

#print LowerSet.coe_inf /-
@[simp, norm_cast]
theorem coe_inf (s t : LowerSet α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align lower_set.coe_inf LowerSet.coe_inf
-/

#print LowerSet.coe_sSup /-
@[simp, norm_cast]
theorem coe_sSup (S : Set (LowerSet α)) : (↑(sSup S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl
#align lower_set.coe_Sup LowerSet.coe_sSup
-/

#print LowerSet.coe_sInf /-
@[simp, norm_cast]
theorem coe_sInf (S : Set (LowerSet α)) : (↑(sInf S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl
#align lower_set.coe_Inf LowerSet.coe_sInf
-/

#print LowerSet.coe_iSup /-
@[simp, norm_cast]
theorem coe_iSup (f : ι → LowerSet α) : (↑(⨆ i, f i) : Set α) = ⋃ i, f i := by
  simp_rw [iSup, coe_Sup, mem_range, Union_exists, Union_Union_eq']
#align lower_set.coe_supr LowerSet.coe_iSup
-/

#print LowerSet.coe_iInf /-
@[simp, norm_cast]
theorem coe_iInf (f : ι → LowerSet α) : (↑(⨅ i, f i) : Set α) = ⋂ i, f i := by
  simp_rw [iInf, coe_Inf, mem_range, Inter_exists, Inter_Inter_eq']
#align lower_set.coe_infi LowerSet.coe_iInf
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print LowerSet.coe_iSup₂ /-
@[simp, norm_cast]
theorem coe_iSup₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j :=
  by simp_rw [coe_supr]
#align lower_set.coe_supr₂ LowerSet.coe_iSup₂
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print LowerSet.coe_iInf₂ /-
@[simp, norm_cast]
theorem coe_iInf₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j :=
  by simp_rw [coe_infi]
#align lower_set.coe_infi₂ LowerSet.coe_iInf₂
-/

#print LowerSet.mem_top /-
@[simp]
theorem mem_top : a ∈ (⊤ : LowerSet α) :=
  trivial
#align lower_set.mem_top LowerSet.mem_top
-/

#print LowerSet.not_mem_bot /-
@[simp]
theorem not_mem_bot : a ∉ (⊥ : LowerSet α) :=
  id
#align lower_set.not_mem_bot LowerSet.not_mem_bot
-/

#print LowerSet.mem_sup_iff /-
@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl
#align lower_set.mem_sup_iff LowerSet.mem_sup_iff
-/

#print LowerSet.mem_inf_iff /-
@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl
#align lower_set.mem_inf_iff LowerSet.mem_inf_iff
-/

#print LowerSet.mem_sSup_iff /-
@[simp]
theorem mem_sSup_iff : a ∈ sSup S ↔ ∃ s ∈ S, a ∈ s :=
  mem_iUnion₂
#align lower_set.mem_Sup_iff LowerSet.mem_sSup_iff
-/

#print LowerSet.mem_sInf_iff /-
@[simp]
theorem mem_sInf_iff : a ∈ sInf S ↔ ∀ s ∈ S, a ∈ s :=
  mem_iInter₂
#align lower_set.mem_Inf_iff LowerSet.mem_sInf_iff
-/

#print LowerSet.mem_iSup_iff /-
@[simp]
theorem mem_iSup_iff {f : ι → LowerSet α} : (a ∈ ⨆ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_supr]; exact mem_Union
#align lower_set.mem_supr_iff LowerSet.mem_iSup_iff
-/

#print LowerSet.mem_iInf_iff /-
@[simp]
theorem mem_iInf_iff {f : ι → LowerSet α} : (a ∈ ⨅ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_infi]; exact mem_Inter
#align lower_set.mem_infi_iff LowerSet.mem_iInf_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print LowerSet.mem_iSup₂_iff /-
@[simp]
theorem mem_iSup₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_supr_iff]
#align lower_set.mem_supr₂_iff LowerSet.mem_iSup₂_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print LowerSet.mem_iInf₂_iff /-
@[simp]
theorem mem_iInf₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_infi_iff]
#align lower_set.mem_infi₂_iff LowerSet.mem_iInf₂_iff
-/

#print LowerSet.disjoint_coe /-
@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, SetLike.ext'_iff]
#align lower_set.disjoint_coe LowerSet.disjoint_coe
-/

end LowerSet

/-! #### Complement -/


#print UpperSet.compl /-
/-- The complement of a lower set as an upper set. -/
def UpperSet.compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩
#align upper_set.compl UpperSet.compl
-/

#print LowerSet.compl /-
/-- The complement of a lower set as an upper set. -/
def LowerSet.compl (s : LowerSet α) : UpperSet α :=
  ⟨sᶜ, s.lower.compl⟩
#align lower_set.compl LowerSet.compl
-/

namespace UpperSet

variable {s t : UpperSet α} {a : α}

#print UpperSet.coe_compl /-
@[simp]
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = sᶜ :=
  rfl
#align upper_set.coe_compl UpperSet.coe_compl
-/

#print UpperSet.mem_compl_iff /-
@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl
#align upper_set.mem_compl_iff UpperSet.mem_compl_iff
-/

#print UpperSet.compl_compl /-
@[simp]
theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
  UpperSet.ext <| compl_compl _
#align upper_set.compl_compl UpperSet.compl_compl
-/

#print UpperSet.compl_le_compl /-
@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl
#align upper_set.compl_le_compl UpperSet.compl_le_compl
-/

#print UpperSet.compl_sup /-
@[simp]
protected theorem compl_sup (s t : UpperSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  LowerSet.ext compl_inf
#align upper_set.compl_sup UpperSet.compl_sup
-/

#print UpperSet.compl_inf /-
@[simp]
protected theorem compl_inf (s t : UpperSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  LowerSet.ext compl_sup
#align upper_set.compl_inf UpperSet.compl_inf
-/

#print UpperSet.compl_top /-
@[simp]
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty
#align upper_set.compl_top UpperSet.compl_top
-/

#print UpperSet.compl_bot /-
@[simp]
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ
#align upper_set.compl_bot UpperSet.compl_bot
-/

#print UpperSet.compl_sSup /-
@[simp]
protected theorem compl_sSup (S : Set (UpperSet α)) : (sSup S).compl = ⨆ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_Sup, compl_Inter₂, LowerSet.coe_iSup₂]
#align upper_set.compl_Sup UpperSet.compl_sSup
-/

#print UpperSet.compl_sInf /-
@[simp]
protected theorem compl_sInf (S : Set (UpperSet α)) : (sInf S).compl = ⨅ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_Inf, compl_Union₂, LowerSet.coe_iInf₂]
#align upper_set.compl_Inf UpperSet.compl_sInf
-/

#print UpperSet.compl_iSup /-
@[simp]
protected theorem compl_iSup (f : ι → UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_supr, compl_Inter, LowerSet.coe_iSup]
#align upper_set.compl_supr UpperSet.compl_iSup
-/

#print UpperSet.compl_iInf /-
@[simp]
protected theorem compl_iInf (f : ι → UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_infi, compl_Union, LowerSet.coe_iInf]
#align upper_set.compl_infi UpperSet.compl_iInf
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print UpperSet.compl_iSup₂ /-
@[simp]
theorem compl_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [UpperSet.compl_iSup]
#align upper_set.compl_supr₂ UpperSet.compl_iSup₂
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print UpperSet.compl_iInf₂ /-
@[simp]
theorem compl_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [UpperSet.compl_iInf]
#align upper_set.compl_infi₂ UpperSet.compl_iInf₂
-/

end UpperSet

namespace LowerSet

variable {s t : LowerSet α} {a : α}

#print LowerSet.coe_compl /-
@[simp]
theorem coe_compl (s : LowerSet α) : (s.compl : Set α) = sᶜ :=
  rfl
#align lower_set.coe_compl LowerSet.coe_compl
-/

#print LowerSet.mem_compl_iff /-
@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl
#align lower_set.mem_compl_iff LowerSet.mem_compl_iff
-/

#print LowerSet.compl_compl /-
@[simp]
theorem compl_compl (s : LowerSet α) : s.compl.compl = s :=
  LowerSet.ext <| compl_compl _
#align lower_set.compl_compl LowerSet.compl_compl
-/

#print LowerSet.compl_le_compl /-
@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl
#align lower_set.compl_le_compl LowerSet.compl_le_compl
-/

#print LowerSet.compl_sup /-
protected theorem compl_sup (s t : LowerSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  UpperSet.ext compl_sup
#align lower_set.compl_sup LowerSet.compl_sup
-/

#print LowerSet.compl_inf /-
protected theorem compl_inf (s t : LowerSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  UpperSet.ext compl_inf
#align lower_set.compl_inf LowerSet.compl_inf
-/

#print LowerSet.compl_top /-
protected theorem compl_top : (⊤ : LowerSet α).compl = ⊤ :=
  UpperSet.ext compl_univ
#align lower_set.compl_top LowerSet.compl_top
-/

#print LowerSet.compl_bot /-
protected theorem compl_bot : (⊥ : LowerSet α).compl = ⊥ :=
  UpperSet.ext compl_empty
#align lower_set.compl_bot LowerSet.compl_bot
-/

#print LowerSet.compl_sSup /-
protected theorem compl_sSup (S : Set (LowerSet α)) : (sSup S).compl = ⨆ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_Sup, compl_Union₂, UpperSet.coe_iSup₂]
#align lower_set.compl_Sup LowerSet.compl_sSup
-/

#print LowerSet.compl_sInf /-
protected theorem compl_sInf (S : Set (LowerSet α)) : (sInf S).compl = ⨅ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_Inf, compl_Inter₂, UpperSet.coe_iInf₂]
#align lower_set.compl_Inf LowerSet.compl_sInf
-/

#print LowerSet.compl_iSup /-
protected theorem compl_iSup (f : ι → LowerSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_supr, compl_Union, UpperSet.coe_iSup]
#align lower_set.compl_supr LowerSet.compl_iSup
-/

#print LowerSet.compl_iInf /-
protected theorem compl_iInf (f : ι → LowerSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_infi, compl_Inter, UpperSet.coe_iInf]
#align lower_set.compl_infi LowerSet.compl_iInf
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print LowerSet.compl_iSup₂ /-
@[simp]
theorem compl_iSup₂ (f : ∀ i, κ i → LowerSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_iSup]
#align lower_set.compl_supr₂ LowerSet.compl_iSup₂
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print LowerSet.compl_iInf₂ /-
@[simp]
theorem compl_iInf₂ (f : ∀ i, κ i → LowerSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_iInf]
#align lower_set.compl_infi₂ LowerSet.compl_iInf₂
-/

end LowerSet

#print upperSetIsoLowerSet /-
/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
def upperSetIsoLowerSet : UpperSet α ≃o LowerSet α
    where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' _ _ := UpperSet.compl_le_compl
#align upper_set_iso_lower_set upperSetIsoLowerSet
-/

end LE

section LinearOrder

variable [LinearOrder α]

#print UpperSet.isTotal_le /-
instance UpperSet.isTotal_le : IsTotal (UpperSet α) (· ≤ ·) :=
  ⟨fun s t => t.upper.Total s.upper⟩
#align upper_set.is_total_le UpperSet.isTotal_le
-/

#print LowerSet.isTotal_le /-
instance LowerSet.isTotal_le : IsTotal (LowerSet α) (· ≤ ·) :=
  ⟨fun s t => s.lower.Total t.lower⟩
#align lower_set.is_total_le LowerSet.isTotal_le
-/

noncomputable instance : CompleteLinearOrder (UpperSet α) :=
  { UpperSet.completeDistribLattice with
    le_total := IsTotal.total
    decidableLe := Classical.decRel _
    DecidableEq := Classical.decRel _
    decidableLt := Classical.decRel _
    max_def := by classical exact sup_eq_maxDefault
    min_def := by classical exact inf_eq_minDefault }

noncomputable instance : CompleteLinearOrder (LowerSet α) :=
  { LowerSet.completeDistribLattice with
    le_total := IsTotal.total
    decidableLe := Classical.decRel _
    DecidableEq := Classical.decRel _
    decidableLt := Classical.decRel _
    max_def := by classical exact sup_eq_maxDefault
    min_def := by classical exact inf_eq_minDefault }

end LinearOrder

/-! #### Map -/


section

variable [Preorder α] [Preorder β] [Preorder γ]

namespace UpperSet

variable {f : α ≃o β} {s t : UpperSet α} {a : α} {b : β}

#print UpperSet.map /-
/-- An order isomorphism of preorders induces an order isomorphism of their upper sets. -/
def map (f : α ≃o β) : UpperSet α ≃o UpperSet β
    where
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.Preimage f.Monotone⟩
  left_inv _ := ext <| f.preimage_image _
  right_inv _ := ext <| f.image_preimage _
  map_rel_iff' s t := image_subset_image_iff f.Injective
#align upper_set.map UpperSet.map
-/

#print UpperSet.symm_map /-
@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  FunLike.ext _ _ fun s => ext <| Set.preimage_equiv_eq_image_symm _ _
#align upper_set.symm_map UpperSet.symm_map
-/

#print UpperSet.mem_map /-
@[simp]
theorem mem_map : b ∈ map f s ↔ f.symm b ∈ s := by rw [← f.symm_symm, ← symm_map, f.symm_symm]; rfl
#align upper_set.mem_map UpperSet.mem_map
-/

#print UpperSet.map_refl /-
@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by ext; simp
#align upper_set.map_refl UpperSet.map_refl
-/

#print UpperSet.map_map /-
@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by ext; simp
#align upper_set.map_map UpperSet.map_map
-/

variable (f s t)

#print UpperSet.coe_map /-
@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl
#align upper_set.coe_map UpperSet.coe_map
-/

end UpperSet

namespace LowerSet

variable {f : α ≃o β} {s t : LowerSet α} {a : α} {b : β}

#print LowerSet.map /-
/-- An order isomorphism of preorders induces an order isomorphism of their lower sets. -/
def map (f : α ≃o β) : LowerSet α ≃o LowerSet β
    where
  toFun s := ⟨f '' s, s.lower.image f⟩
  invFun t := ⟨f ⁻¹' t, t.lower.Preimage f.Monotone⟩
  left_inv _ := SetLike.coe_injective <| f.preimage_image _
  right_inv _ := SetLike.coe_injective <| f.image_preimage _
  map_rel_iff' s t := image_subset_image_iff f.Injective
#align lower_set.map LowerSet.map
-/

#print LowerSet.symm_map /-
@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  FunLike.ext _ _ fun s => SetLike.coe_injective <| Set.preimage_equiv_eq_image_symm _ _
#align lower_set.symm_map LowerSet.symm_map
-/

#print LowerSet.mem_map /-
@[simp]
theorem mem_map {f : α ≃o β} {b : β} : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]; rfl
#align lower_set.mem_map LowerSet.mem_map
-/

#print LowerSet.map_refl /-
@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by ext; simp
#align lower_set.map_refl LowerSet.map_refl
-/

#print LowerSet.map_map /-
@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by ext; simp
#align lower_set.map_map LowerSet.map_map
-/

variable (f s t)

#print LowerSet.coe_map /-
@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl
#align lower_set.coe_map LowerSet.coe_map
-/

end LowerSet

namespace UpperSet

#print UpperSet.compl_map /-
@[simp]
theorem compl_map (f : α ≃o β) (s : UpperSet α) : (map f s).compl = LowerSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.Bijective).symm
#align upper_set.compl_map UpperSet.compl_map
-/

end UpperSet

namespace LowerSet

#print LowerSet.compl_map /-
@[simp]
theorem compl_map (f : α ≃o β) (s : LowerSet α) : (map f s).compl = UpperSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.Bijective).symm
#align lower_set.compl_map LowerSet.compl_map
-/

end LowerSet

end

/-! #### Principal sets -/


namespace UpperSet

section Preorder

variable [Preorder α] [Preorder β] {s : UpperSet α} {a b : α}

#print UpperSet.Ici /-
/-- The smallest upper set containing a given element. -/
def Ici (a : α) : UpperSet α :=
  ⟨Ici a, isUpperSet_Ici a⟩
#align upper_set.Ici UpperSet.Ici
-/

#print UpperSet.Ioi /-
/-- The smallest upper set containing a given element. -/
def Ioi (a : α) : UpperSet α :=
  ⟨Ioi a, isUpperSet_Ioi a⟩
#align upper_set.Ioi UpperSet.Ioi
-/

#print UpperSet.coe_Ici /-
@[simp]
theorem coe_Ici (a : α) : ↑(Ici a) = Set.Ici a :=
  rfl
#align upper_set.coe_Ici UpperSet.coe_Ici
-/

#print UpperSet.coe_Ioi /-
@[simp]
theorem coe_Ioi (a : α) : ↑(Ioi a) = Set.Ioi a :=
  rfl
#align upper_set.coe_Ioi UpperSet.coe_Ioi
-/

#print UpperSet.mem_Ici_iff /-
@[simp]
theorem mem_Ici_iff : b ∈ Ici a ↔ a ≤ b :=
  Iff.rfl
#align upper_set.mem_Ici_iff UpperSet.mem_Ici_iff
-/

#print UpperSet.mem_Ioi_iff /-
@[simp]
theorem mem_Ioi_iff : b ∈ Ioi a ↔ a < b :=
  Iff.rfl
#align upper_set.mem_Ioi_iff UpperSet.mem_Ioi_iff
-/

#print UpperSet.map_Ici /-
@[simp]
theorem map_Ici (f : α ≃o β) (a : α) : map f (Ici a) = Ici (f a) := by ext; simp
#align upper_set.map_Ici UpperSet.map_Ici
-/

#print UpperSet.map_Ioi /-
@[simp]
theorem map_Ioi (f : α ≃o β) (a : α) : map f (Ioi a) = Ioi (f a) := by ext; simp
#align upper_set.map_Ioi UpperSet.map_Ioi
-/

#print UpperSet.Ici_le_Ioi /-
theorem Ici_le_Ioi (a : α) : Ici a ≤ Ioi a :=
  Ioi_subset_Ici_self
#align upper_set.Ici_le_Ioi UpperSet.Ici_le_Ioi
-/

#print UpperSet.Ioi_top /-
@[simp]
theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top
#align upper_set.Ioi_top UpperSet.Ioi_top
-/

#print UpperSet.Ici_bot /-
@[simp]
theorem Ici_bot [OrderBot α] : Ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot
#align upper_set.Ici_bot UpperSet.Ici_bot
-/

end Preorder

#print UpperSet.Ici_sup /-
@[simp]
theorem Ici_sup [SemilatticeSup α] (a b : α) : Ici (a ⊔ b) = Ici a ⊔ Ici b :=
  ext Ici_inter_Ici.symm
#align upper_set.Ici_sup UpperSet.Ici_sup
-/

section CompleteLattice

variable [CompleteLattice α]

#print UpperSet.Ici_sSup /-
@[simp]
theorem Ici_sSup (S : Set α) : Ici (sSup S) = ⨆ a ∈ S, Ici a :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_supr_iff, sSup_le_iff]
#align upper_set.Ici_Sup UpperSet.Ici_sSup
-/

#print UpperSet.Ici_iSup /-
@[simp]
theorem Ici_iSup (f : ι → α) : Ici (⨆ i, f i) = ⨆ i, Ici (f i) :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_supr_iff, iSup_le_iff]
#align upper_set.Ici_supr UpperSet.Ici_iSup
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print UpperSet.Ici_iSup₂ /-
@[simp]
theorem Ici_iSup₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⨆ (i) (j), Ici (f i j) := by
  simp_rw [Ici_supr]
#align upper_set.Ici_supr₂ UpperSet.Ici_iSup₂
-/

end CompleteLattice

end UpperSet

namespace LowerSet

section Preorder

variable [Preorder α] [Preorder β] {s : LowerSet α} {a b : α}

#print LowerSet.Iic /-
/-- Principal lower set. `set.Iic` as a lower set. The smallest lower set containing a given
element. -/
def Iic (a : α) : LowerSet α :=
  ⟨Iic a, isLowerSet_Iic a⟩
#align lower_set.Iic LowerSet.Iic
-/

#print LowerSet.Iio /-
/-- Strict principal lower set. `set.Iio` as a lower set. -/
def Iio (a : α) : LowerSet α :=
  ⟨Iio a, isLowerSet_Iio a⟩
#align lower_set.Iio LowerSet.Iio
-/

#print LowerSet.coe_Iic /-
@[simp]
theorem coe_Iic (a : α) : ↑(Iic a) = Set.Iic a :=
  rfl
#align lower_set.coe_Iic LowerSet.coe_Iic
-/

#print LowerSet.coe_Iio /-
@[simp]
theorem coe_Iio (a : α) : ↑(Iio a) = Set.Iio a :=
  rfl
#align lower_set.coe_Iio LowerSet.coe_Iio
-/

#print LowerSet.mem_Iic_iff /-
@[simp]
theorem mem_Iic_iff : b ∈ Iic a ↔ b ≤ a :=
  Iff.rfl
#align lower_set.mem_Iic_iff LowerSet.mem_Iic_iff
-/

#print LowerSet.mem_Iio_iff /-
@[simp]
theorem mem_Iio_iff : b ∈ Iio a ↔ b < a :=
  Iff.rfl
#align lower_set.mem_Iio_iff LowerSet.mem_Iio_iff
-/

#print LowerSet.map_Iic /-
@[simp]
theorem map_Iic (f : α ≃o β) (a : α) : map f (Iic a) = Iic (f a) := by ext; simp
#align lower_set.map_Iic LowerSet.map_Iic
-/

#print LowerSet.map_Iio /-
@[simp]
theorem map_Iio (f : α ≃o β) (a : α) : map f (Iio a) = Iio (f a) := by ext; simp
#align lower_set.map_Iio LowerSet.map_Iio
-/

#print LowerSet.Ioi_le_Ici /-
theorem Ioi_le_Ici (a : α) : Ioi a ≤ Ici a :=
  Ioi_subset_Ici_self
#align lower_set.Ioi_le_Ici LowerSet.Ioi_le_Ici
-/

#print LowerSet.Iic_top /-
@[simp]
theorem Iic_top [OrderTop α] : Iic (⊤ : α) = ⊤ :=
  SetLike.coe_injective Iic_top
#align lower_set.Iic_top LowerSet.Iic_top
-/

#print LowerSet.Iio_bot /-
@[simp]
theorem Iio_bot [OrderBot α] : Iio (⊥ : α) = ⊥ :=
  SetLike.coe_injective Iio_bot
#align lower_set.Iio_bot LowerSet.Iio_bot
-/

end Preorder

#print LowerSet.Iic_inf /-
@[simp]
theorem Iic_inf [SemilatticeInf α] (a b : α) : Iic (a ⊓ b) = Iic a ⊓ Iic b :=
  SetLike.coe_injective Iic_inter_Iic.symm
#align lower_set.Iic_inf LowerSet.Iic_inf
-/

section CompleteLattice

variable [CompleteLattice α]

#print LowerSet.Iic_sInf /-
@[simp]
theorem Iic_sInf (S : Set α) : Iic (sInf S) = ⨅ a ∈ S, Iic a :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_infi₂_iff, le_sInf_iff]
#align lower_set.Iic_Inf LowerSet.Iic_sInf
-/

#print LowerSet.Iic_iInf /-
@[simp]
theorem Iic_iInf (f : ι → α) : Iic (⨅ i, f i) = ⨅ i, Iic (f i) :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_infi_iff, le_iInf_iff]
#align lower_set.Iic_infi LowerSet.Iic_iInf
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
#print LowerSet.Iic_iInf₂ /-
@[simp]
theorem Iic_iInf₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⨅ (i) (j), Iic (f i j) := by
  simp_rw [Iic_infi]
#align lower_set.Iic_infi₂ LowerSet.Iic_iInf₂
-/

end CompleteLattice

end LowerSet

section closure

variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

#print upperClosure /-
/-- The greatest upper set containing a given set. -/
def upperClosure (s : Set α) : UpperSet α :=
  ⟨{x | ∃ a ∈ s, a ≤ x}, fun x y h => Exists₂.imp fun a _ => h.trans'⟩
#align upper_closure upperClosure
-/

#print lowerClosure /-
/-- The least lower set containing a given set. -/
def lowerClosure (s : Set α) : LowerSet α :=
  ⟨{x | ∃ a ∈ s, x ≤ a}, fun x y h => Exists₂.imp fun a _ => h.trans⟩
#align lower_closure lowerClosure
-/

#print mem_upperClosure /-
@[simp]
theorem mem_upperClosure : x ∈ upperClosure s ↔ ∃ a ∈ s, a ≤ x :=
  Iff.rfl
#align mem_upper_closure mem_upperClosure
-/

#print mem_lowerClosure /-
@[simp]
theorem mem_lowerClosure : x ∈ lowerClosure s ↔ ∃ a ∈ s, x ≤ a :=
  Iff.rfl
#align mem_lower_closure mem_lowerClosure
-/

#print coe_upperClosure /-
-- We do not tag those two as `simp` to respect the abstraction.
@[norm_cast]
theorem coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a ∈ s, Ici a := by ext; simp
#align coe_upper_closure coe_upperClosure
-/

#print coe_lowerClosure /-
@[norm_cast]
theorem coe_lowerClosure (s : Set α) : ↑(lowerClosure s) = ⋃ a ∈ s, Iic a := by ext; simp
#align coe_lower_closure coe_lowerClosure
-/

#print subset_upperClosure /-
theorem subset_upperClosure : s ⊆ upperClosure s := fun x hx => ⟨x, hx, le_rfl⟩
#align subset_upper_closure subset_upperClosure
-/

#print subset_lowerClosure /-
theorem subset_lowerClosure : s ⊆ lowerClosure s := fun x hx => ⟨x, hx, le_rfl⟩
#align subset_lower_closure subset_lowerClosure
-/

#print upperClosure_min /-
theorem upperClosure_min (h : s ⊆ t) (ht : IsUpperSet t) : ↑(upperClosure s) ⊆ t :=
  fun a ⟨b, hb, hba⟩ => ht hba <| h hb
#align upper_closure_min upperClosure_min
-/

#print lowerClosure_min /-
theorem lowerClosure_min (h : s ⊆ t) (ht : IsLowerSet t) : ↑(lowerClosure s) ⊆ t :=
  fun a ⟨b, hb, hab⟩ => ht hab <| h hb
#align lower_closure_min lowerClosure_min
-/

#print IsUpperSet.upperClosure /-
protected theorem IsUpperSet.upperClosure (hs : IsUpperSet s) : ↑(upperClosure s) = s :=
  (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure
#align is_upper_set.upper_closure IsUpperSet.upperClosure
-/

#print IsLowerSet.lowerClosure /-
protected theorem IsLowerSet.lowerClosure (hs : IsLowerSet s) : ↑(lowerClosure s) = s :=
  (lowerClosure_min Subset.rfl hs).antisymm subset_lowerClosure
#align is_lower_set.lower_closure IsLowerSet.lowerClosure
-/

#print UpperSet.upperClosure /-
@[simp]
protected theorem UpperSet.upperClosure (s : UpperSet α) : upperClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.upperClosure
#align upper_set.upper_closure UpperSet.upperClosure
-/

#print LowerSet.lowerClosure /-
@[simp]
protected theorem LowerSet.lowerClosure (s : LowerSet α) : lowerClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.lowerClosure
#align lower_set.lower_closure LowerSet.lowerClosure
-/

#print upperClosure_image /-
@[simp]
theorem upperClosure_image (f : α ≃o β) : upperClosure (f '' s) = UpperSet.map f (upperClosure s) :=
  by
  rw [← f.symm_symm, ← UpperSet.symm_map, f.symm_symm]
  ext
  simp [-UpperSet.symm_map, UpperSet.map, OrderIso.symm, ← f.le_symm_apply]
#align upper_closure_image upperClosure_image
-/

#print lowerClosure_image /-
@[simp]
theorem lowerClosure_image (f : α ≃o β) : lowerClosure (f '' s) = LowerSet.map f (lowerClosure s) :=
  by
  rw [← f.symm_symm, ← LowerSet.symm_map, f.symm_symm]
  ext
  simp [-LowerSet.symm_map, LowerSet.map, OrderIso.symm, ← f.symm_apply_le]
#align lower_closure_image lowerClosure_image
-/

#print UpperSet.iInf_Ici /-
@[simp]
theorem UpperSet.iInf_Ici (s : Set α) : (⨅ a ∈ s, UpperSet.Ici a) = upperClosure s := by ext; simp
#align upper_set.infi_Ici UpperSet.iInf_Ici
-/

#print LowerSet.iSup_Iic /-
@[simp]
theorem LowerSet.iSup_Iic (s : Set α) : (⨆ a ∈ s, LowerSet.Iic a) = lowerClosure s := by ext; simp
#align lower_set.supr_Iic LowerSet.iSup_Iic
-/

#print gc_upperClosure_coe /-
theorem gc_upperClosure_coe :
    GaloisConnection (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) (coe ∘ ofDual) := fun s t =>
  ⟨fun h => subset_upperClosure.trans <| UpperSet.coe_subset_coe.2 h, fun h =>
    upperClosure_min h t.upper⟩
#align gc_upper_closure_coe gc_upperClosure_coe
-/

#print gc_lowerClosure_coe /-
theorem gc_lowerClosure_coe : GaloisConnection (lowerClosure : Set α → LowerSet α) coe := fun s t =>
  ⟨fun h => subset_lowerClosure.trans <| LowerSet.coe_subset_coe.2 h, fun h =>
    lowerClosure_min h t.lower⟩
#align gc_lower_closure_coe gc_lowerClosure_coe
-/

#print giUpperClosureCoe /-
/-- `upper_closure` forms a reversed Galois insertion with the coercion from upper sets to sets. -/
def giUpperClosureCoe :
    GaloisInsertion (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) (coe ∘ ofDual)
    where
  choice s hs := toDual (⟨s, fun a b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
  choice_eq s hs := ofDual.Injective <| SetLike.coe_injective <| subset_upperClosure.antisymm hs
#align gi_upper_closure_coe giUpperClosureCoe
-/

#print giLowerClosureCoe /-
/-- `lower_closure` forms a Galois insertion with the coercion from lower sets to sets. -/
def giLowerClosureCoe : GaloisInsertion (lowerClosure : Set α → LowerSet α) coe
    where
  choice s hs := ⟨s, fun a b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
  choice_eq s hs := SetLike.coe_injective <| subset_lowerClosure.antisymm hs
#align gi_lower_closure_coe giLowerClosureCoe
-/

#print upperClosure_anti /-
theorem upperClosure_anti : Antitone (upperClosure : Set α → UpperSet α) :=
  gc_upperClosure_coe.monotone_l
#align upper_closure_anti upperClosure_anti
-/

#print lowerClosure_mono /-
theorem lowerClosure_mono : Monotone (lowerClosure : Set α → LowerSet α) :=
  gc_lowerClosure_coe.monotone_l
#align lower_closure_mono lowerClosure_mono
-/

#print upperClosure_empty /-
@[simp]
theorem upperClosure_empty : upperClosure (∅ : Set α) = ⊤ := by ext; simp
#align upper_closure_empty upperClosure_empty
-/

#print lowerClosure_empty /-
@[simp]
theorem lowerClosure_empty : lowerClosure (∅ : Set α) = ⊥ := by ext; simp
#align lower_closure_empty lowerClosure_empty
-/

#print upperClosure_singleton /-
@[simp]
theorem upperClosure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.Ici a := by ext; simp
#align upper_closure_singleton upperClosure_singleton
-/

#print lowerClosure_singleton /-
@[simp]
theorem lowerClosure_singleton (a : α) : lowerClosure ({a} : Set α) = LowerSet.Iic a := by ext; simp
#align lower_closure_singleton lowerClosure_singleton
-/

#print upperClosure_univ /-
@[simp]
theorem upperClosure_univ : upperClosure (univ : Set α) = ⊥ :=
  le_bot_iff.1 subset_upperClosure
#align upper_closure_univ upperClosure_univ
-/

#print lowerClosure_univ /-
@[simp]
theorem lowerClosure_univ : lowerClosure (univ : Set α) = ⊤ :=
  top_le_iff.1 subset_lowerClosure
#align lower_closure_univ lowerClosure_univ
-/

#print upperClosure_eq_top_iff /-
@[simp]
theorem upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅ :=
  ⟨fun h => subset_empty_iff.1 <| subset_upperClosure.trans (congr_arg coe h).Subset, by rintro rfl;
    exact upperClosure_empty⟩
#align upper_closure_eq_top_iff upperClosure_eq_top_iff
-/

#print lowerClosure_eq_bot_iff /-
@[simp]
theorem lowerClosure_eq_bot_iff : lowerClosure s = ⊥ ↔ s = ∅ :=
  ⟨fun h => subset_empty_iff.1 <| subset_lowerClosure.trans (congr_arg coe h).Subset, by rintro rfl;
    exact lowerClosure_empty⟩
#align lower_closure_eq_bot_iff lowerClosure_eq_bot_iff
-/

#print upperClosure_union /-
@[simp]
theorem upperClosure_union (s t : Set α) : upperClosure (s ∪ t) = upperClosure s ⊓ upperClosure t :=
  by ext; simp [or_and_right, exists_or]
#align upper_closure_union upperClosure_union
-/

#print lowerClosure_union /-
@[simp]
theorem lowerClosure_union (s t : Set α) : lowerClosure (s ∪ t) = lowerClosure s ⊔ lowerClosure t :=
  by ext; simp [or_and_right, exists_or]
#align lower_closure_union lowerClosure_union
-/

#print upperClosure_iUnion /-
@[simp]
theorem upperClosure_iUnion (f : ι → Set α) : upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i) :=
  by ext; simp [← exists_and_right, @exists_comm α]
#align upper_closure_Union upperClosure_iUnion
-/

#print lowerClosure_iUnion /-
@[simp]
theorem lowerClosure_iUnion (f : ι → Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i) :=
  by ext; simp [← exists_and_right, @exists_comm α]
#align lower_closure_Union lowerClosure_iUnion
-/

#print upperClosure_sUnion /-
@[simp]
theorem upperClosure_sUnion (S : Set (Set α)) : upperClosure (⋃₀ S) = ⨅ s ∈ S, upperClosure s := by
  simp_rw [sUnion_eq_bUnion, upperClosure_iUnion]
#align upper_closure_sUnion upperClosure_sUnion
-/

#print lowerClosure_sUnion /-
@[simp]
theorem lowerClosure_sUnion (S : Set (Set α)) : lowerClosure (⋃₀ S) = ⨆ s ∈ S, lowerClosure s := by
  simp_rw [sUnion_eq_bUnion, lowerClosure_iUnion]
#align lower_closure_sUnion lowerClosure_sUnion
-/

#print Set.OrdConnected.upperClosure_inter_lowerClosure /-
theorem Set.OrdConnected.upperClosure_inter_lowerClosure (h : s.OrdConnected) :
    ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun a ⟨⟨b, hb, hba⟩, c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩
#align set.ord_connected.upper_closure_inter_lower_closure Set.OrdConnected.upperClosure_inter_lowerClosure
-/

#print ordConnected_iff_upperClosure_inter_lowerClosure /-
theorem ordConnected_iff_upperClosure_inter_lowerClosure :
    s.OrdConnected ↔ ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  by
  refine' ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => _⟩
  rw [← h]
  exact (UpperSet.upper _).OrdConnected.inter (LowerSet.lower _).OrdConnected
#align ord_connected_iff_upper_closure_inter_lower_closure ordConnected_iff_upperClosure_inter_lowerClosure
-/

#print upperBounds_lowerClosure /-
@[simp]
theorem upperBounds_lowerClosure : upperBounds (lowerClosure s : Set α) = upperBounds s :=
  (upperBounds_mono_set subset_lowerClosure).antisymm fun a ha b ⟨c, hc, hcb⟩ => hcb.trans <| ha hc
#align upper_bounds_lower_closure upperBounds_lowerClosure
-/

#print lowerBounds_upperClosure /-
@[simp]
theorem lowerBounds_upperClosure : lowerBounds (upperClosure s : Set α) = lowerBounds s :=
  (lowerBounds_mono_set subset_upperClosure).antisymm fun a ha b ⟨c, hc, hcb⟩ => (ha hc).trans hcb
#align lower_bounds_upper_closure lowerBounds_upperClosure
-/

#print bddAbove_lowerClosure /-
@[simp]
theorem bddAbove_lowerClosure : BddAbove (lowerClosure s : Set α) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_lowerClosure]
#align bdd_above_lower_closure bddAbove_lowerClosure
-/

#print bddBelow_upperClosure /-
@[simp]
theorem bddBelow_upperClosure : BddBelow (upperClosure s : Set α) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_upperClosure]
#align bdd_below_upper_closure bddBelow_upperClosure
-/

alias ⟨BddAbove.of_lowerClosure, BddAbove.lowerClosure⟩ := bddAbove_lowerClosure
#align bdd_above.of_lower_closure BddAbove.of_lowerClosure
#align bdd_above.lower_closure BddAbove.lowerClosure

alias ⟨BddBelow.of_upperClosure, BddBelow.upperClosure⟩ := bddBelow_upperClosure
#align bdd_below.of_upper_closure BddBelow.of_upperClosure
#align bdd_below.upper_closure BddBelow.upperClosure

attribute [protected] BddAbove.lowerClosure BddBelow.upperClosure

end closure

/-! ### Product -/


section Preorder

variable [Preorder α] [Preorder β]

section

variable {s : Set α} {t : Set β} {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print IsUpperSet.prod /-
theorem IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ t) :=
  fun a b h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
#align is_upper_set.prod IsUpperSet.prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print IsLowerSet.prod /-
theorem IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ t) :=
  fun a b h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
#align is_lower_set.prod IsLowerSet.prod
-/

end

namespace UpperSet

variable (s s₁ s₂ : UpperSet α) (t t₁ t₂ : UpperSet β) {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod /-
/-- The product of two upper sets as an upper set. -/
def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.Prod t.2⟩
#align upper_set.prod UpperSet.prod
-/

infixr:82 " ×ˢ " => prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.coe_prod /-
@[simp, norm_cast]
theorem coe_prod : (↑(s ×ˢ t) : Set (α × β)) = s ×ˢ t :=
  rfl
#align upper_set.coe_prod UpperSet.coe_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.mem_prod /-
@[simp]
theorem mem_prod {s : UpperSet α} {t : UpperSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl
#align upper_set.mem_prod UpperSet.mem_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.Ici_prod /-
theorem Ici_prod (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2 :=
  rfl
#align upper_set.Ici_prod UpperSet.Ici_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.Ici_prod_Ici /-
@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) :=
  rfl
#align upper_set.Ici_prod_Ici UpperSet.Ici_prod_Ici
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_top /-
@[simp]
theorem prod_top : s ×ˢ (⊤ : UpperSet β) = ⊤ :=
  ext prod_empty
#align upper_set.prod_top UpperSet.prod_top
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.top_prod /-
@[simp]
theorem top_prod : (⊤ : UpperSet α) ×ˢ t = ⊤ :=
  ext empty_prod
#align upper_set.top_prod UpperSet.top_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.bot_prod_bot /-
@[simp]
theorem bot_prod_bot : (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥ :=
  ext univ_prod_univ
#align upper_set.bot_prod_bot UpperSet.bot_prod_bot
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.sup_prod /-
@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext inter_prod
#align upper_set.sup_prod UpperSet.sup_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_sup /-
@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_inter
#align upper_set.prod_sup UpperSet.prod_sup
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.inf_prod /-
@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext union_prod
#align upper_set.inf_prod UpperSet.inf_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_inf /-
@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_union
#align upper_set.prod_inf UpperSet.prod_inf
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_sup_prod /-
theorem prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂) :=
  ext prod_inter_prod
#align upper_set.prod_sup_prod UpperSet.prod_sup_prod
-/

variable {s s₁ s₂ t t₁ t₂}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_mono /-
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  prod_mono
#align upper_set.prod_mono UpperSet.prod_mono
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_mono_left /-
theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  prod_mono_left
#align upper_set.prod_mono_left UpperSet.prod_mono_left
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_mono_right /-
theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  prod_mono_right
#align upper_set.prod_mono_right UpperSet.prod_mono_right
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_self_le_prod_self /-
@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self
#align upper_set.prod_self_le_prod_self UpperSet.prod_self_le_prod_self
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_self_lt_prod_self /-
@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self
#align upper_set.prod_self_lt_prod_self UpperSet.prod_self_lt_prod_self
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_le_prod_iff /-
theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤ :=
  prod_subset_prod_iff.trans <| by simp
#align upper_set.prod_le_prod_iff UpperSet.prod_le_prod_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.prod_eq_top /-
@[simp]
theorem prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤ := by simp_rw [SetLike.ext'_iff];
  exact prod_eq_empty_iff
#align upper_set.prod_eq_top UpperSet.prod_eq_top
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UpperSet.codisjoint_prod /-
@[simp]
theorem codisjoint_prod : Codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Codisjoint s₁ s₂ ∨ Codisjoint t₁ t₂ :=
  by simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]
#align upper_set.codisjoint_prod UpperSet.codisjoint_prod
-/

end UpperSet

namespace LowerSet

variable (s s₁ s₂ : LowerSet α) (t t₁ t₂ : LowerSet β) {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod /-
/-- The product of two lower sets as a lower set. -/
def prod : LowerSet (α × β) :=
  ⟨s ×ˢ t, s.2.Prod t.2⟩
#align lower_set.prod LowerSet.prod
-/

infixr:82 " ×ˢ " => LowerSet.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.coe_prod /-
@[simp, norm_cast]
theorem coe_prod : (↑(s ×ˢ t) : Set (α × β)) = s ×ˢ t :=
  rfl
#align lower_set.coe_prod LowerSet.coe_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.mem_prod /-
@[simp]
theorem mem_prod {s : LowerSet α} {t : LowerSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl
#align lower_set.mem_prod LowerSet.mem_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.Iic_prod /-
theorem Iic_prod (x : α × β) : Iic x = Iic x.1 ×ˢ Iic x.2 :=
  rfl
#align lower_set.Iic_prod LowerSet.Iic_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.Ici_prod_Ici /-
@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl
#align lower_set.Ici_prod_Ici LowerSet.Ici_prod_Ici
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_bot /-
@[simp]
theorem prod_bot : s ×ˢ (⊥ : LowerSet β) = ⊥ :=
  ext prod_empty
#align lower_set.prod_bot LowerSet.prod_bot
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.bot_prod /-
@[simp]
theorem bot_prod : (⊥ : LowerSet α) ×ˢ t = ⊥ :=
  ext empty_prod
#align lower_set.bot_prod LowerSet.bot_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.top_prod_top /-
@[simp]
theorem top_prod_top : (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤ :=
  ext univ_prod_univ
#align lower_set.top_prod_top LowerSet.top_prod_top
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.inf_prod /-
@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext inter_prod
#align lower_set.inf_prod LowerSet.inf_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_inf /-
@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_inter
#align lower_set.prod_inf LowerSet.prod_inf
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.sup_prod /-
@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext union_prod
#align lower_set.sup_prod LowerSet.sup_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_sup /-
@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_union
#align lower_set.prod_sup LowerSet.prod_sup
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_inf_prod /-
theorem prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂) :=
  ext prod_inter_prod
#align lower_set.prod_inf_prod LowerSet.prod_inf_prod
-/

variable {s s₁ s₂ t t₁ t₂}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_mono /-
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  prod_mono
#align lower_set.prod_mono LowerSet.prod_mono
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_mono_left /-
theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  prod_mono_left
#align lower_set.prod_mono_left LowerSet.prod_mono_left
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_mono_right /-
theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  prod_mono_right
#align lower_set.prod_mono_right LowerSet.prod_mono_right
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_self_le_prod_self /-
@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self
#align lower_set.prod_self_le_prod_self LowerSet.prod_self_le_prod_self
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_self_lt_prod_self /-
@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self
#align lower_set.prod_self_lt_prod_self LowerSet.prod_self_lt_prod_self
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_le_prod_iff /-
theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥ :=
  prod_subset_prod_iff.trans <| by simp
#align lower_set.prod_le_prod_iff LowerSet.prod_le_prod_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.prod_eq_bot /-
@[simp]
theorem prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥ := by simp_rw [SetLike.ext'_iff];
  exact prod_eq_empty_iff
#align lower_set.prod_eq_bot LowerSet.prod_eq_bot
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print LowerSet.disjoint_prod /-
@[simp]
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]
#align lower_set.disjoint_prod LowerSet.disjoint_prod
-/

end LowerSet

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print upperClosure_prod /-
@[simp]
theorem upperClosure_prod (s : Set α) (t : Set β) :
    upperClosure (s ×ˢ t) = upperClosure s ×ˢ upperClosure t := by ext;
  simp [Prod.le_def, and_and_and_comm _ (_ ∈ t)]
#align upper_closure_prod upperClosure_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print lowerClosure_prod /-
@[simp]
theorem lowerClosure_prod (s : Set α) (t : Set β) :
    lowerClosure (s ×ˢ t) = lowerClosure s ×ˢ lowerClosure t := by ext;
  simp [Prod.le_def, and_and_and_comm _ (_ ∈ t)]
#align lower_closure_prod lowerClosure_prod
-/

end Preorder

