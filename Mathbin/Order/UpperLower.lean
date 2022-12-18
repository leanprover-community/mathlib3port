/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta

! This file was ported from Lean 3 source module order.upper_lower
! leanprover-community/mathlib commit c5c7e2760814660967bc27f0de95d190a22297f3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Set.Intervals.OrdConnected
import Mathbin.Data.Set.Intervals.OrderIso
import Mathbin.Order.Hom.CompleteLattice

/-!
# Up-sets and down-sets

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

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
def IsUpperSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s
#align is_upper_set IsUpperSet

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
def IsLowerSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s
#align is_lower_set IsLowerSet

theorem is_upper_set_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id
#align is_upper_set_empty is_upper_set_empty

theorem is_lower_set_empty : IsLowerSet (∅ : Set α) := fun _ _ _ => id
#align is_lower_set_empty is_lower_set_empty

theorem is_upper_set_univ : IsUpperSet (univ : Set α) := fun _ _ _ => id
#align is_upper_set_univ is_upper_set_univ

theorem is_lower_set_univ : IsLowerSet (univ : Set α) := fun _ _ _ => id
#align is_lower_set_univ is_lower_set_univ

theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet (sᶜ) := fun a b h hb ha => hb <| hs h ha
#align is_upper_set.compl IsUpperSet.compl

theorem IsLowerSet.compl (hs : IsLowerSet s) : IsUpperSet (sᶜ) := fun a b h hb ha => hb <| hs h ha
#align is_lower_set.compl IsLowerSet.compl

@[simp]
theorem is_upper_set_compl : IsUpperSet (sᶜ) ↔ IsLowerSet s :=
  ⟨fun h => by 
    convert h.compl
    rw [compl_compl], IsLowerSet.compl⟩
#align is_upper_set_compl is_upper_set_compl

@[simp]
theorem is_lower_set_compl : IsLowerSet (sᶜ) ↔ IsUpperSet s :=
  ⟨fun h => by 
    convert h.compl
    rw [compl_compl], IsUpperSet.compl⟩
#align is_lower_set_compl is_lower_set_compl

theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∪ t) :=
  fun a b h => Or.imp (hs h) (ht h)
#align is_upper_set.union IsUpperSet.union

theorem IsLowerSet.union (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∪ t) :=
  fun a b h => Or.imp (hs h) (ht h)
#align is_lower_set.union IsLowerSet.union

theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∩ t) :=
  fun a b h => And.imp (hs h) (ht h)
#align is_upper_set.inter IsUpperSet.inter

theorem IsLowerSet.inter (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∩ t) :=
  fun a b h => And.imp (hs h) (ht h)
#align is_lower_set.inter IsLowerSet.inter

theorem is_upper_set_Union {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) :=
  fun a b h => Exists₂Cat.imp <| forall_range_iff.2 fun i => hf i h
#align is_upper_set_Union is_upper_set_Union

theorem is_lower_set_Union {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋃ i, f i) :=
  fun a b h => Exists₂Cat.imp <| forall_range_iff.2 fun i => hf i h
#align is_lower_set_Union is_lower_set_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem is_upper_set_Union₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋃ (i) (j), f i j) :=
  is_upper_set_Union fun i => is_upper_set_Union <| hf i
#align is_upper_set_Union₂ is_upper_set_Union₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem is_lower_set_Union₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) :
    IsLowerSet (⋃ (i) (j), f i j) :=
  is_lower_set_Union fun i => is_lower_set_Union <| hf i
#align is_lower_set_Union₂ is_lower_set_Union₂

theorem is_upper_set_sUnion {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋃₀S) :=
  fun a b h => Exists₂Cat.imp fun s hs => hf s hs h
#align is_upper_set_sUnion is_upper_set_sUnion

theorem is_lower_set_sUnion {S : Set (Set α)} (hf : ∀ s ∈ S, IsLowerSet s) : IsLowerSet (⋃₀S) :=
  fun a b h => Exists₂Cat.imp fun s hs => hf s hs h
#align is_lower_set_sUnion is_lower_set_sUnion

theorem is_upper_set_Inter {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) :=
  fun a b h => forall₂_imp <| forall_range_iff.2 fun i => hf i h
#align is_upper_set_Inter is_upper_set_Inter

theorem is_lower_set_Inter {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋂ i, f i) :=
  fun a b h => forall₂_imp <| forall_range_iff.2 fun i => hf i h
#align is_lower_set_Inter is_lower_set_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem is_upper_set_Inter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) :
    IsUpperSet (⋂ (i) (j), f i j) :=
  is_upper_set_Inter fun i => is_upper_set_Inter <| hf i
#align is_upper_set_Inter₂ is_upper_set_Inter₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem is_lower_set_Inter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) :
    IsLowerSet (⋂ (i) (j), f i j) :=
  is_lower_set_Inter fun i => is_lower_set_Inter <| hf i
#align is_lower_set_Inter₂ is_lower_set_Inter₂

theorem is_upper_set_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsUpperSet s) : IsUpperSet (⋂₀ S) :=
  fun a b h => forall₂_imp fun s hs => hf s hs h
#align is_upper_set_sInter is_upper_set_sInter

theorem is_lower_set_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsLowerSet s) : IsLowerSet (⋂₀ S) :=
  fun a b h => forall₂_imp fun s hs => hf s hs h
#align is_lower_set_sInter is_lower_set_sInter

@[simp]
theorem is_lower_set_preimage_of_dual_iff : IsLowerSet (of_dual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl
#align is_lower_set_preimage_of_dual_iff is_lower_set_preimage_of_dual_iff

@[simp]
theorem is_upper_set_preimage_of_dual_iff : IsUpperSet (of_dual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl
#align is_upper_set_preimage_of_dual_iff is_upper_set_preimage_of_dual_iff

@[simp]
theorem is_lower_set_preimage_to_dual_iff {s : Set αᵒᵈ} :
    IsLowerSet (to_dual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl
#align is_lower_set_preimage_to_dual_iff is_lower_set_preimage_to_dual_iff

@[simp]
theorem is_upper_set_preimage_to_dual_iff {s : Set αᵒᵈ} :
    IsUpperSet (to_dual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl
#align is_upper_set_preimage_to_dual_iff is_upper_set_preimage_to_dual_iff

alias is_lower_set_preimage_of_dual_iff ↔ _ IsUpperSet.of_dual

alias is_upper_set_preimage_of_dual_iff ↔ _ IsLowerSet.of_dual

alias is_lower_set_preimage_to_dual_iff ↔ _ IsUpperSet.to_dual

alias is_upper_set_preimage_to_dual_iff ↔ _ IsLowerSet.to_dual

end LE

section Preorder

variable [Preorder α] [Preorder β] {s : Set α} {p : α → Prop} (a : α)

theorem is_upper_set_Ici : IsUpperSet (ici a) := fun _ _ => ge_trans
#align is_upper_set_Ici is_upper_set_Ici

theorem is_lower_set_Iic : IsLowerSet (iic a) := fun _ _ => le_trans
#align is_lower_set_Iic is_lower_set_Iic

theorem is_upper_set_Ioi : IsUpperSet (ioi a) := fun _ _ => flip lt_of_lt_of_le
#align is_upper_set_Ioi is_upper_set_Ioi

theorem is_lower_set_Iio : IsLowerSet (iio a) := fun _ _ => lt_of_le_of_lt
#align is_lower_set_Iio is_lower_set_Iio

theorem is_upper_set_iff_Ici_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → ici a ⊆ s := by
  simp [IsUpperSet, subset_def, @forall_swap (_ ∈ s)]
#align is_upper_set_iff_Ici_subset is_upper_set_iff_Ici_subset

theorem is_lower_set_iff_Iic_subset : IsLowerSet s ↔ ∀ ⦃a⦄, a ∈ s → iic a ⊆ s := by
  simp [IsLowerSet, subset_def, @forall_swap (_ ∈ s)]
#align is_lower_set_iff_Iic_subset is_lower_set_iff_Iic_subset

alias is_upper_set_iff_Ici_subset ↔ IsUpperSet.Ici_subset _

alias is_lower_set_iff_Iic_subset ↔ IsLowerSet.Iic_subset _

theorem IsUpperSet.ord_connected (h : IsUpperSet s) : s.OrdConnected :=
  ⟨fun a ha b _ => Icc_subset_Ici_self.trans <| h.Ici_subset ha⟩
#align is_upper_set.ord_connected IsUpperSet.ord_connected

theorem IsLowerSet.ord_connected (h : IsLowerSet s) : s.OrdConnected :=
  ⟨fun a _ b hb => Icc_subset_Iic_self.trans <| h.Iic_subset hb⟩
#align is_lower_set.ord_connected IsLowerSet.ord_connected

theorem IsUpperSet.preimage (hs : IsUpperSet s) {f : β → α} (hf : Monotone f) :
    IsUpperSet (f ⁻¹' s : Set β) := fun x y hxy => hs <| hf hxy
#align is_upper_set.preimage IsUpperSet.preimage

theorem IsLowerSet.preimage (hs : IsLowerSet s) {f : β → α} (hf : Monotone f) :
    IsLowerSet (f ⁻¹' s : Set β) := fun x y hxy => hs <| hf hxy
#align is_lower_set.preimage IsLowerSet.preimage

theorem IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : IsUpperSet (f '' s : Set β) := by
  change IsUpperSet ((f : α ≃ β) '' s)
  rw [Set.image_equiv_eq_preimage_symm]
  exact hs.preimage f.symm.monotone
#align is_upper_set.image IsUpperSet.image

theorem IsLowerSet.image (hs : IsLowerSet s) (f : α ≃o β) : IsLowerSet (f '' s : Set β) := by
  change IsLowerSet ((f : α ≃ β) '' s)
  rw [Set.image_equiv_eq_preimage_symm]
  exact hs.preimage f.symm.monotone
#align is_lower_set.image IsLowerSet.image

@[simp]
theorem Set.monotone_mem : Monotone (· ∈ s) ↔ IsUpperSet s :=
  Iff.rfl
#align set.monotone_mem Set.monotone_mem

@[simp]
theorem Set.antitone_mem : Antitone (· ∈ s) ↔ IsLowerSet s :=
  forall_swap
#align set.antitone_mem Set.antitone_mem

@[simp]
theorem is_upper_set_set_of : IsUpperSet { a | p a } ↔ Monotone p :=
  Iff.rfl
#align is_upper_set_set_of is_upper_set_set_of

@[simp]
theorem is_lower_set_set_of : IsLowerSet { a | p a } ↔ Antitone p :=
  forall_swap
#align is_lower_set_set_of is_lower_set_set_of

section OrderTop

variable [OrderTop α]

theorem IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun a => hs le_top h, fun h => h.symm ▸ mem_univ _⟩
#align is_lower_set.top_mem IsLowerSet.top_mem

theorem IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨a, ha⟩ => hs le_top ha⟩
#align is_upper_set.top_mem IsUpperSet.top_mem

theorem IsUpperSet.not_top_mem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.Not.trans not_nonempty_iff_eq_empty
#align is_upper_set.not_top_mem IsUpperSet.not_top_mem

end OrderTop

section OrderBot

variable [OrderBot α]

theorem IsUpperSet.bot_mem (hs : IsUpperSet s) : ⊥ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun a => hs bot_le h, fun h => h.symm ▸ mem_univ _⟩
#align is_upper_set.bot_mem IsUpperSet.bot_mem

theorem IsLowerSet.bot_mem (hs : IsLowerSet s) : ⊥ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨a, ha⟩ => hs bot_le ha⟩
#align is_lower_set.bot_mem IsLowerSet.bot_mem

theorem IsLowerSet.not_bot_mem (hs : IsLowerSet s) : ⊥ ∉ s ↔ s = ∅ :=
  hs.bot_mem.Not.trans not_nonempty_iff_eq_empty
#align is_lower_set.not_bot_mem IsLowerSet.not_bot_mem

end OrderBot

section NoMaxOrder

variable [NoMaxOrder α] (a)

theorem IsUpperSet.not_bdd_above (hs : IsUpperSet s) : s.Nonempty → ¬BddAbove s := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_gt b
  exact hc.not_le (hb <| hs ((hb ha).trans hc.le) ha)
#align is_upper_set.not_bdd_above IsUpperSet.not_bdd_above

theorem not_bdd_above_Ici : ¬BddAbove (ici a) :=
  (is_upper_set_Ici _).not_bdd_above nonempty_Ici
#align not_bdd_above_Ici not_bdd_above_Ici

theorem not_bdd_above_Ioi : ¬BddAbove (ioi a) :=
  (is_upper_set_Ioi _).not_bdd_above nonempty_Ioi
#align not_bdd_above_Ioi not_bdd_above_Ioi

end NoMaxOrder

section NoMinOrder

variable [NoMinOrder α] (a)

theorem IsLowerSet.not_bdd_below (hs : IsLowerSet s) : s.Nonempty → ¬BddBelow s := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hc⟩ := exists_lt b
  exact hc.not_le (hb <| hs (hc.le.trans <| hb ha) ha)
#align is_lower_set.not_bdd_below IsLowerSet.not_bdd_below

theorem not_bdd_below_Iic : ¬BddBelow (iic a) :=
  (is_lower_set_Iic _).not_bdd_below nonempty_Iic
#align not_bdd_below_Iic not_bdd_below_Iic

theorem not_bdd_below_Iio : ¬BddBelow (iio a) :=
  (is_lower_set_Iio _).not_bdd_below nonempty_Iio
#align not_bdd_below_Iio not_bdd_below_Iio

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α}

theorem is_upper_set_iff_forall_lt : IsUpperSet s ↔ ∀ ⦃a b : α⦄, a < b → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]
#align is_upper_set_iff_forall_lt is_upper_set_iff_forall_lt

theorem is_lower_set_iff_forall_lt : IsLowerSet s ↔ ∀ ⦃a b : α⦄, b < a → a ∈ s → b ∈ s :=
  forall_congr' fun a => by simp [le_iff_eq_or_lt, or_imp, forall_and]
#align is_lower_set_iff_forall_lt is_lower_set_iff_forall_lt

theorem is_upper_set_iff_Ioi_subset : IsUpperSet s ↔ ∀ ⦃a⦄, a ∈ s → ioi a ⊆ s := by
  simp [is_upper_set_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]
#align is_upper_set_iff_Ioi_subset is_upper_set_iff_Ioi_subset

theorem is_lower_set_iff_Iio_subset : IsLowerSet s ↔ ∀ ⦃a⦄, a ∈ s → iio a ⊆ s := by
  simp [is_lower_set_iff_forall_lt, subset_def, @forall_swap (_ ∈ s)]
#align is_lower_set_iff_Iio_subset is_lower_set_iff_Iio_subset

alias is_upper_set_iff_Ioi_subset ↔ IsUpperSet.Ioi_subset _

alias is_lower_set_iff_Iio_subset ↔ IsLowerSet.Iio_subset _

end PartialOrder

/-! ### Bundled upper/lower sets -/


section LE

variable [LE α]

/-- The type of upper sets of an order. -/
structure UpperSet (α : Type _) [LE α] where
  carrier : Set α
  upper' : IsUpperSet carrier
#align upper_set UpperSet

/-- The type of lower sets of an order. -/
structure LowerSet (α : Type _) [LE α] where
  carrier : Set α
  lower' : IsLowerSet carrier
#align lower_set LowerSet

namespace UpperSet

instance : SetLike (UpperSet α) α where 
  coe := UpperSet.carrier
  coe_injective' s t h := by 
    cases s
    cases t
    congr

@[ext]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'
#align upper_set.ext UpperSet.ext

@[simp]
theorem carrier_eq_coe (s : UpperSet α) : s.carrier = s :=
  rfl
#align upper_set.carrier_eq_coe UpperSet.carrier_eq_coe

protected theorem upper (s : UpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'
#align upper_set.upper UpperSet.upper

@[simp]
theorem mem_mk (carrier : Set α) (upper') {a : α} : a ∈ mk carrier upper' ↔ a ∈ carrier :=
  Iff.rfl
#align upper_set.mem_mk UpperSet.mem_mk

end UpperSet

namespace LowerSet

instance : SetLike (LowerSet α) α where 
  coe := LowerSet.carrier
  coe_injective' s t h := by 
    cases s
    cases t
    congr

@[ext]
theorem ext {s t : LowerSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'
#align lower_set.ext LowerSet.ext

@[simp]
theorem carrier_eq_coe (s : LowerSet α) : s.carrier = s :=
  rfl
#align lower_set.carrier_eq_coe LowerSet.carrier_eq_coe

protected theorem lower (s : LowerSet α) : IsLowerSet (s : Set α) :=
  s.lower'
#align lower_set.lower LowerSet.lower

@[simp]
theorem mem_mk (carrier : Set α) (lower') {a : α} : a ∈ mk carrier lower' ↔ a ∈ carrier :=
  Iff.rfl
#align lower_set.mem_mk LowerSet.mem_mk

end LowerSet

/-! #### Order -/


namespace UpperSet

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

instance : HasSup (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

instance : HasInf (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

instance : Top (UpperSet α) :=
  ⟨⟨∅, is_upper_set_empty⟩⟩

instance : Bot (UpperSet α) :=
  ⟨⟨univ, is_upper_set_univ⟩⟩

instance : HasSup (UpperSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, is_upper_set_Inter₂ fun s _ => s.upper⟩⟩

instance : HasInf (UpperSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, is_upper_set_Union₂ fun s _ => s.upper⟩⟩

instance : CompleteDistribLattice (UpperSet α) :=
  (toDual.Injective.comp <| SetLike.coe_injective).CompleteDistribLattice _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ t ≤ s :=
  Iff.rfl
#align upper_set.coe_subset_coe UpperSet.coe_subset_coe

@[simp, norm_cast]
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl
#align upper_set.coe_top UpperSet.coe_top

@[simp, norm_cast]
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl
#align upper_set.coe_bot UpperSet.coe_bot

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊥ := by simp [SetLike.ext'_iff]
#align upper_set.coe_eq_univ UpperSet.coe_eq_univ

@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤ := by simp [SetLike.ext'_iff]
#align upper_set.coe_eq_empty UpperSet.coe_eq_empty

@[simp, norm_cast]
theorem coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = s ∩ t :=
  rfl
#align upper_set.coe_sup UpperSet.coe_sup

@[simp, norm_cast]
theorem coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = s ∪ t :=
  rfl
#align upper_set.coe_inf UpperSet.coe_inf

@[simp, norm_cast]
theorem coe_Sup (S : Set (UpperSet α)) : (↑(sup S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl
#align upper_set.coe_Sup UpperSet.coe_Sup

@[simp, norm_cast]
theorem coe_Inf (S : Set (UpperSet α)) : (↑(inf S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl
#align upper_set.coe_Inf UpperSet.coe_Inf

@[simp, norm_cast]
theorem coe_supr (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by simp [supr]
#align upper_set.coe_supr UpperSet.coe_supr

@[simp, norm_cast]
theorem coe_infi (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [infi]
#align upper_set.coe_infi UpperSet.coe_infi

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_supr₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j :=
  by simp_rw [coe_supr]
#align upper_set.coe_supr₂ UpperSet.coe_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_infi₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j :=
  by simp_rw [coe_infi]
#align upper_set.coe_infi₂ UpperSet.coe_infi₂

@[simp]
theorem not_mem_top : a ∉ (⊤ : UpperSet α) :=
  id
#align upper_set.not_mem_top UpperSet.not_mem_top

@[simp]
theorem mem_bot : a ∈ (⊥ : UpperSet α) :=
  trivial
#align upper_set.mem_bot UpperSet.mem_bot

@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl
#align upper_set.mem_sup_iff UpperSet.mem_sup_iff

@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl
#align upper_set.mem_inf_iff UpperSet.mem_inf_iff

@[simp]
theorem mem_Sup_iff : a ∈ sup S ↔ ∀ s ∈ S, a ∈ s :=
  mem_Inter₂
#align upper_set.mem_Sup_iff UpperSet.mem_Sup_iff

@[simp]
theorem mem_Inf_iff : a ∈ inf S ↔ ∃ s ∈ S, a ∈ s :=
  mem_Union₂
#align upper_set.mem_Inf_iff UpperSet.mem_Inf_iff

@[simp]
theorem mem_supr_iff {f : ι → UpperSet α} : (a ∈ ⨆ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_supr]
  exact mem_Inter
#align upper_set.mem_supr_iff UpperSet.mem_supr_iff

@[simp]
theorem mem_infi_iff {f : ι → UpperSet α} : (a ∈ ⨅ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_infi]
  exact mem_Union
#align upper_set.mem_infi_iff UpperSet.mem_infi_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem mem_supr₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_supr_iff]
#align upper_set.mem_supr₂_iff UpperSet.mem_supr₂_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem mem_infi₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_infi_iff]
#align upper_set.mem_infi₂_iff UpperSet.mem_infi₂_iff

@[simp, norm_cast]
theorem codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]
#align upper_set.codisjoint_coe UpperSet.codisjoint_coe

end UpperSet

namespace LowerSet

variable {S : Set (LowerSet α)} {s t : LowerSet α} {a : α}

instance : HasSup (LowerSet α) :=
  ⟨fun s t => ⟨s ∪ t, fun a b h => Or.imp (s.lower h) (t.lower h)⟩⟩

instance : HasInf (LowerSet α) :=
  ⟨fun s t => ⟨s ∩ t, fun a b h => And.imp (s.lower h) (t.lower h)⟩⟩

instance : Top (LowerSet α) :=
  ⟨⟨univ, fun a b h => id⟩⟩

instance : Bot (LowerSet α) :=
  ⟨⟨∅, fun a b h => id⟩⟩

instance : HasSup (LowerSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, is_lower_set_Union₂ fun s _ => s.lower⟩⟩

instance : HasInf (LowerSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, is_lower_set_Inter₂ fun s _ => s.lower⟩⟩

instance : CompleteDistribLattice (LowerSet α) :=
  SetLike.coe_injective.CompleteDistribLattice _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl rfl

instance : Inhabited (LowerSet α) :=
  ⟨⊥⟩

@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  Iff.rfl
#align lower_set.coe_subset_coe LowerSet.coe_subset_coe

@[simp, norm_cast]
theorem coe_top : ((⊤ : LowerSet α) : Set α) = univ :=
  rfl
#align lower_set.coe_top LowerSet.coe_top

@[simp, norm_cast]
theorem coe_bot : ((⊥ : LowerSet α) : Set α) = ∅ :=
  rfl
#align lower_set.coe_bot LowerSet.coe_bot

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊤ := by simp [SetLike.ext'_iff]
#align lower_set.coe_eq_univ LowerSet.coe_eq_univ

@[simp, norm_cast]
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊥ := by simp [SetLike.ext'_iff]
#align lower_set.coe_eq_empty LowerSet.coe_eq_empty

@[simp, norm_cast]
theorem coe_sup (s t : LowerSet α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align lower_set.coe_sup LowerSet.coe_sup

@[simp, norm_cast]
theorem coe_inf (s t : LowerSet α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align lower_set.coe_inf LowerSet.coe_inf

@[simp, norm_cast]
theorem coe_Sup (S : Set (LowerSet α)) : (↑(sup S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl
#align lower_set.coe_Sup LowerSet.coe_Sup

@[simp, norm_cast]
theorem coe_Inf (S : Set (LowerSet α)) : (↑(inf S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl
#align lower_set.coe_Inf LowerSet.coe_Inf

@[simp, norm_cast]
theorem coe_supr (f : ι → LowerSet α) : (↑(⨆ i, f i) : Set α) = ⋃ i, f i := by
  simp_rw [supr, coe_Sup, mem_range, Union_exists, Union_Union_eq']
#align lower_set.coe_supr LowerSet.coe_supr

@[simp, norm_cast]
theorem coe_infi (f : ι → LowerSet α) : (↑(⨅ i, f i) : Set α) = ⋂ i, f i := by
  simp_rw [infi, coe_Inf, mem_range, Inter_exists, Inter_Inter_eq']
#align lower_set.coe_infi LowerSet.coe_infi

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_supr₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j :=
  by simp_rw [coe_supr]
#align lower_set.coe_supr₂ LowerSet.coe_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_infi₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j :=
  by simp_rw [coe_infi]
#align lower_set.coe_infi₂ LowerSet.coe_infi₂

@[simp]
theorem mem_top : a ∈ (⊤ : LowerSet α) :=
  trivial
#align lower_set.mem_top LowerSet.mem_top

@[simp]
theorem not_mem_bot : a ∉ (⊥ : LowerSet α) :=
  id
#align lower_set.not_mem_bot LowerSet.not_mem_bot

@[simp]
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl
#align lower_set.mem_sup_iff LowerSet.mem_sup_iff

@[simp]
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl
#align lower_set.mem_inf_iff LowerSet.mem_inf_iff

@[simp]
theorem mem_Sup_iff : a ∈ sup S ↔ ∃ s ∈ S, a ∈ s :=
  mem_Union₂
#align lower_set.mem_Sup_iff LowerSet.mem_Sup_iff

@[simp]
theorem mem_Inf_iff : a ∈ inf S ↔ ∀ s ∈ S, a ∈ s :=
  mem_Inter₂
#align lower_set.mem_Inf_iff LowerSet.mem_Inf_iff

@[simp]
theorem mem_supr_iff {f : ι → LowerSet α} : (a ∈ ⨆ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_supr]
  exact mem_Union
#align lower_set.mem_supr_iff LowerSet.mem_supr_iff

@[simp]
theorem mem_infi_iff {f : ι → LowerSet α} : (a ∈ ⨅ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_infi]
  exact mem_Inter
#align lower_set.mem_infi_iff LowerSet.mem_infi_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem mem_supr₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_supr_iff]
#align lower_set.mem_supr₂_iff LowerSet.mem_supr₂_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem mem_infi₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_infi_iff]
#align lower_set.mem_infi₂_iff LowerSet.mem_infi₂_iff

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, SetLike.ext'_iff]
#align lower_set.disjoint_coe LowerSet.disjoint_coe

end LowerSet

/-! #### Complement -/


/-- The complement of a lower set as an upper set. -/
def UpperSet.compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩
#align upper_set.compl UpperSet.compl

/-- The complement of a lower set as an upper set. -/
def LowerSet.compl (s : LowerSet α) : UpperSet α :=
  ⟨sᶜ, s.lower.compl⟩
#align lower_set.compl LowerSet.compl

namespace UpperSet

variable {s t : UpperSet α} {a : α}

@[simp]
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = sᶜ :=
  rfl
#align upper_set.coe_compl UpperSet.coe_compl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl
#align upper_set.mem_compl_iff UpperSet.mem_compl_iff

@[simp]
theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
  UpperSet.ext <| compl_compl _
#align upper_set.compl_compl UpperSet.compl_compl

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl
#align upper_set.compl_le_compl UpperSet.compl_le_compl

@[simp]
protected theorem compl_sup (s t : UpperSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  LowerSet.ext compl_inf
#align upper_set.compl_sup UpperSet.compl_sup

@[simp]
protected theorem compl_inf (s t : UpperSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  LowerSet.ext compl_sup
#align upper_set.compl_inf UpperSet.compl_inf

@[simp]
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty
#align upper_set.compl_top UpperSet.compl_top

@[simp]
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ
#align upper_set.compl_bot UpperSet.compl_bot

@[simp]
protected theorem compl_Sup (S : Set (UpperSet α)) : (sup S).compl = ⨆ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_Sup, compl_Inter₂, LowerSet.coe_supr₂]
#align upper_set.compl_Sup UpperSet.compl_Sup

@[simp]
protected theorem compl_Inf (S : Set (UpperSet α)) : (inf S).compl = ⨅ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_Inf, compl_Union₂, LowerSet.coe_infi₂]
#align upper_set.compl_Inf UpperSet.compl_Inf

@[simp]
protected theorem compl_supr (f : ι → UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_supr, compl_Inter, LowerSet.coe_supr]
#align upper_set.compl_supr UpperSet.compl_supr

@[simp]
protected theorem compl_infi (f : ι → UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_infi, compl_Union, LowerSet.coe_infi]
#align upper_set.compl_infi UpperSet.compl_infi

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem compl_supr₂ (f : ∀ i, κ i → UpperSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [UpperSet.compl_supr]
#align upper_set.compl_supr₂ UpperSet.compl_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem compl_infi₂ (f : ∀ i, κ i → UpperSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [UpperSet.compl_infi]
#align upper_set.compl_infi₂ UpperSet.compl_infi₂

end UpperSet

namespace LowerSet

variable {s t : LowerSet α} {a : α}

@[simp]
theorem coe_compl (s : LowerSet α) : (s.compl : Set α) = sᶜ :=
  rfl
#align lower_set.coe_compl LowerSet.coe_compl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl
#align lower_set.mem_compl_iff LowerSet.mem_compl_iff

@[simp]
theorem compl_compl (s : LowerSet α) : s.compl.compl = s :=
  LowerSet.ext <| compl_compl _
#align lower_set.compl_compl LowerSet.compl_compl

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl
#align lower_set.compl_le_compl LowerSet.compl_le_compl

protected theorem compl_sup (s t : LowerSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  UpperSet.ext compl_sup
#align lower_set.compl_sup LowerSet.compl_sup

protected theorem compl_inf (s t : LowerSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  UpperSet.ext compl_inf
#align lower_set.compl_inf LowerSet.compl_inf

protected theorem compl_top : (⊤ : LowerSet α).compl = ⊤ :=
  UpperSet.ext compl_univ
#align lower_set.compl_top LowerSet.compl_top

protected theorem compl_bot : (⊥ : LowerSet α).compl = ⊥ :=
  UpperSet.ext compl_empty
#align lower_set.compl_bot LowerSet.compl_bot

protected theorem compl_Sup (S : Set (LowerSet α)) : (sup S).compl = ⨆ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_Sup, compl_Union₂, UpperSet.coe_supr₂]
#align lower_set.compl_Sup LowerSet.compl_Sup

protected theorem compl_Inf (S : Set (LowerSet α)) : (inf S).compl = ⨅ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by simp only [coe_compl, coe_Inf, compl_Inter₂, UpperSet.coe_infi₂]
#align lower_set.compl_Inf LowerSet.compl_Inf

protected theorem compl_supr (f : ι → LowerSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_supr, compl_Union, UpperSet.coe_supr]
#align lower_set.compl_supr LowerSet.compl_supr

protected theorem compl_infi (f : ι → LowerSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  UpperSet.ext <| by simp only [coe_compl, coe_infi, compl_Inter, UpperSet.coe_infi]
#align lower_set.compl_infi LowerSet.compl_infi

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem compl_supr₂ (f : ∀ i, κ i → LowerSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_supr]
#align lower_set.compl_supr₂ LowerSet.compl_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem compl_infi₂ (f : ∀ i, κ i → LowerSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp_rw [LowerSet.compl_infi]
#align lower_set.compl_infi₂ LowerSet.compl_infi₂

end LowerSet

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
def upperSetIsoLowerSet :
    UpperSet α ≃o LowerSet α where 
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' _ _ := UpperSet.compl_le_compl
#align upper_set_iso_lower_set upperSetIsoLowerSet

end LE

/-! #### Map -/


section

variable [Preorder α] [Preorder β] [Preorder γ]

namespace UpperSet

variable {f : α ≃o β} {s t : UpperSet α} {a : α} {b : β}

/-- An order isomorphism of preorders induces an order isomorphism of their upper sets. -/
def map (f : α ≃o β) :
    UpperSet α ≃o UpperSet
        β where 
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.Preimage f.Monotone⟩
  left_inv _ := ext <| f.preimage_image _
  right_inv _ := ext <| f.image_preimage _
  map_rel_iff' s t := image_subset_image_iff f.Injective
#align upper_set.map UpperSet.map

@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  (FunLike.ext _ _) fun s => ext <| Set.preimage_equiv_eq_image_symm _ _
#align upper_set.symm_map UpperSet.symm_map

@[simp]
theorem mem_map : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl
#align upper_set.mem_map UpperSet.mem_map

@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp
#align upper_set.map_refl UpperSet.map_refl

@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp
#align upper_set.map_map UpperSet.map_map

variable (f s t)

@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl
#align upper_set.coe_map UpperSet.coe_map

@[simp]
protected theorem map_sup : map f (s ⊔ t) = map f s ⊔ map f t :=
  ext <| image_inter f.Injective
#align upper_set.map_sup UpperSet.map_sup

@[simp]
protected theorem map_inf : map f (s ⊓ t) = map f s ⊓ map f t :=
  ext <| image_union _ _ _
#align upper_set.map_inf UpperSet.map_inf

@[simp]
protected theorem map_top : map f ⊤ = ⊤ :=
  ext <| image_empty _
#align upper_set.map_top UpperSet.map_top

@[simp]
protected theorem map_bot : map f ⊥ = ⊥ :=
  ext <| image_univ_of_surjective f.Surjective
#align upper_set.map_bot UpperSet.map_bot

@[simp]
protected theorem map_Sup (S : Set (UpperSet α)) : map f (sup S) = ⨆ s ∈ S, map f s :=
  ext <| by 
    push_cast
    exact image_Inter₂ f.bijective _
#align upper_set.map_Sup UpperSet.map_Sup

@[simp]
protected theorem map_Inf (S : Set (UpperSet α)) : map f (inf S) = ⨅ s ∈ S, map f s :=
  ext <| by 
    push_cast
    exact image_Union₂ _ _
#align upper_set.map_Inf UpperSet.map_Inf

@[simp]
protected theorem map_supr (g : ι → UpperSet α) : map f (⨆ i, g i) = ⨆ i, map f (g i) :=
  ext <| by 
    push_cast
    exact image_Inter f.bijective _
#align upper_set.map_supr UpperSet.map_supr

@[simp]
protected theorem map_infi (g : ι → UpperSet α) : map f (⨅ i, g i) = ⨅ i, map f (g i) :=
  ext <| by 
    push_cast
    exact image_Union
#align upper_set.map_infi UpperSet.map_infi

end UpperSet

namespace LowerSet

variable {f : α ≃o β} {s t : LowerSet α} {a : α} {b : β}

/-- An order isomorphism of preorders induces an order isomorphism of their lower sets. -/
def map (f : α ≃o β) :
    LowerSet α ≃o LowerSet
        β where 
  toFun s := ⟨f '' s, s.lower.image f⟩
  invFun t := ⟨f ⁻¹' t, t.lower.Preimage f.Monotone⟩
  left_inv _ := SetLike.coe_injective <| f.preimage_image _
  right_inv _ := SetLike.coe_injective <| f.image_preimage _
  map_rel_iff' s t := image_subset_image_iff f.Injective
#align lower_set.map LowerSet.map

@[simp]
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm :=
  (FunLike.ext _ _) fun s => SetLike.coe_injective <| Set.preimage_equiv_eq_image_symm _ _
#align lower_set.symm_map LowerSet.symm_map

@[simp]
theorem mem_map {f : α ≃o β} {b : β} : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl
#align lower_set.mem_map LowerSet.mem_map

@[simp]
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp
#align lower_set.map_refl LowerSet.map_refl

@[simp]
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp
#align lower_set.map_map LowerSet.map_map

variable (f s t)

@[simp, norm_cast]
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl
#align lower_set.coe_map LowerSet.coe_map

@[simp]
protected theorem map_sup : map f (s ⊔ t) = map f s ⊔ map f t :=
  ext <| image_union _ _ _
#align lower_set.map_sup LowerSet.map_sup

@[simp]
protected theorem map_inf : map f (s ⊓ t) = map f s ⊓ map f t :=
  ext <| image_inter f.Injective
#align lower_set.map_inf LowerSet.map_inf

@[simp]
protected theorem map_top : map f ⊤ = ⊤ :=
  ext <| image_univ_of_surjective f.Surjective
#align lower_set.map_top LowerSet.map_top

@[simp]
protected theorem map_bot : map f ⊥ = ⊥ :=
  ext <| image_empty _
#align lower_set.map_bot LowerSet.map_bot

@[simp]
protected theorem map_Sup (S : Set (LowerSet α)) : map f (sup S) = ⨆ s ∈ S, map f s :=
  ext <| by 
    push_cast
    exact image_Union₂ _ _
#align lower_set.map_Sup LowerSet.map_Sup

protected theorem map_Inf (S : Set (LowerSet α)) : map f (inf S) = ⨅ s ∈ S, map f s :=
  ext <| by 
    push_cast
    exact image_Inter₂ f.bijective _
#align lower_set.map_Inf LowerSet.map_Inf

protected theorem map_supr (g : ι → LowerSet α) : map f (⨆ i, g i) = ⨆ i, map f (g i) :=
  ext <| by 
    push_cast
    exact image_Union
#align lower_set.map_supr LowerSet.map_supr

protected theorem map_infi (g : ι → LowerSet α) : map f (⨅ i, g i) = ⨅ i, map f (g i) :=
  ext <| by 
    push_cast
    exact image_Inter f.bijective _
#align lower_set.map_infi LowerSet.map_infi

end LowerSet

namespace UpperSet

@[simp]
theorem compl_map (f : α ≃o β) (s : UpperSet α) : (map f s).compl = LowerSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.Bijective).symm
#align upper_set.compl_map UpperSet.compl_map

end UpperSet

namespace LowerSet

@[simp]
theorem compl_map (f : α ≃o β) (s : LowerSet α) : (map f s).compl = UpperSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.Bijective).symm
#align lower_set.compl_map LowerSet.compl_map

end LowerSet

end

/-! #### Principal sets -/


namespace UpperSet

section Preorder

variable [Preorder α] [Preorder β] {s : UpperSet α} {a b : α}

/-- The smallest upper set containing a given element. -/
def ici (a : α) : UpperSet α :=
  ⟨ici a, is_upper_set_Ici a⟩
#align upper_set.Ici UpperSet.ici

/-- The smallest upper set containing a given element. -/
def ioi (a : α) : UpperSet α :=
  ⟨ioi a, is_upper_set_Ioi a⟩
#align upper_set.Ioi UpperSet.ioi

@[simp]
theorem coe_Ici (a : α) : ↑(ici a) = Set.ici a :=
  rfl
#align upper_set.coe_Ici UpperSet.coe_Ici

@[simp]
theorem coe_Ioi (a : α) : ↑(ioi a) = Set.ioi a :=
  rfl
#align upper_set.coe_Ioi UpperSet.coe_Ioi

@[simp]
theorem mem_Ici_iff : b ∈ ici a ↔ a ≤ b :=
  Iff.rfl
#align upper_set.mem_Ici_iff UpperSet.mem_Ici_iff

@[simp]
theorem mem_Ioi_iff : b ∈ ioi a ↔ a < b :=
  Iff.rfl
#align upper_set.mem_Ioi_iff UpperSet.mem_Ioi_iff

@[simp]
theorem map_Ici (f : α ≃o β) (a : α) : map f (ici a) = ici (f a) := by
  ext
  simp
#align upper_set.map_Ici UpperSet.map_Ici

@[simp]
theorem map_Ioi (f : α ≃o β) (a : α) : map f (ioi a) = ioi (f a) := by
  ext
  simp
#align upper_set.map_Ioi UpperSet.map_Ioi

theorem Ici_le_Ioi (a : α) : ici a ≤ ioi a :=
  Ioi_subset_Ici_self
#align upper_set.Ici_le_Ioi UpperSet.Ici_le_Ioi

@[simp]
theorem Ioi_top [OrderTop α] : ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top
#align upper_set.Ioi_top UpperSet.Ioi_top

@[simp]
theorem Ici_bot [OrderBot α] : ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot
#align upper_set.Ici_bot UpperSet.Ici_bot

end Preorder

section SemilatticeSup

variable [SemilatticeSup α]

@[simp]
theorem Ici_sup (a b : α) : ici (a ⊔ b) = ici a ⊔ ici b :=
  ext Ici_inter_Ici.symm
#align upper_set.Ici_sup UpperSet.Ici_sup

/-- `upper_set.Ici` as a `sup_hom`. -/
def iciSupHom : SupHom α (UpperSet α) :=
  ⟨ici, Ici_sup⟩
#align upper_set.Ici_sup_hom UpperSet.iciSupHom

@[simp]
theorem Ici_sup_hom_apply (a : α) : iciSupHom a = ici a :=
  rfl
#align upper_set.Ici_sup_hom_apply UpperSet.Ici_sup_hom_apply

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Ici_Sup (S : Set α) : ici (sup S) = ⨆ a ∈ S, ici a :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_supr_iff, Sup_le_iff]
#align upper_set.Ici_Sup UpperSet.Ici_Sup

@[simp]
theorem Ici_supr (f : ι → α) : ici (⨆ i, f i) = ⨆ i, ici (f i) :=
  SetLike.ext fun c => by simp only [mem_Ici_iff, mem_supr_iff, supr_le_iff]
#align upper_set.Ici_supr UpperSet.Ici_supr

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem Ici_supr₂ (f : ∀ i, κ i → α) : ici (⨆ (i) (j), f i j) = ⨆ (i) (j), ici (f i j) := by
  simp_rw [Ici_supr]
#align upper_set.Ici_supr₂ UpperSet.Ici_supr₂

/- warning: upper_set.Ici_Sup_hom clashes with upper_set.Ici_sup_hom -> UpperSet.iciSupHom
Case conversion may be inaccurate. Consider using '#align upper_set.Ici_Sup_hom UpperSet.iciSupHomₓ'. -/
#print UpperSet.iciSupHom /-
/-- `upper_set.Ici` as a `Sup_hom`. -/
def iciSupHom : SupHom α (UpperSet α) :=
  ⟨ici, fun s => (Ici_Sup s).trans Sup_image.symm⟩
#align upper_set.Ici_Sup_hom UpperSet.iciSupHom
-/

@[simp]
theorem Ici_Sup_hom_apply (a : α) : iciSupHom a = toDual (ici a) :=
  rfl
#align upper_set.Ici_Sup_hom_apply UpperSet.Ici_Sup_hom_apply

end CompleteLattice

end UpperSet

namespace LowerSet

section Preorder

variable [Preorder α] [Preorder β] {s : LowerSet α} {a b : α}

/-- Principal lower set. `set.Iic` as a lower set. The smallest lower set containing a given
element. -/
def iic (a : α) : LowerSet α :=
  ⟨iic a, is_lower_set_Iic a⟩
#align lower_set.Iic LowerSet.iic

/-- Strict principal lower set. `set.Iio` as a lower set. -/
def iio (a : α) : LowerSet α :=
  ⟨iio a, is_lower_set_Iio a⟩
#align lower_set.Iio LowerSet.iio

@[simp]
theorem coe_Iic (a : α) : ↑(iic a) = Set.iic a :=
  rfl
#align lower_set.coe_Iic LowerSet.coe_Iic

@[simp]
theorem coe_Iio (a : α) : ↑(iio a) = Set.iio a :=
  rfl
#align lower_set.coe_Iio LowerSet.coe_Iio

@[simp]
theorem mem_Iic_iff : b ∈ iic a ↔ b ≤ a :=
  Iff.rfl
#align lower_set.mem_Iic_iff LowerSet.mem_Iic_iff

@[simp]
theorem mem_Iio_iff : b ∈ iio a ↔ b < a :=
  Iff.rfl
#align lower_set.mem_Iio_iff LowerSet.mem_Iio_iff

@[simp]
theorem map_Iic (f : α ≃o β) (a : α) : map f (iic a) = iic (f a) := by
  ext
  simp
#align lower_set.map_Iic LowerSet.map_Iic

@[simp]
theorem map_Iio (f : α ≃o β) (a : α) : map f (iio a) = iio (f a) := by
  ext
  simp
#align lower_set.map_Iio LowerSet.map_Iio

theorem Ioi_le_Ici (a : α) : ioi a ≤ ici a :=
  Ioi_subset_Ici_self
#align lower_set.Ioi_le_Ici LowerSet.Ioi_le_Ici

@[simp]
theorem Iic_top [OrderTop α] : iic (⊤ : α) = ⊤ :=
  SetLike.coe_injective Iic_top
#align lower_set.Iic_top LowerSet.Iic_top

@[simp]
theorem Iio_bot [OrderBot α] : iio (⊥ : α) = ⊥ :=
  SetLike.coe_injective Iio_bot
#align lower_set.Iio_bot LowerSet.Iio_bot

end Preorder

section SemilatticeInf

variable [SemilatticeInf α]

@[simp]
theorem Iic_inf (a b : α) : iic (a ⊓ b) = iic a ⊓ iic b :=
  SetLike.coe_injective Iic_inter_Iic.symm
#align lower_set.Iic_inf LowerSet.Iic_inf

/-- `lower_set.Iic` as an `inf_hom`. -/
def iicInfHom : InfHom α (LowerSet α) :=
  ⟨iic, Iic_inf⟩
#align lower_set.Iic_inf_hom LowerSet.iicInfHom

@[simp]
theorem coe_Iic_inf_hom : (iicInfHom : α → LowerSet α) = Iic :=
  rfl
#align lower_set.coe_Iic_inf_hom LowerSet.coe_Iic_inf_hom

@[simp]
theorem Iic_inf_hom_apply (a : α) : iicInfHom a = iic a :=
  rfl
#align lower_set.Iic_inf_hom_apply LowerSet.Iic_inf_hom_apply

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Iic_Inf (S : Set α) : iic (inf S) = ⨅ a ∈ S, iic a :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_infi₂_iff, le_Inf_iff]
#align lower_set.Iic_Inf LowerSet.Iic_Inf

@[simp]
theorem Iic_infi (f : ι → α) : iic (⨅ i, f i) = ⨅ i, iic (f i) :=
  SetLike.ext fun c => by simp only [mem_Iic_iff, mem_infi_iff, le_infi_iff]
#align lower_set.Iic_infi LowerSet.Iic_infi

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem Iic_infi₂ (f : ∀ i, κ i → α) : iic (⨅ (i) (j), f i j) = ⨅ (i) (j), iic (f i j) := by
  simp_rw [Iic_infi]
#align lower_set.Iic_infi₂ LowerSet.Iic_infi₂

/- warning: lower_set.Iic_Inf_hom clashes with lower_set.Iic_inf_hom -> LowerSet.iicInfHom
Case conversion may be inaccurate. Consider using '#align lower_set.Iic_Inf_hom LowerSet.iicInfHomₓ'. -/
#print LowerSet.iicInfHom /-
/-- `lower_set.Iic` as an `Inf_hom`. -/
def iicInfHom : InfHom α (LowerSet α) :=
  ⟨iic, fun s => (Iic_Inf s).trans Inf_image.symm⟩
#align lower_set.Iic_Inf_hom LowerSet.iicInfHom
-/

@[simp]
theorem coe_Iic_Inf_hom : (iicInfHom : α → LowerSet α) = Iic :=
  rfl
#align lower_set.coe_Iic_Inf_hom LowerSet.coe_Iic_Inf_hom

@[simp]
theorem Iic_Inf_hom_apply (a : α) : iicInfHom a = iic a :=
  rfl
#align lower_set.Iic_Inf_hom_apply LowerSet.Iic_Inf_hom_apply

end CompleteLattice

end LowerSet

section Closure

variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

/-- The greatest upper set containing a given set. -/
def upperClosure (s : Set α) : UpperSet α :=
  ⟨{ x | ∃ a ∈ s, a ≤ x }, fun x y h => Exists₂Cat.imp fun a _ => h.trans'⟩
#align upper_closure upperClosure

/-- The least lower set containing a given set. -/
def lowerClosure (s : Set α) : LowerSet α :=
  ⟨{ x | ∃ a ∈ s, x ≤ a }, fun x y h => Exists₂Cat.imp fun a _ => h.trans⟩
#align lower_closure lowerClosure

-- We do not tag those two as `simp` to respect the abstraction.
@[norm_cast]
theorem coe_upper_closure (s : Set α) : ↑(upperClosure s) = { x | ∃ a ∈ s, a ≤ x } :=
  rfl
#align coe_upper_closure coe_upper_closure

@[norm_cast]
theorem coe_lower_closure (s : Set α) : ↑(lowerClosure s) = { x | ∃ a ∈ s, x ≤ a } :=
  rfl
#align coe_lower_closure coe_lower_closure

@[simp]
theorem mem_upper_closure : x ∈ upperClosure s ↔ ∃ a ∈ s, a ≤ x :=
  Iff.rfl
#align mem_upper_closure mem_upper_closure

@[simp]
theorem mem_lower_closure : x ∈ lowerClosure s ↔ ∃ a ∈ s, x ≤ a :=
  Iff.rfl
#align mem_lower_closure mem_lower_closure

theorem subset_upper_closure : s ⊆ upperClosure s := fun x hx => ⟨x, hx, le_rfl⟩
#align subset_upper_closure subset_upper_closure

theorem subset_lower_closure : s ⊆ lowerClosure s := fun x hx => ⟨x, hx, le_rfl⟩
#align subset_lower_closure subset_lower_closure

theorem upper_closure_min (h : s ⊆ t) (ht : IsUpperSet t) : ↑(upperClosure s) ⊆ t :=
  fun a ⟨b, hb, hba⟩ => ht hba <| h hb
#align upper_closure_min upper_closure_min

theorem lower_closure_min (h : s ⊆ t) (ht : IsLowerSet t) : ↑(lowerClosure s) ⊆ t :=
  fun a ⟨b, hb, hab⟩ => ht hab <| h hb
#align lower_closure_min lower_closure_min

protected theorem IsUpperSet.upper_closure (hs : IsUpperSet s) : ↑(upperClosure s) = s :=
  (upper_closure_min Subset.rfl hs).antisymm subset_upper_closure
#align is_upper_set.upper_closure IsUpperSet.upper_closure

protected theorem IsLowerSet.lower_closure (hs : IsLowerSet s) : ↑(lowerClosure s) = s :=
  (lower_closure_min Subset.rfl hs).antisymm subset_lower_closure
#align is_lower_set.lower_closure IsLowerSet.lower_closure

@[simp]
protected theorem UpperSet.upper_closure (s : UpperSet α) : upperClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.upperClosure
#align upper_set.upper_closure UpperSet.upper_closure

@[simp]
protected theorem LowerSet.lower_closure (s : LowerSet α) : lowerClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.lowerClosure
#align lower_set.lower_closure LowerSet.lower_closure

@[simp]
theorem upper_closure_image (f : α ≃o β) :
    upperClosure (f '' s) = UpperSet.map f (upperClosure s) := by
  rw [← f.symm_symm, ← UpperSet.symm_map, f.symm_symm]
  ext
  simp [-UpperSet.symm_map, UpperSet.map, OrderIso.symm, ← f.le_symm_apply]
#align upper_closure_image upper_closure_image

@[simp]
theorem lower_closure_image (f : α ≃o β) :
    lowerClosure (f '' s) = LowerSet.map f (lowerClosure s) := by
  rw [← f.symm_symm, ← LowerSet.symm_map, f.symm_symm]
  ext
  simp [-LowerSet.symm_map, LowerSet.map, OrderIso.symm, ← f.symm_apply_le]
#align lower_closure_image lower_closure_image

@[simp]
theorem UpperSet.infi_Ici (s : Set α) : (⨅ a ∈ s, UpperSet.ici a) = upperClosure s := by
  ext
  simp
#align upper_set.infi_Ici UpperSet.infi_Ici

@[simp]
theorem LowerSet.supr_Iic (s : Set α) : (⨆ a ∈ s, LowerSet.iic a) = lowerClosure s := by
  ext
  simp
#align lower_set.supr_Iic LowerSet.supr_Iic

theorem gc_upper_closure_coe :
    GaloisConnection (to_dual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) (coe ∘ of_dual) := fun s t =>
  ⟨fun h => subset_upper_closure.trans <| UpperSet.coe_subset_coe.2 h, fun h =>
    upper_closure_min h t.upper⟩
#align gc_upper_closure_coe gc_upper_closure_coe

theorem gc_lower_closure_coe : GaloisConnection (lowerClosure : Set α → LowerSet α) coe :=
  fun s t =>
  ⟨fun h => subset_lower_closure.trans <| LowerSet.coe_subset_coe.2 h, fun h =>
    lower_closure_min h t.lower⟩
#align gc_lower_closure_coe gc_lower_closure_coe

/-- `upper_closure` forms a reversed Galois insertion with the coercion from upper sets to sets. -/
def giUpperClosureCoe :
    GaloisInsertion (to_dual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ)
      (coe ∘
        of_dual) where 
  choice s hs := toDual (⟨s, fun a b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upper_closure_coe
  le_l_u _ := subset_upper_closure
  choice_eq s hs := ofDual.Injective <| SetLike.coe_injective <| subset_upper_closure.antisymm hs
#align gi_upper_closure_coe giUpperClosureCoe

/-- `lower_closure` forms a Galois insertion with the coercion from lower sets to sets. -/
def giLowerClosureCoe :
    GaloisInsertion (lowerClosure : Set α → LowerSet α)
      coe where 
  choice s hs := ⟨s, fun a b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lower_closure_coe
  le_l_u _ := subset_lower_closure
  choice_eq s hs := SetLike.coe_injective <| subset_lower_closure.antisymm hs
#align gi_lower_closure_coe giLowerClosureCoe

theorem upper_closure_anti : Antitone (upperClosure : Set α → UpperSet α) :=
  gc_upper_closure_coe.monotone_l
#align upper_closure_anti upper_closure_anti

theorem lower_closure_mono : Monotone (lowerClosure : Set α → LowerSet α) :=
  gc_lower_closure_coe.monotone_l
#align lower_closure_mono lower_closure_mono

@[simp]
theorem upper_closure_empty : upperClosure (∅ : Set α) = ⊤ := by
  ext
  simp
#align upper_closure_empty upper_closure_empty

@[simp]
theorem lower_closure_empty : lowerClosure (∅ : Set α) = ⊥ := by
  ext
  simp
#align lower_closure_empty lower_closure_empty

@[simp]
theorem upper_closure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.ici a := by
  ext
  simp
#align upper_closure_singleton upper_closure_singleton

@[simp]
theorem lower_closure_singleton (a : α) : lowerClosure ({a} : Set α) = LowerSet.iic a := by
  ext
  simp
#align lower_closure_singleton lower_closure_singleton

@[simp]
theorem upper_closure_univ : upperClosure (univ : Set α) = ⊥ :=
  le_bot_iff.1 subset_upper_closure
#align upper_closure_univ upper_closure_univ

@[simp]
theorem lower_closure_univ : lowerClosure (univ : Set α) = ⊤ :=
  top_le_iff.1 subset_lower_closure
#align lower_closure_univ lower_closure_univ

@[simp]
theorem upper_closure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅ :=
  ⟨fun h => subset_empty_iff.1 <| subset_upper_closure.trans (congr_arg coe h).Subset, by
    rintro rfl
    exact upper_closure_empty⟩
#align upper_closure_eq_top_iff upper_closure_eq_top_iff

@[simp]
theorem lower_closure_eq_bot_iff : lowerClosure s = ⊥ ↔ s = ∅ :=
  ⟨fun h => subset_empty_iff.1 <| subset_lower_closure.trans (congr_arg coe h).Subset, by
    rintro rfl
    exact lower_closure_empty⟩
#align lower_closure_eq_bot_iff lower_closure_eq_bot_iff

@[simp]
theorem upper_closure_union (s t : Set α) :
    upperClosure (s ∪ t) = upperClosure s ⊓ upperClosure t := by
  ext
  simp [or_and_right, exists_or]
#align upper_closure_union upper_closure_union

@[simp]
theorem lower_closure_union (s t : Set α) :
    lowerClosure (s ∪ t) = lowerClosure s ⊔ lowerClosure t := by
  ext
  simp [or_and_right, exists_or]
#align lower_closure_union lower_closure_union

@[simp]
theorem upper_closure_Union (f : ι → Set α) : upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i) :=
  by 
  ext
  simp [← exists_and_right, @exists_comm α]
#align upper_closure_Union upper_closure_Union

@[simp]
theorem lower_closure_Union (f : ι → Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i) :=
  by 
  ext
  simp [← exists_and_right, @exists_comm α]
#align lower_closure_Union lower_closure_Union

@[simp]
theorem upper_closure_sUnion (S : Set (Set α)) : upperClosure (⋃₀S) = ⨅ s ∈ S, upperClosure s := by
  simp_rw [sUnion_eq_bUnion, upper_closure_Union]
#align upper_closure_sUnion upper_closure_sUnion

@[simp]
theorem lower_closure_sUnion (S : Set (Set α)) : lowerClosure (⋃₀S) = ⨆ s ∈ S, lowerClosure s := by
  simp_rw [sUnion_eq_bUnion, lower_closure_Union]
#align lower_closure_sUnion lower_closure_sUnion

theorem Set.OrdConnected.upper_closure_inter_lower_closure (h : s.OrdConnected) :
    ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  (subset_inter subset_upper_closure subset_lower_closure).antisymm'
    fun a ⟨⟨b, hb, hba⟩, c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩
#align
  set.ord_connected.upper_closure_inter_lower_closure Set.OrdConnected.upper_closure_inter_lower_closure

theorem ord_connected_iff_upper_closure_inter_lower_closure :
    s.OrdConnected ↔ ↑(upperClosure s) ∩ ↑(lowerClosure s) = s := by
  refine' ⟨Set.OrdConnected.upper_closure_inter_lower_closure, fun h => _⟩
  rw [← h]
  exact (UpperSet.upper _).OrdConnected.inter (LowerSet.lower _).OrdConnected
#align
  ord_connected_iff_upper_closure_inter_lower_closure ord_connected_iff_upper_closure_inter_lower_closure

end Closure

/-! ### Product -/


section Preorder

variable [Preorder α] [Preorder β]

section

variable {s : Set α} {t : Set β} {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ t) :=
  fun a b h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
#align is_upper_set.prod IsUpperSet.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ t) :=
  fun a b h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
#align is_lower_set.prod IsLowerSet.prod

end

namespace UpperSet

variable (s s₁ s₂ : UpperSet α) (t t₁ t₂ : UpperSet β) {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two upper sets as an upper set. -/
def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.Prod t.2⟩
#align upper_set.prod UpperSet.prod

-- mathport name: upper_set.prod
infixr:82 " ×ˢ " => prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, norm_cast]
theorem coe_prod : (↑(s ×ˢ t) : Set (α × β)) = s ×ˢ t :=
  rfl
#align upper_set.coe_prod UpperSet.coe_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mem_prod {s : UpperSet α} {t : UpperSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl
#align upper_set.mem_prod UpperSet.mem_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Ici_prod (x : α × β) : ici x = ici x.1 ×ˢ ici x.2 :=
  rfl
#align upper_set.Ici_prod UpperSet.Ici_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : ici a ×ˢ ici b = ici (a, b) :=
  rfl
#align upper_set.Ici_prod_Ici UpperSet.Ici_prod_Ici

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_top : s ×ˢ (⊤ : UpperSet β) = ⊤ :=
  ext prod_empty
#align upper_set.prod_top UpperSet.prod_top

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem top_prod : (⊤ : UpperSet α) ×ˢ t = ⊤ :=
  ext empty_prod
#align upper_set.top_prod UpperSet.top_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bot_prod_bot : (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥ :=
  ext univ_prod_univ
#align upper_set.bot_prod_bot UpperSet.bot_prod_bot

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext inter_prod
#align upper_set.sup_prod UpperSet.sup_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_inter
#align upper_set.prod_sup UpperSet.prod_sup

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext union_prod
#align upper_set.inf_prod UpperSet.inf_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_union
#align upper_set.prod_inf UpperSet.prod_inf

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂) :=
  ext prod_inter_prod
#align upper_set.prod_sup_prod UpperSet.prod_sup_prod

variable {s s₁ s₂ t t₁ t₂}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  prod_mono
#align upper_set.prod_mono UpperSet.prod_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  prod_mono_left
#align upper_set.prod_mono_left UpperSet.prod_mono_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  prod_mono_right
#align upper_set.prod_mono_right UpperSet.prod_mono_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self
#align upper_set.prod_self_le_prod_self UpperSet.prod_self_le_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self
#align upper_set.prod_self_lt_prod_self UpperSet.prod_self_lt_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤ :=
  prod_subset_prod_iff.trans <| by simp
#align upper_set.prod_le_prod_iff UpperSet.prod_le_prod_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff
#align upper_set.prod_eq_top UpperSet.prod_eq_top

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem codisjoint_prod : Codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Codisjoint s₁ s₂ ∨ Codisjoint t₁ t₂ :=
  by simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]
#align upper_set.codisjoint_prod UpperSet.codisjoint_prod

end UpperSet

namespace LowerSet

variable (s s₁ s₂ : LowerSet α) (t t₁ t₂ : LowerSet β) {x : α × β}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two lower sets as a lower set. -/
def prod : LowerSet (α × β) :=
  ⟨s ×ˢ t, s.2.Prod t.2⟩
#align lower_set.prod LowerSet.prod

-- mathport name: lower_set.prod
infixr:82 " ×ˢ " => LowerSet.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, norm_cast]
theorem coe_prod : (↑(s ×ˢ t) : Set (α × β)) = s ×ˢ t :=
  rfl
#align lower_set.coe_prod LowerSet.coe_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mem_prod {s : LowerSet α} {t : LowerSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl
#align lower_set.mem_prod LowerSet.mem_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Iic_prod (x : α × β) : iic x = iic x.1 ×ˢ iic x.2 :=
  rfl
#align lower_set.Iic_prod LowerSet.Iic_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : iic a ×ˢ iic b = iic (a, b) :=
  rfl
#align lower_set.Ici_prod_Ici LowerSet.Ici_prod_Ici

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_bot : s ×ˢ (⊥ : LowerSet β) = ⊥ :=
  ext prod_empty
#align lower_set.prod_bot LowerSet.prod_bot

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem bot_prod : (⊥ : LowerSet α) ×ˢ t = ⊥ :=
  ext empty_prod
#align lower_set.bot_prod LowerSet.bot_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem top_prod_top : (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤ :=
  ext univ_prod_univ
#align lower_set.top_prod_top LowerSet.top_prod_top

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext inter_prod
#align lower_set.inf_prod LowerSet.inf_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_inter
#align lower_set.prod_inf LowerSet.prod_inf

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext union_prod
#align lower_set.sup_prod LowerSet.sup_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_union
#align lower_set.prod_sup LowerSet.prod_sup

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂) :=
  ext prod_inter_prod
#align lower_set.prod_inf_prod LowerSet.prod_inf_prod

variable {s s₁ s₂ t t₁ t₂}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  prod_mono
#align lower_set.prod_mono LowerSet.prod_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  prod_mono_left
#align lower_set.prod_mono_left LowerSet.prod_mono_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  prod_mono_right
#align lower_set.prod_mono_right LowerSet.prod_mono_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self
#align lower_set.prod_self_le_prod_self LowerSet.prod_self_le_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self
#align lower_set.prod_self_lt_prod_self LowerSet.prod_self_lt_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥ :=
  prod_subset_prod_iff.trans <| by simp
#align lower_set.prod_le_prod_iff LowerSet.prod_le_prod_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff
#align lower_set.prod_eq_bot LowerSet.prod_eq_bot

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]
#align lower_set.disjoint_prod LowerSet.disjoint_prod

end LowerSet

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem upper_closure_prod (s : Set α) (t : Set β) :
    upperClosure (s ×ˢ t) = upperClosure s ×ˢ upperClosure t := by
  ext
  simp [Prod.le_def, and_and_and_comm _ (_ ∈ t)]
#align upper_closure_prod upper_closure_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem lower_closure_prod (s : Set α) (t : Set β) :
    lowerClosure (s ×ˢ t) = lowerClosure s ×ˢ lowerClosure t := by
  ext
  simp [Prod.le_def, and_and_and_comm _ (_ ∈ t)]
#align lower_closure_prod lower_closure_prod

end Preorder

