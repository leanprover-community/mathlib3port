/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.filter.n_ary
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Prod

/-!
# N-ary maps of filter

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the binary and ternary maps of filters. This is mostly useful to define pointwise
operations on filters.

## Main declarations

* `filter.map₂`: Binary map of filters.
* `filter.map₃`: Ternary map of filters.

## Notes

This file is very similar to `data.set.n_ary`, `data.finset.n_ary` and `data.option.n_ary`. Please
keep them in sync.
-/


open Function Set

open Filter

namespace Filter

variable {α α' β β' γ γ' δ δ' ε ε' : Type _} {m : α → β → γ} {f f₁ f₂ : Filter α}
  {g g₁ g₂ : Filter β} {h h₁ h₂ : Filter γ} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {u : Set γ}
  {v : Set δ} {a : α} {b : β} {c : γ}

#print Filter.map₂ /-
/-- The image of a binary function `m : α → β → γ` as a function `filter α → filter β → filter γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ (m : α → β → γ) (f : Filter α) (g : Filter β) : Filter γ
    where
  sets := { s | ∃ u v, u ∈ f ∧ v ∈ g ∧ image2 m u v ⊆ s }
  univ_sets := ⟨univ, univ, univ_sets _, univ_sets _, subset_univ _⟩
  sets_of_superset s t hs hst :=
    Exists₂Cat.imp (fun u v => And.imp_right <| And.imp_right fun h => Subset.trans h hst) hs
  inter_sets s t := by
    simp only [exists_prop, mem_set_of_eq, subset_inter_iff]
    rintro ⟨s₁, s₂, hs₁, hs₂, hs⟩ ⟨t₁, t₂, ht₁, ht₂, ht⟩
    exact
      ⟨s₁ ∩ t₁, s₂ ∩ t₂, inter_sets f hs₁ ht₁, inter_sets g hs₂ ht₂,
        (image2_subset (inter_subset_left _ _) <| inter_subset_left _ _).trans hs,
        (image2_subset (inter_subset_right _ _) <| inter_subset_right _ _).trans ht⟩
#align filter.map₂ Filter.map₂
-/

/- warning: filter.mem_map₂_iff -> Filter.mem_map₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β} {u : Set.{u3} γ}, Iff (Membership.Mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (Filter.hasMem.{u3} γ) u (Filter.map₂.{u1, u2, u3} α β γ m f g)) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (And (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t g) (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ m s t) u)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g : Filter.{u1} β} {u : Set.{u3} γ}, Iff (Membership.mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (instMembershipSetFilter.{u3} γ) u (Filter.map₂.{u2, u1, u3} α β γ m f g)) (Exists.{succ u2} (Set.{u2} α) (fun (s : Set.{u2} α) => Exists.{succ u1} (Set.{u1} β) (fun (t : Set.{u1} β) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) (And (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) t g) (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet.{u3} γ) (Set.image2.{u2, u1, u3} α β γ m s t) u)))))
Case conversion may be inaccurate. Consider using '#align filter.mem_map₂_iff Filter.mem_map₂_iffₓ'. -/
@[simp]
theorem mem_map₂_iff : u ∈ map₂ m f g ↔ ∃ s t, s ∈ f ∧ t ∈ g ∧ image2 m s t ⊆ u :=
  Iff.rfl
#align filter.mem_map₂_iff Filter.mem_map₂_iff

/- warning: filter.image2_mem_map₂ -> Filter.image2_mem_map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β} {s : Set.{u1} α} {t : Set.{u2} β}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t g) -> (Membership.Mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (Filter.hasMem.{u3} γ) (Set.image2.{u1, u2, u3} α β γ m s t) (Filter.map₂.{u1, u2, u3} α β γ m f g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : α -> β -> γ} {f : Filter.{u3} α} {g : Filter.{u2} β} {s : Set.{u3} α} {t : Set.{u2} β}, (Membership.mem.{u3, u3} (Set.{u3} α) (Filter.{u3} α) (instMembershipSetFilter.{u3} α) s f) -> (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) t g) -> (Membership.mem.{u1, u1} (Set.{u1} γ) (Filter.{u1} γ) (instMembershipSetFilter.{u1} γ) (Set.image2.{u3, u2, u1} α β γ m s t) (Filter.map₂.{u3, u2, u1} α β γ m f g))
Case conversion may be inaccurate. Consider using '#align filter.image2_mem_map₂ Filter.image2_mem_map₂ₓ'. -/
theorem image2_mem_map₂ (hs : s ∈ f) (ht : t ∈ g) : image2 m s t ∈ map₂ m f g :=
  ⟨_, _, hs, ht, Subset.rfl⟩
#align filter.image2_mem_map₂ Filter.image2_mem_map₂

/- warning: filter.map_prod_eq_map₂ -> Filter.map_prod_eq_map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : α -> β -> γ) (f : Filter.{u1} α) (g : Filter.{u2} β), Eq.{succ u3} (Filter.{u3} γ) (Filter.map.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (fun (p : Prod.{u1, u2} α β) => m (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)) (Filter.prod.{u1, u2} α β f g)) (Filter.map₂.{u1, u2, u3} α β γ m f g)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (m : α -> β -> γ) (f : Filter.{u3} α) (g : Filter.{u2} β), Eq.{succ u1} (Filter.{u1} γ) (Filter.map.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (fun (p : Prod.{u3, u2} α β) => m (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)) (Filter.prod.{u3, u2} α β f g)) (Filter.map₂.{u3, u2, u1} α β γ m f g)
Case conversion may be inaccurate. Consider using '#align filter.map_prod_eq_map₂ Filter.map_prod_eq_map₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem map_prod_eq_map₂ (m : α → β → γ) (f : Filter α) (g : Filter β) :
    Filter.map (fun p : α × β => m p.1 p.2) (f ×ᶠ g) = map₂ m f g :=
  by
  ext s
  constructor
  · intro hmem
    rw [Filter.mem_map_iff_exists_image] at hmem
    obtain ⟨s', hs', hsub⟩ := hmem
    rw [Filter.mem_prod_iff] at hs'
    obtain ⟨t, ht, t', ht', hsub'⟩ := hs'
    refine' ⟨t, t', ht, ht', _⟩
    rw [← Set.image_prod]
    exact subset_trans (Set.image_subset (fun p : α × β => m p.fst p.snd) hsub') hsub
  · intro hmem
    rw [mem_map₂_iff] at hmem
    obtain ⟨t, t', ht, ht', hsub⟩ := hmem
    rw [← Set.image_prod] at hsub
    rw [Filter.mem_map_iff_exists_image]
    exact ⟨t ×ˢ t', Filter.prod_mem_prod ht ht', hsub⟩
#align filter.map_prod_eq_map₂ Filter.map_prod_eq_map₂

/- warning: filter.map_prod_eq_map₂' -> Filter.map_prod_eq_map₂' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : (Prod.{u1, u2} α β) -> γ) (f : Filter.{u1} α) (g : Filter.{u2} β), Eq.{succ u3} (Filter.{u3} γ) (Filter.map.{max u1 u2, u3} (Prod.{u1, u2} α β) γ m (Filter.prod.{u1, u2} α β f g)) (Filter.map₂.{u1, u2, u3} α β γ (fun (a : α) (b : β) => m (Prod.mk.{u1, u2} α β a b)) f g)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (m : (Prod.{u3, u2} α β) -> γ) (f : Filter.{u3} α) (g : Filter.{u2} β), Eq.{succ u1} (Filter.{u1} γ) (Filter.map.{max u3 u2, u1} (Prod.{u3, u2} α β) γ m (Filter.prod.{u3, u2} α β f g)) (Filter.map₂.{u3, u2, u1} α β γ (fun (a : α) (b : β) => m (Prod.mk.{u3, u2} α β a b)) f g)
Case conversion may be inaccurate. Consider using '#align filter.map_prod_eq_map₂' Filter.map_prod_eq_map₂'ₓ'. -/
theorem map_prod_eq_map₂' (m : α × β → γ) (f : Filter α) (g : Filter β) :
    Filter.map m (f ×ᶠ g) = map₂ (fun a b => m (a, b)) f g :=
  by
  refine' Eq.trans _ (map_prod_eq_map₂ (curry m) f g)
  ext
  simp
#align filter.map_prod_eq_map₂' Filter.map_prod_eq_map₂'

/- warning: filter.map₂_mk_eq_prod -> Filter.map₂_mk_eq_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Filter.{u1} α) (g : Filter.{u2} β), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.map₂.{u1, u2, max u1 u2} α β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β) f g) (Filter.prod.{u1, u2} α β f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Filter.{u2} α) (g : Filter.{u1} β), Eq.{max (succ u2) (succ u1)} (Filter.{max u1 u2} (Prod.{u2, u1} α β)) (Filter.map₂.{u2, u1, max u1 u2} α β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β) f g) (Filter.prod.{u2, u1} α β f g)
Case conversion may be inaccurate. Consider using '#align filter.map₂_mk_eq_prod Filter.map₂_mk_eq_prodₓ'. -/
@[simp]
theorem map₂_mk_eq_prod (f : Filter α) (g : Filter β) : map₂ Prod.mk f g = f ×ᶠ g := by
  ext <;> simp [mem_prod_iff]
#align filter.map₂_mk_eq_prod Filter.map₂_mk_eq_prod

/- warning: filter.map₂_mono -> Filter.map₂_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f₁ f₂) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) g₁ g₂) -> (LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ))) (Filter.map₂.{u1, u2, u3} α β γ m f₁ g₁) (Filter.map₂.{u1, u2, u3} α β γ m f₂ g₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : α -> β -> γ} {f₁ : Filter.{u3} α} {f₂ : Filter.{u3} α} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β}, (LE.le.{u3} (Filter.{u3} α) (Preorder.toLE.{u3} (Filter.{u3} α) (PartialOrder.toPreorder.{u3} (Filter.{u3} α) (Filter.instPartialOrderFilter.{u3} α))) f₁ f₂) -> (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) g₁ g₂) -> (LE.le.{u1} (Filter.{u1} γ) (Preorder.toLE.{u1} (Filter.{u1} γ) (PartialOrder.toPreorder.{u1} (Filter.{u1} γ) (Filter.instPartialOrderFilter.{u1} γ))) (Filter.map₂.{u3, u2, u1} α β γ m f₁ g₁) (Filter.map₂.{u3, u2, u1} α β γ m f₂ g₂))
Case conversion may be inaccurate. Consider using '#align filter.map₂_mono Filter.map₂_monoₓ'. -/
-- lemma image2_mem_map₂_iff (hm : injective2 m) : image2 m s t ∈ map₂ m f g ↔ s ∈ f ∧ t ∈ g :=
-- ⟨by { rintro ⟨u, v, hu, hv, h⟩, rw image2_subset_image2_iff hm at h,
--   exact ⟨mem_of_superset hu h.1, mem_of_superset hv h.2⟩ }, λ h, image2_mem_map₂ h.1 h.2⟩
theorem map₂_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : map₂ m f₁ g₁ ≤ map₂ m f₂ g₂ :=
  fun _ ⟨s, t, hs, ht, hst⟩ => ⟨s, t, hf hs, hg ht, hst⟩
#align filter.map₂_mono Filter.map₂_mono

/- warning: filter.map₂_mono_left -> Filter.map₂_mono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β}, (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) g₁ g₂) -> (LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ))) (Filter.map₂.{u1, u2, u3} α β γ m f g₁) (Filter.map₂.{u1, u2, u3} α β γ m f g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m : α -> β -> γ} {f : Filter.{u1} α} {g₁ : Filter.{u3} β} {g₂ : Filter.{u3} β}, (LE.le.{u3} (Filter.{u3} β) (Preorder.toLE.{u3} (Filter.{u3} β) (PartialOrder.toPreorder.{u3} (Filter.{u3} β) (Filter.instPartialOrderFilter.{u3} β))) g₁ g₂) -> (LE.le.{u2} (Filter.{u2} γ) (Preorder.toLE.{u2} (Filter.{u2} γ) (PartialOrder.toPreorder.{u2} (Filter.{u2} γ) (Filter.instPartialOrderFilter.{u2} γ))) (Filter.map₂.{u1, u3, u2} α β γ m f g₁) (Filter.map₂.{u1, u3, u2} α β γ m f g₂))
Case conversion may be inaccurate. Consider using '#align filter.map₂_mono_left Filter.map₂_mono_leftₓ'. -/
theorem map₂_mono_left (h : g₁ ≤ g₂) : map₂ m f g₁ ≤ map₂ m f g₂ :=
  map₂_mono Subset.rfl h
#align filter.map₂_mono_left Filter.map₂_mono_left

/- warning: filter.map₂_mono_right -> Filter.map₂_mono_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {g : Filter.{u2} β}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f₁ f₂) -> (LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ))) (Filter.map₂.{u1, u2, u3} α β γ m f₁ g) (Filter.map₂.{u1, u2, u3} α β γ m f₂ g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {m : α -> β -> γ} {f₁ : Filter.{u3} α} {f₂ : Filter.{u3} α} {g : Filter.{u1} β}, (LE.le.{u3} (Filter.{u3} α) (Preorder.toLE.{u3} (Filter.{u3} α) (PartialOrder.toPreorder.{u3} (Filter.{u3} α) (Filter.instPartialOrderFilter.{u3} α))) f₁ f₂) -> (LE.le.{u2} (Filter.{u2} γ) (Preorder.toLE.{u2} (Filter.{u2} γ) (PartialOrder.toPreorder.{u2} (Filter.{u2} γ) (Filter.instPartialOrderFilter.{u2} γ))) (Filter.map₂.{u3, u1, u2} α β γ m f₁ g) (Filter.map₂.{u3, u1, u2} α β γ m f₂ g))
Case conversion may be inaccurate. Consider using '#align filter.map₂_mono_right Filter.map₂_mono_rightₓ'. -/
theorem map₂_mono_right (h : f₁ ≤ f₂) : map₂ m f₁ g ≤ map₂ m f₂ g :=
  map₂_mono h Subset.rfl
#align filter.map₂_mono_right Filter.map₂_mono_right

/- warning: filter.le_map₂_iff -> Filter.le_map₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β} {h : Filter.{u3} γ}, Iff (LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ))) h (Filter.map₂.{u1, u2, u3} α β γ m f g)) (forall {{s : Set.{u1} α}}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (forall {{t : Set.{u2} β}}, (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t g) -> (Membership.Mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (Filter.hasMem.{u3} γ) (Set.image2.{u1, u2, u3} α β γ m s t) h)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g : Filter.{u1} β} {h : Filter.{u3} γ}, Iff (LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.instPartialOrderFilter.{u3} γ))) h (Filter.map₂.{u2, u1, u3} α β γ m f g)) (forall {{s : Set.{u2} α}}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s f) -> (forall {{t : Set.{u1} β}}, (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) t g) -> (Membership.mem.{u3, u3} (Set.{u3} γ) (Filter.{u3} γ) (instMembershipSetFilter.{u3} γ) (Set.image2.{u2, u1, u3} α β γ m s t) h)))
Case conversion may be inaccurate. Consider using '#align filter.le_map₂_iff Filter.le_map₂_iffₓ'. -/
@[simp]
theorem le_map₂_iff {h : Filter γ} :
    h ≤ map₂ m f g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → image2 m s t ∈ h :=
  ⟨fun H s hs t ht => H <| image2_mem_map₂ hs ht, fun H u ⟨s, t, hs, ht, hu⟩ =>
    mem_of_superset (H hs ht) hu⟩
#align filter.le_map₂_iff Filter.le_map₂_iff

/- warning: filter.map₂_bot_left -> Filter.map₂_bot_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {g : Filter.{u2} β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) g) (Bot.bot.{u3} (Filter.{u3} γ) (CompleteLattice.toHasBot.{u3} (Filter.{u3} γ) (Filter.completeLattice.{u3} γ)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {g : Filter.{u1} β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m (Bot.bot.{u2} (Filter.{u2} α) (CompleteLattice.toBot.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) g) (Bot.bot.{u3} (Filter.{u3} γ) (CompleteLattice.toBot.{u3} (Filter.{u3} γ) (Filter.instCompleteLatticeFilter.{u3} γ)))
Case conversion may be inaccurate. Consider using '#align filter.map₂_bot_left Filter.map₂_bot_leftₓ'. -/
@[simp]
theorem map₂_bot_left : map₂ m ⊥ g = ⊥ :=
  empty_mem_iff_bot.1 ⟨∅, univ, trivial, univ_mem, image2_empty_left.Subset⟩
#align filter.map₂_bot_left Filter.map₂_bot_left

/- warning: filter.map₂_bot_right -> Filter.map₂_bot_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m f (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toHasBot.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β)))) (Bot.bot.{u3} (Filter.{u3} γ) (CompleteLattice.toHasBot.{u3} (Filter.{u3} γ) (Filter.completeLattice.{u3} γ)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m f (Bot.bot.{u1} (Filter.{u1} β) (CompleteLattice.toBot.{u1} (Filter.{u1} β) (Filter.instCompleteLatticeFilter.{u1} β)))) (Bot.bot.{u3} (Filter.{u3} γ) (CompleteLattice.toBot.{u3} (Filter.{u3} γ) (Filter.instCompleteLatticeFilter.{u3} γ)))
Case conversion may be inaccurate. Consider using '#align filter.map₂_bot_right Filter.map₂_bot_rightₓ'. -/
@[simp]
theorem map₂_bot_right : map₂ m f ⊥ = ⊥ :=
  empty_mem_iff_bot.1 ⟨univ, ∅, univ_mem, trivial, image2_empty_right.Subset⟩
#align filter.map₂_bot_right Filter.map₂_bot_right

/- warning: filter.map₂_eq_bot_iff -> Filter.map₂_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β}, Iff (Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m f g) (Bot.bot.{u3} (Filter.{u3} γ) (CompleteLattice.toHasBot.{u3} (Filter.{u3} γ) (Filter.completeLattice.{u3} γ)))) (Or (Eq.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Eq.{succ u2} (Filter.{u2} β) g (Bot.bot.{u2} (Filter.{u2} β) (CompleteLattice.toHasBot.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g : Filter.{u1} β}, Iff (Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m f g) (Bot.bot.{u3} (Filter.{u3} γ) (CompleteLattice.toBot.{u3} (Filter.{u3} γ) (Filter.instCompleteLatticeFilter.{u3} γ)))) (Or (Eq.{succ u2} (Filter.{u2} α) f (Bot.bot.{u2} (Filter.{u2} α) (CompleteLattice.toBot.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)))) (Eq.{succ u1} (Filter.{u1} β) g (Bot.bot.{u1} (Filter.{u1} β) (CompleteLattice.toBot.{u1} (Filter.{u1} β) (Filter.instCompleteLatticeFilter.{u1} β)))))
Case conversion may be inaccurate. Consider using '#align filter.map₂_eq_bot_iff Filter.map₂_eq_bot_iffₓ'. -/
@[simp]
theorem map₂_eq_bot_iff : map₂ m f g = ⊥ ↔ f = ⊥ ∨ g = ⊥ :=
  by
  simp only [← empty_mem_iff_bot, mem_map₂_iff, subset_empty_iff, image2_eq_empty_iff]
  constructor
  · rintro ⟨s, t, hs, ht, rfl | rfl⟩
    · exact Or.inl hs
    · exact Or.inr ht
  · rintro (h | h)
    · exact ⟨_, _, h, univ_mem, Or.inl rfl⟩
    · exact ⟨_, _, univ_mem, h, Or.inr rfl⟩
#align filter.map₂_eq_bot_iff Filter.map₂_eq_bot_iff

/- warning: filter.map₂_ne_bot_iff -> Filter.map₂_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β}, Iff (Filter.NeBot.{u3} γ (Filter.map₂.{u1, u2, u3} α β γ m f g)) (And (Filter.NeBot.{u1} α f) (Filter.NeBot.{u2} β g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g : Filter.{u1} β}, Iff (Filter.NeBot.{u3} γ (Filter.map₂.{u2, u1, u3} α β γ m f g)) (And (Filter.NeBot.{u2} α f) (Filter.NeBot.{u1} β g))
Case conversion may be inaccurate. Consider using '#align filter.map₂_ne_bot_iff Filter.map₂_neBot_iffₓ'. -/
@[simp]
theorem map₂_neBot_iff : (map₂ m f g).ne_bot ↔ f.ne_bot ∧ g.ne_bot :=
  by
  simp_rw [ne_bot_iff]
  exact map₂_eq_bot_iff.not.trans not_or
#align filter.map₂_ne_bot_iff Filter.map₂_neBot_iff

/- warning: filter.ne_bot.map₂ -> Filter.NeBot.map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β}, (Filter.NeBot.{u1} α f) -> (Filter.NeBot.{u2} β g) -> (Filter.NeBot.{u3} γ (Filter.map₂.{u1, u2, u3} α β γ m f g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : α -> β -> γ} {f : Filter.{u3} α} {g : Filter.{u2} β}, (Filter.NeBot.{u3} α f) -> (Filter.NeBot.{u2} β g) -> (Filter.NeBot.{u1} γ (Filter.map₂.{u3, u2, u1} α β γ m f g))
Case conversion may be inaccurate. Consider using '#align filter.ne_bot.map₂ Filter.NeBot.map₂ₓ'. -/
theorem NeBot.map₂ (hf : f.ne_bot) (hg : g.ne_bot) : (map₂ m f g).ne_bot :=
  map₂_neBot_iff.2 ⟨hf, hg⟩
#align filter.ne_bot.map₂ Filter.NeBot.map₂

/- warning: filter.ne_bot.of_map₂_left -> Filter.NeBot.of_map₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β}, (Filter.NeBot.{u3} γ (Filter.map₂.{u1, u2, u3} α β γ m f g)) -> (Filter.NeBot.{u1} α f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g : Filter.{u1} β}, (Filter.NeBot.{u3} γ (Filter.map₂.{u2, u1, u3} α β γ m f g)) -> (Filter.NeBot.{u2} α f)
Case conversion may be inaccurate. Consider using '#align filter.ne_bot.of_map₂_left Filter.NeBot.of_map₂_leftₓ'. -/
theorem NeBot.of_map₂_left (h : (map₂ m f g).ne_bot) : f.ne_bot :=
  (map₂_neBot_iff.1 h).1
#align filter.ne_bot.of_map₂_left Filter.NeBot.of_map₂_left

/- warning: filter.ne_bot.of_map₂_right -> Filter.NeBot.of_map₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β}, (Filter.NeBot.{u3} γ (Filter.map₂.{u1, u2, u3} α β γ m f g)) -> (Filter.NeBot.{u2} β g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g : Filter.{u1} β}, (Filter.NeBot.{u3} γ (Filter.map₂.{u2, u1, u3} α β γ m f g)) -> (Filter.NeBot.{u1} β g)
Case conversion may be inaccurate. Consider using '#align filter.ne_bot.of_map₂_right Filter.NeBot.of_map₂_rightₓ'. -/
theorem NeBot.of_map₂_right (h : (map₂ m f g).ne_bot) : g.ne_bot :=
  (map₂_neBot_iff.1 h).2
#align filter.ne_bot.of_map₂_right Filter.NeBot.of_map₂_right

/- warning: filter.map₂_sup_left -> Filter.map₂_sup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {g : Filter.{u2} β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f₁ f₂) g) (HasSup.sup.{u3} (Filter.{u3} γ) (SemilatticeSup.toHasSup.{u3} (Filter.{u3} γ) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} γ) (ConditionallyCompleteLattice.toLattice.{u3} (Filter.{u3} γ) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} γ) (Filter.completeLattice.{u3} γ))))) (Filter.map₂.{u1, u2, u3} α β γ m f₁ g) (Filter.map₂.{u1, u2, u3} α β γ m f₂ g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f₁ : Filter.{u2} α} {f₂ : Filter.{u2} α} {g : Filter.{u1} β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m (HasSup.sup.{u2} (Filter.{u2} α) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} α) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} α) (CompleteLattice.toLattice.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α)))) f₁ f₂) g) (HasSup.sup.{u3} (Filter.{u3} γ) (SemilatticeSup.toHasSup.{u3} (Filter.{u3} γ) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} γ) (CompleteLattice.toLattice.{u3} (Filter.{u3} γ) (Filter.instCompleteLatticeFilter.{u3} γ)))) (Filter.map₂.{u2, u1, u3} α β γ m f₁ g) (Filter.map₂.{u2, u1, u3} α β γ m f₂ g))
Case conversion may be inaccurate. Consider using '#align filter.map₂_sup_left Filter.map₂_sup_leftₓ'. -/
theorem map₂_sup_left : map₂ m (f₁ ⊔ f₂) g = map₂ m f₁ g ⊔ map₂ m f₂ g :=
  by
  ext u
  constructor
  · rintro ⟨s, t, ⟨h₁, h₂⟩, ht, hu⟩
    exact ⟨mem_of_superset (image2_mem_map₂ h₁ ht) hu, mem_of_superset (image2_mem_map₂ h₂ ht) hu⟩
  · rintro ⟨⟨s₁, t₁, hs₁, ht₁, hu₁⟩, s₂, t₂, hs₂, ht₂, hu₂⟩
    refine' ⟨s₁ ∪ s₂, t₁ ∩ t₂, union_mem_sup hs₁ hs₂, inter_mem ht₁ ht₂, _⟩
    rw [image2_union_left]
    exact
      union_subset ((image2_subset_left <| inter_subset_left _ _).trans hu₁)
        ((image2_subset_left <| inter_subset_right _ _).trans hu₂)
#align filter.map₂_sup_left Filter.map₂_sup_left

/- warning: filter.map₂_sup_right -> Filter.map₂_sup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m f (HasSup.sup.{u2} (Filter.{u2} β) (SemilatticeSup.toHasSup.{u2} (Filter.{u2} β) (Lattice.toSemilatticeSup.{u2} (Filter.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (Filter.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} β) (Filter.completeLattice.{u2} β))))) g₁ g₂)) (HasSup.sup.{u3} (Filter.{u3} γ) (SemilatticeSup.toHasSup.{u3} (Filter.{u3} γ) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} γ) (ConditionallyCompleteLattice.toLattice.{u3} (Filter.{u3} γ) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Filter.{u3} γ) (Filter.completeLattice.{u3} γ))))) (Filter.map₂.{u1, u2, u3} α β γ m f g₁) (Filter.map₂.{u1, u2, u3} α β γ m f g₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g₁ : Filter.{u1} β} {g₂ : Filter.{u1} β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m f (HasSup.sup.{u1} (Filter.{u1} β) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} β) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} β) (CompleteLattice.toLattice.{u1} (Filter.{u1} β) (Filter.instCompleteLatticeFilter.{u1} β)))) g₁ g₂)) (HasSup.sup.{u3} (Filter.{u3} γ) (SemilatticeSup.toHasSup.{u3} (Filter.{u3} γ) (Lattice.toSemilatticeSup.{u3} (Filter.{u3} γ) (CompleteLattice.toLattice.{u3} (Filter.{u3} γ) (Filter.instCompleteLatticeFilter.{u3} γ)))) (Filter.map₂.{u2, u1, u3} α β γ m f g₁) (Filter.map₂.{u2, u1, u3} α β γ m f g₂))
Case conversion may be inaccurate. Consider using '#align filter.map₂_sup_right Filter.map₂_sup_rightₓ'. -/
theorem map₂_sup_right : map₂ m f (g₁ ⊔ g₂) = map₂ m f g₁ ⊔ map₂ m f g₂ :=
  by
  ext u
  constructor
  · rintro ⟨s, t, hs, ⟨h₁, h₂⟩, hu⟩
    exact ⟨mem_of_superset (image2_mem_map₂ hs h₁) hu, mem_of_superset (image2_mem_map₂ hs h₂) hu⟩
  · rintro ⟨⟨s₁, t₁, hs₁, ht₁, hu₁⟩, s₂, t₂, hs₂, ht₂, hu₂⟩
    refine' ⟨s₁ ∩ s₂, t₁ ∪ t₂, inter_mem hs₁ hs₂, union_mem_sup ht₁ ht₂, _⟩
    rw [image2_union_right]
    exact
      union_subset ((image2_subset_right <| inter_subset_left _ _).trans hu₁)
        ((image2_subset_right <| inter_subset_right _ _).trans hu₂)
#align filter.map₂_sup_right Filter.map₂_sup_right

/- warning: filter.map₂_inf_subset_left -> Filter.map₂_inf_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f₁ : Filter.{u1} α} {f₂ : Filter.{u1} α} {g : Filter.{u2} β}, LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ))) (Filter.map₂.{u1, u2, u3} α β γ m (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) f₁ f₂) g) (HasInf.inf.{u3} (Filter.{u3} γ) (Filter.hasInf.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m f₁ g) (Filter.map₂.{u1, u2, u3} α β γ m f₂ g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f₁ : Filter.{u2} α} {f₂ : Filter.{u2} α} {g : Filter.{u1} β}, LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.instPartialOrderFilter.{u3} γ))) (Filter.map₂.{u2, u1, u3} α β γ m (HasInf.inf.{u2} (Filter.{u2} α) (Filter.instHasInfFilter.{u2} α) f₁ f₂) g) (HasInf.inf.{u3} (Filter.{u3} γ) (Filter.instHasInfFilter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m f₁ g) (Filter.map₂.{u2, u1, u3} α β γ m f₂ g))
Case conversion may be inaccurate. Consider using '#align filter.map₂_inf_subset_left Filter.map₂_inf_subset_leftₓ'. -/
theorem map₂_inf_subset_left : map₂ m (f₁ ⊓ f₂) g ≤ map₂ m f₁ g ⊓ map₂ m f₂ g :=
  le_inf (map₂_mono_right inf_le_left) (map₂_mono_right inf_le_right)
#align filter.map₂_inf_subset_left Filter.map₂_inf_subset_left

/- warning: filter.map₂_inf_subset_right -> Filter.map₂_inf_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g₁ : Filter.{u2} β} {g₂ : Filter.{u2} β}, LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.partialOrder.{u3} γ))) (Filter.map₂.{u1, u2, u3} α β γ m f (HasInf.inf.{u2} (Filter.{u2} β) (Filter.hasInf.{u2} β) g₁ g₂)) (HasInf.inf.{u3} (Filter.{u3} γ) (Filter.hasInf.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m f g₁) (Filter.map₂.{u1, u2, u3} α β γ m f g₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g₁ : Filter.{u1} β} {g₂ : Filter.{u1} β}, LE.le.{u3} (Filter.{u3} γ) (Preorder.toLE.{u3} (Filter.{u3} γ) (PartialOrder.toPreorder.{u3} (Filter.{u3} γ) (Filter.instPartialOrderFilter.{u3} γ))) (Filter.map₂.{u2, u1, u3} α β γ m f (HasInf.inf.{u1} (Filter.{u1} β) (Filter.instHasInfFilter.{u1} β) g₁ g₂)) (HasInf.inf.{u3} (Filter.{u3} γ) (Filter.instHasInfFilter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m f g₁) (Filter.map₂.{u2, u1, u3} α β γ m f g₂))
Case conversion may be inaccurate. Consider using '#align filter.map₂_inf_subset_right Filter.map₂_inf_subset_rightₓ'. -/
theorem map₂_inf_subset_right : map₂ m f (g₁ ⊓ g₂) ≤ map₂ m f g₁ ⊓ map₂ m f g₂ :=
  le_inf (map₂_mono_left inf_le_left) (map₂_mono_left inf_le_right)
#align filter.map₂_inf_subset_right Filter.map₂_inf_subset_right

/- warning: filter.map₂_pure_left -> Filter.map₂_pure_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {g : Filter.{u2} β} {a : α}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a) g) (Filter.map.{u2, u3} β γ (fun (b : β) => m a b) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {g : Filter.{u1} β} {a : α}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m (Pure.pure.{u2, u2} Filter.{u2} Filter.instPureFilter.{u2} α a) g) (Filter.map.{u1, u3} β γ (fun (b : β) => m a b) g)
Case conversion may be inaccurate. Consider using '#align filter.map₂_pure_left Filter.map₂_pure_leftₓ'. -/
@[simp]
theorem map₂_pure_left : map₂ m (pure a) g = g.map fun b => m a b :=
  Filter.ext fun u =>
    ⟨fun ⟨s, t, hs, ht, hu⟩ =>
      mem_of_superset (image_mem_map ht) ((image_subset_image2_right <| mem_pure.1 hs).trans hu),
      fun h => ⟨{a}, _, singleton_mem_pure, h, by rw [image2_singleton_left, image_subset_iff]⟩⟩
#align filter.map₂_pure_left Filter.map₂_pure_left

/- warning: filter.map₂_pure_right -> Filter.map₂_pure_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {b : β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m f (Pure.pure.{u2, u2} Filter.{u2} Filter.hasPure.{u2} β b)) (Filter.map.{u1, u3} α γ (fun (a : α) => m a b) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {b : β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m f (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} β b)) (Filter.map.{u2, u3} α γ (fun (a : α) => m a b) f)
Case conversion may be inaccurate. Consider using '#align filter.map₂_pure_right Filter.map₂_pure_rightₓ'. -/
@[simp]
theorem map₂_pure_right : map₂ m f (pure b) = f.map fun a => m a b :=
  Filter.ext fun u =>
    ⟨fun ⟨s, t, hs, ht, hu⟩ =>
      mem_of_superset (image_mem_map hs) ((image_subset_image2_left <| mem_pure.1 ht).trans hu),
      fun h => ⟨_, {b}, h, singleton_mem_pure, by rw [image2_singleton_right, image_subset_iff]⟩⟩
#align filter.map₂_pure_right Filter.map₂_pure_right

/- warning: filter.map₂_pure -> Filter.map₂_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {a : α} {b : β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a) (Pure.pure.{u2, u2} Filter.{u2} Filter.hasPure.{u2} β b)) (Pure.pure.{u3, u3} Filter.{u3} Filter.hasPure.{u3} γ (m a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {a : α} {b : β}, Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m (Pure.pure.{u2, u2} Filter.{u2} Filter.instPureFilter.{u2} α a) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} β b)) (Pure.pure.{u3, u3} Filter.{u3} Filter.instPureFilter.{u3} γ (m a b))
Case conversion may be inaccurate. Consider using '#align filter.map₂_pure Filter.map₂_pureₓ'. -/
theorem map₂_pure : map₂ m (pure a) (pure b) = pure (m a b) := by rw [map₂_pure_right, map_pure]
#align filter.map₂_pure Filter.map₂_pure

/- warning: filter.map₂_swap -> Filter.map₂_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : α -> β -> γ) (f : Filter.{u1} α) (g : Filter.{u2} β), Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m f g) (Filter.map₂.{u2, u1, u3} β α γ (fun (a : β) (b : α) => m b a) g f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (m : α -> β -> γ) (f : Filter.{u3} α) (g : Filter.{u2} β), Eq.{succ u1} (Filter.{u1} γ) (Filter.map₂.{u3, u2, u1} α β γ m f g) (Filter.map₂.{u2, u3, u1} β α γ (fun (a : β) (b : α) => m b a) g f)
Case conversion may be inaccurate. Consider using '#align filter.map₂_swap Filter.map₂_swapₓ'. -/
theorem map₂_swap (m : α → β → γ) (f : Filter α) (g : Filter β) :
    map₂ m f g = map₂ (fun a b => m b a) g f :=
  by
  ext u
  constructor <;> rintro ⟨s, t, hs, ht, hu⟩ <;> refine' ⟨t, s, ht, hs, by rwa [image2_swap]⟩
#align filter.map₂_swap Filter.map₂_swap

#print Filter.map₂_left /-
@[simp]
theorem map₂_left (h : g.ne_bot) : map₂ (fun x y => x) f g = f :=
  by
  ext u
  refine' ⟨_, fun hu => ⟨_, _, hu, univ_mem, (image2_left <| h.nonempty_of_mem univ_mem).Subset⟩⟩
  rintro ⟨s, t, hs, ht, hu⟩
  rw [image2_left (h.nonempty_of_mem ht)] at hu
  exact mem_of_superset hs hu
#align filter.map₂_left Filter.map₂_left
-/

/- warning: filter.map₂_right -> Filter.map₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Filter.{u1} α} {g : Filter.{u2} β}, (Filter.NeBot.{u1} α f) -> (Eq.{succ u2} (Filter.{u2} β) (Filter.map₂.{u1, u2, u2} α β β (fun (x : α) (y : β) => y) f g) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Filter.{u2} α} {g : Filter.{u1} β}, (Filter.NeBot.{u2} α f) -> (Eq.{succ u1} (Filter.{u1} β) (Filter.map₂.{u2, u1, u1} α β β (fun (x : α) (y : β) => y) f g) g)
Case conversion may be inaccurate. Consider using '#align filter.map₂_right Filter.map₂_rightₓ'. -/
@[simp]
theorem map₂_right (h : f.ne_bot) : map₂ (fun x y => y) f g = g := by rw [map₂_swap, map₂_left h]
#align filter.map₂_right Filter.map₂_right

#print Filter.map₃ /-
/-- The image of a ternary function `m : α → β → γ → δ` as a function
`filter α → filter β → filter γ → filter δ`. Mathematically this should be thought of as the image
of the corresponding function `α × β × γ → δ`. -/
def map₃ (m : α → β → γ → δ) (f : Filter α) (g : Filter β) (h : Filter γ) : Filter δ
    where
  sets := { s | ∃ u v w, u ∈ f ∧ v ∈ g ∧ w ∈ h ∧ image3 m u v w ⊆ s }
  univ_sets := ⟨univ, univ, univ, univ_sets _, univ_sets _, univ_sets _, subset_univ _⟩
  sets_of_superset s t hs hst :=
    Exists₃Cat.imp
      (fun u v w => And.imp_right <| And.imp_right <| And.imp_right fun h => Subset.trans h hst) hs
  inter_sets s t := by
    simp only [exists_prop, mem_set_of_eq, subset_inter_iff]
    rintro ⟨s₁, s₂, s₃, hs₁, hs₂, hs₃, hs⟩ ⟨t₁, t₂, t₃, ht₁, ht₂, ht₃, ht⟩
    exact
      ⟨s₁ ∩ t₁, s₂ ∩ t₂, s₃ ∩ t₃, inter_mem hs₁ ht₁, inter_mem hs₂ ht₂, inter_mem hs₃ ht₃,
        (image3_mono (inter_subset_left _ _) (inter_subset_left _ _) <| inter_subset_left _ _).trans
          hs,
        (image3_mono (inter_subset_right _ _) (inter_subset_right _ _) <|
              inter_subset_right _ _).trans
          ht⟩
#align filter.map₃ Filter.map₃
-/

/- warning: filter.map₂_map₂_left -> Filter.map₂_map₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {f : Filter.{u1} α} {g : Filter.{u2} β} {h : Filter.{u3} γ} (m : δ -> γ -> ε) (n : α -> β -> δ), Eq.{succ u5} (Filter.{u5} ε) (Filter.map₂.{u4, u3, u5} δ γ ε m (Filter.map₂.{u1, u2, u4} α β δ n f g) h) (Filter.map₃.{u1, u2, u3, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => m (n a b) c) f g h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {f : Filter.{u2} α} {g : Filter.{u1} β} {h : Filter.{u3} γ} (m : δ -> γ -> ε) (n : α -> β -> δ), Eq.{succ u5} (Filter.{u5} ε) (Filter.map₂.{u4, u3, u5} δ γ ε m (Filter.map₂.{u2, u1, u4} α β δ n f g) h) (Filter.map₃.{u2, u1, u3, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => m (n a b) c) f g h)
Case conversion may be inaccurate. Consider using '#align filter.map₂_map₂_left Filter.map₂_map₂_leftₓ'. -/
theorem map₂_map₂_left (m : δ → γ → ε) (n : α → β → δ) :
    map₂ m (map₂ n f g) h = map₃ (fun a b c => m (n a b) c) f g h :=
  by
  ext w
  constructor
  · rintro ⟨s, t, ⟨u, v, hu, hv, hs⟩, ht, hw⟩
    refine' ⟨u, v, t, hu, hv, ht, _⟩
    rw [← image2_image2_left]
    exact (image2_subset_right hs).trans hw
  · rintro ⟨s, t, u, hs, ht, hu, hw⟩
    exact ⟨_, u, image2_mem_map₂ hs ht, hu, by rwa [image2_image2_left]⟩
#align filter.map₂_map₂_left Filter.map₂_map₂_left

/- warning: filter.map₂_map₂_right -> Filter.map₂_map₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {f : Filter.{u1} α} {g : Filter.{u2} β} {h : Filter.{u3} γ} (m : α -> δ -> ε) (n : β -> γ -> δ), Eq.{succ u5} (Filter.{u5} ε) (Filter.map₂.{u1, u4, u5} α δ ε m f (Filter.map₂.{u2, u3, u4} β γ δ n g h)) (Filter.map₃.{u1, u2, u3, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => m a (n b c)) f g h)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u3}} {ε : Type.{u5}} {f : Filter.{u4} α} {g : Filter.{u2} β} {h : Filter.{u1} γ} (m : α -> δ -> ε) (n : β -> γ -> δ), Eq.{succ u5} (Filter.{u5} ε) (Filter.map₂.{u4, u3, u5} α δ ε m f (Filter.map₂.{u2, u1, u3} β γ δ n g h)) (Filter.map₃.{u4, u2, u1, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => m a (n b c)) f g h)
Case conversion may be inaccurate. Consider using '#align filter.map₂_map₂_right Filter.map₂_map₂_rightₓ'. -/
theorem map₂_map₂_right (m : α → δ → ε) (n : β → γ → δ) :
    map₂ m f (map₂ n g h) = map₃ (fun a b c => m a (n b c)) f g h :=
  by
  ext w
  constructor
  · rintro ⟨s, t, hs, ⟨u, v, hu, hv, ht⟩, hw⟩
    refine' ⟨s, u, v, hs, hu, hv, _⟩
    rw [← image2_image2_right]
    exact (image2_subset_left ht).trans hw
  · rintro ⟨s, t, u, hs, ht, hu, hw⟩
    exact ⟨s, _, hs, image2_mem_map₂ ht hu, by rwa [image2_image2_right]⟩
#align filter.map₂_map₂_right Filter.map₂_map₂_right

/- warning: filter.map_map₂ -> Filter.map_map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {f : Filter.{u1} α} {g : Filter.{u2} β} (m : α -> β -> γ) (n : γ -> δ), Eq.{succ u4} (Filter.{u4} δ) (Filter.map.{u3, u4} γ δ n (Filter.map₂.{u1, u2, u3} α β γ m f g)) (Filter.map₂.{u1, u2, u4} α β δ (fun (a : α) (b : β) => n (m a b)) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Type.{u4}} {f : Filter.{u2} α} {g : Filter.{u1} β} (m : α -> β -> γ) (n : γ -> δ), Eq.{succ u4} (Filter.{u4} δ) (Filter.map.{u3, u4} γ δ n (Filter.map₂.{u2, u1, u3} α β γ m f g)) (Filter.map₂.{u2, u1, u4} α β δ (fun (a : α) (b : β) => n (m a b)) f g)
Case conversion may be inaccurate. Consider using '#align filter.map_map₂ Filter.map_map₂ₓ'. -/
theorem map_map₂ (m : α → β → γ) (n : γ → δ) :
    (map₂ m f g).map n = map₂ (fun a b => n (m a b)) f g :=
  Filter.ext fun u => exists₂_congr fun s t => by rw [← image_subset_iff, image_image2]
#align filter.map_map₂ Filter.map_map₂

#print Filter.map₂_map_left /-
theorem map₂_map_left (m : γ → β → δ) (n : α → γ) :
    map₂ m (f.map n) g = map₂ (fun a b => m (n a) b) f g :=
  by
  ext u
  constructor
  · rintro ⟨s, t, hs, ht, hu⟩
    refine' ⟨_, t, hs, ht, _⟩
    rw [← image2_image_left]
    exact (image2_subset_right <| image_preimage_subset _ _).trans hu
  · rintro ⟨s, t, hs, ht, hu⟩
    exact ⟨_, t, image_mem_map hs, ht, by rwa [image2_image_left]⟩
#align filter.map₂_map_left Filter.map₂_map_left
-/

/- warning: filter.map₂_map_right -> Filter.map₂_map_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {f : Filter.{u1} α} {g : Filter.{u2} β} (m : α -> γ -> δ) (n : β -> γ), Eq.{succ u4} (Filter.{u4} δ) (Filter.map₂.{u1, u3, u4} α γ δ m f (Filter.map.{u2, u3} β γ n g)) (Filter.map₂.{u1, u2, u4} α β δ (fun (a : α) (b : β) => m a (n b)) f g)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {δ : Type.{u4}} {f : Filter.{u3} α} {g : Filter.{u1} β} (m : α -> γ -> δ) (n : β -> γ), Eq.{succ u4} (Filter.{u4} δ) (Filter.map₂.{u3, u2, u4} α γ δ m f (Filter.map.{u1, u2} β γ n g)) (Filter.map₂.{u3, u1, u4} α β δ (fun (a : α) (b : β) => m a (n b)) f g)
Case conversion may be inaccurate. Consider using '#align filter.map₂_map_right Filter.map₂_map_rightₓ'. -/
theorem map₂_map_right (m : α → γ → δ) (n : β → γ) :
    map₂ m f (g.map n) = map₂ (fun a b => m a (n b)) f g := by
  rw [map₂_swap, map₂_map_left, map₂_swap]
#align filter.map₂_map_right Filter.map₂_map_right

/- warning: filter.map₂_curry -> Filter.map₂_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : (Prod.{u1, u2} α β) -> γ) (f : Filter.{u1} α) (g : Filter.{u2} β), Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ (Function.curry.{u1, u2, u3} α β γ m) f g) (Filter.map.{max u1 u2, u3} (Prod.{u1, u2} α β) γ m (Filter.prod.{u1, u2} α β f g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (m : (Prod.{u3, u2} α β) -> γ) (f : Filter.{u3} α) (g : Filter.{u2} β), Eq.{succ u1} (Filter.{u1} γ) (Filter.map₂.{u3, u2, u1} α β γ (Function.curry.{u3, u2, u1} α β γ m) f g) (Filter.map.{max u3 u2, u1} (Prod.{u3, u2} α β) γ m (Filter.prod.{u3, u2} α β f g))
Case conversion may be inaccurate. Consider using '#align filter.map₂_curry Filter.map₂_curryₓ'. -/
@[simp]
theorem map₂_curry (m : α × β → γ) (f : Filter α) (g : Filter β) :
    map₂ (curry m) f g = (f ×ᶠ g).map m := by classical rw [← map₂_mk_eq_prod, map_map₂, curry]
#align filter.map₂_curry Filter.map₂_curry

/- warning: filter.map_uncurry_prod -> Filter.map_uncurry_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (m : α -> β -> γ) (f : Filter.{u1} α) (g : Filter.{u2} β), Eq.{succ u3} (Filter.{u3} γ) (Filter.map.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Function.uncurry.{u1, u2, u3} α β γ m) (Filter.prod.{u1, u2} α β f g)) (Filter.map₂.{u1, u2, u3} α β γ m f g)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (m : α -> β -> γ) (f : Filter.{u3} α) (g : Filter.{u2} β), Eq.{succ u1} (Filter.{u1} γ) (Filter.map.{max u2 u3, u1} (Prod.{u3, u2} α β) γ (Function.uncurry.{u3, u2, u1} α β γ m) (Filter.prod.{u3, u2} α β f g)) (Filter.map₂.{u3, u2, u1} α β γ m f g)
Case conversion may be inaccurate. Consider using '#align filter.map_uncurry_prod Filter.map_uncurry_prodₓ'. -/
@[simp]
theorem map_uncurry_prod (m : α → β → γ) (f : Filter α) (g : Filter β) :
    (f ×ᶠ g).map (uncurry m) = map₂ m f g := by rw [← map₂_curry, curry_uncurry]
#align filter.map_uncurry_prod Filter.map_uncurry_prod

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `filter.map₂` of those operations.

The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) f g = map₂ (*) g f` in a `comm_semigroup`.
-/


/- warning: filter.map₂_assoc -> Filter.map₂_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {ε' : Type.{u6}} {f : Filter.{u1} α} {g : Filter.{u2} β} {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> ε' -> ε} {n' : β -> γ -> ε'} {h : Filter.{u3} γ}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (m (n a b) c) (m' a (n' b c))) -> (Eq.{succ u5} (Filter.{u5} ε) (Filter.map₂.{u4, u3, u5} δ γ ε m (Filter.map₂.{u1, u2, u4} α β δ n f g) h) (Filter.map₂.{u1, u6, u5} α ε' ε m' f (Filter.map₂.{u2, u3, u6} β γ ε' n' g h)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u6}} {δ : Type.{u4}} {ε : Type.{u5}} {ε' : Type.{u1}} {f : Filter.{u3} α} {g : Filter.{u2} β} {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> ε' -> ε} {n' : β -> γ -> ε'} {h : Filter.{u6} γ}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (m (n a b) c) (m' a (n' b c))) -> (Eq.{succ u5} (Filter.{u5} ε) (Filter.map₂.{u4, u6, u5} δ γ ε m (Filter.map₂.{u3, u2, u4} α β δ n f g) h) (Filter.map₂.{u3, u1, u5} α ε' ε m' f (Filter.map₂.{u2, u6, u1} β γ ε' n' g h)))
Case conversion may be inaccurate. Consider using '#align filter.map₂_assoc Filter.map₂_assocₓ'. -/
theorem map₂_assoc {m : δ → γ → ε} {n : α → β → δ} {m' : α → ε' → ε} {n' : β → γ → ε'}
    {h : Filter γ} (h_assoc : ∀ a b c, m (n a b) c = m' a (n' b c)) :
    map₂ m (map₂ n f g) h = map₂ m' f (map₂ n' g h) := by
  simp only [map₂_map₂_left, map₂_map₂_right, h_assoc]
#align filter.map₂_assoc Filter.map₂_assoc

/- warning: filter.map₂_comm -> Filter.map₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β} {n : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u3} γ (m a b) (n b a)) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u1, u2, u3} α β γ m f g) (Filter.map₂.{u2, u1, u3} β α γ n g f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {m : α -> β -> γ} {f : Filter.{u2} α} {g : Filter.{u1} β} {n : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u3} γ (m a b) (n b a)) -> (Eq.{succ u3} (Filter.{u3} γ) (Filter.map₂.{u2, u1, u3} α β γ m f g) (Filter.map₂.{u1, u2, u3} β α γ n g f))
Case conversion may be inaccurate. Consider using '#align filter.map₂_comm Filter.map₂_commₓ'. -/
theorem map₂_comm {n : β → α → γ} (h_comm : ∀ a b, m a b = n b a) : map₂ m f g = map₂ n g f :=
  (map₂_swap _ _ _).trans <| by simp_rw [h_comm]
#align filter.map₂_comm Filter.map₂_comm

/- warning: filter.map₂_left_comm -> Filter.map₂_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {δ' : Type.{u5}} {ε : Type.{u6}} {f : Filter.{u1} α} {g : Filter.{u2} β} {h : Filter.{u3} γ} {m : α -> δ -> ε} {n : β -> γ -> δ} {m' : α -> γ -> δ'} {n' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (m a (n b c)) (n' b (m' a c))) -> (Eq.{succ u6} (Filter.{u6} ε) (Filter.map₂.{u1, u4, u6} α δ ε m f (Filter.map₂.{u2, u3, u4} β γ δ n g h)) (Filter.map₂.{u2, u5, u6} β δ' ε n' g (Filter.map₂.{u1, u3, u5} α γ δ' m' f h)))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u4}} {δ' : Type.{u1}} {ε : Type.{u6}} {f : Filter.{u5} α} {g : Filter.{u3} β} {h : Filter.{u2} γ} {m : α -> δ -> ε} {n : β -> γ -> δ} {m' : α -> γ -> δ'} {n' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (m a (n b c)) (n' b (m' a c))) -> (Eq.{succ u6} (Filter.{u6} ε) (Filter.map₂.{u5, u4, u6} α δ ε m f (Filter.map₂.{u3, u2, u4} β γ δ n g h)) (Filter.map₂.{u3, u1, u6} β δ' ε n' g (Filter.map₂.{u5, u2, u1} α γ δ' m' f h)))
Case conversion may be inaccurate. Consider using '#align filter.map₂_left_comm Filter.map₂_left_commₓ'. -/
theorem map₂_left_comm {m : α → δ → ε} {n : β → γ → δ} {m' : α → γ → δ'} {n' : β → δ' → ε}
    (h_left_comm : ∀ a b c, m a (n b c) = n' b (m' a c)) :
    map₂ m f (map₂ n g h) = map₂ n' g (map₂ m' f h) :=
  by
  rw [map₂_swap m', map₂_swap m]
  exact map₂_assoc fun _ _ _ => h_left_comm _ _ _
#align filter.map₂_left_comm Filter.map₂_left_comm

/- warning: filter.map₂_right_comm -> Filter.map₂_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {δ' : Type.{u5}} {ε : Type.{u6}} {f : Filter.{u1} α} {g : Filter.{u2} β} {h : Filter.{u3} γ} {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> γ -> δ'} {n' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (m (n a b) c) (n' (m' a c) b)) -> (Eq.{succ u6} (Filter.{u6} ε) (Filter.map₂.{u4, u3, u6} δ γ ε m (Filter.map₂.{u1, u2, u4} α β δ n f g) h) (Filter.map₂.{u5, u2, u6} δ' β ε n' (Filter.map₂.{u1, u3, u5} α γ δ' m' f h) g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} {δ' : Type.{u1}} {ε : Type.{u6}} {f : Filter.{u3} α} {g : Filter.{u2} β} {h : Filter.{u4} γ} {m : δ -> γ -> ε} {n : α -> β -> δ} {m' : α -> γ -> δ'} {n' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (m (n a b) c) (n' (m' a c) b)) -> (Eq.{succ u6} (Filter.{u6} ε) (Filter.map₂.{u5, u4, u6} δ γ ε m (Filter.map₂.{u3, u2, u5} α β δ n f g) h) (Filter.map₂.{u1, u2, u6} δ' β ε n' (Filter.map₂.{u3, u4, u1} α γ δ' m' f h) g))
Case conversion may be inaccurate. Consider using '#align filter.map₂_right_comm Filter.map₂_right_commₓ'. -/
theorem map₂_right_comm {m : δ → γ → ε} {n : α → β → δ} {m' : α → γ → δ'} {n' : δ' → β → ε}
    (h_right_comm : ∀ a b c, m (n a b) c = n' (m' a c) b) :
    map₂ m (map₂ n f g) h = map₂ n' (map₂ m' f h) g :=
  by
  rw [map₂_swap n, map₂_swap n']
  exact map₂_assoc fun _ _ _ => h_right_comm _ _ _
#align filter.map₂_right_comm Filter.map₂_right_comm

/- warning: filter.map_map₂_distrib -> Filter.map_map₂_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u3} β} {n : γ -> δ} {m' : α' -> β' -> δ} {n₁ : α -> α'} {n₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u6} δ (n (m a b)) (m' (n₁ a) (n₂ b))) -> (Eq.{succ u6} (Filter.{u6} δ) (Filter.map.{u5, u6} γ δ n (Filter.map₂.{u1, u3, u5} α β γ m f g)) (Filter.map₂.{u2, u4, u6} α' β' δ m' (Filter.map.{u1, u2} α α' n₁ f) (Filter.map.{u3, u4} β β' n₂ g)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u1}} {γ : Type.{u5}} {δ : Type.{u6}} {m : α -> β -> γ} {f : Filter.{u4} α} {g : Filter.{u3} β} {n : γ -> δ} {m' : α' -> β' -> δ} {n₁ : α -> α'} {n₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u6} δ (n (m a b)) (m' (n₁ a) (n₂ b))) -> (Eq.{succ u6} (Filter.{u6} δ) (Filter.map.{u5, u6} γ δ n (Filter.map₂.{u4, u3, u5} α β γ m f g)) (Filter.map₂.{u2, u1, u6} α' β' δ m' (Filter.map.{u4, u2} α α' n₁ f) (Filter.map.{u3, u1} β β' n₂ g)))
Case conversion may be inaccurate. Consider using '#align filter.map_map₂_distrib Filter.map_map₂_distribₓ'. -/
theorem map_map₂_distrib {n : γ → δ} {m' : α' → β' → δ} {n₁ : α → α'} {n₂ : β → β'}
    (h_distrib : ∀ a b, n (m a b) = m' (n₁ a) (n₂ b)) :
    (map₂ m f g).map n = map₂ m' (f.map n₁) (g.map n₂) := by
  simp_rw [map_map₂, map₂_map_left, map₂_map_right, h_distrib]
#align filter.map_map₂_distrib Filter.map_map₂_distrib

/- warning: filter.map_map₂_distrib_left -> Filter.map_map₂_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u3} β} {n : γ -> δ} {m' : α' -> β -> δ} {n' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (n (m a b)) (m' (n' a) b)) -> (Eq.{succ u5} (Filter.{u5} δ) (Filter.map.{u4, u5} γ δ n (Filter.map₂.{u1, u3, u4} α β γ m f g)) (Filter.map₂.{u2, u3, u5} α' β δ m' (Filter.map.{u1, u2} α α' n' f) g))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} {m : α -> β -> γ} {f : Filter.{u3} α} {g : Filter.{u2} β} {n : γ -> δ} {m' : α' -> β -> δ} {n' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (n (m a b)) (m' (n' a) b)) -> (Eq.{succ u5} (Filter.{u5} δ) (Filter.map.{u4, u5} γ δ n (Filter.map₂.{u3, u2, u4} α β γ m f g)) (Filter.map₂.{u1, u2, u5} α' β δ m' (Filter.map.{u3, u1} α α' n' f) g))
Case conversion may be inaccurate. Consider using '#align filter.map_map₂_distrib_left Filter.map_map₂_distrib_leftₓ'. -/
/-- Symmetric statement to `filter.map₂_map_left_comm`. -/
theorem map_map₂_distrib_left {n : γ → δ} {m' : α' → β → δ} {n' : α → α'}
    (h_distrib : ∀ a b, n (m a b) = m' (n' a) b) : (map₂ m f g).map n = map₂ m' (f.map n') g :=
  map_map₂_distrib h_distrib
#align filter.map_map₂_distrib_left Filter.map_map₂_distrib_left

/- warning: filter.map_map₂_distrib_right -> Filter.map_map₂_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β} {n : γ -> δ} {m' : α -> β' -> δ} {n' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (n (m a b)) (m' a (n' b))) -> (Eq.{succ u5} (Filter.{u5} δ) (Filter.map.{u4, u5} γ δ n (Filter.map₂.{u1, u2, u4} α β γ m f g)) (Filter.map₂.{u1, u3, u5} α β' δ m' f (Filter.map.{u2, u3} β β' n' g)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {β' : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u5}} {m : α -> β -> γ} {f : Filter.{u3} α} {g : Filter.{u2} β} {n : γ -> δ} {m' : α -> β' -> δ} {n' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (n (m a b)) (m' a (n' b))) -> (Eq.{succ u5} (Filter.{u5} δ) (Filter.map.{u4, u5} γ δ n (Filter.map₂.{u3, u2, u4} α β γ m f g)) (Filter.map₂.{u3, u1, u5} α β' δ m' f (Filter.map.{u2, u1} β β' n' g)))
Case conversion may be inaccurate. Consider using '#align filter.map_map₂_distrib_right Filter.map_map₂_distrib_rightₓ'. -/
/-- Symmetric statement to `filter.map_map₂_right_comm`. -/
theorem map_map₂_distrib_right {n : γ → δ} {m' : α → β' → δ} {n' : β → β'}
    (h_distrib : ∀ a b, n (m a b) = m' a (n' b)) : (map₂ m f g).map n = map₂ m' f (g.map n') :=
  map_map₂_distrib h_distrib
#align filter.map_map₂_distrib_right Filter.map_map₂_distrib_right

/- warning: filter.map₂_map_left_comm -> Filter.map₂_map_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : Filter.{u1} α} {g : Filter.{u3} β} {m : α' -> β -> γ} {n : α -> α'} {m' : α -> β -> δ} {n' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (m (n a) b) (n' (m' a b))) -> (Eq.{succ u4} (Filter.{u4} γ) (Filter.map₂.{u2, u3, u4} α' β γ m (Filter.map.{u1, u2} α α' n f) g) (Filter.map.{u5, u4} δ γ n' (Filter.map₂.{u1, u3, u5} α β δ m' f g)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u4}} {β : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} {f : Filter.{u2} α} {g : Filter.{u3} β} {m : α' -> β -> γ} {n : α -> α'} {m' : α -> β -> δ} {n' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (m (n a) b) (n' (m' a b))) -> (Eq.{succ u5} (Filter.{u5} γ) (Filter.map₂.{u4, u3, u5} α' β γ m (Filter.map.{u2, u4} α α' n f) g) (Filter.map.{u1, u5} δ γ n' (Filter.map₂.{u2, u3, u1} α β δ m' f g)))
Case conversion may be inaccurate. Consider using '#align filter.map₂_map_left_comm Filter.map₂_map_left_commₓ'. -/
/-- Symmetric statement to `filter.map_map₂_distrib_left`. -/
theorem map₂_map_left_comm {m : α' → β → γ} {n : α → α'} {m' : α → β → δ} {n' : δ → γ}
    (h_left_comm : ∀ a b, m (n a) b = n' (m' a b)) : map₂ m (f.map n) g = (map₂ m' f g).map n' :=
  (map_map₂_distrib_left fun a b => (h_left_comm a b).symm).symm
#align filter.map₂_map_left_comm Filter.map₂_map_left_comm

/- warning: filter.map_map₂_right_comm -> Filter.map_map₂_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : Filter.{u1} α} {g : Filter.{u2} β} {m : α -> β' -> γ} {n : β -> β'} {m' : α -> β -> δ} {n' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (m a (n b)) (n' (m' a b))) -> (Eq.{succ u4} (Filter.{u4} γ) (Filter.map₂.{u1, u3, u4} α β' γ m f (Filter.map.{u2, u3} β β' n g)) (Filter.map.{u5, u4} δ γ n' (Filter.map₂.{u1, u2, u5} α β δ m' f g)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} {f : Filter.{u4} α} {g : Filter.{u2} β} {m : α -> β' -> γ} {n : β -> β'} {m' : α -> β -> δ} {n' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (m a (n b)) (n' (m' a b))) -> (Eq.{succ u5} (Filter.{u5} γ) (Filter.map₂.{u4, u3, u5} α β' γ m f (Filter.map.{u2, u3} β β' n g)) (Filter.map.{u1, u5} δ γ n' (Filter.map₂.{u4, u2, u1} α β δ m' f g)))
Case conversion may be inaccurate. Consider using '#align filter.map_map₂_right_comm Filter.map_map₂_right_commₓ'. -/
/-- Symmetric statement to `filter.map_map₂_distrib_right`. -/
theorem map_map₂_right_comm {m : α → β' → γ} {n : β → β'} {m' : α → β → δ} {n' : δ → γ}
    (h_right_comm : ∀ a b, m a (n b) = n' (m' a b)) : map₂ m f (g.map n) = (map₂ m' f g).map n' :=
  (map_map₂_distrib_right fun a b => (h_right_comm a b).symm).symm
#align filter.map_map₂_right_comm Filter.map_map₂_right_comm

/- warning: filter.map₂_distrib_le_left -> Filter.map₂_distrib_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {γ' : Type.{u5}} {δ : Type.{u6}} {ε : Type.{u7}} {f : Filter.{u1} α} {g : Filter.{u2} β} {h : Filter.{u4} γ} {m : α -> δ -> ε} {n : β -> γ -> δ} {m₁ : α -> β -> β'} {m₂ : α -> γ -> γ'} {n' : β' -> γ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u7} ε (m a (n b c)) (n' (m₁ a b) (m₂ a c))) -> (LE.le.{u7} (Filter.{u7} ε) (Preorder.toLE.{u7} (Filter.{u7} ε) (PartialOrder.toPreorder.{u7} (Filter.{u7} ε) (Filter.partialOrder.{u7} ε))) (Filter.map₂.{u1, u6, u7} α δ ε m f (Filter.map₂.{u2, u4, u6} β γ δ n g h)) (Filter.map₂.{u3, u5, u7} β' γ' ε n' (Filter.map₂.{u1, u2, u3} α β β' m₁ f g) (Filter.map₂.{u1, u4, u5} α γ γ' m₂ f h)))
but is expected to have type
  forall {α : Type.{u6}} {β : Type.{u4}} {β' : Type.{u2}} {γ : Type.{u3}} {γ' : Type.{u1}} {δ : Type.{u5}} {ε : Type.{u7}} {f : Filter.{u6} α} {g : Filter.{u4} β} {h : Filter.{u3} γ} {m : α -> δ -> ε} {n : β -> γ -> δ} {m₁ : α -> β -> β'} {m₂ : α -> γ -> γ'} {n' : β' -> γ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u7} ε (m a (n b c)) (n' (m₁ a b) (m₂ a c))) -> (LE.le.{u7} (Filter.{u7} ε) (Preorder.toLE.{u7} (Filter.{u7} ε) (PartialOrder.toPreorder.{u7} (Filter.{u7} ε) (Filter.instPartialOrderFilter.{u7} ε))) (Filter.map₂.{u6, u5, u7} α δ ε m f (Filter.map₂.{u4, u3, u5} β γ δ n g h)) (Filter.map₂.{u2, u1, u7} β' γ' ε n' (Filter.map₂.{u6, u4, u2} α β β' m₁ f g) (Filter.map₂.{u6, u3, u1} α γ γ' m₂ f h)))
Case conversion may be inaccurate. Consider using '#align filter.map₂_distrib_le_left Filter.map₂_distrib_le_leftₓ'. -/
/-- The other direction does not hold because of the `f`-`f` cross terms on the RHS. -/
theorem map₂_distrib_le_left {m : α → δ → ε} {n : β → γ → δ} {m₁ : α → β → β'} {m₂ : α → γ → γ'}
    {n' : β' → γ' → ε} (h_distrib : ∀ a b c, m a (n b c) = n' (m₁ a b) (m₂ a c)) :
    map₂ m f (map₂ n g h) ≤ map₂ n' (map₂ m₁ f g) (map₂ m₂ f h) :=
  by
  rintro s ⟨t₁, t₂, ⟨u₁, v, hu₁, hv, ht₁⟩, ⟨u₂, w, hu₂, hw, ht₂⟩, hs⟩
  refine' ⟨u₁ ∩ u₂, _, inter_mem hu₁ hu₂, image2_mem_map₂ hv hw, _⟩
  refine' (image2_distrib_subset_left h_distrib).trans ((image2_subset _ _).trans hs)
  · exact (image2_subset_right <| inter_subset_left _ _).trans ht₁
  · exact (image2_subset_right <| inter_subset_right _ _).trans ht₂
#align filter.map₂_distrib_le_left Filter.map₂_distrib_le_left

/- warning: filter.map₂_distrib_le_right -> Filter.map₂_distrib_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} {ε : Type.{u7}} {f : Filter.{u1} α} {g : Filter.{u3} β} {h : Filter.{u5} γ} {m : δ -> γ -> ε} {n : α -> β -> δ} {m₁ : α -> γ -> α'} {m₂ : β -> γ -> β'} {n' : α' -> β' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u7} ε (m (n a b) c) (n' (m₁ a c) (m₂ b c))) -> (LE.le.{u7} (Filter.{u7} ε) (Preorder.toLE.{u7} (Filter.{u7} ε) (PartialOrder.toPreorder.{u7} (Filter.{u7} ε) (Filter.partialOrder.{u7} ε))) (Filter.map₂.{u6, u5, u7} δ γ ε m (Filter.map₂.{u1, u3, u6} α β δ n f g) h) (Filter.map₂.{u2, u4, u7} α' β' ε n' (Filter.map₂.{u1, u5, u2} α γ α' m₁ f h) (Filter.map₂.{u3, u5, u4} β γ β' m₂ g h)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u1}} {γ : Type.{u5}} {δ : Type.{u6}} {ε : Type.{u7}} {f : Filter.{u4} α} {g : Filter.{u3} β} {h : Filter.{u5} γ} {m : δ -> γ -> ε} {n : α -> β -> δ} {m₁ : α -> γ -> α'} {m₂ : β -> γ -> β'} {n' : α' -> β' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u7} ε (m (n a b) c) (n' (m₁ a c) (m₂ b c))) -> (LE.le.{u7} (Filter.{u7} ε) (Preorder.toLE.{u7} (Filter.{u7} ε) (PartialOrder.toPreorder.{u7} (Filter.{u7} ε) (Filter.instPartialOrderFilter.{u7} ε))) (Filter.map₂.{u6, u5, u7} δ γ ε m (Filter.map₂.{u4, u3, u6} α β δ n f g) h) (Filter.map₂.{u2, u1, u7} α' β' ε n' (Filter.map₂.{u4, u5, u2} α γ α' m₁ f h) (Filter.map₂.{u3, u5, u1} β γ β' m₂ g h)))
Case conversion may be inaccurate. Consider using '#align filter.map₂_distrib_le_right Filter.map₂_distrib_le_rightₓ'. -/
/-- The other direction does not hold because of the `h`-`h` cross terms on the RHS. -/
theorem map₂_distrib_le_right {m : δ → γ → ε} {n : α → β → δ} {m₁ : α → γ → α'} {m₂ : β → γ → β'}
    {n' : α' → β' → ε} (h_distrib : ∀ a b c, m (n a b) c = n' (m₁ a c) (m₂ b c)) :
    map₂ m (map₂ n f g) h ≤ map₂ n' (map₂ m₁ f h) (map₂ m₂ g h) :=
  by
  rintro s ⟨t₁, t₂, ⟨u, w₁, hu, hw₁, ht₁⟩, ⟨v, w₂, hv, hw₂, ht₂⟩, hs⟩
  refine' ⟨_, w₁ ∩ w₂, image2_mem_map₂ hu hv, inter_mem hw₁ hw₂, _⟩
  refine' (image2_distrib_subset_right h_distrib).trans ((image2_subset _ _).trans hs)
  · exact (image2_subset_left <| inter_subset_left _ _).trans ht₁
  · exact (image2_subset_left <| inter_subset_right _ _).trans ht₂
#align filter.map₂_distrib_le_right Filter.map₂_distrib_le_right

/- warning: filter.map_map₂_antidistrib -> Filter.map_map₂_antidistrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u3} β} {n : γ -> δ} {m' : β' -> α' -> δ} {n₁ : β -> β'} {n₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u6} δ (n (m a b)) (m' (n₁ b) (n₂ a))) -> (Eq.{succ u6} (Filter.{u6} δ) (Filter.map.{u5, u6} γ δ n (Filter.map₂.{u1, u3, u5} α β γ m f g)) (Filter.map₂.{u4, u2, u6} β' α' δ m' (Filter.map.{u3, u4} β β' n₁ g) (Filter.map.{u1, u2} α α' n₂ f)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u1}} {β : Type.{u3}} {β' : Type.{u2}} {γ : Type.{u5}} {δ : Type.{u6}} {m : α -> β -> γ} {f : Filter.{u4} α} {g : Filter.{u3} β} {n : γ -> δ} {m' : β' -> α' -> δ} {n₁ : β -> β'} {n₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u6} δ (n (m a b)) (m' (n₁ b) (n₂ a))) -> (Eq.{succ u6} (Filter.{u6} δ) (Filter.map.{u5, u6} γ δ n (Filter.map₂.{u4, u3, u5} α β γ m f g)) (Filter.map₂.{u2, u1, u6} β' α' δ m' (Filter.map.{u3, u2} β β' n₁ g) (Filter.map.{u4, u1} α α' n₂ f)))
Case conversion may be inaccurate. Consider using '#align filter.map_map₂_antidistrib Filter.map_map₂_antidistribₓ'. -/
theorem map_map₂_antidistrib {n : γ → δ} {m' : β' → α' → δ} {n₁ : β → β'} {n₂ : α → α'}
    (h_antidistrib : ∀ a b, n (m a b) = m' (n₁ b) (n₂ a)) :
    (map₂ m f g).map n = map₂ m' (g.map n₁) (f.map n₂) :=
  by
  rw [map₂_swap m]
  exact map_map₂_distrib fun _ _ => h_antidistrib _ _
#align filter.map_map₂_antidistrib Filter.map_map₂_antidistrib

/- warning: filter.map_map₂_antidistrib_left -> Filter.map_map₂_antidistrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u2} β} {n : γ -> δ} {m' : β' -> α -> δ} {n' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (n (m a b)) (m' (n' b) a)) -> (Eq.{succ u5} (Filter.{u5} δ) (Filter.map.{u4, u5} γ δ n (Filter.map₂.{u1, u2, u4} α β γ m f g)) (Filter.map₂.{u3, u1, u5} β' α δ m' (Filter.map.{u2, u3} β β' n' g) f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {β' : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u5}} {m : α -> β -> γ} {f : Filter.{u3} α} {g : Filter.{u2} β} {n : γ -> δ} {m' : β' -> α -> δ} {n' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (n (m a b)) (m' (n' b) a)) -> (Eq.{succ u5} (Filter.{u5} δ) (Filter.map.{u4, u5} γ δ n (Filter.map₂.{u3, u2, u4} α β γ m f g)) (Filter.map₂.{u1, u3, u5} β' α δ m' (Filter.map.{u2, u1} β β' n' g) f))
Case conversion may be inaccurate. Consider using '#align filter.map_map₂_antidistrib_left Filter.map_map₂_antidistrib_leftₓ'. -/
/-- Symmetric statement to `filter.map₂_map_left_anticomm`. -/
theorem map_map₂_antidistrib_left {n : γ → δ} {m' : β' → α → δ} {n' : β → β'}
    (h_antidistrib : ∀ a b, n (m a b) = m' (n' b) a) : (map₂ m f g).map n = map₂ m' (g.map n') f :=
  map_map₂_antidistrib h_antidistrib
#align filter.map_map₂_antidistrib_left Filter.map_map₂_antidistrib_left

/- warning: filter.map_map₂_antidistrib_right -> Filter.map_map₂_antidistrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {m : α -> β -> γ} {f : Filter.{u1} α} {g : Filter.{u3} β} {n : γ -> δ} {m' : β -> α' -> δ} {n' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (n (m a b)) (m' b (n' a))) -> (Eq.{succ u5} (Filter.{u5} δ) (Filter.map.{u4, u5} γ δ n (Filter.map₂.{u1, u3, u4} α β γ m f g)) (Filter.map₂.{u3, u2, u5} β α' δ m' g (Filter.map.{u1, u2} α α' n' f)))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} {m : α -> β -> γ} {f : Filter.{u3} α} {g : Filter.{u2} β} {n : γ -> δ} {m' : β -> α' -> δ} {n' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (n (m a b)) (m' b (n' a))) -> (Eq.{succ u5} (Filter.{u5} δ) (Filter.map.{u4, u5} γ δ n (Filter.map₂.{u3, u2, u4} α β γ m f g)) (Filter.map₂.{u2, u1, u5} β α' δ m' g (Filter.map.{u3, u1} α α' n' f)))
Case conversion may be inaccurate. Consider using '#align filter.map_map₂_antidistrib_right Filter.map_map₂_antidistrib_rightₓ'. -/
/-- Symmetric statement to `filter.map_map₂_right_anticomm`. -/
theorem map_map₂_antidistrib_right {n : γ → δ} {m' : β → α' → δ} {n' : α → α'}
    (h_antidistrib : ∀ a b, n (m a b) = m' b (n' a)) : (map₂ m f g).map n = map₂ m' g (f.map n') :=
  map_map₂_antidistrib h_antidistrib
#align filter.map_map₂_antidistrib_right Filter.map_map₂_antidistrib_right

/- warning: filter.map₂_map_left_anticomm -> Filter.map₂_map_left_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : Filter.{u1} α} {g : Filter.{u3} β} {m : α' -> β -> γ} {n : α -> α'} {m' : β -> α -> δ} {n' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (m (n a) b) (n' (m' b a))) -> (Eq.{succ u4} (Filter.{u4} γ) (Filter.map₂.{u2, u3, u4} α' β γ m (Filter.map.{u1, u2} α α' n f) g) (Filter.map.{u5, u4} δ γ n' (Filter.map₂.{u3, u1, u5} β α δ m' g f)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u4}} {β : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} {f : Filter.{u2} α} {g : Filter.{u3} β} {m : α' -> β -> γ} {n : α -> α'} {m' : β -> α -> δ} {n' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (m (n a) b) (n' (m' b a))) -> (Eq.{succ u5} (Filter.{u5} γ) (Filter.map₂.{u4, u3, u5} α' β γ m (Filter.map.{u2, u4} α α' n f) g) (Filter.map.{u1, u5} δ γ n' (Filter.map₂.{u3, u2, u1} β α δ m' g f)))
Case conversion may be inaccurate. Consider using '#align filter.map₂_map_left_anticomm Filter.map₂_map_left_anticommₓ'. -/
/-- Symmetric statement to `filter.map_map₂_antidistrib_left`. -/
theorem map₂_map_left_anticomm {m : α' → β → γ} {n : α → α'} {m' : β → α → δ} {n' : δ → γ}
    (h_left_anticomm : ∀ a b, m (n a) b = n' (m' b a)) :
    map₂ m (f.map n) g = (map₂ m' g f).map n' :=
  (map_map₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm
#align filter.map₂_map_left_anticomm Filter.map₂_map_left_anticomm

/- warning: filter.map_map₂_right_anticomm -> Filter.map_map₂_right_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : Filter.{u1} α} {g : Filter.{u2} β} {m : α -> β' -> γ} {n : β -> β'} {m' : β -> α -> δ} {n' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (m a (n b)) (n' (m' b a))) -> (Eq.{succ u4} (Filter.{u4} γ) (Filter.map₂.{u1, u3, u4} α β' γ m f (Filter.map.{u2, u3} β β' n g)) (Filter.map.{u5, u4} δ γ n' (Filter.map₂.{u2, u1, u5} β α δ m' g f)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} {f : Filter.{u4} α} {g : Filter.{u2} β} {m : α -> β' -> γ} {n : β -> β'} {m' : β -> α -> δ} {n' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (m a (n b)) (n' (m' b a))) -> (Eq.{succ u5} (Filter.{u5} γ) (Filter.map₂.{u4, u3, u5} α β' γ m f (Filter.map.{u2, u3} β β' n g)) (Filter.map.{u1, u5} δ γ n' (Filter.map₂.{u2, u4, u1} β α δ m' g f)))
Case conversion may be inaccurate. Consider using '#align filter.map_map₂_right_anticomm Filter.map_map₂_right_anticommₓ'. -/
/-- Symmetric statement to `filter.map_map₂_antidistrib_right`. -/
theorem map_map₂_right_anticomm {m : α → β' → γ} {n : β → β'} {m' : β → α → δ} {n' : δ → γ}
    (h_right_anticomm : ∀ a b, m a (n b) = n' (m' b a)) :
    map₂ m f (g.map n) = (map₂ m' g f).map n' :=
  (map_map₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm
#align filter.map_map₂_right_anticomm Filter.map_map₂_right_anticomm

#print Filter.map₂_left_identity /-
/-- If `a` is a left identity for `f : α → β → β`, then `pure a` is a left identity for
`filter.map₂ f`. -/
theorem map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (l : Filter β) :
    map₂ f (pure a) l = l := by rw [map₂_pure_left, show f a = id from funext h, map_id]
#align filter.map₂_left_identity Filter.map₂_left_identity
-/

/- warning: filter.map₂_right_identity -> Filter.map₂_right_identity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β -> α} {b : β}, (forall (a : α), Eq.{succ u1} α (f a b) a) -> (forall (l : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} α) (Filter.map₂.{u1, u2, u1} α β α f l (Pure.pure.{u2, u2} Filter.{u2} Filter.hasPure.{u2} β b)) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β -> α} {b : β}, (forall (a : α), Eq.{succ u2} α (f a b) a) -> (forall (l : Filter.{u2} α), Eq.{succ u2} (Filter.{u2} α) (Filter.map₂.{u2, u1, u2} α β α f l (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} β b)) l)
Case conversion may be inaccurate. Consider using '#align filter.map₂_right_identity Filter.map₂_right_identityₓ'. -/
/-- If `b` is a right identity for `f : α → β → α`, then `pure b` is a right identity for
`filter.map₂ f`. -/
theorem map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (l : Filter α) :
    map₂ f l (pure b) = l := by rw [map₂_pure_right, funext h, map_id']
#align filter.map₂_right_identity Filter.map₂_right_identity

end Filter

