/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.finset.pimage
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Option
import Mathbin.Data.Pfun

/-!
# Image of a `finset α` under a partially defined function

In this file we define `part.to_finset` and `finset.pimage`. We also prove some trivial lemmas about
these definitions.

## Tags

finite set, image, partial function
-/


variable {α β : Type _}

namespace Part

/-- Convert a `o : part α` with decidable `part.dom o` to `finset α`. -/
def toFinset (o : Part α) [Decidable o.Dom] : Finset α :=
  o.toOption.toFinset
#align part.to_finset Part.toFinset

@[simp]
theorem mem_to_finset {o : Part α} [Decidable o.Dom] {x : α} : x ∈ o.toFinset ↔ x ∈ o := by
  simp [to_finset]
#align part.mem_to_finset Part.mem_to_finset

@[simp]
theorem to_finset_none [Decidable (none : Part α).Dom] : none.toFinset = (∅ : Finset α) := by
  simp [to_finset]
#align part.to_finset_none Part.to_finset_none

@[simp]
theorem to_finset_some {a : α} [Decidable (some a).Dom] : (some a).toFinset = {a} := by
  simp [to_finset]
#align part.to_finset_some Part.to_finset_some

@[simp]
theorem coe_to_finset (o : Part α) [Decidable o.Dom] : (o.toFinset : Set α) = { x | x ∈ o } :=
  Set.ext fun x => mem_to_finset
#align part.coe_to_finset Part.coe_to_finset

end Part

namespace Finset

variable [DecidableEq β] {f g : α →. β} [∀ x, Decidable (f x).Dom] [∀ x, Decidable (g x).Dom]
  {s t : Finset α} {b : β}

/-- Image of `s : finset α` under a partially defined function `f : α →. β`. -/
def pimage (f : α →. β) [∀ x, Decidable (f x).Dom] (s : Finset α) : Finset β :=
  s.bUnion fun x => (f x).toFinset
#align finset.pimage Finset.pimage

@[simp]
theorem mem_pimage : b ∈ s.pimage f ↔ ∃ a ∈ s, b ∈ f a := by simp [pimage]
#align finset.mem_pimage Finset.mem_pimage

@[simp, norm_cast]
theorem coe_pimage : (s.pimage f : Set β) = f.image s :=
  Set.ext fun x => mem_pimage
#align finset.coe_pimage Finset.coe_pimage

@[simp]
theorem pimage_some (s : Finset α) (f : α → β) [∀ x, Decidable (Part.some <| f x).Dom] :
    (s.pimage fun x => Part.some (f x)) = s.image f :=
  by
  ext
  simp [eq_comm]
#align finset.pimage_some Finset.pimage_some

theorem pimage_congr (h₁ : s = t) (h₂ : ∀ x ∈ t, f x = g x) : s.pimage f = t.pimage g :=
  by
  subst s
  ext y
  simp (config := { contextual := true }) [h₂]
#align finset.pimage_congr Finset.pimage_congr

/-- Rewrite `s.pimage f` in terms of `finset.filter`, `finset.attach`, and `finset.image`. -/
theorem pimage_eq_image_filter :
    s.pimage f =
      (filter (fun x => (f x).Dom) s).attach.image fun x => (f x).get (mem_filter.1 x.coe_prop).2 :=
  by
  ext x
  simp [Part.mem_eq, And.exists, -exists_prop]
#align finset.pimage_eq_image_filter Finset.pimage_eq_image_filter

theorem pimage_union [DecidableEq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
  coe_inj.1 <| by simp only [coe_pimage, Pfun.image_union, coe_union]
#align finset.pimage_union Finset.pimage_union

@[simp]
theorem pimage_empty : pimage f ∅ = ∅ := by
  ext
  simp
#align finset.pimage_empty Finset.pimage_empty

theorem pimage_subset {t : Finset β} : s.pimage f ⊆ t ↔ ∀ x ∈ s, ∀ y ∈ f x, y ∈ t := by
  simp [subset_iff, @forall_swap _ β]
#align finset.pimage_subset Finset.pimage_subset

@[mono]
theorem pimage_mono (h : s ⊆ t) : s.pimage f ⊆ t.pimage f :=
  pimage_subset.2 fun x hx y hy => mem_pimage.2 ⟨x, h hx, hy⟩
#align finset.pimage_mono Finset.pimage_mono

theorem pimage_inter [DecidableEq α] : (s ∩ t).pimage f ⊆ s.pimage f ∩ t.pimage f := by
  simp only [← coe_subset, coe_pimage, coe_inter, Pfun.image_inter]
#align finset.pimage_inter Finset.pimage_inter

end Finset

