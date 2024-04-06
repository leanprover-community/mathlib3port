/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Data.Finset.Option
import Data.PFun

#align_import data.finset.pimage from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# Image of a `finset α` under a partially defined function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `part.to_finset` and `finset.pimage`. We also prove some trivial lemmas about
these definitions.

## Tags

finite set, image, partial function
-/


variable {α β : Type _}

namespace Part

#print Part.toFinset /-
/-- Convert a `o : part α` with decidable `part.dom o` to `finset α`. -/
def toFinset (o : Part α) [Decidable o.Dom] : Finset α :=
  o.toOption.toFinset
#align part.to_finset Part.toFinset
-/

#print Part.mem_toFinset /-
@[simp]
theorem mem_toFinset {o : Part α} [Decidable o.Dom] {x : α} : x ∈ o.toFinset ↔ x ∈ o := by
  simp [to_finset]
#align part.mem_to_finset Part.mem_toFinset
-/

#print Part.toFinset_none /-
@[simp]
theorem toFinset_none [Decidable (none : Part α).Dom] : none.toFinset = (∅ : Finset α) := by
  simp [to_finset]
#align part.to_finset_none Part.toFinset_none
-/

#print Part.toFinset_some /-
@[simp]
theorem toFinset_some {a : α} [Decidable (some a).Dom] : (some a).toFinset = {a} := by
  simp [to_finset]
#align part.to_finset_some Part.toFinset_some
-/

#print Part.coe_toFinset /-
@[simp]
theorem coe_toFinset (o : Part α) [Decidable o.Dom] : (o.toFinset : Set α) = {x | x ∈ o} :=
  Set.ext fun x => mem_toFinset
#align part.coe_to_finset Part.coe_toFinset
-/

end Part

namespace Finset

variable [DecidableEq β] {f g : α →. β} [∀ x, Decidable (f x).Dom] [∀ x, Decidable (g x).Dom]
  {s t : Finset α} {b : β}

#print Finset.pimage /-
/-- Image of `s : finset α` under a partially defined function `f : α →. β`. -/
def pimage (f : α →. β) [∀ x, Decidable (f x).Dom] (s : Finset α) : Finset β :=
  s.biUnion fun x => (f x).toFinset
#align finset.pimage Finset.pimage
-/

#print Finset.mem_pimage /-
@[simp]
theorem mem_pimage : b ∈ s.pimage f ↔ ∃ a ∈ s, b ∈ f a := by simp [pimage]
#align finset.mem_pimage Finset.mem_pimage
-/

#print Finset.coe_pimage /-
@[simp, norm_cast]
theorem coe_pimage : (s.pimage f : Set β) = f.image s :=
  Set.ext fun x => mem_pimage
#align finset.coe_pimage Finset.coe_pimage
-/

#print Finset.pimage_some /-
@[simp]
theorem pimage_some (s : Finset α) (f : α → β) [∀ x, Decidable (Part.some <| f x).Dom] :
    (s.pimage fun x => Part.some (f x)) = s.image f := by ext; simp [eq_comm]
#align finset.pimage_some Finset.pimage_some
-/

#print Finset.pimage_congr /-
theorem pimage_congr (h₁ : s = t) (h₂ : ∀ x ∈ t, f x = g x) : s.pimage f = t.pimage g := by subst s;
  ext y; simp (config := { contextual := true }) [h₂]
#align finset.pimage_congr Finset.pimage_congr
-/

#print Finset.pimage_eq_image_filter /-
/-- Rewrite `s.pimage f` in terms of `finset.filter`, `finset.attach`, and `finset.image`. -/
theorem pimage_eq_image_filter :
    s.pimage f =
      (filter (fun x => (f x).Dom) s).attach.image fun x => (f x).get (mem_filter.1 x.coe_prop).2 :=
  by ext x; simp [Part.mem_eq, And.exists, -exists_prop]
#align finset.pimage_eq_image_filter Finset.pimage_eq_image_filter
-/

#print Finset.pimage_union /-
theorem pimage_union [DecidableEq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
  coe_inj.1 <| by simp only [coe_pimage, PFun.image_union, coe_union]
#align finset.pimage_union Finset.pimage_union
-/

#print Finset.pimage_empty /-
@[simp]
theorem pimage_empty : pimage f ∅ = ∅ := by ext; simp
#align finset.pimage_empty Finset.pimage_empty
-/

#print Finset.pimage_subset /-
theorem pimage_subset {t : Finset β} : s.pimage f ⊆ t ↔ ∀ x ∈ s, ∀ y ∈ f x, y ∈ t := by
  simp [subset_iff, @forall_swap _ β]
#align finset.pimage_subset Finset.pimage_subset
-/

#print Finset.pimage_mono /-
@[mono]
theorem pimage_mono (h : s ⊆ t) : s.pimage f ⊆ t.pimage f :=
  pimage_subset.2 fun x hx y hy => mem_pimage.2 ⟨x, h hx, hy⟩
#align finset.pimage_mono Finset.pimage_mono
-/

#print Finset.pimage_inter /-
theorem pimage_inter [DecidableEq α] : (s ∩ t).pimage f ⊆ s.pimage f ∩ t.pimage f := by
  simp only [← coe_subset, coe_pimage, coe_inter, PFun.image_inter]
#align finset.pimage_inter Finset.pimage_inter
-/

end Finset

