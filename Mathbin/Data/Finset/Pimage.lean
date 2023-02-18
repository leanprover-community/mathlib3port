/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.finset.pimage
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Option
import Mathbin.Data.Pfun

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
theorem coe_toFinset (o : Part α) [Decidable o.Dom] : (o.toFinset : Set α) = { x | x ∈ o } :=
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
  s.bunionᵢ fun x => (f x).toFinset
#align finset.pimage Finset.pimage
-/

/- warning: finset.mem_pimage -> Finset.mem_pimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : PFun.{u1, u2} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u2} β (f x))] {s : Finset.{u1} α} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Part.{u2} β) (Part.hasMem.{u2} β) b (f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : PFun.{u1, u2} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u2} β (f x))] {s : Finset.{u1} α} {b : β}, Iff (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Membership.mem.{u2, u2} β (Part.{u2} β) (Part.instMembershipPart.{u2} β) b (f a))))
Case conversion may be inaccurate. Consider using '#align finset.mem_pimage Finset.mem_pimageₓ'. -/
@[simp]
theorem mem_pimage : b ∈ s.pimage f ↔ ∃ a ∈ s, b ∈ f a := by simp [pimage]
#align finset.mem_pimage Finset.mem_pimage

#print Finset.coe_pimage /-
@[simp, norm_cast]
theorem coe_pimage : (s.pimage f : Set β) = f.image s :=
  Set.ext fun x => mem_pimage
#align finset.coe_pimage Finset.coe_pimage
-/

/- warning: finset.pimage_some -> Finset.pimage_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> β) [_inst_4 : forall (x : α), Decidable (Part.Dom.{u2} β (Part.some.{u2} β (f x)))], Eq.{succ u2} (Finset.{u2} β) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (fun (x : α) => Part.some.{u2} β (f x)) (fun (x : α) => _inst_4 x) s) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (f : α -> β) [_inst_4 : forall (x : α), Decidable (Part.Dom.{u1} β (Part.some.{u1} β (f x)))], Eq.{succ u1} (Finset.{u1} β) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (fun (x : α) => Part.some.{u1} β (f x)) (fun (x : α) => _inst_4 x) s) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s)
Case conversion may be inaccurate. Consider using '#align finset.pimage_some Finset.pimage_someₓ'. -/
@[simp]
theorem pimage_some (s : Finset α) (f : α → β) [∀ x, Decidable (Part.some <| f x).Dom] :
    (s.pimage fun x => Part.some (f x)) = s.image f :=
  by
  ext
  simp [eq_comm]
#align finset.pimage_some Finset.pimage_some

/- warning: finset.pimage_congr -> Finset.pimage_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : PFun.{u1, u2} α β} {g : PFun.{u1, u2} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u2} β (f x))] [_inst_3 : forall (x : α), Decidable (Part.Dom.{u2} β (g x))] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Eq.{succ u1} (Finset.{u1} α) s t) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) -> (Eq.{succ u2} (Part.{u2} β) (f x) (g x))) -> (Eq.{succ u2} (Finset.{u2} β) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) g (fun (x : α) => _inst_3 x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : PFun.{u2, u1} α β} {g : PFun.{u2, u1} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u1} β (f x))] [_inst_3 : forall (x : α), Decidable (Part.Dom.{u1} β (g x))] {s : Finset.{u2} α} {t : Finset.{u2} α}, (Eq.{succ u2} (Finset.{u2} α) s t) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) -> (Eq.{succ u1} (Part.{u1} β) (f x) (g x))) -> (Eq.{succ u1} (Finset.{u1} β) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) g (fun (x : α) => _inst_3 x) t))
Case conversion may be inaccurate. Consider using '#align finset.pimage_congr Finset.pimage_congrₓ'. -/
theorem pimage_congr (h₁ : s = t) (h₂ : ∀ x ∈ t, f x = g x) : s.pimage f = t.pimage g :=
  by
  subst s
  ext y
  simp (config := { contextual := true }) [h₂]
#align finset.pimage_congr Finset.pimage_congr

#print Finset.pimage_eq_image_filter /-
/-- Rewrite `s.pimage f` in terms of `finset.filter`, `finset.attach`, and `finset.image`. -/
theorem pimage_eq_image_filter :
    s.pimage f =
      (filter (fun x => (f x).Dom) s).attach.image fun x => (f x).get (mem_filter.1 x.coe_prop).2 :=
  by
  ext x
  simp [Part.mem_eq, And.exists, -exists_prop]
#align finset.pimage_eq_image_filter Finset.pimage_eq_image_filter
-/

/- warning: finset.pimage_union -> Finset.pimage_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : PFun.{u1, u2} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u2} β (f x))] {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_4 : DecidableEq.{succ u1} α], Eq.{succ u2} (Finset.{u2} β) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_4 a b)) s t)) (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : PFun.{u2, u1} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u1} β (f x))] {s : Finset.{u2} α} {t : Finset.{u2} α} [_inst_4 : DecidableEq.{succ u2} α], Eq.{succ u1} (Finset.{u1} β) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_4 a b)) s t)) (Union.union.{u1} (Finset.{u1} β) (Finset.instUnionFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) t))
Case conversion may be inaccurate. Consider using '#align finset.pimage_union Finset.pimage_unionₓ'. -/
theorem pimage_union [DecidableEq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
  coe_inj.1 <| by simp only [coe_pimage, PFun.image_union, coe_union]
#align finset.pimage_union Finset.pimage_union

#print Finset.pimage_empty /-
@[simp]
theorem pimage_empty : pimage f ∅ = ∅ := by
  ext
  simp
#align finset.pimage_empty Finset.pimage_empty
-/

#print Finset.pimage_subset /-
theorem pimage_subset {t : Finset β} : s.pimage f ⊆ t ↔ ∀ x ∈ s, ∀ y ∈ f x, y ∈ t := by
  simp [subset_iff, @forall_swap _ β]
#align finset.pimage_subset Finset.pimage_subset
-/

/- warning: finset.pimage_mono -> Finset.pimage_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : PFun.{u1, u2} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u2} β (f x))] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : PFun.{u2, u1} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u1} β (f x))] {s : Finset.{u2} α} {t : Finset.{u2} α}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s t) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) t))
Case conversion may be inaccurate. Consider using '#align finset.pimage_mono Finset.pimage_monoₓ'. -/
@[mono]
theorem pimage_mono (h : s ⊆ t) : s.pimage f ⊆ t.pimage f :=
  pimage_subset.2 fun x hx y hy => mem_pimage.2 ⟨x, h hx, hy⟩
#align finset.pimage_mono Finset.pimage_mono

/- warning: finset.pimage_inter -> Finset.pimage_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : PFun.{u1, u2} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u2} β (f x))] {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_4 : DecidableEq.{succ u1} α], HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_4 a b)) s t)) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s) (Finset.pimage.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : PFun.{u2, u1} α β} [_inst_2 : forall (x : α), Decidable (Part.Dom.{u1} β (f x))] {s : Finset.{u2} α} {t : Finset.{u2} α} [_inst_4 : DecidableEq.{succ u2} α], HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_4 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) s) (Finset.pimage.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (fun (x : α) => _inst_2 x) t))
Case conversion may be inaccurate. Consider using '#align finset.pimage_inter Finset.pimage_interₓ'. -/
theorem pimage_inter [DecidableEq α] : (s ∩ t).pimage f ⊆ s.pimage f ∩ t.pimage f := by
  simp only [← coe_subset, coe_pimage, coe_inter, PFun.image_inter]
#align finset.pimage_inter Finset.pimage_inter

end Finset

