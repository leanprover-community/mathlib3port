/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.set.n_ary
! leanprover-community/mathlib commit 422e70f7ce183d2900c586a8cda8381e788a0c62
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Prod

/-!
# N-ary images of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/969
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `finset.image₂`, the binary image of finsets. This is the finset version of
`set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to the n-ary section of `data.set.basic`, to `order.filter.n_ary` and to
`data.option.n_ary`. Please keep them in sync.

We do not define `finset.image₃` as its only purpose would be to prove properties of `finset.image₂`
and `set.image2` already fulfills this task.
-/


open Function

namespace Set

variable {α α' β β' γ γ' δ δ' ε ε' : Type _} {f f' : α → β → γ} {g g' : α → β → γ → δ}

variable {s s' : Set α} {t t' : Set β} {u u' : Set γ} {a a' : α} {b b' : β} {c c' : γ} {d d' : δ}

#print Set.image2 /-
/-- The image of a binary function `f : α → β → γ` as a function `set α → set β → set γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`.-/
def image2 (f : α → β → γ) (s : Set α) (t : Set β) : Set γ :=
  { c | ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c }
#align set.image2 Set.image2
-/

/- warning: set.mem_image2 -> Set.mem_image2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {c : γ}, Iff (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image2.{u1, u2, u3} α β γ f s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u2} β (fun (b : β) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (And (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) (Eq.{succ u3} γ (f a b) c)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β} {c : γ}, Iff (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image2.{u2, u1, u3} α β γ f s t)) (Exists.{succ u2} α (fun (a : α) => Exists.{succ u1} β (fun (b : β) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (And (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b t) (Eq.{succ u3} γ (f a b) c)))))
Case conversion may be inaccurate. Consider using '#align set.mem_image2 Set.mem_image2ₓ'. -/
@[simp]
theorem mem_image2 : c ∈ image2 f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c :=
  Iff.rfl
#align set.mem_image2 Set.mem_image2

/- warning: set.mem_image2_of_mem -> Set.mem_image2_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {a : α} {b : β}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) (f a b) (Set.image2.{u1, u2, u3} α β γ f s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β} {a : α} {b : β}, (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a s) -> (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) -> (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) (f a b) (Set.image2.{u3, u2, u1} α β γ f s t))
Case conversion may be inaccurate. Consider using '#align set.mem_image2_of_mem Set.mem_image2_of_memₓ'. -/
theorem mem_image2_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image2 f s t :=
  ⟨a, b, ha, hb, rfl⟩
#align set.mem_image2_of_mem Set.mem_image2_of_mem

/- warning: set.mem_image2_iff -> Set.mem_image2_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {a : α} {b : β}, (Function.Injective2.{succ u1, succ u2, succ u3} α β γ f) -> (Iff (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) (f a b) (Set.image2.{u1, u2, u3} α β γ f s t)) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β} {a : α} {b : β}, (Function.Injective2.{succ u3, succ u2, succ u1} α β γ f) -> (Iff (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) (f a b) (Set.image2.{u3, u2, u1} α β γ f s t)) (And (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a s) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t)))
Case conversion may be inaccurate. Consider using '#align set.mem_image2_iff Set.mem_image2_iffₓ'. -/
theorem mem_image2_iff (hf : Injective2 f) : f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
  ⟨by
    rintro ⟨a', b', ha', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩
#align set.mem_image2_iff Set.mem_image2_iff

/- warning: set.image2_subset -> Set.image2_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u2} β} {t' : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s s') -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t t') -> (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s' t'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {s : Set.{u3} α} {s' : Set.{u3} α} {t : Set.{u2} β} {t' : Set.{u2} β}, (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet_1.{u3} α) s s') -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet_1.{u2} β) t t') -> (HasSubset.Subset.{u1} (Set.{u1} γ) (Set.instHasSubsetSet_1.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f s t) (Set.image2.{u3, u2, u1} α β γ f s' t'))
Case conversion may be inaccurate. Consider using '#align set.image2_subset Set.image2_subsetₓ'. -/
/-- image2 is monotone with respect to `⊆`. -/
theorem image2_subset (hs : s ⊆ s') (ht : t ⊆ t') : image2 f s t ⊆ image2 f s' t' :=
  by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_image2_of_mem (hs ha) (ht hb)
#align set.image2_subset Set.image2_subset

/- warning: set.image2_subset_left -> Set.image2_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {t' : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t t') -> (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s t'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u3} β} {t' : Set.{u3} β}, (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet_1.{u3} β) t t') -> (HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet_1.{u2} γ) (Set.image2.{u1, u3, u2} α β γ f s t) (Set.image2.{u1, u3, u2} α β γ f s t'))
Case conversion may be inaccurate. Consider using '#align set.image2_subset_left Set.image2_subset_leftₓ'. -/
theorem image2_subset_left (ht : t ⊆ t') : image2 f s t ⊆ image2 f s t' :=
  image2_subset Subset.rfl ht
#align set.image2_subset_left Set.image2_subset_left

/- warning: set.image2_subset_right -> Set.image2_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s s') -> (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s' t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {f : α -> β -> γ} {s : Set.{u3} α} {s' : Set.{u3} α} {t : Set.{u1} β}, (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet_1.{u3} α) s s') -> (HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet_1.{u2} γ) (Set.image2.{u3, u1, u2} α β γ f s t) (Set.image2.{u3, u1, u2} α β γ f s' t))
Case conversion may be inaccurate. Consider using '#align set.image2_subset_right Set.image2_subset_rightₓ'. -/
theorem image2_subset_right (hs : s ⊆ s') : image2 f s t ⊆ image2 f s' t :=
  image2_subset hs Subset.rfl
#align set.image2_subset_right Set.image2_subset_right

/- warning: set.image_subset_image2_left -> Set.image_subset_image2_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {b : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image.{u1, u3} α γ (fun (a : α) => f a b) s) (Set.image2.{u1, u2, u3} α β γ f s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u3} β} {b : β}, (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b t) -> (HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet_1.{u2} γ) (Set.image.{u1, u2} α γ (fun (a : α) => f a b) s) (Set.image2.{u1, u3, u2} α β γ f s t))
Case conversion may be inaccurate. Consider using '#align set.image_subset_image2_left Set.image_subset_image2_leftₓ'. -/
theorem image_subset_image2_left (hb : b ∈ t) : (fun a => f a b) '' s ⊆ image2 f s t :=
  ball_image_of_ball fun a ha => mem_image2_of_mem ha hb
#align set.image_subset_image2_left Set.image_subset_image2_left

/- warning: set.image_subset_image2_right -> Set.image_subset_image2_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image.{u2, u3} β γ (f a) t) (Set.image2.{u1, u2, u3} α β γ f s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u1} β} {a : α}, (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a s) -> (HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet_1.{u2} γ) (Set.image.{u1, u2} β γ (f a) t) (Set.image2.{u3, u1, u2} α β γ f s t))
Case conversion may be inaccurate. Consider using '#align set.image_subset_image2_right Set.image_subset_image2_rightₓ'. -/
theorem image_subset_image2_right (ha : a ∈ s) : f a '' t ⊆ image2 f s t :=
  ball_image_of_ball fun b => mem_image2_of_mem ha
#align set.image_subset_image2_right Set.image_subset_image2_right

/- warning: set.forall_image2_iff -> Set.forall_image2_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {p : γ -> Prop}, Iff (forall (z : γ), (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) z (Set.image2.{u1, u2, u3} α β γ f s t)) -> (p z)) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (p (f x y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β} {p : γ -> Prop}, Iff (forall (z : γ), (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) z (Set.image2.{u2, u1, u3} α β γ f s t)) -> (p z)) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (y : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t) -> (p (f x y))))
Case conversion may be inaccurate. Consider using '#align set.forall_image2_iff Set.forall_image2_iffₓ'. -/
theorem forall_image2_iff {p : γ → Prop} :
    (∀ z ∈ image2 f s t, p z) ↔ ∀ x ∈ s, ∀ y ∈ t, p (f x y) :=
  ⟨fun h x hx y hy => h _ ⟨x, y, hx, hy, rfl⟩, fun h z ⟨x, y, hx, hy, hz⟩ => hz ▸ h x hx y hy⟩
#align set.forall_image2_iff Set.forall_image2_iff

/- warning: set.image2_subset_iff -> Set.image2_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ}, Iff (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) u) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) (f x y) u)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β} {u : Set.{u3} γ}, Iff (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet_1.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s t) u) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (y : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t) -> (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) (f x y) u)))
Case conversion may be inaccurate. Consider using '#align set.image2_subset_iff Set.image2_subset_iffₓ'. -/
@[simp]
theorem image2_subset_iff {u : Set γ} : image2 f s t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u :=
  forall_image2_iff
#align set.image2_subset_iff Set.image2_subset_iff

variable (f)

/- warning: set.image_prod -> Set.image_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ u3} (Set.{u3} γ) (Set.image.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (fun (x : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β x) (Prod.snd.{u1, u2} α β x)) (Set.prod.{u1, u2} α β s t)) (Set.image2.{u1, u2, u3} α β γ f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (f : α -> β -> γ) {s : Set.{u2} α} {t : Set.{u1} β}, Eq.{succ u3} (Set.{u3} γ) (Set.image.{max u2 u1, u3} (Prod.{u2, u1} α β) γ (fun (x : Prod.{u2, u1} α β) => f (Prod.fst.{u2, u1} α β x) (Prod.snd.{u2, u1} α β x)) (Set.prod.{u2, u1} α β s t)) (Set.image2.{u2, u1, u3} α β γ f s t)
Case conversion may be inaccurate. Consider using '#align set.image_prod Set.image_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = image2 f s t :=
  ext fun a =>
    ⟨by
      rintro ⟨_, _, rfl⟩
      exact ⟨_, _, (mem_prod.1 ‹_›).1, (mem_prod.1 ‹_›).2, rfl⟩,
      by
      rintro ⟨_, _, _, _, rfl⟩
      exact ⟨(_, _), ⟨‹_›, ‹_›⟩, rfl⟩⟩
#align set.image_prod Set.image_prod

/- warning: set.image_uncurry_prod -> Set.image_uncurry_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u3} (Set.{u3} γ) (Set.image.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Function.uncurry.{u1, u2, u3} α β γ f) (Set.prod.{u1, u2} α β s t)) (Set.image2.{u1, u2, u3} α β γ f s t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (s : Set.{u3} α) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} γ) (Set.image.{max u2 u3, u1} (Prod.{u3, u2} α β) γ (Function.uncurry.{u3, u2, u1} α β γ f) (Set.prod.{u3, u2} α β s t)) (Set.image2.{u3, u2, u1} α β γ f s t)
Case conversion may be inaccurate. Consider using '#align set.image_uncurry_prod Set.image_uncurry_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_uncurry_prod (s : Set α) (t : Set β) : uncurry f '' s ×ˢ t = image2 f s t :=
  image_prod _
#align set.image_uncurry_prod Set.image_uncurry_prod

/- warning: set.image2_mk_eq_prod -> Set.image2_mk_eq_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.image2.{u1, u2, max u1 u2} α β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β) s t) (Set.prod.{u1, u2} α β s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.image2.{u2, u1, max u1 u2} α β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β) s t) (Set.prod.{u2, u1} α β s t)
Case conversion may be inaccurate. Consider using '#align set.image2_mk_eq_prod Set.image2_mk_eq_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image2_mk_eq_prod : image2 Prod.mk s t = s ×ˢ t :=
  ext <| by simp
#align set.image2_mk_eq_prod Set.image2_mk_eq_prod

/- warning: set.image2_curry -> Set.image2_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : (Prod.{u1, u2} α β) -> γ) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ (fun (a : α) (b : β) => f (Prod.mk.{u1, u2} α β a b)) s t) (Set.image.{max u1 u2, u3} (Prod.{u1, u2} α β) γ f (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : (Prod.{u3, u2} α β) -> γ) (s : Set.{u3} α) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} γ) (Set.image2.{u3, u2, u1} α β γ (fun (a : α) (b : β) => f (Prod.mk.{u3, u2} α β a b)) s t) (Set.image.{max u3 u2, u1} (Prod.{u3, u2} α β) γ f (Set.prod.{u3, u2} α β s t))
Case conversion may be inaccurate. Consider using '#align set.image2_curry Set.image2_curryₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image2_curry (f : α × β → γ) (s : Set α) (t : Set β) :
    image2 (fun a b => f (a, b)) s t = f '' s ×ˢ t := by simp [← image_uncurry_prod, uncurry]
#align set.image2_curry Set.image2_curry

variable {f}

/- warning: set.image2_union_left -> Set.image2_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s s') t) (Union.union.{u3} (Set.{u3} γ) (Set.hasUnion.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s' t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {s' : Set.{u2} α} {t : Set.{u1} β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s s') t) (Union.union.{u3} (Set.{u3} γ) (Set.instUnionSet_1.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s t) (Set.image2.{u2, u1, u3} α β γ f s' t))
Case conversion may be inaccurate. Consider using '#align set.image2_union_left Set.image2_union_leftₓ'. -/
theorem image2_union_left : image2 f (s ∪ s') t = image2 f s t ∪ image2 f s' t :=
  by
  ext c
  constructor
  · rintro ⟨a, b, ha | ha, hb, rfl⟩ <;> [left, right] <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
  ·
    rintro (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> refine' ⟨_, _, _, ‹_›, rfl⟩ <;>
      simp [mem_union, *]
#align set.image2_union_left Set.image2_union_left

/- warning: set.image2_union_right -> Set.image2_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {t' : Set.{u2} β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t t')) (Union.union.{u3} (Set.{u3} γ) (Set.hasUnion.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β} {t' : Set.{u1} β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet_1.{u1} β) t t')) (Union.union.{u3} (Set.{u3} γ) (Set.instUnionSet_1.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s t) (Set.image2.{u2, u1, u3} α β γ f s t'))
Case conversion may be inaccurate. Consider using '#align set.image2_union_right Set.image2_union_rightₓ'. -/
theorem image2_union_right : image2 f s (t ∪ t') = image2 f s t ∪ image2 f s t' :=
  by
  ext c
  constructor
  · rintro ⟨a, b, ha, h1b | h2b, rfl⟩ <;> [left, right] <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
  ·
    rintro (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> refine' ⟨_, _, ‹_›, _, rfl⟩ <;>
      simp [mem_union, *]
#align set.image2_union_right Set.image2_union_right

/- warning: set.image2_inter_left -> Set.image2_inter_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u2} β}, (Function.Injective2.{succ u1, succ u2, succ u3} α β γ f) -> (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') t) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s' t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {s : Set.{u3} α} {s' : Set.{u3} α} {t : Set.{u2} β}, (Function.Injective2.{succ u3, succ u2, succ u1} α β γ f) -> (Eq.{succ u1} (Set.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet_1.{u3} α) s s') t) (Inter.inter.{u1} (Set.{u1} γ) (Set.instInterSet_1.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f s t) (Set.image2.{u3, u2, u1} α β γ f s' t)))
Case conversion may be inaccurate. Consider using '#align set.image2_inter_left Set.image2_inter_leftₓ'. -/
theorem image2_inter_left (hf : Injective2 f) :
    image2 f (s ∩ s') t = image2 f s t ∩ image2 f s' t := by
  simp_rw [← image_uncurry_prod, inter_prod, image_inter hf.uncurry]
#align set.image2_inter_left Set.image2_inter_left

/- warning: set.image2_inter_right -> Set.image2_inter_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {t' : Set.{u2} β}, (Function.Injective2.{succ u1, succ u2, succ u3} α β γ f) -> (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t t')) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s t')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β} {t' : Set.{u2} β}, (Function.Injective2.{succ u3, succ u2, succ u1} α β γ f) -> (Eq.{succ u1} (Set.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f s (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet_1.{u2} β) t t')) (Inter.inter.{u1} (Set.{u1} γ) (Set.instInterSet_1.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f s t) (Set.image2.{u3, u2, u1} α β γ f s t')))
Case conversion may be inaccurate. Consider using '#align set.image2_inter_right Set.image2_inter_rightₓ'. -/
theorem image2_inter_right (hf : Injective2 f) :
    image2 f s (t ∩ t') = image2 f s t ∩ image2 f s t' := by
  simp_rw [← image_uncurry_prod, prod_inter, image_inter hf.uncurry]
#align set.image2_inter_right Set.image2_inter_right

/- warning: set.image2_empty_left -> Set.image2_empty_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {t : Set.{u2} β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) t) (EmptyCollection.emptyCollection.{u3} (Set.{u3} γ) (Set.hasEmptyc.{u3} γ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {t : Set.{u1} β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)) t) (EmptyCollection.emptyCollection.{u3} (Set.{u3} γ) (Set.instEmptyCollectionSet.{u3} γ))
Case conversion may be inaccurate. Consider using '#align set.image2_empty_left Set.image2_empty_leftₓ'. -/
@[simp]
theorem image2_empty_left : image2 f ∅ t = ∅ :=
  ext <| by simp
#align set.image2_empty_left Set.image2_empty_left

/- warning: set.image2_empty_right -> Set.image2_empty_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (EmptyCollection.emptyCollection.{u3} (Set.{u3} γ) (Set.hasEmptyc.{u3} γ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (EmptyCollection.emptyCollection.{u3} (Set.{u3} γ) (Set.instEmptyCollectionSet.{u3} γ))
Case conversion may be inaccurate. Consider using '#align set.image2_empty_right Set.image2_empty_rightₓ'. -/
@[simp]
theorem image2_empty_right : image2 f s ∅ = ∅ :=
  ext <| by simp
#align set.image2_empty_right Set.image2_empty_right

/- warning: set.nonempty.image2 -> Set.Nonempty.image2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β t) -> (Set.Nonempty.{u3} γ (Set.image2.{u1, u2, u3} α β γ f s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β}, (Set.Nonempty.{u3} α s) -> (Set.Nonempty.{u2} β t) -> (Set.Nonempty.{u1} γ (Set.image2.{u3, u2, u1} α β γ f s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty.image2 Set.Nonempty.image2ₓ'. -/
theorem Nonempty.image2 : s.Nonempty → t.Nonempty → (image2 f s t).Nonempty :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨_, mem_image2_of_mem ha hb⟩
#align set.nonempty.image2 Set.Nonempty.image2

/- warning: set.image2_nonempty_iff -> Set.image2_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (Set.Nonempty.{u3} γ (Set.image2.{u1, u2, u3} α β γ f s t)) (And (Set.Nonempty.{u1} α s) (Set.Nonempty.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (Set.Nonempty.{u3} γ (Set.image2.{u2, u1, u3} α β γ f s t)) (And (Set.Nonempty.{u2} α s) (Set.Nonempty.{u1} β t))
Case conversion may be inaccurate. Consider using '#align set.image2_nonempty_iff Set.image2_nonempty_iffₓ'. -/
@[simp]
theorem image2_nonempty_iff : (image2 f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun ⟨_, a, b, ha, hb, _⟩ => ⟨⟨a, ha⟩, b, hb⟩, fun h => h.1.image2 h.2⟩
#align set.image2_nonempty_iff Set.image2_nonempty_iff

/- warning: set.nonempty.of_image2_left -> Set.Nonempty.of_image2_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u3} γ (Set.image2.{u1, u2, u3} α β γ f s t)) -> (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u3} γ (Set.image2.{u2, u1, u3} α β γ f s t)) -> (Set.Nonempty.{u2} α s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.of_image2_left Set.Nonempty.of_image2_leftₓ'. -/
theorem Nonempty.of_image2_left (h : (image2 f s t).Nonempty) : s.Nonempty :=
  (image2_nonempty_iff.1 h).1
#align set.nonempty.of_image2_left Set.Nonempty.of_image2_left

/- warning: set.nonempty.of_image2_right -> Set.Nonempty.of_image2_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u3} γ (Set.image2.{u1, u2, u3} α β γ f s t)) -> (Set.Nonempty.{u2} β t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u3} γ (Set.image2.{u2, u1, u3} α β γ f s t)) -> (Set.Nonempty.{u1} β t)
Case conversion may be inaccurate. Consider using '#align set.nonempty.of_image2_right Set.Nonempty.of_image2_rightₓ'. -/
theorem Nonempty.of_image2_right (h : (image2 f s t).Nonempty) : t.Nonempty :=
  (image2_nonempty_iff.1 h).2
#align set.nonempty.of_image2_right Set.Nonempty.of_image2_right

/- warning: set.image2_eq_empty_iff -> Set.image2_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (EmptyCollection.emptyCollection.{u3} (Set.{u3} γ) (Set.hasEmptyc.{u3} γ))) (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s t) (EmptyCollection.emptyCollection.{u3} (Set.{u3} γ) (Set.instEmptyCollectionSet.{u3} γ))) (Or (Eq.{succ u2} (Set.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Eq.{succ u1} (Set.{u1} β) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))))
Case conversion may be inaccurate. Consider using '#align set.image2_eq_empty_iff Set.image2_eq_empty_iffₓ'. -/
@[simp]
theorem image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp_rw [← not_nonempty_iff_eq_empty, image2_nonempty_iff, not_and_or]
#align set.image2_eq_empty_iff Set.image2_eq_empty_iff

/- warning: set.image2_inter_subset_left -> Set.image2_inter_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u2} β}, HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') t) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s' t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {s' : Set.{u2} α} {t : Set.{u1} β}, HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet_1.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s s') t) (Inter.inter.{u3} (Set.{u3} γ) (Set.instInterSet_1.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s t) (Set.image2.{u2, u1, u3} α β γ f s' t))
Case conversion may be inaccurate. Consider using '#align set.image2_inter_subset_left Set.image2_inter_subset_leftₓ'. -/
theorem image2_inter_subset_left : image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t :=
  by
  rintro _ ⟨a, b, ⟨h1a, h2a⟩, hb, rfl⟩
  constructor <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
#align set.image2_inter_subset_left Set.image2_inter_subset_left

/- warning: set.image2_inter_subset_right -> Set.image2_inter_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {t' : Set.{u2} β}, HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t t')) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f s t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β} {t' : Set.{u1} β}, HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet_1.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t t')) (Inter.inter.{u3} (Set.{u3} γ) (Set.instInterSet_1.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s t) (Set.image2.{u2, u1, u3} α β γ f s t'))
Case conversion may be inaccurate. Consider using '#align set.image2_inter_subset_right Set.image2_inter_subset_rightₓ'. -/
theorem image2_inter_subset_right : image2 f s (t ∩ t') ⊆ image2 f s t ∩ image2 f s t' :=
  by
  rintro _ ⟨a, b, ha, ⟨h1b, h2b⟩, rfl⟩
  constructor <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
#align set.image2_inter_subset_right Set.image2_inter_subset_right

/- warning: set.image2_singleton_left -> Set.image2_singleton_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {t : Set.{u2} β} {a : α}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) t) (Set.image.{u2, u3} β γ (f a) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {t : Set.{u1} β} {a : α}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a) t) (Set.image.{u1, u3} β γ (f a) t)
Case conversion may be inaccurate. Consider using '#align set.image2_singleton_left Set.image2_singleton_leftₓ'. -/
@[simp]
theorem image2_singleton_left : image2 f {a} t = f a '' t :=
  ext fun x => by simp
#align set.image2_singleton_left Set.image2_singleton_left

/- warning: set.image2_singleton_right -> Set.image2_singleton_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {b : β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (Set.image.{u1, u3} α γ (fun (a : α) => f a b) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {b : β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (Set.image.{u2, u3} α γ (fun (a : α) => f a b) s)
Case conversion may be inaccurate. Consider using '#align set.image2_singleton_right Set.image2_singleton_rightₓ'. -/
@[simp]
theorem image2_singleton_right : image2 f s {b} = (fun a => f a b) '' s :=
  ext fun x => by simp
#align set.image2_singleton_right Set.image2_singleton_right

/- warning: set.image2_singleton -> Set.image2_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {a : α} {b : β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (Singleton.singleton.{u3, u3} γ (Set.{u3} γ) (Set.hasSingleton.{u3} γ) (f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {a : α} {b : β}, Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (Singleton.singleton.{u3, u3} γ (Set.{u3} γ) (Set.instSingletonSet.{u3} γ) (f a b))
Case conversion may be inaccurate. Consider using '#align set.image2_singleton Set.image2_singletonₓ'. -/
theorem image2_singleton : image2 f {a} {b} = {f a b} := by simp
#align set.image2_singleton Set.image2_singleton

/- warning: set.image2_congr -> Set.image2_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {f' : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (Eq.{succ u3} γ (f a b) (f' a b)))) -> (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f' s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {f' : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β}, (forall (a : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a s) -> (forall (b : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) -> (Eq.{succ u1} γ (f a b) (f' a b)))) -> (Eq.{succ u1} (Set.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f s t) (Set.image2.{u3, u2, u1} α β γ f' s t))
Case conversion may be inaccurate. Consider using '#align set.image2_congr Set.image2_congrₓ'. -/
@[congr]
theorem image2_congr (h : ∀ a ∈ s, ∀ b ∈ t, f a b = f' a b) : image2 f s t = image2 f' s t :=
  by
  ext
  constructor <;> rintro ⟨a, b, ha, hb, rfl⟩ <;> refine' ⟨a, b, ha, hb, by rw [h a ha b hb]⟩
#align set.image2_congr Set.image2_congr

/- warning: set.image2_congr' -> Set.image2_congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {f' : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (f' a b)) -> (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u1, u2, u3} α β γ f' s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {f' : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (f' a b)) -> (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s t) (Set.image2.{u2, u1, u3} α β γ f' s t))
Case conversion may be inaccurate. Consider using '#align set.image2_congr' Set.image2_congr'ₓ'. -/
/-- A common special case of `image2_congr` -/
theorem image2_congr' (h : ∀ a b, f a b = f' a b) : image2 f s t = image2 f' s t :=
  image2_congr fun a _ b _ => h a b
#align set.image2_congr' Set.image2_congr'

#print Set.image3 /-
/-- The image of a ternary function `f : α → β → γ → δ` as a function
  `set α → set β → set γ → set δ`. Mathematically this should be thought of as the image of the
  corresponding function `α × β × γ → δ`.
-/
def image3 (g : α → β → γ → δ) (s : Set α) (t : Set β) (u : Set γ) : Set δ :=
  { d | ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d }
#align set.image3 Set.image3
-/

/- warning: set.mem_image3 -> Set.mem_image3 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {g : α -> β -> γ -> δ} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ} {d : δ}, Iff (Membership.Mem.{u4, u4} δ (Set.{u4} δ) (Set.hasMem.{u4} δ) d (Set.image3.{u1, u2, u3, u4} α β γ δ g s t u)) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u2} β (fun (b : β) => Exists.{succ u3} γ (fun (c : γ) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (And (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) (And (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c u) (Eq.{succ u4} δ (g a b c) d)))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u4}} {g : α -> β -> γ -> δ} {s : Set.{u3} α} {t : Set.{u2} β} {u : Set.{u1} γ} {d : δ}, Iff (Membership.mem.{u4, u4} δ (Set.{u4} δ) (Set.instMembershipSet.{u4} δ) d (Set.image3.{u3, u2, u1, u4} α β γ δ g s t u)) (Exists.{succ u3} α (fun (a : α) => Exists.{succ u2} β (fun (b : β) => Exists.{succ u1} γ (fun (c : γ) => And (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a s) (And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) (And (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) c u) (Eq.{succ u4} δ (g a b c) d)))))))
Case conversion may be inaccurate. Consider using '#align set.mem_image3 Set.mem_image3ₓ'. -/
@[simp]
theorem mem_image3 : d ∈ image3 g s t u ↔ ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d :=
  Iff.rfl
#align set.mem_image3 Set.mem_image3

/- warning: set.image3_mono -> Set.image3_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {g : α -> β -> γ -> δ} {s : Set.{u1} α} {s' : Set.{u1} α} {t : Set.{u2} β} {t' : Set.{u2} β} {u : Set.{u3} γ} {u' : Set.{u3} γ}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s s') -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t t') -> (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) u u') -> (HasSubset.Subset.{u4} (Set.{u4} δ) (Set.hasSubset.{u4} δ) (Set.image3.{u1, u2, u3, u4} α β γ δ g s t u) (Set.image3.{u1, u2, u3, u4} α β γ δ g s' t' u'))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} {g : α -> β -> γ -> δ} {s : Set.{u4} α} {s' : Set.{u4} α} {t : Set.{u3} β} {t' : Set.{u3} β} {u : Set.{u2} γ} {u' : Set.{u2} γ}, (HasSubset.Subset.{u4} (Set.{u4} α) (Set.instHasSubsetSet_1.{u4} α) s s') -> (HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet_1.{u3} β) t t') -> (HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet_1.{u2} γ) u u') -> (HasSubset.Subset.{u1} (Set.{u1} δ) (Set.instHasSubsetSet_1.{u1} δ) (Set.image3.{u4, u3, u2, u1} α β γ δ g s t u) (Set.image3.{u4, u3, u2, u1} α β γ δ g s' t' u'))
Case conversion may be inaccurate. Consider using '#align set.image3_mono Set.image3_monoₓ'. -/
theorem image3_mono (hs : s ⊆ s') (ht : t ⊆ t') (hu : u ⊆ u') :
    image3 g s t u ⊆ image3 g s' t' u' := fun x =>
  Exists₃Cat.imp fun a b c ⟨ha, hb, hc, hx⟩ => ⟨hs ha, ht hb, hu hc, hx⟩
#align set.image3_mono Set.image3_mono

/- warning: set.image3_congr -> Set.image3_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {g : α -> β -> γ -> δ} {g' : α -> β -> γ -> δ} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (forall (c : γ), (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c u) -> (Eq.{succ u4} δ (g a b c) (g' a b c))))) -> (Eq.{succ u4} (Set.{u4} δ) (Set.image3.{u1, u2, u3, u4} α β γ δ g s t u) (Set.image3.{u1, u2, u3, u4} α β γ δ g' s t u))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} {g : α -> β -> γ -> δ} {g' : α -> β -> γ -> δ} {s : Set.{u4} α} {t : Set.{u3} β} {u : Set.{u2} γ}, (forall (a : α), (Membership.mem.{u4, u4} α (Set.{u4} α) (Set.instMembershipSet.{u4} α) a s) -> (forall (b : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b t) -> (forall (c : γ), (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) c u) -> (Eq.{succ u1} δ (g a b c) (g' a b c))))) -> (Eq.{succ u1} (Set.{u1} δ) (Set.image3.{u4, u3, u2, u1} α β γ δ g s t u) (Set.image3.{u4, u3, u2, u1} α β γ δ g' s t u))
Case conversion may be inaccurate. Consider using '#align set.image3_congr Set.image3_congrₓ'. -/
@[congr]
theorem image3_congr (h : ∀ a ∈ s, ∀ b ∈ t, ∀ c ∈ u, g a b c = g' a b c) :
    image3 g s t u = image3 g' s t u := by
  ext x
  constructor <;> rintro ⟨a, b, c, ha, hb, hc, rfl⟩ <;>
    exact ⟨a, b, c, ha, hb, hc, by rw [h a ha b hb c hc]⟩
#align set.image3_congr Set.image3_congr

/- warning: set.image3_congr' -> Set.image3_congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {g : α -> β -> γ -> δ} {g' : α -> β -> γ -> δ} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ}, (forall (a : α) (b : β) (c : γ), Eq.{succ u4} δ (g a b c) (g' a b c)) -> (Eq.{succ u4} (Set.{u4} δ) (Set.image3.{u1, u2, u3, u4} α β γ δ g s t u) (Set.image3.{u1, u2, u3, u4} α β γ δ g' s t u))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u4}} {g : α -> β -> γ -> δ} {g' : α -> β -> γ -> δ} {s : Set.{u3} α} {t : Set.{u2} β} {u : Set.{u1} γ}, (forall (a : α) (b : β) (c : γ), Eq.{succ u4} δ (g a b c) (g' a b c)) -> (Eq.{succ u4} (Set.{u4} δ) (Set.image3.{u3, u2, u1, u4} α β γ δ g s t u) (Set.image3.{u3, u2, u1, u4} α β γ δ g' s t u))
Case conversion may be inaccurate. Consider using '#align set.image3_congr' Set.image3_congr'ₓ'. -/
/-- A common special case of `image3_congr` -/
theorem image3_congr' (h : ∀ a b c, g a b c = g' a b c) : image3 g s t u = image3 g' s t u :=
  image3_congr fun a _ b _ c _ => h a b c
#align set.image3_congr' Set.image3_congr'

/- warning: set.image2_image2_left -> Set.image2_image2_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ} (f : δ -> γ -> ε) (g : α -> β -> δ), Eq.{succ u5} (Set.{u5} ε) (Set.image2.{u4, u3, u5} δ γ ε f (Set.image2.{u1, u2, u4} α β δ g s t) u) (Set.image3.{u1, u2, u3, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => f (g a b) c) s t u)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {s : Set.{u2} α} {t : Set.{u1} β} {u : Set.{u3} γ} (f : δ -> γ -> ε) (g : α -> β -> δ), Eq.{succ u5} (Set.{u5} ε) (Set.image2.{u4, u3, u5} δ γ ε f (Set.image2.{u2, u1, u4} α β δ g s t) u) (Set.image3.{u2, u1, u3, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => f (g a b) c) s t u)
Case conversion may be inaccurate. Consider using '#align set.image2_image2_left Set.image2_image2_leftₓ'. -/
theorem image2_image2_left (f : δ → γ → ε) (g : α → β → δ) :
    image2 f (image2 g s t) u = image3 (fun a b c => f (g a b) c) s t u :=
  by
  ext; constructor
  · rintro ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
    refine' ⟨a, b, c, ha, hb, hc, rfl⟩
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    refine' ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
#align set.image2_image2_left Set.image2_image2_left

/- warning: set.image2_image2_right -> Set.image2_image2_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ} (f : α -> δ -> ε) (g : β -> γ -> δ), Eq.{succ u5} (Set.{u5} ε) (Set.image2.{u1, u4, u5} α δ ε f s (Set.image2.{u2, u3, u4} β γ δ g t u)) (Set.image3.{u1, u2, u3, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => f a (g b c)) s t u)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u3}} {ε : Type.{u5}} {s : Set.{u4} α} {t : Set.{u2} β} {u : Set.{u1} γ} (f : α -> δ -> ε) (g : β -> γ -> δ), Eq.{succ u5} (Set.{u5} ε) (Set.image2.{u4, u3, u5} α δ ε f s (Set.image2.{u2, u1, u3} β γ δ g t u)) (Set.image3.{u4, u2, u1, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => f a (g b c)) s t u)
Case conversion may be inaccurate. Consider using '#align set.image2_image2_right Set.image2_image2_rightₓ'. -/
theorem image2_image2_right (f : α → δ → ε) (g : β → γ → δ) :
    image2 f s (image2 g t u) = image3 (fun a b c => f a (g b c)) s t u :=
  by
  ext; constructor
  · rintro ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
    refine' ⟨a, b, c, ha, hb, hc, rfl⟩
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    refine' ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
#align set.image2_image2_right Set.image2_image2_right

/- warning: set.image_image2 -> Set.image_image2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {s : Set.{u1} α} {t : Set.{u2} β} (f : α -> β -> γ) (g : γ -> δ), Eq.{succ u4} (Set.{u4} δ) (Set.image.{u3, u4} γ δ g (Set.image2.{u1, u2, u3} α β γ f s t)) (Set.image2.{u1, u2, u4} α β δ (fun (a : α) (b : β) => g (f a b)) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Type.{u4}} {s : Set.{u2} α} {t : Set.{u1} β} (f : α -> β -> γ) (g : γ -> δ), Eq.{succ u4} (Set.{u4} δ) (Set.image.{u3, u4} γ δ g (Set.image2.{u2, u1, u3} α β γ f s t)) (Set.image2.{u2, u1, u4} α β δ (fun (a : α) (b : β) => g (f a b)) s t)
Case conversion may be inaccurate. Consider using '#align set.image_image2 Set.image_image2ₓ'. -/
theorem image_image2 (f : α → β → γ) (g : γ → δ) :
    g '' image2 f s t = image2 (fun a b => g (f a b)) s t :=
  by
  ext; constructor
  · rintro ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩
#align set.image_image2 Set.image_image2

#print Set.image2_image_left /-
theorem image2_image_left (f : γ → β → δ) (g : α → γ) :
    image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t :=
  by
  ext; constructor
  · rintro ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩
#align set.image2_image_left Set.image2_image_left
-/

/- warning: set.image2_image_right -> Set.image2_image_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {s : Set.{u1} α} {t : Set.{u2} β} (f : α -> γ -> δ) (g : β -> γ), Eq.{succ u4} (Set.{u4} δ) (Set.image2.{u1, u3, u4} α γ δ f s (Set.image.{u2, u3} β γ g t)) (Set.image2.{u1, u2, u4} α β δ (fun (a : α) (b : β) => f a (g b)) s t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {δ : Type.{u4}} {s : Set.{u3} α} {t : Set.{u1} β} (f : α -> γ -> δ) (g : β -> γ), Eq.{succ u4} (Set.{u4} δ) (Set.image2.{u3, u2, u4} α γ δ f s (Set.image.{u1, u2} β γ g t)) (Set.image2.{u3, u1, u4} α β δ (fun (a : α) (b : β) => f a (g b)) s t)
Case conversion may be inaccurate. Consider using '#align set.image2_image_right Set.image2_image_rightₓ'. -/
theorem image2_image_right (f : α → γ → δ) (g : β → γ) :
    image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t :=
  by
  ext; constructor
  · rintro ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩
#align set.image2_image_right Set.image2_image_right

/- warning: set.image2_swap -> Set.image2_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u2, u1, u3} β α γ (fun (a : β) (b : α) => f b a) t s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (s : Set.{u3} α) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} γ) (Set.image2.{u3, u2, u1} α β γ f s t) (Set.image2.{u2, u3, u1} β α γ (fun (a : β) (b : α) => f b a) t s)
Case conversion may be inaccurate. Consider using '#align set.image2_swap Set.image2_swapₓ'. -/
theorem image2_swap (f : α → β → γ) (s : Set α) (t : Set β) :
    image2 f s t = image2 (fun a b => f b a) t s :=
  by
  ext
  constructor <;> rintro ⟨a, b, ha, hb, rfl⟩ <;> refine' ⟨b, a, hb, ha, rfl⟩
#align set.image2_swap Set.image2_swap

#print Set.image2_left /-
@[simp]
theorem image2_left (h : t.Nonempty) : image2 (fun x y => x) s t = s := by
  simp [nonempty_def.mp h, ext_iff]
#align set.image2_left Set.image2_left
-/

/- warning: set.image2_right -> Set.image2_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} (Set.{u2} β) (Set.image2.{u1, u2, u2} α β β (fun (x : α) (y : β) => y) s t) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u2} α s) -> (Eq.{succ u1} (Set.{u1} β) (Set.image2.{u2, u1, u1} α β β (fun (x : α) (y : β) => y) s t) t)
Case conversion may be inaccurate. Consider using '#align set.image2_right Set.image2_rightₓ'. -/
@[simp]
theorem image2_right (h : s.Nonempty) : image2 (fun x y => y) s t = t := by
  simp [nonempty_def.mp h, ext_iff]
#align set.image2_right Set.image2_right

/- warning: set.image2_assoc -> Set.image2_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {ε' : Type.{u6}} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (f (g a b) c) (f' a (g' b c))) -> (Eq.{succ u5} (Set.{u5} ε) (Set.image2.{u4, u3, u5} δ γ ε f (Set.image2.{u1, u2, u4} α β δ g s t) u) (Set.image2.{u1, u6, u5} α ε' ε f' s (Set.image2.{u2, u3, u6} β γ ε' g' t u)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} {ε : Type.{u6}} {ε' : Type.{u1}} {s : Set.{u3} α} {t : Set.{u2} β} {u : Set.{u4} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f (g a b) c) (f' a (g' b c))) -> (Eq.{succ u6} (Set.{u6} ε) (Set.image2.{u5, u4, u6} δ γ ε f (Set.image2.{u3, u2, u5} α β δ g s t) u) (Set.image2.{u3, u1, u6} α ε' ε f' s (Set.image2.{u2, u4, u1} β γ ε' g' t u)))
Case conversion may be inaccurate. Consider using '#align set.image2_assoc Set.image2_assocₓ'. -/
theorem image2_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    image2 f (image2 g s t) u = image2 f' s (image2 g' t u) := by
  simp only [image2_image2_left, image2_image2_right, h_assoc]
#align set.image2_assoc Set.image2_assoc

/- warning: set.image2_comm -> Set.image2_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {g : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (g b a)) -> (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u1, u2, u3} α β γ f s t) (Set.image2.{u2, u1, u3} β α γ g t s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β -> γ} {s : Set.{u2} α} {t : Set.{u1} β} {g : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (g b a)) -> (Eq.{succ u3} (Set.{u3} γ) (Set.image2.{u2, u1, u3} α β γ f s t) (Set.image2.{u1, u2, u3} β α γ g t s))
Case conversion may be inaccurate. Consider using '#align set.image2_comm Set.image2_commₓ'. -/
theorem image2_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image2 f s t = image2 g t s :=
  (image2_swap _ _ _).trans <| by simp_rw [h_comm]
#align set.image2_comm Set.image2_comm

/- warning: set.image2_left_comm -> Set.image2_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {δ' : Type.{u5}} {ε : Type.{u6}} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f a (g b c)) (g' b (f' a c))) -> (Eq.{succ u6} (Set.{u6} ε) (Set.image2.{u1, u4, u6} α δ ε f s (Set.image2.{u2, u3, u4} β γ δ g t u)) (Set.image2.{u2, u5, u6} β δ' ε g' t (Set.image2.{u1, u3, u5} α γ δ' f' s u)))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u4}} {δ' : Type.{u1}} {ε : Type.{u6}} {s : Set.{u5} α} {t : Set.{u3} β} {u : Set.{u2} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f a (g b c)) (g' b (f' a c))) -> (Eq.{succ u6} (Set.{u6} ε) (Set.image2.{u5, u4, u6} α δ ε f s (Set.image2.{u3, u2, u4} β γ δ g t u)) (Set.image2.{u3, u1, u6} β δ' ε g' t (Set.image2.{u5, u2, u1} α γ δ' f' s u)))
Case conversion may be inaccurate. Consider using '#align set.image2_left_comm Set.image2_left_commₓ'. -/
theorem image2_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    image2 f s (image2 g t u) = image2 g' t (image2 f' s u) :=
  by
  rw [image2_swap f', image2_swap f]
  exact image2_assoc fun _ _ _ => h_left_comm _ _ _
#align set.image2_left_comm Set.image2_left_comm

/- warning: set.image2_right_comm -> Set.image2_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {δ' : Type.{u5}} {ε : Type.{u6}} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f (g a b) c) (g' (f' a c) b)) -> (Eq.{succ u6} (Set.{u6} ε) (Set.image2.{u4, u3, u6} δ γ ε f (Set.image2.{u1, u2, u4} α β δ g s t) u) (Set.image2.{u5, u2, u6} δ' β ε g' (Set.image2.{u1, u3, u5} α γ δ' f' s u) t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} {δ' : Type.{u1}} {ε : Type.{u6}} {s : Set.{u3} α} {t : Set.{u2} β} {u : Set.{u4} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f (g a b) c) (g' (f' a c) b)) -> (Eq.{succ u6} (Set.{u6} ε) (Set.image2.{u5, u4, u6} δ γ ε f (Set.image2.{u3, u2, u5} α β δ g s t) u) (Set.image2.{u1, u2, u6} δ' β ε g' (Set.image2.{u3, u4, u1} α γ δ' f' s u) t))
Case conversion may be inaccurate. Consider using '#align set.image2_right_comm Set.image2_right_commₓ'. -/
theorem image2_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image2 f (image2 g s t) u = image2 g' (image2 f' s u) t :=
  by
  rw [image2_swap g, image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _
#align set.image2_right_comm Set.image2_right_comm

/- warning: set.image_image2_distrib -> Set.image_image2_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u3} β} {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ a) (g₂ b))) -> (Eq.{succ u6} (Set.{u6} δ) (Set.image.{u5, u6} γ δ g (Set.image2.{u1, u3, u5} α β γ f s t)) (Set.image2.{u2, u4, u6} α' β' δ f' (Set.image.{u1, u2} α α' g₁ s) (Set.image.{u3, u4} β β' g₂ t)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u1}} {γ : Type.{u5}} {δ : Type.{u6}} {f : α -> β -> γ} {s : Set.{u4} α} {t : Set.{u3} β} {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ a) (g₂ b))) -> (Eq.{succ u6} (Set.{u6} δ) (Set.image.{u5, u6} γ δ g (Set.image2.{u4, u3, u5} α β γ f s t)) (Set.image2.{u2, u1, u6} α' β' δ f' (Set.image.{u4, u2} α α' g₁ s) (Set.image.{u3, u1} β β' g₂ t)))
Case conversion may be inaccurate. Consider using '#align set.image_image2_distrib Set.image_image2_distribₓ'. -/
theorem image_image2_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image2 f s t).image g = image2 f' (s.image g₁) (t.image g₂) := by
  simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]
#align set.image_image2_distrib Set.image_image2_distrib

/- warning: set.image_image2_distrib_left -> Set.image_image2_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u3} β} {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' a) b)) -> (Eq.{succ u5} (Set.{u5} δ) (Set.image.{u4, u5} γ δ g (Set.image2.{u1, u3, u4} α β γ f s t)) (Set.image2.{u2, u3, u5} α' β δ f' (Set.image.{u1, u2} α α' g' s) t))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β} {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' a) b)) -> (Eq.{succ u5} (Set.{u5} δ) (Set.image.{u4, u5} γ δ g (Set.image2.{u3, u2, u4} α β γ f s t)) (Set.image2.{u1, u2, u5} α' β δ f' (Set.image.{u3, u1} α α' g' s) t))
Case conversion may be inaccurate. Consider using '#align set.image_image2_distrib_left Set.image_image2_distrib_leftₓ'. -/
/-- Symmetric statement to `set.image2_image_left_comm`. -/
theorem image_image2_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
    (image2 f s t).image g = image2 f' (s.image g') t :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']
#align set.image_image2_distrib_left Set.image_image2_distrib_left

/- warning: set.image_image2_distrib_right -> Set.image_image2_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' a (g' b))) -> (Eq.{succ u5} (Set.{u5} δ) (Set.image.{u4, u5} γ δ g (Set.image2.{u1, u2, u4} α β γ f s t)) (Set.image2.{u1, u3, u5} α β' δ f' s (Set.image.{u2, u3} β β' g' t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {β' : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β} {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' a (g' b))) -> (Eq.{succ u5} (Set.{u5} δ) (Set.image.{u4, u5} γ δ g (Set.image2.{u3, u2, u4} α β γ f s t)) (Set.image2.{u3, u1, u5} α β' δ f' s (Set.image.{u2, u1} β β' g' t)))
Case conversion may be inaccurate. Consider using '#align set.image_image2_distrib_right Set.image_image2_distrib_rightₓ'. -/
/-- Symmetric statement to `set.image_image2_right_comm`. -/
theorem image_image2_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
    (image2 f s t).image g = image2 f' s (t.image g') :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']
#align set.image_image2_distrib_right Set.image_image2_distrib_right

/- warning: set.image2_image_left_comm -> Set.image2_image_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {s : Set.{u1} α} {t : Set.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f (g a) b) (g' (f' a b))) -> (Eq.{succ u4} (Set.{u4} γ) (Set.image2.{u2, u3, u4} α' β γ f (Set.image.{u1, u2} α α' g s) t) (Set.image.{u5, u4} δ γ g' (Set.image2.{u1, u3, u5} α β δ f' s t)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u4}} {β : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} {s : Set.{u2} α} {t : Set.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (f (g a) b) (g' (f' a b))) -> (Eq.{succ u5} (Set.{u5} γ) (Set.image2.{u4, u3, u5} α' β γ f (Set.image.{u2, u4} α α' g s) t) (Set.image.{u1, u5} δ γ g' (Set.image2.{u2, u3, u1} α β δ f' s t)))
Case conversion may be inaccurate. Consider using '#align set.image2_image_left_comm Set.image2_image_left_commₓ'. -/
/-- Symmetric statement to `set.image_image2_distrib_left`. -/
theorem image2_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
    image2 f (s.image g) t = (image2 f' s t).image g' :=
  (image_image2_distrib_left fun a b => (h_left_comm a b).symm).symm
#align set.image2_image_left_comm Set.image2_image_left_comm

/- warning: set.image_image2_right_comm -> Set.image_image2_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f a (g b)) (g' (f' a b))) -> (Eq.{succ u4} (Set.{u4} γ) (Set.image2.{u1, u3, u4} α β' γ f s (Set.image.{u2, u3} β β' g t)) (Set.image.{u5, u4} δ γ g' (Set.image2.{u1, u2, u5} α β δ f' s t)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} {s : Set.{u4} α} {t : Set.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (f a (g b)) (g' (f' a b))) -> (Eq.{succ u5} (Set.{u5} γ) (Set.image2.{u4, u3, u5} α β' γ f s (Set.image.{u2, u3} β β' g t)) (Set.image.{u1, u5} δ γ g' (Set.image2.{u4, u2, u1} α β δ f' s t)))
Case conversion may be inaccurate. Consider using '#align set.image_image2_right_comm Set.image_image2_right_commₓ'. -/
/-- Symmetric statement to `set.image_image2_distrib_right`. -/
theorem image_image2_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
    image2 f s (t.image g) = (image2 f' s t).image g' :=
  (image_image2_distrib_right fun a b => (h_right_comm a b).symm).symm
#align set.image_image2_right_comm Set.image_image2_right_comm

/- warning: set.image2_distrib_subset_left -> Set.image2_distrib_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {γ' : Type.{u5}} {δ : Type.{u6}} {ε : Type.{u7}} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u4} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u7} ε (f a (g b c)) (g' (f₁ a b) (f₂ a c))) -> (HasSubset.Subset.{u7} (Set.{u7} ε) (Set.hasSubset.{u7} ε) (Set.image2.{u1, u6, u7} α δ ε f s (Set.image2.{u2, u4, u6} β γ δ g t u)) (Set.image2.{u3, u5, u7} β' γ' ε g' (Set.image2.{u1, u2, u3} α β β' f₁ s t) (Set.image2.{u1, u4, u5} α γ γ' f₂ s u)))
but is expected to have type
  forall {α : Type.{u6}} {β : Type.{u4}} {β' : Type.{u2}} {γ : Type.{u3}} {γ' : Type.{u1}} {δ : Type.{u5}} {ε : Type.{u7}} {s : Set.{u6} α} {t : Set.{u4} β} {u : Set.{u3} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u7} ε (f a (g b c)) (g' (f₁ a b) (f₂ a c))) -> (HasSubset.Subset.{u7} (Set.{u7} ε) (Set.instHasSubsetSet_1.{u7} ε) (Set.image2.{u6, u5, u7} α δ ε f s (Set.image2.{u4, u3, u5} β γ δ g t u)) (Set.image2.{u2, u1, u7} β' γ' ε g' (Set.image2.{u6, u4, u2} α β β' f₁ s t) (Set.image2.{u6, u3, u1} α γ γ' f₂ s u)))
Case conversion may be inaccurate. Consider using '#align set.image2_distrib_subset_left Set.image2_distrib_subset_leftₓ'. -/
/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
theorem image2_distrib_subset_left {f : α → δ → ε} {g : β → γ → δ} {f₁ : α → β → β'}
    {f₂ : α → γ → γ'} {g' : β' → γ' → ε} (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image2 f s (image2 g t u) ⊆ image2 g' (image2 f₁ s t) (image2 f₂ s u) :=
  by
  rintro _ ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
  rw [h_distrib]
  exact mem_image2_of_mem (mem_image2_of_mem ha hb) (mem_image2_of_mem ha hc)
#align set.image2_distrib_subset_left Set.image2_distrib_subset_left

/- warning: set.image2_distrib_subset_right -> Set.image2_distrib_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} {ε : Type.{u7}} {s : Set.{u1} α} {t : Set.{u3} β} {u : Set.{u5} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u7} ε (f (g a b) c) (g' (f₁ a c) (f₂ b c))) -> (HasSubset.Subset.{u7} (Set.{u7} ε) (Set.hasSubset.{u7} ε) (Set.image2.{u6, u5, u7} δ γ ε f (Set.image2.{u1, u3, u6} α β δ g s t) u) (Set.image2.{u2, u4, u7} α' β' ε g' (Set.image2.{u1, u5, u2} α γ α' f₁ s u) (Set.image2.{u3, u5, u4} β γ β' f₂ t u)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u1}} {γ : Type.{u5}} {δ : Type.{u6}} {ε : Type.{u7}} {s : Set.{u4} α} {t : Set.{u3} β} {u : Set.{u5} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u7} ε (f (g a b) c) (g' (f₁ a c) (f₂ b c))) -> (HasSubset.Subset.{u7} (Set.{u7} ε) (Set.instHasSubsetSet_1.{u7} ε) (Set.image2.{u6, u5, u7} δ γ ε f (Set.image2.{u4, u3, u6} α β δ g s t) u) (Set.image2.{u2, u1, u7} α' β' ε g' (Set.image2.{u4, u5, u2} α γ α' f₁ s u) (Set.image2.{u3, u5, u1} β γ β' f₂ t u)))
Case conversion may be inaccurate. Consider using '#align set.image2_distrib_subset_right Set.image2_distrib_subset_rightₓ'. -/
/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
theorem image2_distrib_subset_right {f : δ → γ → ε} {g : α → β → δ} {f₁ : α → γ → α'}
    {f₂ : β → γ → β'} {g' : α' → β' → ε} (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image2 f (image2 g s t) u ⊆ image2 g' (image2 f₁ s u) (image2 f₂ t u) :=
  by
  rintro _ ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
  rw [h_distrib]
  exact mem_image2_of_mem (mem_image2_of_mem ha hc) (mem_image2_of_mem hb hc)
#align set.image2_distrib_subset_right Set.image2_distrib_subset_right

/- warning: set.image_image2_antidistrib -> Set.image_image2_antidistrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u3} β} {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ b) (g₂ a))) -> (Eq.{succ u6} (Set.{u6} δ) (Set.image.{u5, u6} γ δ g (Set.image2.{u1, u3, u5} α β γ f s t)) (Set.image2.{u4, u2, u6} β' α' δ f' (Set.image.{u3, u4} β β' g₁ t) (Set.image.{u1, u2} α α' g₂ s)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u1}} {β : Type.{u3}} {β' : Type.{u2}} {γ : Type.{u5}} {δ : Type.{u6}} {f : α -> β -> γ} {s : Set.{u4} α} {t : Set.{u3} β} {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ b) (g₂ a))) -> (Eq.{succ u6} (Set.{u6} δ) (Set.image.{u5, u6} γ δ g (Set.image2.{u4, u3, u5} α β γ f s t)) (Set.image2.{u2, u1, u6} β' α' δ f' (Set.image.{u3, u2} β β' g₁ t) (Set.image.{u4, u1} α α' g₂ s)))
Case conversion may be inaccurate. Consider using '#align set.image_image2_antidistrib Set.image_image2_antidistribₓ'. -/
theorem image_image2_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image2 f s t).image g = image2 f' (t.image g₁) (s.image g₂) :=
  by
  rw [image2_swap f]
  exact image_image2_distrib fun _ _ => h_antidistrib _ _
#align set.image_image2_antidistrib Set.image_image2_antidistrib

/- warning: set.image_image2_antidistrib_left -> Set.image_image2_antidistrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u2} β} {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' b) a)) -> (Eq.{succ u5} (Set.{u5} δ) (Set.image.{u4, u5} γ δ g (Set.image2.{u1, u2, u4} α β γ f s t)) (Set.image2.{u3, u1, u5} β' α δ f' (Set.image.{u2, u3} β β' g' t) s))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {β' : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β} {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' b) a)) -> (Eq.{succ u5} (Set.{u5} δ) (Set.image.{u4, u5} γ δ g (Set.image2.{u3, u2, u4} α β γ f s t)) (Set.image2.{u1, u3, u5} β' α δ f' (Set.image.{u2, u1} β β' g' t) s))
Case conversion may be inaccurate. Consider using '#align set.image_image2_antidistrib_left Set.image_image2_antidistrib_leftₓ'. -/
/-- Symmetric statement to `set.image2_image_left_anticomm`. -/
theorem image_image2_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
    (image2 f s t).image g = image2 f' (t.image g') s :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']
#align set.image_image2_antidistrib_left Set.image_image2_antidistrib_left

/- warning: set.image_image2_antidistrib_right -> Set.image_image2_antidistrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {s : Set.{u1} α} {t : Set.{u3} β} {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' b (g' a))) -> (Eq.{succ u5} (Set.{u5} δ) (Set.image.{u4, u5} γ δ g (Set.image2.{u1, u3, u4} α β γ f s t)) (Set.image2.{u3, u2, u5} β α' δ f' t (Set.image.{u1, u2} α α' g' s)))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} {f : α -> β -> γ} {s : Set.{u3} α} {t : Set.{u2} β} {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' b (g' a))) -> (Eq.{succ u5} (Set.{u5} δ) (Set.image.{u4, u5} γ δ g (Set.image2.{u3, u2, u4} α β γ f s t)) (Set.image2.{u2, u1, u5} β α' δ f' t (Set.image.{u3, u1} α α' g' s)))
Case conversion may be inaccurate. Consider using '#align set.image_image2_antidistrib_right Set.image_image2_antidistrib_rightₓ'. -/
/-- Symmetric statement to `set.image_image2_right_anticomm`. -/
theorem image_image2_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
    (image2 f s t).image g = image2 f' t (s.image g') :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']
#align set.image_image2_antidistrib_right Set.image_image2_antidistrib_right

/- warning: set.image2_image_left_anticomm -> Set.image2_image_left_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {s : Set.{u1} α} {t : Set.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f (g a) b) (g' (f' b a))) -> (Eq.{succ u4} (Set.{u4} γ) (Set.image2.{u2, u3, u4} α' β γ f (Set.image.{u1, u2} α α' g s) t) (Set.image.{u5, u4} δ γ g' (Set.image2.{u3, u1, u5} β α δ f' t s)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u4}} {β : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} {s : Set.{u2} α} {t : Set.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (f (g a) b) (g' (f' b a))) -> (Eq.{succ u5} (Set.{u5} γ) (Set.image2.{u4, u3, u5} α' β γ f (Set.image.{u2, u4} α α' g s) t) (Set.image.{u1, u5} δ γ g' (Set.image2.{u3, u2, u1} β α δ f' t s)))
Case conversion may be inaccurate. Consider using '#align set.image2_image_left_anticomm Set.image2_image_left_anticommₓ'. -/
/-- Symmetric statement to `set.image_image2_antidistrib_left`. -/
theorem image2_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    image2 f (s.image g) t = (image2 f' t s).image g' :=
  (image_image2_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm
#align set.image2_image_left_anticomm Set.image2_image_left_anticomm

/- warning: set.image_image2_right_anticomm -> Set.image_image2_right_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f a (g b)) (g' (f' b a))) -> (Eq.{succ u4} (Set.{u4} γ) (Set.image2.{u1, u3, u4} α β' γ f s (Set.image.{u2, u3} β β' g t)) (Set.image.{u5, u4} δ γ g' (Set.image2.{u2, u1, u5} β α δ f' t s)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} {s : Set.{u4} α} {t : Set.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (f a (g b)) (g' (f' b a))) -> (Eq.{succ u5} (Set.{u5} γ) (Set.image2.{u4, u3, u5} α β' γ f s (Set.image.{u2, u3} β β' g t)) (Set.image.{u1, u5} δ γ g' (Set.image2.{u2, u4, u1} β α δ f' t s)))
Case conversion may be inaccurate. Consider using '#align set.image_image2_right_anticomm Set.image_image2_right_anticommₓ'. -/
/-- Symmetric statement to `set.image_image2_antidistrib_right`. -/
theorem image_image2_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    image2 f s (t.image g) = (image2 f' t s).image g' :=
  (image_image2_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm
#align set.image_image2_right_anticomm Set.image_image2_right_anticomm

end Set

