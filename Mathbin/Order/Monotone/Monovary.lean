/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.monotone.monovary
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image

/-!
# Monovariance of functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Two functions *vary together* if a strict change in the first implies a change in the second.

This is in some sense a way to say that two functions `f : ι → α`, `g : ι → β` are "monotone
together", without actually having an order on `ι`.

This condition comes up in the rearrangement inequality. See `algebra.order.rearrangement`.

## Main declarations

* `monovary f g`: `f` monovaries with `g`. If `g i < g j`, then `f i ≤ f j`.
* `antivary f g`: `f` antivaries with `g`. If `g i < g j`, then `f j ≤ f i`.
* `monovary_on f g s`: `f` monovaries with `g` on `s`.
* `monovary_on f g s`: `f` antivaries with `g` on `s`.
-/


open Function Set

variable {ι ι' α β γ : Type _}

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β} {g' : β → γ}
  {s t : Set ι}

#print Monovary /-
/-- `f` monovaries with `g` if `g i < g j` implies `f i ≤ f j`. -/
def Monovary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f i ≤ f j
#align monovary Monovary
-/

#print Antivary /-
/-- `f` antivaries with `g` if `g i < g j` implies `f j ≤ f i`. -/
def Antivary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f j ≤ f i
#align antivary Antivary
-/

#print MonovaryOn /-
/-- `f` monovaries with `g` on `s` if `g i < g j` implies `f i ≤ f j` for all `i, j ∈ s`. -/
def MonovaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (hi : i ∈ s) ⦃j⦄ (hj : j ∈ s), g i < g j → f i ≤ f j
#align monovary_on MonovaryOn
-/

#print AntivaryOn /-
/-- `f` antivaries with `g` on `s` if `g i < g j` implies `f j ≤ f i` for all `i, j ∈ s`. -/
def AntivaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (hi : i ∈ s) ⦃j⦄ (hj : j ∈ s), g i < g j → f j ≤ f i
#align antivary_on AntivaryOn
-/

/- warning: monovary.monovary_on -> Monovary.monovaryOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (forall (s : Set.{u1} ι), MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g) -> (forall (s : Set.{u3} ι), MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align monovary.monovary_on Monovary.monovaryOnₓ'. -/
protected theorem Monovary.monovaryOn (h : Monovary f g) (s : Set ι) : MonovaryOn f g s :=
  fun i _ j _ hij => h hij
#align monovary.monovary_on Monovary.monovaryOn

/- warning: antivary.antivary_on -> Antivary.antivaryOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (forall (s : Set.{u1} ι), AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g) -> (forall (s : Set.{u3} ι), AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align antivary.antivary_on Antivary.antivaryOnₓ'. -/
protected theorem Antivary.antivaryOn (h : Antivary f g) (s : Set ι) : AntivaryOn f g s :=
  fun i _ j _ hij => h hij
#align antivary.antivary_on Antivary.antivaryOn

/- warning: monovary_on.empty -> MonovaryOn.empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g (EmptyCollection.emptyCollection.{u1} (Set.{u1} ι) (Set.hasEmptyc.{u1} ι))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g (EmptyCollection.emptyCollection.{u3} (Set.{u3} ι) (Set.instEmptyCollectionSet.{u3} ι))
Case conversion may be inaccurate. Consider using '#align monovary_on.empty MonovaryOn.emptyₓ'. -/
@[simp]
theorem MonovaryOn.empty : MonovaryOn f g ∅ := fun i => False.elim
#align monovary_on.empty MonovaryOn.empty

/- warning: antivary_on.empty -> AntivaryOn.empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g (EmptyCollection.emptyCollection.{u1} (Set.{u1} ι) (Set.hasEmptyc.{u1} ι))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g (EmptyCollection.emptyCollection.{u3} (Set.{u3} ι) (Set.instEmptyCollectionSet.{u3} ι))
Case conversion may be inaccurate. Consider using '#align antivary_on.empty AntivaryOn.emptyₓ'. -/
@[simp]
theorem AntivaryOn.empty : AntivaryOn f g ∅ := fun i => False.elim
#align antivary_on.empty AntivaryOn.empty

/- warning: monovary_on_univ -> monovaryOn_univ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, Iff (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g (Set.univ.{u1} ι)) (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, Iff (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g (Set.univ.{u3} ι)) (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align monovary_on_univ monovaryOn_univₓ'. -/
@[simp]
theorem monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g :=
  ⟨fun h i j => h trivial trivial, fun h i _ j _ hij => h hij⟩
#align monovary_on_univ monovaryOn_univ

/- warning: antivary_on_univ -> antivaryOn_univ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, Iff (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g (Set.univ.{u1} ι)) (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, Iff (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g (Set.univ.{u3} ι)) (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align antivary_on_univ antivaryOn_univₓ'. -/
@[simp]
theorem antivaryOn_univ : AntivaryOn f g univ ↔ Antivary f g :=
  ⟨fun h i j => h trivial trivial, fun h i _ j _ hij => h hij⟩
#align antivary_on_univ antivaryOn_univ

/- warning: monovary_on.subset -> MonovaryOn.subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι} {t : Set.{u1} ι}, (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.hasSubset.{u1} ι) s t) -> (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g t) -> (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι} {t : Set.{u3} ι}, (HasSubset.Subset.{u3} (Set.{u3} ι) (Set.instHasSubsetSet.{u3} ι) s t) -> (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g t) -> (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align monovary_on.subset MonovaryOn.subsetₓ'. -/
protected theorem MonovaryOn.subset (hst : s ⊆ t) (h : MonovaryOn f g t) : MonovaryOn f g s :=
  fun i hi j hj => h (hst hi) (hst hj)
#align monovary_on.subset MonovaryOn.subset

/- warning: antivary_on.subset -> AntivaryOn.subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι} {t : Set.{u1} ι}, (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.hasSubset.{u1} ι) s t) -> (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g t) -> (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι} {t : Set.{u3} ι}, (HasSubset.Subset.{u3} (Set.{u3} ι) (Set.instHasSubsetSet.{u3} ι) s t) -> (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g t) -> (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align antivary_on.subset AntivaryOn.subsetₓ'. -/
protected theorem AntivaryOn.subset (hst : s ⊆ t) (h : AntivaryOn f g t) : AntivaryOn f g s :=
  fun i hi j hj => h (hst hi) (hst hj)
#align antivary_on.subset AntivaryOn.subset

/- warning: monovary_const_left -> monovary_const_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] (g : ι -> β) (a : α), Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 (Function.const.{succ u2, succ u1} α ι a) g
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (g : ι -> β) (a : α), Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 (Function.const.{succ u2, succ u3} α ι a) g
Case conversion may be inaccurate. Consider using '#align monovary_const_left monovary_const_leftₓ'. -/
theorem monovary_const_left (g : ι → β) (a : α) : Monovary (const ι a) g := fun i j _ => le_rfl
#align monovary_const_left monovary_const_left

/- warning: antivary_const_left -> antivary_const_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] (g : ι -> β) (a : α), Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 (Function.const.{succ u2, succ u1} α ι a) g
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (g : ι -> β) (a : α), Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 (Function.const.{succ u2, succ u3} α ι a) g
Case conversion may be inaccurate. Consider using '#align antivary_const_left antivary_const_leftₓ'. -/
theorem antivary_const_left (g : ι → β) (a : α) : Antivary (const ι a) g := fun i j _ => le_rfl
#align antivary_const_left antivary_const_left

/- warning: monovary_const_right -> monovary_const_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] (f : ι -> α) (b : β), Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f (Function.const.{succ u3, succ u1} β ι b)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : ι -> α) (b : β), Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f (Function.const.{succ u1, succ u3} β ι b)
Case conversion may be inaccurate. Consider using '#align monovary_const_right monovary_const_rightₓ'. -/
theorem monovary_const_right (f : ι → α) (b : β) : Monovary f (const ι b) := fun i j h =>
  (h.Ne rfl).elim
#align monovary_const_right monovary_const_right

/- warning: antivary_const_right -> antivary_const_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] (f : ι -> α) (b : β), Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f (Function.const.{succ u3, succ u1} β ι b)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : ι -> α) (b : β), Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f (Function.const.{succ u1, succ u3} β ι b)
Case conversion may be inaccurate. Consider using '#align antivary_const_right antivary_const_rightₓ'. -/
theorem antivary_const_right (f : ι → α) (b : β) : Antivary f (const ι b) := fun i j h =>
  (h.Ne rfl).elim
#align antivary_const_right antivary_const_right

/- warning: monovary_self -> monovary_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] (f : ι -> α), Monovary.{u1, u2, u2} ι α α _inst_1 _inst_1 f f
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (f : ι -> α), Monovary.{u2, u1, u1} ι α α _inst_1 _inst_1 f f
Case conversion may be inaccurate. Consider using '#align monovary_self monovary_selfₓ'. -/
theorem monovary_self (f : ι → α) : Monovary f f := fun i j => le_of_lt
#align monovary_self monovary_self

/- warning: monovary_on_self -> monovaryOn_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] (f : ι -> α) (s : Set.{u1} ι), MonovaryOn.{u1, u2, u2} ι α α _inst_1 _inst_1 f f s
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (f : ι -> α) (s : Set.{u2} ι), MonovaryOn.{u2, u1, u1} ι α α _inst_1 _inst_1 f f s
Case conversion may be inaccurate. Consider using '#align monovary_on_self monovaryOn_selfₓ'. -/
theorem monovaryOn_self (f : ι → α) (s : Set ι) : MonovaryOn f f s := fun i _ j _ => le_of_lt
#align monovary_on_self monovaryOn_self

/- warning: subsingleton.monovary -> Subsingleton.monovary is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_4 : Subsingleton.{succ u1} ι] (f : ι -> α) (g : ι -> β), Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_4 : Subsingleton.{succ u3} ι] (f : ι -> α) (g : ι -> β), Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g
Case conversion may be inaccurate. Consider using '#align subsingleton.monovary Subsingleton.monovaryₓ'. -/
protected theorem Subsingleton.monovary [Subsingleton ι] (f : ι → α) (g : ι → β) : Monovary f g :=
  fun i j h => (ne_of_apply_ne _ h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.monovary Subsingleton.monovary

/- warning: subsingleton.antivary -> Subsingleton.antivary is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_4 : Subsingleton.{succ u1} ι] (f : ι -> α) (g : ι -> β), Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_4 : Subsingleton.{succ u3} ι] (f : ι -> α) (g : ι -> β), Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g
Case conversion may be inaccurate. Consider using '#align subsingleton.antivary Subsingleton.antivaryₓ'. -/
protected theorem Subsingleton.antivary [Subsingleton ι] (f : ι → α) (g : ι → β) : Antivary f g :=
  fun i j h => (ne_of_apply_ne _ h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.antivary Subsingleton.antivary

/- warning: subsingleton.monovary_on -> Subsingleton.monovaryOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_4 : Subsingleton.{succ u1} ι] (f : ι -> α) (g : ι -> β) (s : Set.{u1} ι), MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_4 : Subsingleton.{succ u3} ι] (f : ι -> α) (g : ι -> β) (s : Set.{u3} ι), MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s
Case conversion may be inaccurate. Consider using '#align subsingleton.monovary_on Subsingleton.monovaryOnₓ'. -/
protected theorem Subsingleton.monovaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    MonovaryOn f g s := fun i _ j _ h => (ne_of_apply_ne _ h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.monovary_on Subsingleton.monovaryOn

/- warning: subsingleton.antivary_on -> Subsingleton.antivaryOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_4 : Subsingleton.{succ u1} ι] (f : ι -> α) (g : ι -> β) (s : Set.{u1} ι), AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] [_inst_4 : Subsingleton.{succ u3} ι] (f : ι -> α) (g : ι -> β) (s : Set.{u3} ι), AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s
Case conversion may be inaccurate. Consider using '#align subsingleton.antivary_on Subsingleton.antivaryOnₓ'. -/
protected theorem Subsingleton.antivaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    AntivaryOn f g s := fun i _ j _ h => (ne_of_apply_ne _ h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.antivary_on Subsingleton.antivaryOn

/- warning: monovary_on_const_left -> monovaryOn_const_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] (g : ι -> β) (a : α) (s : Set.{u1} ι), MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 (Function.const.{succ u2, succ u1} α ι a) g s
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (g : ι -> β) (a : α) (s : Set.{u3} ι), MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 (Function.const.{succ u2, succ u3} α ι a) g s
Case conversion may be inaccurate. Consider using '#align monovary_on_const_left monovaryOn_const_leftₓ'. -/
theorem monovaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : MonovaryOn (const ι a) g s :=
  fun i _ j _ _ => le_rfl
#align monovary_on_const_left monovaryOn_const_left

/- warning: antivary_on_const_left -> antivaryOn_const_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] (g : ι -> β) (a : α) (s : Set.{u1} ι), AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 (Function.const.{succ u2, succ u1} α ι a) g s
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (g : ι -> β) (a : α) (s : Set.{u3} ι), AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 (Function.const.{succ u2, succ u3} α ι a) g s
Case conversion may be inaccurate. Consider using '#align antivary_on_const_left antivaryOn_const_leftₓ'. -/
theorem antivaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : AntivaryOn (const ι a) g s :=
  fun i _ j _ _ => le_rfl
#align antivary_on_const_left antivaryOn_const_left

/- warning: monovary_on_const_right -> monovaryOn_const_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] (f : ι -> α) (b : β) (s : Set.{u1} ι), MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f (Function.const.{succ u3, succ u1} β ι b) s
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : ι -> α) (b : β) (s : Set.{u3} ι), MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f (Function.const.{succ u1, succ u3} β ι b) s
Case conversion may be inaccurate. Consider using '#align monovary_on_const_right monovaryOn_const_rightₓ'. -/
theorem monovaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : MonovaryOn f (const ι b) s :=
  fun i _ j _ h => (h.Ne rfl).elim
#align monovary_on_const_right monovaryOn_const_right

/- warning: antivary_on_const_right -> antivaryOn_const_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] (f : ι -> α) (b : β) (s : Set.{u1} ι), AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f (Function.const.{succ u3, succ u1} β ι b) s
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : ι -> α) (b : β) (s : Set.{u3} ι), AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f (Function.const.{succ u1, succ u3} β ι b) s
Case conversion may be inaccurate. Consider using '#align antivary_on_const_right antivaryOn_const_rightₓ'. -/
theorem antivaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : AntivaryOn f (const ι b) s :=
  fun i _ j _ h => (h.Ne rfl).elim
#align antivary_on_const_right antivaryOn_const_right

/- warning: monovary.comp_right -> Monovary.comp_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u4} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u1, u3, u4} ι α β _inst_1 _inst_2 f g) -> (forall (k : ι' -> ι), Monovary.{u2, u3, u4} ι' α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u1, succ u3} ι' ι α f k) (Function.comp.{succ u2, succ u1, succ u4} ι' ι β g k))
but is expected to have type
  forall {ι : Type.{u4}} {ι' : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u4, u3, u2} ι α β _inst_1 _inst_2 f g) -> (forall (k : ι' -> ι), Monovary.{u1, u3, u2} ι' α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u4, succ u3} ι' ι α f k) (Function.comp.{succ u1, succ u4, succ u2} ι' ι β g k))
Case conversion may be inaccurate. Consider using '#align monovary.comp_right Monovary.comp_rightₓ'. -/
theorem Monovary.comp_right (h : Monovary f g) (k : ι' → ι) : Monovary (f ∘ k) (g ∘ k) :=
  fun i j hij => h hij
#align monovary.comp_right Monovary.comp_right

/- warning: antivary.comp_right -> Antivary.comp_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u4} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u1, u3, u4} ι α β _inst_1 _inst_2 f g) -> (forall (k : ι' -> ι), Antivary.{u2, u3, u4} ι' α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u1, succ u3} ι' ι α f k) (Function.comp.{succ u2, succ u1, succ u4} ι' ι β g k))
but is expected to have type
  forall {ι : Type.{u4}} {ι' : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u4, u3, u2} ι α β _inst_1 _inst_2 f g) -> (forall (k : ι' -> ι), Antivary.{u1, u3, u2} ι' α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u4, succ u3} ι' ι α f k) (Function.comp.{succ u1, succ u4, succ u2} ι' ι β g k))
Case conversion may be inaccurate. Consider using '#align antivary.comp_right Antivary.comp_rightₓ'. -/
theorem Antivary.comp_right (h : Antivary f g) (k : ι' → ι) : Antivary (f ∘ k) (g ∘ k) :=
  fun i j hij => h hij
#align antivary.comp_right Antivary.comp_right

/- warning: monovary_on.comp_right -> MonovaryOn.comp_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u4} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (MonovaryOn.{u1, u3, u4} ι α β _inst_1 _inst_2 f g s) -> (forall (k : ι' -> ι), MonovaryOn.{u2, u3, u4} ι' α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u1, succ u3} ι' ι α f k) (Function.comp.{succ u2, succ u1, succ u4} ι' ι β g k) (Set.preimage.{u2, u1} ι' ι k s))
but is expected to have type
  forall {ι : Type.{u4}} {ι' : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] {f : ι -> α} {g : ι -> β} {s : Set.{u4} ι}, (MonovaryOn.{u4, u3, u2} ι α β _inst_1 _inst_2 f g s) -> (forall (k : ι' -> ι), MonovaryOn.{u1, u3, u2} ι' α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u4, succ u3} ι' ι α f k) (Function.comp.{succ u1, succ u4, succ u2} ι' ι β g k) (Set.preimage.{u1, u4} ι' ι k s))
Case conversion may be inaccurate. Consider using '#align monovary_on.comp_right MonovaryOn.comp_rightₓ'. -/
theorem MonovaryOn.comp_right (h : MonovaryOn f g s) (k : ι' → ι) :
    MonovaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun i hi j hj => h hi hj
#align monovary_on.comp_right MonovaryOn.comp_right

/- warning: antivary_on.comp_right -> AntivaryOn.comp_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u4} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (AntivaryOn.{u1, u3, u4} ι α β _inst_1 _inst_2 f g s) -> (forall (k : ι' -> ι), AntivaryOn.{u2, u3, u4} ι' α β _inst_1 _inst_2 (Function.comp.{succ u2, succ u1, succ u3} ι' ι α f k) (Function.comp.{succ u2, succ u1, succ u4} ι' ι β g k) (Set.preimage.{u2, u1} ι' ι k s))
but is expected to have type
  forall {ι : Type.{u4}} {ι' : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] {f : ι -> α} {g : ι -> β} {s : Set.{u4} ι}, (AntivaryOn.{u4, u3, u2} ι α β _inst_1 _inst_2 f g s) -> (forall (k : ι' -> ι), AntivaryOn.{u1, u3, u2} ι' α β _inst_1 _inst_2 (Function.comp.{succ u1, succ u4, succ u3} ι' ι α f k) (Function.comp.{succ u1, succ u4, succ u2} ι' ι β g k) (Set.preimage.{u1, u4} ι' ι k s))
Case conversion may be inaccurate. Consider using '#align antivary_on.comp_right AntivaryOn.comp_rightₓ'. -/
theorem AntivaryOn.comp_right (h : AntivaryOn f g s) (k : ι' → ι) :
    AntivaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun i hi j hj => h hi hj
#align antivary_on.comp_right AntivaryOn.comp_right

/- warning: monovary.comp_monotone_left -> Monovary.comp_monotone_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}, (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Monotone.{u2, u4} α γ _inst_1 _inst_3 f') -> (Monovary.{u1, u4, u3} ι γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u2, succ u4} ι α γ f' f) g)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}, (Monovary.{u4, u3, u2} ι α β _inst_1 _inst_2 f g) -> (Monotone.{u3, u1} α γ _inst_1 _inst_3 f') -> (Monovary.{u4, u1, u2} ι γ β _inst_3 _inst_2 (Function.comp.{succ u4, succ u3, succ u1} ι α γ f' f) g)
Case conversion may be inaccurate. Consider using '#align monovary.comp_monotone_left Monovary.comp_monotone_leftₓ'. -/
theorem Monovary.comp_monotone_left (h : Monovary f g) (hf : Monotone f') : Monovary (f' ∘ f) g :=
  fun i j hij => hf <| h hij
#align monovary.comp_monotone_left Monovary.comp_monotone_left

/- warning: monovary.comp_antitone_left -> Monovary.comp_antitone_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}, (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Antitone.{u2, u4} α γ _inst_1 _inst_3 f') -> (Antivary.{u1, u4, u3} ι γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u2, succ u4} ι α γ f' f) g)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}, (Monovary.{u4, u3, u2} ι α β _inst_1 _inst_2 f g) -> (Antitone.{u3, u1} α γ _inst_1 _inst_3 f') -> (Antivary.{u4, u1, u2} ι γ β _inst_3 _inst_2 (Function.comp.{succ u4, succ u3, succ u1} ι α γ f' f) g)
Case conversion may be inaccurate. Consider using '#align monovary.comp_antitone_left Monovary.comp_antitone_leftₓ'. -/
theorem Monovary.comp_antitone_left (h : Monovary f g) (hf : Antitone f') : Antivary (f' ∘ f) g :=
  fun i j hij => hf <| h hij
#align monovary.comp_antitone_left Monovary.comp_antitone_left

/- warning: antivary.comp_monotone_left -> Antivary.comp_monotone_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}, (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Monotone.{u2, u4} α γ _inst_1 _inst_3 f') -> (Antivary.{u1, u4, u3} ι γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u2, succ u4} ι α γ f' f) g)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}, (Antivary.{u4, u3, u2} ι α β _inst_1 _inst_2 f g) -> (Monotone.{u3, u1} α γ _inst_1 _inst_3 f') -> (Antivary.{u4, u1, u2} ι γ β _inst_3 _inst_2 (Function.comp.{succ u4, succ u3, succ u1} ι α γ f' f) g)
Case conversion may be inaccurate. Consider using '#align antivary.comp_monotone_left Antivary.comp_monotone_leftₓ'. -/
theorem Antivary.comp_monotone_left (h : Antivary f g) (hf : Monotone f') : Antivary (f' ∘ f) g :=
  fun i j hij => hf <| h hij
#align antivary.comp_monotone_left Antivary.comp_monotone_left

/- warning: antivary.comp_antitone_left -> Antivary.comp_antitone_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}, (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Antitone.{u2, u4} α γ _inst_1 _inst_3 f') -> (Monovary.{u1, u4, u3} ι γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u2, succ u4} ι α γ f' f) g)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β}, (Antivary.{u4, u3, u2} ι α β _inst_1 _inst_2 f g) -> (Antitone.{u3, u1} α γ _inst_1 _inst_3 f') -> (Monovary.{u4, u1, u2} ι γ β _inst_3 _inst_2 (Function.comp.{succ u4, succ u3, succ u1} ι α γ f' f) g)
Case conversion may be inaccurate. Consider using '#align antivary.comp_antitone_left Antivary.comp_antitone_leftₓ'. -/
theorem Antivary.comp_antitone_left (h : Antivary f g) (hf : Antitone f') : Monovary (f' ∘ f) g :=
  fun i j hij => hf <| h hij
#align antivary.comp_antitone_left Antivary.comp_antitone_left

/- warning: monovary_on.comp_monotone_on_left -> MonovaryOn.comp_monotone_on_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β} {s : Set.{u1} ι}, (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (Monotone.{u2, u4} α γ _inst_1 _inst_3 f') -> (MonovaryOn.{u1, u4, u3} ι γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u2, succ u4} ι α γ f' f) g s)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β} {s : Set.{u4} ι}, (MonovaryOn.{u4, u3, u2} ι α β _inst_1 _inst_2 f g s) -> (Monotone.{u3, u1} α γ _inst_1 _inst_3 f') -> (MonovaryOn.{u4, u1, u2} ι γ β _inst_3 _inst_2 (Function.comp.{succ u4, succ u3, succ u1} ι α γ f' f) g s)
Case conversion may be inaccurate. Consider using '#align monovary_on.comp_monotone_on_left MonovaryOn.comp_monotone_on_leftₓ'. -/
theorem MonovaryOn.comp_monotone_on_left (h : MonovaryOn f g s) (hf : Monotone f') :
    MonovaryOn (f' ∘ f) g s := fun i hi j hj hij => hf <| h hi hj hij
#align monovary_on.comp_monotone_on_left MonovaryOn.comp_monotone_on_left

/- warning: monovary_on.comp_antitone_on_left -> MonovaryOn.comp_antitone_on_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β} {s : Set.{u1} ι}, (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (Antitone.{u2, u4} α γ _inst_1 _inst_3 f') -> (AntivaryOn.{u1, u4, u3} ι γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u2, succ u4} ι α γ f' f) g s)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β} {s : Set.{u4} ι}, (MonovaryOn.{u4, u3, u2} ι α β _inst_1 _inst_2 f g s) -> (Antitone.{u3, u1} α γ _inst_1 _inst_3 f') -> (AntivaryOn.{u4, u1, u2} ι γ β _inst_3 _inst_2 (Function.comp.{succ u4, succ u3, succ u1} ι α γ f' f) g s)
Case conversion may be inaccurate. Consider using '#align monovary_on.comp_antitone_on_left MonovaryOn.comp_antitone_on_leftₓ'. -/
theorem MonovaryOn.comp_antitone_on_left (h : MonovaryOn f g s) (hf : Antitone f') :
    AntivaryOn (f' ∘ f) g s := fun i hi j hj hij => hf <| h hi hj hij
#align monovary_on.comp_antitone_on_left MonovaryOn.comp_antitone_on_left

/- warning: antivary_on.comp_monotone_on_left -> AntivaryOn.comp_monotone_on_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β} {s : Set.{u1} ι}, (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (Monotone.{u2, u4} α γ _inst_1 _inst_3 f') -> (AntivaryOn.{u1, u4, u3} ι γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u2, succ u4} ι α γ f' f) g s)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β} {s : Set.{u4} ι}, (AntivaryOn.{u4, u3, u2} ι α β _inst_1 _inst_2 f g s) -> (Monotone.{u3, u1} α γ _inst_1 _inst_3 f') -> (AntivaryOn.{u4, u1, u2} ι γ β _inst_3 _inst_2 (Function.comp.{succ u4, succ u3, succ u1} ι α γ f' f) g s)
Case conversion may be inaccurate. Consider using '#align antivary_on.comp_monotone_on_left AntivaryOn.comp_monotone_on_leftₓ'. -/
theorem AntivaryOn.comp_monotone_on_left (h : AntivaryOn f g s) (hf : Monotone f') :
    AntivaryOn (f' ∘ f) g s := fun i hi j hj hij => hf <| h hi hj hij
#align antivary_on.comp_monotone_on_left AntivaryOn.comp_monotone_on_left

/- warning: antivary_on.comp_antitone_on_left -> AntivaryOn.comp_antitone_on_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β} {s : Set.{u1} ι}, (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (Antitone.{u2, u4} α γ _inst_1 _inst_3 f') -> (MonovaryOn.{u1, u4, u3} ι γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u2, succ u4} ι α γ f' f) g s)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {f' : α -> γ} {g : ι -> β} {s : Set.{u4} ι}, (AntivaryOn.{u4, u3, u2} ι α β _inst_1 _inst_2 f g s) -> (Antitone.{u3, u1} α γ _inst_1 _inst_3 f') -> (MonovaryOn.{u4, u1, u2} ι γ β _inst_3 _inst_2 (Function.comp.{succ u4, succ u3, succ u1} ι α γ f' f) g s)
Case conversion may be inaccurate. Consider using '#align antivary_on.comp_antitone_on_left AntivaryOn.comp_antitone_on_leftₓ'. -/
theorem AntivaryOn.comp_antitone_on_left (h : AntivaryOn f g s) (hf : Antitone f') :
    MonovaryOn (f' ∘ f) g s := fun i hi j hj hij => hf <| h hi hj hij
#align antivary_on.comp_antitone_on_left AntivaryOn.comp_antitone_on_left

section OrderDual

open OrderDual

/- warning: monovary.dual -> Monovary.dual is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Monovary.{u1, u2, u3} ι (OrderDual.{u2} α) (OrderDual.{u3} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u3} β _inst_2) (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g) -> (Monovary.{u3, u2, u1} ι (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2) (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g))
Case conversion may be inaccurate. Consider using '#align monovary.dual Monovary.dualₓ'. -/
theorem Monovary.dual : Monovary f g → Monovary (toDual ∘ f) (toDual ∘ g) :=
  swap
#align monovary.dual Monovary.dual

/- warning: antivary.dual -> Antivary.dual is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Antivary.{u1, u2, u3} ι (OrderDual.{u2} α) (OrderDual.{u3} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u3} β _inst_2) (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g) -> (Antivary.{u3, u2, u1} ι (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2) (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g))
Case conversion may be inaccurate. Consider using '#align antivary.dual Antivary.dualₓ'. -/
theorem Antivary.dual : Antivary f g → Antivary (toDual ∘ f) (toDual ∘ g) :=
  swap
#align antivary.dual Antivary.dual

/- warning: monovary.dual_left -> Monovary.dual_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Antivary.{u1, u2, u3} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g) -> (Antivary.{u3, u2, u1} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g)
Case conversion may be inaccurate. Consider using '#align monovary.dual_left Monovary.dual_leftₓ'. -/
theorem Monovary.dual_left : Monovary f g → Antivary (toDual ∘ f) g :=
  id
#align monovary.dual_left Monovary.dual_left

/- warning: antivary.dual_left -> Antivary.dual_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Monovary.{u1, u2, u3} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g) -> (Monovary.{u3, u2, u1} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g)
Case conversion may be inaccurate. Consider using '#align antivary.dual_left Antivary.dual_leftₓ'. -/
theorem Antivary.dual_left : Antivary f g → Monovary (toDual ∘ f) g :=
  id
#align antivary.dual_left Antivary.dual_left

/- warning: monovary.dual_right -> Monovary.dual_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Antivary.{u1, u2, u3} ι α (OrderDual.{u3} β) _inst_1 (OrderDual.preorder.{u3} β _inst_2) f (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g) -> (Antivary.{u3, u2, u1} ι α (OrderDual.{u1} β) _inst_1 (OrderDual.preorder.{u1} β _inst_2) f (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g))
Case conversion may be inaccurate. Consider using '#align monovary.dual_right Monovary.dual_rightₓ'. -/
theorem Monovary.dual_right : Monovary f g → Antivary f (toDual ∘ g) :=
  swap
#align monovary.dual_right Monovary.dual_right

/- warning: antivary.dual_right -> Antivary.dual_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g) -> (Monovary.{u1, u2, u3} ι α (OrderDual.{u3} β) _inst_1 (OrderDual.preorder.{u3} β _inst_2) f (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g) -> (Monovary.{u3, u2, u1} ι α (OrderDual.{u1} β) _inst_1 (OrderDual.preorder.{u1} β _inst_2) f (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g))
Case conversion may be inaccurate. Consider using '#align antivary.dual_right Antivary.dual_rightₓ'. -/
theorem Antivary.dual_right : Antivary f g → Monovary f (toDual ∘ g) :=
  swap
#align antivary.dual_right Antivary.dual_right

/- warning: monovary_on.dual -> MonovaryOn.dual is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (MonovaryOn.{u1, u2, u3} ι (OrderDual.{u2} α) (OrderDual.{u3} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u3} β _inst_2) (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g) s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s) -> (MonovaryOn.{u3, u2, u1} ι (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2) (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g) s)
Case conversion may be inaccurate. Consider using '#align monovary_on.dual MonovaryOn.dualₓ'. -/
theorem MonovaryOn.dual : MonovaryOn f g s → MonovaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂
#align monovary_on.dual MonovaryOn.dual

/- warning: antivary_on.dual -> AntivaryOn.dual is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (AntivaryOn.{u1, u2, u3} ι (OrderDual.{u2} α) (OrderDual.{u3} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u3} β _inst_2) (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g) s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s) -> (AntivaryOn.{u3, u2, u1} ι (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2) (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g) s)
Case conversion may be inaccurate. Consider using '#align antivary_on.dual AntivaryOn.dualₓ'. -/
theorem AntivaryOn.dual : AntivaryOn f g s → AntivaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂
#align antivary_on.dual AntivaryOn.dual

/- warning: monovary_on.dual_left -> MonovaryOn.dual_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (AntivaryOn.{u1, u2, u3} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s) -> (AntivaryOn.{u3, u2, u1} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g s)
Case conversion may be inaccurate. Consider using '#align monovary_on.dual_left MonovaryOn.dual_leftₓ'. -/
theorem MonovaryOn.dual_left : MonovaryOn f g s → AntivaryOn (toDual ∘ f) g s :=
  id
#align monovary_on.dual_left MonovaryOn.dual_left

/- warning: antivary_on.dual_left -> AntivaryOn.dual_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (MonovaryOn.{u1, u2, u3} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s) -> (MonovaryOn.{u3, u2, u1} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g s)
Case conversion may be inaccurate. Consider using '#align antivary_on.dual_left AntivaryOn.dual_leftₓ'. -/
theorem AntivaryOn.dual_left : AntivaryOn f g s → MonovaryOn (toDual ∘ f) g s :=
  id
#align antivary_on.dual_left AntivaryOn.dual_left

/- warning: monovary_on.dual_right -> MonovaryOn.dual_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (AntivaryOn.{u1, u2, u3} ι α (OrderDual.{u3} β) _inst_1 (OrderDual.preorder.{u3} β _inst_2) f (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g) s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s) -> (AntivaryOn.{u3, u2, u1} ι α (OrderDual.{u1} β) _inst_1 (OrderDual.preorder.{u1} β _inst_2) f (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g) s)
Case conversion may be inaccurate. Consider using '#align monovary_on.dual_right MonovaryOn.dual_rightₓ'. -/
theorem MonovaryOn.dual_right : MonovaryOn f g s → AntivaryOn f (toDual ∘ g) s :=
  swap₂
#align monovary_on.dual_right MonovaryOn.dual_right

/- warning: antivary_on.dual_right -> AntivaryOn.dual_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s) -> (MonovaryOn.{u1, u2, u3} ι α (OrderDual.{u3} β) _inst_1 (OrderDual.preorder.{u3} β _inst_2) f (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g) s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s) -> (MonovaryOn.{u3, u2, u1} ι α (OrderDual.{u1} β) _inst_1 (OrderDual.preorder.{u1} β _inst_2) f (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g) s)
Case conversion may be inaccurate. Consider using '#align antivary_on.dual_right AntivaryOn.dual_rightₓ'. -/
theorem AntivaryOn.dual_right : AntivaryOn f g s → MonovaryOn f (toDual ∘ g) s :=
  swap₂
#align antivary_on.dual_right AntivaryOn.dual_right

/- warning: monovary_to_dual_left -> monovary_toDual_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, Iff (Monovary.{u1, u2, u3} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g) (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, Iff (Monovary.{u3, u2, u1} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g) (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align monovary_to_dual_left monovary_toDual_leftₓ'. -/
@[simp]
theorem monovary_toDual_left : Monovary (toDual ∘ f) g ↔ Antivary f g :=
  Iff.rfl
#align monovary_to_dual_left monovary_toDual_left

/- warning: monovary_to_dual_right -> monovary_toDual_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, Iff (Monovary.{u1, u2, u3} ι α (OrderDual.{u3} β) _inst_1 (OrderDual.preorder.{u3} β _inst_2) f (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g)) (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, Iff (Monovary.{u3, u2, u1} ι α (OrderDual.{u1} β) _inst_1 (OrderDual.preorder.{u1} β _inst_2) f (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g)) (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align monovary_to_dual_right monovary_toDual_rightₓ'. -/
@[simp]
theorem monovary_toDual_right : Monovary f (toDual ∘ g) ↔ Antivary f g :=
  forall_swap
#align monovary_to_dual_right monovary_toDual_right

/- warning: antivary_to_dual_left -> antivary_toDual_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, Iff (Antivary.{u1, u2, u3} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g) (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, Iff (Antivary.{u3, u2, u1} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g) (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align antivary_to_dual_left antivary_toDual_leftₓ'. -/
@[simp]
theorem antivary_toDual_left : Antivary (toDual ∘ f) g ↔ Monovary f g :=
  Iff.rfl
#align antivary_to_dual_left antivary_toDual_left

/- warning: antivary_to_dual_right -> antivary_toDual_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β}, Iff (Antivary.{u1, u2, u3} ι α (OrderDual.{u3} β) _inst_1 (OrderDual.preorder.{u3} β _inst_2) f (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g)) (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β}, Iff (Antivary.{u3, u2, u1} ι α (OrderDual.{u1} β) _inst_1 (OrderDual.preorder.{u1} β _inst_2) f (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g)) (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align antivary_to_dual_right antivary_toDual_rightₓ'. -/
@[simp]
theorem antivary_toDual_right : Antivary f (toDual ∘ g) ↔ Monovary f g :=
  forall_swap
#align antivary_to_dual_right antivary_toDual_right

/- warning: monovary_on_to_dual_left -> monovaryOn_toDual_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, Iff (MonovaryOn.{u1, u2, u3} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g s) (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, Iff (MonovaryOn.{u3, u2, u1} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g s) (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align monovary_on_to_dual_left monovaryOn_toDual_leftₓ'. -/
@[simp]
theorem monovaryOn_toDual_left : MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s :=
  Iff.rfl
#align monovary_on_to_dual_left monovaryOn_toDual_left

/- warning: monovary_on_to_dual_right -> monovaryOn_toDual_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, Iff (MonovaryOn.{u1, u2, u3} ι α (OrderDual.{u3} β) _inst_1 (OrderDual.preorder.{u3} β _inst_2) f (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g) s) (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, Iff (MonovaryOn.{u3, u2, u1} ι α (OrderDual.{u1} β) _inst_1 (OrderDual.preorder.{u1} β _inst_2) f (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g) s) (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align monovary_on_to_dual_right monovaryOn_toDual_rightₓ'. -/
@[simp]
theorem monovaryOn_toDual_right : MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s :=
  forall₂_swap
#align monovary_on_to_dual_right monovaryOn_toDual_right

/- warning: antivary_on_to_dual_left -> antivaryOn_toDual_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, Iff (AntivaryOn.{u1, u2, u3} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (fun (_x : Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) => α -> (OrderDual.{u2} α)) (Equiv.hasCoeToFun.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g s) (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, Iff (AntivaryOn.{u3, u2, u1} ι (OrderDual.{u2} α) β (OrderDual.preorder.{u2} α _inst_1) _inst_2 (Function.comp.{succ u3, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f) g s) (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align antivary_on_to_dual_left antivaryOn_toDual_leftₓ'. -/
@[simp]
theorem antivaryOn_toDual_left : AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s :=
  Iff.rfl
#align antivary_on_to_dual_left antivaryOn_toDual_left

/- warning: antivary_on_to_dual_right -> antivaryOn_toDual_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, Iff (AntivaryOn.{u1, u2, u3} ι α (OrderDual.{u3} β) _inst_1 (OrderDual.preorder.{u3} β _inst_2) f (Function.comp.{succ u1, succ u3, succ u3} ι β (OrderDual.{u3} β) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) (fun (_x : Equiv.{succ u3, succ u3} β (OrderDual.{u3} β)) => β -> (OrderDual.{u3} β)) (Equiv.hasCoeToFun.{succ u3, succ u3} β (OrderDual.{u3} β)) (OrderDual.toDual.{u3} β)) g) s) (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, Iff (AntivaryOn.{u3, u2, u1} ι α (OrderDual.{u1} β) _inst_1 (OrderDual.preorder.{u1} β _inst_2) f (Function.comp.{succ u3, succ u1, succ u1} ι β (OrderDual.{u1} β) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => OrderDual.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)) (OrderDual.toDual.{u1} β)) g) s) (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align antivary_on_to_dual_right antivaryOn_toDual_rightₓ'. -/
@[simp]
theorem antivaryOn_toDual_right : AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s :=
  forall₂_swap
#align antivary_on_to_dual_right antivaryOn_toDual_right

end OrderDual

section PartialOrder

variable [PartialOrder ι]

/- warning: monovary_id_iff -> monovary_id_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] {f : ι -> α} [_inst_4 : PartialOrder.{u1} ι], Iff (Monovary.{u1, u2, u1} ι α ι _inst_1 (PartialOrder.toPreorder.{u1} ι _inst_4) f (id.{succ u1} ι)) (Monotone.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι _inst_4) _inst_1 f)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {f : ι -> α} [_inst_4 : PartialOrder.{u2} ι], Iff (Monovary.{u2, u1, u2} ι α ι _inst_1 (PartialOrder.toPreorder.{u2} ι _inst_4) f (id.{succ u2} ι)) (Monotone.{u2, u1} ι α (PartialOrder.toPreorder.{u2} ι _inst_4) _inst_1 f)
Case conversion may be inaccurate. Consider using '#align monovary_id_iff monovary_id_iffₓ'. -/
@[simp]
theorem monovary_id_iff : Monovary f id ↔ Monotone f :=
  monotone_iff_forall_lt.symm
#align monovary_id_iff monovary_id_iff

/- warning: antivary_id_iff -> antivary_id_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] {f : ι -> α} [_inst_4 : PartialOrder.{u1} ι], Iff (Antivary.{u1, u2, u1} ι α ι _inst_1 (PartialOrder.toPreorder.{u1} ι _inst_4) f (id.{succ u1} ι)) (Antitone.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι _inst_4) _inst_1 f)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {f : ι -> α} [_inst_4 : PartialOrder.{u2} ι], Iff (Antivary.{u2, u1, u2} ι α ι _inst_1 (PartialOrder.toPreorder.{u2} ι _inst_4) f (id.{succ u2} ι)) (Antitone.{u2, u1} ι α (PartialOrder.toPreorder.{u2} ι _inst_4) _inst_1 f)
Case conversion may be inaccurate. Consider using '#align antivary_id_iff antivary_id_iffₓ'. -/
@[simp]
theorem antivary_id_iff : Antivary f id ↔ Antitone f :=
  antitone_iff_forall_lt.symm
#align antivary_id_iff antivary_id_iff

/- warning: monovary_on_id_iff -> monovaryOn_id_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] {f : ι -> α} {s : Set.{u1} ι} [_inst_4 : PartialOrder.{u1} ι], Iff (MonovaryOn.{u1, u2, u1} ι α ι _inst_1 (PartialOrder.toPreorder.{u1} ι _inst_4) f (id.{succ u1} ι) s) (MonotoneOn.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι _inst_4) _inst_1 f s)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {f : ι -> α} {s : Set.{u2} ι} [_inst_4 : PartialOrder.{u2} ι], Iff (MonovaryOn.{u2, u1, u2} ι α ι _inst_1 (PartialOrder.toPreorder.{u2} ι _inst_4) f (id.{succ u2} ι) s) (MonotoneOn.{u2, u1} ι α (PartialOrder.toPreorder.{u2} ι _inst_4) _inst_1 f s)
Case conversion may be inaccurate. Consider using '#align monovary_on_id_iff monovaryOn_id_iffₓ'. -/
@[simp]
theorem monovaryOn_id_iff : MonovaryOn f id s ↔ MonotoneOn f s :=
  monotoneOn_iff_forall_lt.symm
#align monovary_on_id_iff monovaryOn_id_iff

/- warning: antivary_on_id_iff -> antivaryOn_id_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] {f : ι -> α} {s : Set.{u1} ι} [_inst_4 : PartialOrder.{u1} ι], Iff (AntivaryOn.{u1, u2, u1} ι α ι _inst_1 (PartialOrder.toPreorder.{u1} ι _inst_4) f (id.{succ u1} ι) s) (AntitoneOn.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι _inst_4) _inst_1 f s)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {f : ι -> α} {s : Set.{u2} ι} [_inst_4 : PartialOrder.{u2} ι], Iff (AntivaryOn.{u2, u1, u2} ι α ι _inst_1 (PartialOrder.toPreorder.{u2} ι _inst_4) f (id.{succ u2} ι) s) (AntitoneOn.{u2, u1} ι α (PartialOrder.toPreorder.{u2} ι _inst_4) _inst_1 f s)
Case conversion may be inaccurate. Consider using '#align antivary_on_id_iff antivaryOn_id_iffₓ'. -/
@[simp]
theorem antivaryOn_id_iff : AntivaryOn f id s ↔ AntitoneOn f s :=
  antitoneOn_iff_forall_lt.symm
#align antivary_on_id_iff antivaryOn_id_iff

end PartialOrder

variable [LinearOrder ι]

/- warning: monotone.monovary -> Monotone.monovary is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} [_inst_4 : LinearOrder.{u1} ι], (Monotone.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_1 f) -> (Monotone.{u1, u3} ι β (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_2 g) -> (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} [_inst_4 : LinearOrder.{u3} ι], (Monotone.{u3, u2} ι α (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_1 f) -> (Monotone.{u3, u1} ι β (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_2 g) -> (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align monotone.monovary Monotone.monovaryₓ'. -/
protected theorem Monotone.monovary (hf : Monotone f) (hg : Monotone g) : Monovary f g :=
  fun i j hij => hf (hg.reflect_lt hij).le
#align monotone.monovary Monotone.monovary

/- warning: monotone.antivary -> Monotone.antivary is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} [_inst_4 : LinearOrder.{u1} ι], (Monotone.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_1 f) -> (Antitone.{u1, u3} ι β (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_2 g) -> (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} [_inst_4 : LinearOrder.{u3} ι], (Monotone.{u3, u2} ι α (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_1 f) -> (Antitone.{u3, u1} ι β (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_2 g) -> (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align monotone.antivary Monotone.antivaryₓ'. -/
protected theorem Monotone.antivary (hf : Monotone f) (hg : Antitone g) : Antivary f g :=
  (hf.Monovary hg.dual_right).dual_right
#align monotone.antivary Monotone.antivary

/- warning: antitone.monovary -> Antitone.monovary is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} [_inst_4 : LinearOrder.{u1} ι], (Antitone.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_1 f) -> (Antitone.{u1, u3} ι β (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_2 g) -> (Monovary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} [_inst_4 : LinearOrder.{u3} ι], (Antitone.{u3, u2} ι α (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_1 f) -> (Antitone.{u3, u1} ι β (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_2 g) -> (Monovary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align antitone.monovary Antitone.monovaryₓ'. -/
protected theorem Antitone.monovary (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  (hf.dual_right.Antivary hg).dual_left
#align antitone.monovary Antitone.monovary

/- warning: antitone.antivary -> Antitone.antivary is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} [_inst_4 : LinearOrder.{u1} ι], (Antitone.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_1 f) -> (Monotone.{u1, u3} ι β (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_2 g) -> (Antivary.{u1, u2, u3} ι α β _inst_1 _inst_2 f g)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} [_inst_4 : LinearOrder.{u3} ι], (Antitone.{u3, u2} ι α (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_1 f) -> (Monotone.{u3, u1} ι β (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_2 g) -> (Antivary.{u3, u2, u1} ι α β _inst_1 _inst_2 f g)
Case conversion may be inaccurate. Consider using '#align antitone.antivary Antitone.antivaryₓ'. -/
protected theorem Antitone.antivary (hf : Antitone f) (hg : Monotone g) : Antivary f g :=
  (hf.Monovary hg.dual_right).dual_right
#align antitone.antivary Antitone.antivary

/- warning: monotone_on.monovary_on -> MonotoneOn.monovaryOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι} [_inst_4 : LinearOrder.{u1} ι], (MonotoneOn.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_1 f s) -> (MonotoneOn.{u1, u3} ι β (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_2 g s) -> (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι} [_inst_4 : LinearOrder.{u3} ι], (MonotoneOn.{u3, u2} ι α (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_1 f s) -> (MonotoneOn.{u3, u1} ι β (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_2 g s) -> (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align monotone_on.monovary_on MonotoneOn.monovaryOnₓ'. -/
protected theorem MonotoneOn.monovaryOn (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonovaryOn f g s := fun i hi j hj hij => hf hi hj (hg.reflect_lt hi hj hij).le
#align monotone_on.monovary_on MonotoneOn.monovaryOn

/- warning: monotone_on.antivary_on -> MonotoneOn.antivaryOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι} [_inst_4 : LinearOrder.{u1} ι], (MonotoneOn.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_1 f s) -> (AntitoneOn.{u1, u3} ι β (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_2 g s) -> (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι} [_inst_4 : LinearOrder.{u3} ι], (MonotoneOn.{u3, u2} ι α (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_1 f s) -> (AntitoneOn.{u3, u1} ι β (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_2 g s) -> (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align monotone_on.antivary_on MonotoneOn.antivaryOnₓ'. -/
protected theorem MonotoneOn.antivaryOn (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntivaryOn f g s :=
  (hf.MonovaryOn hg.dual_right).dual_right
#align monotone_on.antivary_on MonotoneOn.antivaryOn

/- warning: antitone_on.monovary_on -> AntitoneOn.monovaryOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι} [_inst_4 : LinearOrder.{u1} ι], (AntitoneOn.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_1 f s) -> (AntitoneOn.{u1, u3} ι β (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_2 g s) -> (MonovaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι} [_inst_4 : LinearOrder.{u3} ι], (AntitoneOn.{u3, u2} ι α (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_1 f s) -> (AntitoneOn.{u3, u1} ι β (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_2 g s) -> (MonovaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align antitone_on.monovary_on AntitoneOn.monovaryOnₓ'. -/
protected theorem AntitoneOn.monovaryOn (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    MonovaryOn f g s :=
  (hf.dual_right.AntivaryOn hg).dual_left
#align antitone_on.monovary_on AntitoneOn.monovaryOn

/- warning: antitone_on.antivary_on -> AntitoneOn.antivaryOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι} [_inst_4 : LinearOrder.{u1} ι], (AntitoneOn.{u1, u2} ι α (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_1 f s) -> (MonotoneOn.{u1, u3} ι β (PartialOrder.toPreorder.{u1} ι (SemilatticeInf.toPartialOrder.{u1} ι (Lattice.toSemilatticeInf.{u1} ι (LinearOrder.toLattice.{u1} ι _inst_4)))) _inst_2 g s) -> (AntivaryOn.{u1, u2, u3} ι α β _inst_1 _inst_2 f g s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι} [_inst_4 : LinearOrder.{u3} ι], (AntitoneOn.{u3, u2} ι α (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_1 f s) -> (MonotoneOn.{u3, u1} ι β (PartialOrder.toPreorder.{u3} ι (SemilatticeInf.toPartialOrder.{u3} ι (Lattice.toSemilatticeInf.{u3} ι (DistribLattice.toLattice.{u3} ι (instDistribLattice.{u3} ι _inst_4))))) _inst_2 g s) -> (AntivaryOn.{u3, u2, u1} ι α β _inst_1 _inst_2 f g s)
Case conversion may be inaccurate. Consider using '#align antitone_on.antivary_on AntitoneOn.antivaryOnₓ'. -/
protected theorem AntitoneOn.antivaryOn (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    AntivaryOn f g s :=
  (hf.MonovaryOn hg.dual_right).dual_right
#align antitone_on.antivary_on AntitoneOn.antivaryOn

end Preorder

section LinearOrder

variable [Preorder α] [LinearOrder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β} {g' : β → γ}
  {s : Set ι}

/- warning: monovary_on.comp_monotone_on_right -> MonovaryOn.comp_monotoneOn_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ} {s : Set.{u1} ι}, (MonovaryOn.{u1, u2, u3} ι α β _inst_1 (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g s) -> (MonotoneOn.{u3, u4} β γ (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) _inst_3 g' (Set.image.{u1, u3} ι β g s)) -> (MonovaryOn.{u1, u2, u4} ι α γ _inst_1 _inst_3 f (Function.comp.{succ u1, succ u3, succ u4} ι β γ g' g) s)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ} {s : Set.{u4} ι}, (MonovaryOn.{u4, u3, u2} ι α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f g s) -> (MonotoneOn.{u2, u1} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) _inst_3 g' (Set.image.{u4, u2} ι β g s)) -> (MonovaryOn.{u4, u3, u1} ι α γ _inst_1 _inst_3 f (Function.comp.{succ u4, succ u2, succ u1} ι β γ g' g) s)
Case conversion may be inaccurate. Consider using '#align monovary_on.comp_monotone_on_right MonovaryOn.comp_monotoneOn_rightₓ'. -/
theorem MonovaryOn.comp_monotoneOn_right (h : MonovaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun i hi j hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align monovary_on.comp_monotone_on_right MonovaryOn.comp_monotoneOn_right

/- warning: monovary_on.comp_antitone_on_right -> MonovaryOn.comp_antitoneOn_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ} {s : Set.{u1} ι}, (MonovaryOn.{u1, u2, u3} ι α β _inst_1 (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g s) -> (AntitoneOn.{u3, u4} β γ (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) _inst_3 g' (Set.image.{u1, u3} ι β g s)) -> (AntivaryOn.{u1, u2, u4} ι α γ _inst_1 _inst_3 f (Function.comp.{succ u1, succ u3, succ u4} ι β γ g' g) s)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ} {s : Set.{u4} ι}, (MonovaryOn.{u4, u3, u2} ι α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f g s) -> (AntitoneOn.{u2, u1} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) _inst_3 g' (Set.image.{u4, u2} ι β g s)) -> (AntivaryOn.{u4, u3, u1} ι α γ _inst_1 _inst_3 f (Function.comp.{succ u4, succ u2, succ u1} ι β γ g' g) s)
Case conversion may be inaccurate. Consider using '#align monovary_on.comp_antitone_on_right MonovaryOn.comp_antitoneOn_rightₓ'. -/
theorem MonovaryOn.comp_antitoneOn_right (h : MonovaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun i hi j hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align monovary_on.comp_antitone_on_right MonovaryOn.comp_antitoneOn_right

/- warning: antivary_on.comp_monotone_on_right -> AntivaryOn.comp_monotoneOn_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ} {s : Set.{u1} ι}, (AntivaryOn.{u1, u2, u3} ι α β _inst_1 (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g s) -> (MonotoneOn.{u3, u4} β γ (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) _inst_3 g' (Set.image.{u1, u3} ι β g s)) -> (AntivaryOn.{u1, u2, u4} ι α γ _inst_1 _inst_3 f (Function.comp.{succ u1, succ u3, succ u4} ι β γ g' g) s)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ} {s : Set.{u4} ι}, (AntivaryOn.{u4, u3, u2} ι α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f g s) -> (MonotoneOn.{u2, u1} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) _inst_3 g' (Set.image.{u4, u2} ι β g s)) -> (AntivaryOn.{u4, u3, u1} ι α γ _inst_1 _inst_3 f (Function.comp.{succ u4, succ u2, succ u1} ι β γ g' g) s)
Case conversion may be inaccurate. Consider using '#align antivary_on.comp_monotone_on_right AntivaryOn.comp_monotoneOn_rightₓ'. -/
theorem AntivaryOn.comp_monotoneOn_right (h : AntivaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun i hi j hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align antivary_on.comp_monotone_on_right AntivaryOn.comp_monotoneOn_right

/- warning: antivary_on.comp_antitone_on_right -> AntivaryOn.comp_antitoneOn_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u3} β] [_inst_3 : Preorder.{u4} γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ} {s : Set.{u1} ι}, (AntivaryOn.{u1, u2, u3} ι α β _inst_1 (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g s) -> (AntitoneOn.{u3, u4} β γ (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) _inst_3 g' (Set.image.{u1, u3} ι β g s)) -> (MonovaryOn.{u1, u2, u4} ι α γ _inst_1 _inst_3 f (Function.comp.{succ u1, succ u3, succ u4} ι β γ g' g) s)
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Preorder.{u1} γ] {f : ι -> α} {g : ι -> β} {g' : β -> γ} {s : Set.{u4} ι}, (AntivaryOn.{u4, u3, u2} ι α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f g s) -> (AntitoneOn.{u2, u1} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) _inst_3 g' (Set.image.{u4, u2} ι β g s)) -> (MonovaryOn.{u4, u3, u1} ι α γ _inst_1 _inst_3 f (Function.comp.{succ u4, succ u2, succ u1} ι β γ g' g) s)
Case conversion may be inaccurate. Consider using '#align antivary_on.comp_antitone_on_right AntivaryOn.comp_antitoneOn_rightₓ'. -/
theorem AntivaryOn.comp_antitoneOn_right (h : AntivaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun i hi j hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align antivary_on.comp_antitone_on_right AntivaryOn.comp_antitoneOn_right

/- warning: monovary.symm -> Monovary.symm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u3} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u1, u2, u3} ι α β _inst_1 (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g) -> (Monovary.{u1, u3, u2} ι β α (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) _inst_1 g f)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : ι -> α} {g : ι -> β}, (Monovary.{u3, u2, u1} ι α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f g) -> (Monovary.{u3, u1, u2} ι β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) _inst_1 g f)
Case conversion may be inaccurate. Consider using '#align monovary.symm Monovary.symmₓ'. -/
protected theorem Monovary.symm (h : Monovary f g) : Monovary g f := fun i j hf =>
  le_of_not_lt fun hg => hf.not_le <| h hg
#align monovary.symm Monovary.symm

/- warning: antivary.symm -> Antivary.symm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u3} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u1, u2, u3} ι α β _inst_1 (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g) -> (Antivary.{u1, u3, u2} ι β α (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) _inst_1 g f)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : ι -> α} {g : ι -> β}, (Antivary.{u3, u2, u1} ι α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f g) -> (Antivary.{u3, u1, u2} ι β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) _inst_1 g f)
Case conversion may be inaccurate. Consider using '#align antivary.symm Antivary.symmₓ'. -/
protected theorem Antivary.symm (h : Antivary f g) : Antivary g f := fun i j hf =>
  le_of_not_lt fun hg => hf.not_le <| h hg
#align antivary.symm Antivary.symm

/- warning: monovary_on.symm -> MonovaryOn.symm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (MonovaryOn.{u1, u2, u3} ι α β _inst_1 (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g s) -> (MonovaryOn.{u1, u3, u2} ι β α (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) _inst_1 g f s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, (MonovaryOn.{u3, u2, u1} ι α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f g s) -> (MonovaryOn.{u3, u1, u2} ι β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) _inst_1 g f s)
Case conversion may be inaccurate. Consider using '#align monovary_on.symm MonovaryOn.symmₓ'. -/
protected theorem MonovaryOn.symm (h : MonovaryOn f g s) : MonovaryOn g f s := fun i hi j hj hf =>
  le_of_not_lt fun hg => hf.not_le <| h hj hi hg
#align monovary_on.symm MonovaryOn.symm

/- warning: antivary_on.symm -> AntivaryOn.symm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, (AntivaryOn.{u1, u2, u3} ι α β _inst_1 (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g s) -> (AntivaryOn.{u1, u3, u2} ι β α (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) _inst_1 g f s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, (AntivaryOn.{u3, u2, u1} ι α β _inst_1 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f g s) -> (AntivaryOn.{u3, u1, u2} ι β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) _inst_1 g f s)
Case conversion may be inaccurate. Consider using '#align antivary_on.symm AntivaryOn.symmₓ'. -/
protected theorem AntivaryOn.symm (h : AntivaryOn f g s) : AntivaryOn g f s := fun i hi j hj hf =>
  le_of_not_lt fun hg => hf.not_le <| h hi hj hg
#align antivary_on.symm AntivaryOn.symm

end LinearOrder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : ι → α} {g : ι → β} {s : Set ι}

/- warning: monovary_comm -> monovary_comm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u3} β] {f : ι -> α} {g : ι -> β}, Iff (Monovary.{u1, u2, u3} ι α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g) (Monovary.{u1, u3, u2} ι β α (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_1)))) g f)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : ι -> α} {g : ι -> β}, Iff (Monovary.{u3, u2, u1} ι α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f g) (Monovary.{u3, u1, u2} ι β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) g f)
Case conversion may be inaccurate. Consider using '#align monovary_comm monovary_commₓ'. -/
protected theorem monovary_comm : Monovary f g ↔ Monovary g f :=
  ⟨Monovary.symm, Monovary.symm⟩
#align monovary_comm monovary_comm

/- warning: antivary_comm -> antivary_comm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u3} β] {f : ι -> α} {g : ι -> β}, Iff (Antivary.{u1, u2, u3} ι α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g) (Antivary.{u1, u3, u2} ι β α (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_1)))) g f)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : ι -> α} {g : ι -> β}, Iff (Antivary.{u3, u2, u1} ι α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f g) (Antivary.{u3, u1, u2} ι β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) g f)
Case conversion may be inaccurate. Consider using '#align antivary_comm antivary_commₓ'. -/
protected theorem antivary_comm : Antivary f g ↔ Antivary g f :=
  ⟨Antivary.symm, Antivary.symm⟩
#align antivary_comm antivary_comm

/- warning: monovary_on_comm -> monovaryOn_comm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, Iff (MonovaryOn.{u1, u2, u3} ι α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g s) (MonovaryOn.{u1, u3, u2} ι β α (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_1)))) g f s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, Iff (MonovaryOn.{u3, u2, u1} ι α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f g s) (MonovaryOn.{u3, u1, u2} ι β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) g f s)
Case conversion may be inaccurate. Consider using '#align monovary_on_comm monovaryOn_commₓ'. -/
protected theorem monovaryOn_comm : MonovaryOn f g s ↔ MonovaryOn g f s :=
  ⟨MonovaryOn.symm, MonovaryOn.symm⟩
#align monovary_on_comm monovaryOn_comm

/- warning: antivary_on_comm -> antivaryOn_comm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u3} β] {f : ι -> α} {g : ι -> β} {s : Set.{u1} ι}, Iff (AntivaryOn.{u1, u2, u3} ι α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_1)))) (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) f g s) (AntivaryOn.{u1, u3, u2} ι β α (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (LinearOrder.toLattice.{u3} β _inst_2)))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (LinearOrder.toLattice.{u2} α _inst_1)))) g f s)
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : ι -> α} {g : ι -> β} {s : Set.{u3} ι}, Iff (AntivaryOn.{u3, u2, u1} ι α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f g s) (AntivaryOn.{u3, u1, u2} ι β α (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) g f s)
Case conversion may be inaccurate. Consider using '#align antivary_on_comm antivaryOn_commₓ'. -/
protected theorem antivaryOn_comm : AntivaryOn f g s ↔ AntivaryOn g f s :=
  ⟨AntivaryOn.symm, AntivaryOn.symm⟩
#align antivary_on_comm antivaryOn_comm

end LinearOrder

