/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

! This file was ported from Lean 3 source module data.set.image
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Basic

/-!
# Images and preimages of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `preimage f t : set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `range f : set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

## Notation

* `f ⁻¹' t` for `set.preimage f t`

* `f '' s` for `set.image f s`

## Tags

set, sets, image, preimage, pre-image, range

-/


universe u v

open Function

namespace Set

variable {α β γ : Type _} {ι : Sort _}

/-! ### Inverse image -/


#print Set.preimage /-
/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage {α : Type u} {β : Type v} (f : α → β) (s : Set β) : Set α :=
  { x | f x ∈ s }
#align set.preimage Set.preimage
-/

-- mathport name: «expr ⁻¹' »
infixl:80 " ⁻¹' " => preimage

section Preimage

variable {f : α → β} {g : β → γ}

/- warning: set.preimage_empty -> Set.preimage_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β f (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))
Case conversion may be inaccurate. Consider using '#align set.preimage_empty Set.preimage_emptyₓ'. -/
@[simp]
theorem preimage_empty : f ⁻¹' ∅ = ∅ :=
  rfl
#align set.preimage_empty Set.preimage_empty

#print Set.mem_preimage /-
@[simp]
theorem mem_preimage {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s :=
  Iff.rfl
#align set.mem_preimage Set.mem_preimage
-/

#print Set.preimage_congr /-
theorem preimage_congr {f g : α → β} {s : Set β} (h : ∀ x : α, f x = g x) : f ⁻¹' s = g ⁻¹' s :=
  by
  congr with x
  apply_assumption
#align set.preimage_congr Set.preimage_congr
-/

#print Set.preimage_mono /-
theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t := fun x hx => h hx
#align set.preimage_mono Set.preimage_mono
-/

/- warning: set.preimage_univ -> Set.preimage_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.univ.{u2} β)) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β f (Set.univ.{u1} β)) (Set.univ.{u2} α)
Case conversion may be inaccurate. Consider using '#align set.preimage_univ Set.preimage_univₓ'. -/
@[simp]
theorem preimage_univ : f ⁻¹' univ = univ :=
  rfl
#align set.preimage_univ Set.preimage_univ

/- warning: set.subset_preimage_univ -> Set.subset_preimage_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.preimage.{u1, u2} α β f (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.preimage.{u2, u1} α β f (Set.univ.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.subset_preimage_univ Set.subset_preimage_univₓ'. -/
theorem subset_preimage_univ {s : Set α} : s ⊆ f ⁻¹' univ :=
  subset_univ _
#align set.subset_preimage_univ Set.subset_preimage_univ

/- warning: set.preimage_inter -> Set.preimage_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t))
Case conversion may be inaccurate. Consider using '#align set.preimage_inter Set.preimage_interₓ'. -/
@[simp]
theorem preimage_inter {s t : Set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  rfl
#align set.preimage_inter Set.preimage_inter

/- warning: set.preimage_union -> Set.preimage_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t))
Case conversion may be inaccurate. Consider using '#align set.preimage_union Set.preimage_unionₓ'. -/
@[simp]
theorem preimage_union {s t : Set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
  rfl
#align set.preimage_union Set.preimage_union

/- warning: set.preimage_compl -> Set.preimage_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.preimage.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Set.preimage.{u1, u2} α β f s))
Case conversion may be inaccurate. Consider using '#align set.preimage_compl Set.preimage_complₓ'. -/
@[simp]
theorem preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ :=
  rfl
#align set.preimage_compl Set.preimage_compl

/- warning: set.preimage_diff -> Set.preimage_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (SDiff.sdiff.{u2} (Set.{u2} β) (Set.instSDiffSet.{u2} β) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t))
Case conversion may be inaccurate. Consider using '#align set.preimage_diff Set.preimage_diffₓ'. -/
@[simp]
theorem preimage_diff (f : α → β) (s t : Set β) : f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t :=
  rfl
#align set.preimage_diff Set.preimage_diff

#print Set.preimage_ite /-
@[simp]
theorem preimage_ite (f : α → β) (s t₁ t₂ : Set β) :
    f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
  rfl
#align set.preimage_ite Set.preimage_ite
-/

#print Set.preimage_setOf_eq /-
@[simp]
theorem preimage_setOf_eq {p : α → Prop} {f : β → α} : f ⁻¹' { a | p a } = { a | p (f a) } :=
  rfl
#align set.preimage_set_of_eq Set.preimage_setOf_eq
-/

#print Set.preimage_id_eq /-
@[simp]
theorem preimage_id_eq : preimage (id : α → α) = id :=
  rfl
#align set.preimage_id_eq Set.preimage_id_eq
-/

#print Set.preimage_id /-
theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  rfl
#align set.preimage_id Set.preimage_id
-/

#print Set.preimage_id' /-
@[simp]
theorem preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s :=
  rfl
#align set.preimage_id' Set.preimage_id'
-/

#print Set.preimage_const_of_mem /-
@[simp]
theorem preimage_const_of_mem {b : β} {s : Set β} (h : b ∈ s) : (fun x : α => b) ⁻¹' s = univ :=
  eq_univ_of_forall fun x => h
#align set.preimage_const_of_mem Set.preimage_const_of_mem
-/

#print Set.preimage_const_of_not_mem /-
@[simp]
theorem preimage_const_of_not_mem {b : β} {s : Set β} (h : b ∉ s) : (fun x : α => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty fun x hx => h hx
#align set.preimage_const_of_not_mem Set.preimage_const_of_not_mem
-/

#print Set.preimage_const /-
theorem preimage_const (b : β) (s : Set β) [Decidable (b ∈ s)] :
    (fun x : α => b) ⁻¹' s = if b ∈ s then univ else ∅ :=
  by
  split_ifs with hb hb
  exacts[preimage_const_of_mem hb, preimage_const_of_not_mem hb]
#align set.preimage_const Set.preimage_const
-/

/- warning: set.preimage_comp -> Set.preimage_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : β -> γ} {s : Set.{u3} γ}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) s) (Set.preimage.{u1, u2} α β f (Set.preimage.{u2, u3} β γ g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {f : α -> β} {g : β -> γ} {s : Set.{u3} γ}, Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u3} α γ (Function.comp.{succ u2, succ u1, succ u3} α β γ g f) s) (Set.preimage.{u2, u1} α β f (Set.preimage.{u1, u3} β γ g s))
Case conversion may be inaccurate. Consider using '#align set.preimage_comp Set.preimage_compₓ'. -/
theorem preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' (g ⁻¹' s) :=
  rfl
#align set.preimage_comp Set.preimage_comp

/- warning: set.preimage_comp_eq -> Set.preimage_comp_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : β -> γ}, Eq.{max (succ u3) (succ u1)} ((Set.{u3} γ) -> (Set.{u1} α)) (Set.preimage.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Function.comp.{succ u3, succ u2, succ u1} (Set.{u3} γ) (Set.{u2} β) (Set.{u1} α) (Set.preimage.{u1, u2} α β f) (Set.preimage.{u2, u3} β γ g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {f : α -> β} {g : β -> γ}, Eq.{max (succ u3) (succ u2)} ((Set.{u2} γ) -> (Set.{u3} α)) (Set.preimage.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f)) (Function.comp.{succ u2, succ u1, succ u3} (Set.{u2} γ) (Set.{u1} β) (Set.{u3} α) (Set.preimage.{u3, u1} α β f) (Set.preimage.{u1, u2} β γ g))
Case conversion may be inaccurate. Consider using '#align set.preimage_comp_eq Set.preimage_comp_eqₓ'. -/
theorem preimage_comp_eq : preimage (g ∘ f) = preimage f ∘ preimage g :=
  rfl
#align set.preimage_comp_eq Set.preimage_comp_eq

#print Set.preimage_iterate_eq /-
@[simp]
theorem preimage_iterate_eq {f : α → α} {n : ℕ} : Set.preimage (f^[n]) = Set.preimage f^[n] :=
  by
  induction' n with n ih; · simp
  rw [iterate_succ, iterate_succ', Set.preimage_comp_eq, ih]
#align set.preimage_iterate_eq Set.preimage_iterate_eq
-/

/- warning: set.preimage_preimage -> Set.preimage_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {g : β -> γ} {f : α -> β} {s : Set.{u3} γ}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.preimage.{u2, u3} β γ g s)) (Set.preimage.{u1, u3} α γ (fun (x : α) => g (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {g : β -> γ} {f : α -> β} {s : Set.{u3} γ}, Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β f (Set.preimage.{u1, u3} β γ g s)) (Set.preimage.{u2, u3} α γ (fun (x : α) => g (f x)) s)
Case conversion may be inaccurate. Consider using '#align set.preimage_preimage Set.preimage_preimageₓ'. -/
theorem preimage_preimage {g : β → γ} {f : α → β} {s : Set γ} :
    f ⁻¹' (g ⁻¹' s) = (fun x => g (f x)) ⁻¹' s :=
  preimage_comp.symm
#align set.preimage_preimage Set.preimage_preimage

#print Set.eq_preimage_subtype_val_iff /-
theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : Set (Subtype p)} {t : Set α} :
    s = Subtype.val ⁻¹' t ↔ ∀ (x) (h : p x), (⟨x, h⟩ : Subtype p) ∈ s ↔ x ∈ t :=
  ⟨fun s_eq x h => by
    rw [s_eq]
    simp, fun h => ext fun ⟨x, hx⟩ => by simp [h]⟩
#align set.eq_preimage_subtype_val_iff Set.eq_preimage_subtype_val_iff
-/

#print Set.nonempty_of_nonempty_preimage /-
theorem nonempty_of_nonempty_preimage {s : Set β} {f : α → β} (hf : (f ⁻¹' s).Nonempty) :
    s.Nonempty :=
  let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩
#align set.nonempty_of_nonempty_preimage Set.nonempty_of_nonempty_preimage
-/

/- warning: set.preimage_subtype_coe_eq_compl -> Set.preimage_subtype_coe_eq_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {u : Set.{u1} α} {v : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) u v)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u v)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Eq.{succ u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) u) (HasCompl.compl.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.booleanAlgebra.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s))) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) v)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {u : Set.{u1} α} {v : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) u v)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u v)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Eq.{succ u1} (Set.{u1} (Set.Elem.{u1} α s)) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) u) (HasCompl.compl.{u1} (Set.{u1} (Set.Elem.{u1} α s)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Set.Elem.{u1} α s)) (Set.instBooleanAlgebraSet.{u1} (Set.Elem.{u1} α s))) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) v)))
Case conversion may be inaccurate. Consider using '#align set.preimage_subtype_coe_eq_compl Set.preimage_subtype_coe_eq_complₓ'. -/
theorem preimage_subtype_coe_eq_compl {α : Type _} {s u v : Set α} (hsuv : s ⊆ u ∪ v)
    (H : s ∩ (u ∩ v) = ∅) : (coe : s → α) ⁻¹' u = (coe ⁻¹' v)ᶜ :=
  by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_not_mem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
  · intro hx
    exact Or.elim (hsuv x_in_s) id fun hx' => hx.elim hx'
#align set.preimage_subtype_coe_eq_compl Set.preimage_subtype_coe_eq_compl

end Preimage

/-! ### Image of a set under a function -/


section Image

variable {f : α → β} {s t : Set α}

#print Set.image /-
/-- The image of `s : set α` by `f : α → β`, written `f '' s`,
  is the set of `y : β` such that `f x = y` for some `x ∈ s`. -/
def image (f : α → β) (s : Set α) : Set β :=
  { y | ∃ x, x ∈ s ∧ f x = y }
#align set.image Set.image
-/

-- mathport name: «expr '' »
infixl:80 " '' " => image

/- warning: set.mem_image_iff_bex -> Set.mem_image_iff_bex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {y : β}, Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.image.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (_x : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Eq.{succ u2} β (f x) y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {y : β}, Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.image.{u2, u1} α β f s)) (Exists.{succ u2} α (fun (x : α) => Exists.{0} (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (fun (_x : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) => Eq.{succ u1} β (f x) y)))
Case conversion may be inaccurate. Consider using '#align set.mem_image_iff_bex Set.mem_image_iff_bexₓ'. -/
theorem mem_image_iff_bex {f : α → β} {s : Set α} {y : β} :
    y ∈ f '' s ↔ ∃ (x : _)(_ : x ∈ s), f x = y :=
  bex_def.symm
#align set.mem_image_iff_bex Set.mem_image_iff_bex

/- warning: set.mem_image -> Set.mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (y : β), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.image.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (x : α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (Eq.{succ u2} β (f x) y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (y : β), Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.image.{u2, u1} α β f s)) (Exists.{succ u2} α (fun (x : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (Eq.{succ u1} β (f x) y)))
Case conversion may be inaccurate. Consider using '#align set.mem_image Set.mem_imageₓ'. -/
@[simp]
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y :=
  Iff.rfl
#align set.mem_image Set.mem_image

#print Set.image_eta /-
theorem image_eta (f : α → β) : f '' s = (fun x => f x) '' s :=
  rfl
#align set.image_eta Set.image_eta
-/

/- warning: set.mem_image_of_mem -> Set.mem_image_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) {x : α} {a : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) (Set.image.{u1, u2} α β f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) {x : α} {a : Set.{u2} α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x a) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) (Set.image.{u2, u1} α β f a))
Case conversion may be inaccurate. Consider using '#align set.mem_image_of_mem Set.mem_image_of_memₓ'. -/
theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f '' a :=
  ⟨_, h, rfl⟩
#align set.mem_image_of_mem Set.mem_image_of_mem

/- warning: function.injective.mem_set_image -> Function.Injective.mem_set_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f a) (Set.image.{u1, u2} α β f s)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {s : Set.{u2} α} {a : α}, Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f a) (Set.image.{u2, u1} α β f s)) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s))
Case conversion may be inaccurate. Consider using '#align function.injective.mem_set_image Function.Injective.mem_set_imageₓ'. -/
theorem Function.Injective.mem_set_image {f : α → β} (hf : Injective f) {s : Set α} {a : α} :
    f a ∈ f '' s ↔ a ∈ s :=
  ⟨fun ⟨b, hb, Eq⟩ => hf Eq ▸ hb, mem_image_of_mem f⟩
#align function.injective.mem_set_image Function.Injective.mem_set_image

/- warning: set.ball_image_iff -> Set.ball_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {p : β -> Prop}, Iff (forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.image.{u1, u2} α β f s)) -> (p y)) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (p (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {p : β -> Prop}, Iff (forall (y : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.image.{u2, u1} α β f s)) -> (p y)) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (p (f x)))
Case conversion may be inaccurate. Consider using '#align set.ball_image_iff Set.ball_image_iffₓ'. -/
theorem ball_image_iff {f : α → β} {s : Set α} {p : β → Prop} :
    (∀ y ∈ f '' s, p y) ↔ ∀ x ∈ s, p (f x) := by simp
#align set.ball_image_iff Set.ball_image_iff

/- warning: set.ball_image_of_ball -> Set.ball_image_of_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {p : β -> Prop}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (p (f x))) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.image.{u1, u2} α β f s)) -> (p y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {p : β -> Prop}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (p (f x))) -> (forall (y : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.image.{u2, u1} α β f s)) -> (p y))
Case conversion may be inaccurate. Consider using '#align set.ball_image_of_ball Set.ball_image_of_ballₓ'. -/
theorem ball_image_of_ball {f : α → β} {s : Set α} {p : β → Prop} (h : ∀ x ∈ s, p (f x)) :
    ∀ y ∈ f '' s, p y :=
  ball_image_iff.2 h
#align set.ball_image_of_ball Set.ball_image_of_ball

/- warning: set.bex_image_iff -> Set.bex_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {p : β -> Prop}, Iff (Exists.{succ u2} β (fun (y : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.image.{u1, u2} α β f s)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.image.{u1, u2} α β f s)) => p y))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => p (f x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {p : β -> Prop}, Iff (Exists.{succ u1} β (fun (y : β) => And (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.image.{u2, u1} α β f s)) (p y))) (Exists.{succ u2} α (fun (x : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (p (f x))))
Case conversion may be inaccurate. Consider using '#align set.bex_image_iff Set.bex_image_iffₓ'. -/
theorem bex_image_iff {f : α → β} {s : Set α} {p : β → Prop} :
    (∃ y ∈ f '' s, p y) ↔ ∃ x ∈ s, p (f x) := by simp
#align set.bex_image_iff Set.bex_image_iff

/- warning: set.mem_image_elim -> Set.mem_image_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {C : β -> Prop}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (C (f x))) -> (forall {y : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.image.{u1, u2} α β f s)) -> (C y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {C : β -> Prop}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (C (f x))) -> (forall {y : β}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.image.{u2, u1} α β f s)) -> (C y))
Case conversion may be inaccurate. Consider using '#align set.mem_image_elim Set.mem_image_elimₓ'. -/
theorem mem_image_elim {f : α → β} {s : Set α} {C : β → Prop} (h : ∀ x : α, x ∈ s → C (f x)) :
    ∀ {y : β}, y ∈ f '' s → C y
  | _, ⟨a, a_in, rfl⟩ => h a a_in
#align set.mem_image_elim Set.mem_image_elim

/- warning: set.mem_image_elim_on -> Set.mem_image_elim_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {C : β -> Prop} {y : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.image.{u1, u2} α β f s)) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (C (f x))) -> (C y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {C : β -> Prop} {y : β}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.image.{u2, u1} α β f s)) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (C (f x))) -> (C y)
Case conversion may be inaccurate. Consider using '#align set.mem_image_elim_on Set.mem_image_elim_onₓ'. -/
theorem mem_image_elim_on {f : α → β} {s : Set α} {C : β → Prop} {y : β} (h_y : y ∈ f '' s)
    (h : ∀ x : α, x ∈ s → C (f x)) : C y :=
  mem_image_elim h h_y
#align set.mem_image_elim_on Set.mem_image_elim_on

/- warning: set.image_congr -> Set.image_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u2} β (f a) (g a))) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Eq.{succ u1} β (f a) (g a))) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β g s))
Case conversion may be inaccurate. Consider using '#align set.image_congr Set.image_congrₓ'. -/
@[congr]
theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a ∈ s, f a = g a) : f '' s = g '' s := by
  safe [ext_iff, iff_def]
#align set.image_congr Set.image_congr

/- warning: set.image_congr' -> Set.image_congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (forall (x : α), Eq.{succ u2} β (f x) (g x)) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (forall (x : α), Eq.{succ u1} β (f x) (g x)) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β g s))
Case conversion may be inaccurate. Consider using '#align set.image_congr' Set.image_congr'ₓ'. -/
/-- A common special case of `image_congr` -/
theorem image_congr' {f g : α → β} {s : Set α} (h : ∀ x : α, f x = g x) : f '' s = g '' s :=
  image_congr fun x _ => h x
#align set.image_congr' Set.image_congr'

/- warning: set.image_comp -> Set.image_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : β -> γ) (g : α -> β) (a : Set.{u1} α), Eq.{succ u3} (Set.{u3} γ) (Set.image.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ f g) a) (Set.image.{u2, u3} β γ f (Set.image.{u1, u2} α β g a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (f : β -> γ) (g : α -> β) (a : Set.{u3} α), Eq.{succ u2} (Set.{u2} γ) (Set.image.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ f g) a) (Set.image.{u1, u2} β γ f (Set.image.{u3, u1} α β g a))
Case conversion may be inaccurate. Consider using '#align set.image_comp Set.image_compₓ'. -/
theorem image_comp (f : β → γ) (g : α → β) (a : Set α) : f ∘ g '' a = f '' (g '' a) :=
  Subset.antisymm (ball_image_of_ball fun a ha => mem_image_of_mem _ <| mem_image_of_mem _ ha)
    (ball_image_of_ball <| ball_image_of_ball fun a ha => mem_image_of_mem _ ha)
#align set.image_comp Set.image_comp

/- warning: set.image_image -> Set.image_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (g : β -> γ) (f : α -> β) (s : Set.{u1} α), Eq.{succ u3} (Set.{u3} γ) (Set.image.{u2, u3} β γ g (Set.image.{u1, u2} α β f s)) (Set.image.{u1, u3} α γ (fun (x : α) => g (f x)) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (g : β -> γ) (f : α -> β) (s : Set.{u3} α), Eq.{succ u2} (Set.{u2} γ) (Set.image.{u1, u2} β γ g (Set.image.{u3, u1} α β f s)) (Set.image.{u3, u2} α γ (fun (x : α) => g (f x)) s)
Case conversion may be inaccurate. Consider using '#align set.image_image Set.image_imageₓ'. -/
/-- A variant of `image_comp`, useful for rewriting -/
theorem image_image (g : β → γ) (f : α → β) (s : Set α) : g '' (f '' s) = (fun x => g (f x)) '' s :=
  (image_comp g f s).symm
#align set.image_image Set.image_image

#print Set.image_comm /-
theorem image_comm {β'} {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.image g).image f = (s.image f').image g' := by
  simp_rw [image_image, h_comm]
#align set.image_comm Set.image_comm
-/

/- warning: function.semiconj.set_image -> Function.Semiconj.set_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {ga : α -> α} {gb : β -> β}, (Function.Semiconj.{u1, u2} α β f ga gb) -> (Function.Semiconj.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.image.{u1, u2} α β f) (Set.image.{u1, u1} α α ga) (Set.image.{u2, u2} β β gb))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {ga : α -> α} {gb : β -> β}, (Function.Semiconj.{u2, u1} α β f ga gb) -> (Function.Semiconj.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.image.{u2, u1} α β f) (Set.image.{u2, u2} α α ga) (Set.image.{u1, u1} β β gb))
Case conversion may be inaccurate. Consider using '#align function.semiconj.set_image Function.Semiconj.set_imageₓ'. -/
theorem Function.Semiconj.set_image {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun s =>
  image_comm h
#align function.semiconj.set_image Function.Semiconj.set_image

#print Function.Commute.set_image /-
theorem Function.Commute.set_image {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  h.set_image
#align function.commute.set_image Function.Commute.set_image
-/

/- warning: set.image_subset -> Set.image_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {a : Set.{u1} α} {b : Set.{u1} α} (f : α -> β), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a b) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f a) (Set.image.{u1, u2} α β f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {a : Set.{u2} α} {b : Set.{u2} α} (f : α -> β), (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) a b) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f a) (Set.image.{u2, u1} α β f b))
Case conversion may be inaccurate. Consider using '#align set.image_subset Set.image_subsetₓ'. -/
/-- Image is monotone with respect to `⊆`. See `set.monotone_image` for the statement in
terms of `≤`. -/
theorem image_subset {a b : Set α} (f : α → β) (h : a ⊆ b) : f '' a ⊆ f '' b :=
  by
  simp only [subset_def, mem_image]
  exact fun x => fun ⟨w, h1, h2⟩ => ⟨w, h h1, h2⟩
#align set.image_subset Set.image_subset

/- warning: set.monotone_image -> Set.monotone_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) (Set.image.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)))))))) (Set.image.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align set.monotone_image Set.monotone_imageₓ'. -/
/-- `set.image` is monotone. See `set.image_subset` for the statement in terms of `⊆`. -/
theorem monotone_image {f : α → β} : Monotone (image f) := fun s t => image_subset _
#align set.monotone_image Set.monotone_image

/- warning: set.image_union -> Set.image_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align set.image_union Set.image_unionₓ'. -/
theorem image_union (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t :=
  ext fun x =>
    ⟨by rintro ⟨a, h | h, rfl⟩ <;> [left, right] <;> exact ⟨_, h, rfl⟩, by
      rintro (⟨a, h, rfl⟩ | ⟨a, h, rfl⟩) <;> refine' ⟨_, _, rfl⟩ <;> [left, right] <;> exact h⟩
#align set.image_union Set.image_union

#print Set.image_empty /-
@[simp]
theorem image_empty (f : α → β) : f '' ∅ = ∅ := by
  ext
  simp
#align set.image_empty Set.image_empty
-/

/- warning: set.image_inter_subset -> Set.image_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align set.image_inter_subset Set.image_inter_subsetₓ'. -/
theorem image_inter_subset (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  subset_inter (image_subset _ <| inter_subset_left _ _) (image_subset _ <| inter_subset_right _ _)
#align set.image_inter_subset Set.image_inter_subset

/- warning: set.image_inter_on -> Set.image_inter_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Eq.{succ u2} β (f x) (f y)) -> (Eq.{succ u1} α x y))) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Eq.{succ u1} β (f x) (f y)) -> (Eq.{succ u2} α x y))) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align set.image_inter_on Set.image_inter_onₓ'. -/
theorem image_inter_on {f : α → β} {s t : Set α} (h : ∀ x ∈ t, ∀ y ∈ s, f x = f y → x = y) :
    f '' (s ∩ t) = f '' s ∩ f '' t :=
  (image_inter_subset _ _ _).antisymm fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ =>
    have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
    ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩
#align set.image_inter_on Set.image_inter_on

/- warning: set.image_inter -> Set.image_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (Function.Injective.{succ u1, succ u2} α β f) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (Function.Injective.{succ u2, succ u1} α β f) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align set.image_inter Set.image_interₓ'. -/
theorem image_inter {f : α → β} {s t : Set α} (H : Injective f) : f '' (s ∩ t) = f '' s ∩ f '' t :=
  image_inter_on fun x _ y _ h => H h
#align set.image_inter Set.image_inter

#print Set.image_univ_of_surjective /-
theorem image_univ_of_surjective {ι : Type _} {f : ι → β} (H : Surjective f) : f '' univ = univ :=
  eq_univ_of_forall <| by simpa [image]
#align set.image_univ_of_surjective Set.image_univ_of_surjective
-/

#print Set.image_singleton /-
@[simp]
theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
  by
  ext
  simp [image, eq_comm]
#align set.image_singleton Set.image_singleton
-/

/- warning: set.nonempty.image_const -> Set.Nonempty.image_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall (a : β), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (fun (_x : α) => a) s) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall (a : β), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (fun (_x : α) => a) s) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) a))
Case conversion may be inaccurate. Consider using '#align set.nonempty.image_const Set.Nonempty.image_constₓ'. -/
@[simp]
theorem Nonempty.image_const {s : Set α} (hs : s.Nonempty) (a : β) : (fun _ => a) '' s = {a} :=
  ext fun x =>
    ⟨fun ⟨y, _, h⟩ => h ▸ mem_singleton _, fun h =>
      (eq_of_mem_singleton h).symm ▸ hs.imp fun y hy => ⟨hy, rfl⟩⟩
#align set.nonempty.image_const Set.Nonempty.image_const

/- warning: set.image_eq_empty -> Set.image_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, Iff (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, Iff (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (Eq.{succ u2} (Set.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)))
Case conversion may be inaccurate. Consider using '#align set.image_eq_empty Set.image_eq_emptyₓ'. -/
@[simp]
theorem image_eq_empty {α β} {f : α → β} {s : Set α} : f '' s = ∅ ↔ s = ∅ :=
  by
  simp only [eq_empty_iff_forall_not_mem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩
#align set.image_eq_empty Set.image_eq_empty

#print Set.preimage_compl_eq_image_compl /-
theorem preimage_compl_eq_image_compl [BooleanAlgebra α] (S : Set α) : compl ⁻¹' S = compl '' S :=
  Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h =>
      Exists.elim h fun y hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩
#align set.preimage_compl_eq_image_compl Set.preimage_compl_eq_image_compl
-/

#print Set.mem_compl_image /-
theorem mem_compl_image [BooleanAlgebra α] (t : α) (S : Set α) : t ∈ compl '' S ↔ tᶜ ∈ S := by
  simp [← preimage_compl_eq_image_compl]
#align set.mem_compl_image Set.mem_compl_image
-/

#print Set.image_id' /-
/-- A variant of `image_id` -/
@[simp]
theorem image_id' (s : Set α) : (fun x => x) '' s = s :=
  by
  ext
  simp
#align set.image_id' Set.image_id'
-/

#print Set.image_id /-
theorem image_id (s : Set α) : id '' s = s := by simp
#align set.image_id Set.image_id
-/

#print Set.compl_compl_image /-
theorem compl_compl_image [BooleanAlgebra α] (S : Set α) : compl '' (compl '' S) = S := by
  rw [← image_comp, compl_comp_compl, image_id]
#align set.compl_compl_image Set.compl_compl_image
-/

/- warning: set.image_insert_eq -> Set.image_insert_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {a : α} {s : Set.{u1} α}, Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) (f a) (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {a : α} {s : Set.{u2} α}, Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) (f a) (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.image_insert_eq Set.image_insert_eqₓ'. -/
theorem image_insert_eq {f : α → β} {a : α} {s : Set α} : f '' insert a s = insert (f a) (f '' s) :=
  by
  ext
  simp [and_or_left, exists_or, eq_comm, or_comm', and_comm']
#align set.image_insert_eq Set.image_insert_eq

#print Set.image_pair /-
theorem image_pair (f : α → β) (a b : α) : f '' {a, b} = {f a, f b} := by
  simp only [image_insert_eq, image_singleton]
#align set.image_pair Set.image_pair
-/

/- warning: set.image_subset_preimage_of_inverse -> Set.image_subset_preimage_of_inverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u1, succ u2} α β g f) -> (forall (s : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f s) (Set.preimage.{u2, u1} β α g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u2, succ u1} α β g f) -> (forall (s : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.preimage.{u1, u2} β α g s))
Case conversion may be inaccurate. Consider using '#align set.image_subset_preimage_of_inverse Set.image_subset_preimage_of_inverseₓ'. -/
theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set α) :
    f '' s ⊆ g ⁻¹' s := fun b ⟨a, h, e⟩ => e ▸ ((I a).symm ▸ h : g (f a) ∈ s)
#align set.image_subset_preimage_of_inverse Set.image_subset_preimage_of_inverse

/- warning: set.preimage_subset_image_of_inverse -> Set.preimage_subset_image_of_inverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u1, succ u2} α β g f) -> (forall (s : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.preimage.{u1, u2} α β f s) (Set.image.{u2, u1} β α g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u2, succ u1} α β g f) -> (forall (s : Set.{u1} β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.preimage.{u2, u1} α β f s) (Set.image.{u1, u2} β α g s))
Case conversion may be inaccurate. Consider using '#align set.preimage_subset_image_of_inverse Set.preimage_subset_image_of_inverseₓ'. -/
theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set β) :
    f ⁻¹' s ⊆ g '' s := fun b h => ⟨f b, h, I b⟩
#align set.preimage_subset_image_of_inverse Set.preimage_subset_image_of_inverse

/- warning: set.image_eq_preimage_of_inverse -> Set.image_eq_preimage_of_inverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u1, succ u2} α β g f) -> (Function.RightInverse.{succ u1, succ u2} α β g f) -> (Eq.{max (succ u1) (succ u2)} ((Set.{u1} α) -> (Set.{u2} β)) (Set.image.{u1, u2} α β f) (Set.preimage.{u2, u1} β α g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u2, succ u1} α β g f) -> (Function.RightInverse.{succ u2, succ u1} α β g f) -> (Eq.{max (succ u2) (succ u1)} ((Set.{u2} α) -> (Set.{u1} β)) (Set.image.{u2, u1} α β f) (Set.preimage.{u1, u2} β α g))
Case conversion may be inaccurate. Consider using '#align set.image_eq_preimage_of_inverse Set.image_eq_preimage_of_inverseₓ'. -/
theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : image f = preimage g :=
  funext fun s =>
    Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)
#align set.image_eq_preimage_of_inverse Set.image_eq_preimage_of_inverse

/- warning: set.mem_image_iff_of_inverse -> Set.mem_image_iff_of_inverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : β -> α} {b : β} {s : Set.{u1} α}, (Function.LeftInverse.{succ u1, succ u2} α β g f) -> (Function.RightInverse.{succ u1, succ u2} α β g f) -> (Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.image.{u1, u2} α β f s)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (g b) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : β -> α} {b : β} {s : Set.{u2} α}, (Function.LeftInverse.{succ u2, succ u1} α β g f) -> (Function.RightInverse.{succ u2, succ u1} α β g f) -> (Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b (Set.image.{u2, u1} α β f s)) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (g b) s))
Case conversion may be inaccurate. Consider using '#align set.mem_image_iff_of_inverse Set.mem_image_iff_of_inverseₓ'. -/
theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : b ∈ f '' s ↔ g b ∈ s := by
  rw [image_eq_preimage_of_inverse h₁ h₂] <;> rfl
#align set.mem_image_iff_of_inverse Set.mem_image_iff_of_inverse

/- warning: set.image_compl_subset -> Set.image_compl_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, (Function.Injective.{succ u1, succ u2} α β f) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, (Function.Injective.{succ u2, succ u1} α β f) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.image_compl_subset Set.image_compl_subsetₓ'. -/
theorem image_compl_subset {f : α → β} {s : Set α} (H : Injective f) : f '' sᶜ ⊆ (f '' s)ᶜ :=
  Disjoint.subset_compl_left <| by simp [disjoint_iff_inf_le, ← image_inter H]
#align set.image_compl_subset Set.image_compl_subset

/- warning: set.subset_image_compl -> Set.subset_image_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, (Function.Surjective.{succ u1, succ u2} α β f) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s)) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, (Function.Surjective.{succ u2, succ u1} α β f) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) (Set.image.{u2, u1} α β f s)) (Set.image.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)))
Case conversion may be inaccurate. Consider using '#align set.subset_image_compl Set.subset_image_complₓ'. -/
theorem subset_image_compl {f : α → β} {s : Set α} (H : Surjective f) : (f '' s)ᶜ ⊆ f '' sᶜ :=
  compl_subset_iff_union.2 <| by
    rw [← image_union]
    simp [image_univ_of_surjective H]
#align set.subset_image_compl Set.subset_image_compl

/- warning: set.image_compl_eq -> Set.image_compl_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, (Function.Bijective.{succ u1, succ u2} α β f) -> (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, (Function.Bijective.{succ u2, succ u1} α β f) -> (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.image_compl_eq Set.image_compl_eqₓ'. -/
theorem image_compl_eq {f : α → β} {s : Set α} (H : Bijective f) : f '' sᶜ = (f '' s)ᶜ :=
  Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)
#align set.image_compl_eq Set.image_compl_eq

/- warning: set.subset_image_diff -> Set.subset_image_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)) (Set.image.{u1, u2} α β f (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)) (Set.image.{u2, u1} α β f (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s t))
Case conversion may be inaccurate. Consider using '#align set.subset_image_diff Set.subset_image_diffₓ'. -/
theorem subset_image_diff (f : α → β) (s t : Set α) : f '' s \ f '' t ⊆ f '' (s \ t) :=
  by
  rw [diff_subset_iff, ← image_union, union_diff_self]
  exact image_subset f (subset_union_right t s)
#align set.subset_image_diff Set.subset_image_diff

/- warning: set.subset_image_symm_diff -> Set.subset_image_symm_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toHasSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)) (Set.image.{u1, u2} α β f (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toHasSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))) (Set.instSDiffSet.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)) (Set.image.{u1, u2} α β f (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.subset_image_symm_diff Set.subset_image_symm_diffₓ'. -/
theorem subset_image_symm_diff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
  (union_subset_union (subset_image_diff _ _ _) <| subset_image_diff _ _ _).trans
    (image_union _ _ _).Superset
#align set.subset_image_symm_diff Set.subset_image_symm_diff

/- warning: set.image_diff -> Set.image_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u2} α) (t : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s t)) (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align set.image_diff Set.image_diffₓ'. -/
theorem image_diff {f : α → β} (hf : Injective f) (s t : Set α) : f '' (s \ t) = f '' s \ f '' t :=
  Subset.antisymm
    (Subset.trans (image_inter_subset _ _ _) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_diff f s t)
#align set.image_diff Set.image_diff

/- warning: set.image_symm_diff -> Set.image_symm_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toHasSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u2} α) (t : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (symmDiff.{u2} (Set.{u2} α) (SemilatticeSup.toHasSup.{u2} (Set.{u2} α) (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (Set.instSDiffSet.{u2} α) s t)) (symmDiff.{u1} (Set.{u1} β) (SemilatticeSup.toHasSup.{u1} (Set.{u1} β) (Lattice.toSemilatticeSup.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (Set.instSDiffSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align set.image_symm_diff Set.image_symm_diffₓ'. -/
theorem image_symm_diff (hf : Injective f) (s t : Set α) : f '' s ∆ t = (f '' s) ∆ (f '' t) := by
  simp_rw [Set.symmDiff_def, image_union, image_diff hf]
#align set.image_symm_diff Set.image_symm_diff

/- warning: set.nonempty.image -> Set.Nonempty.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u1} β (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.nonempty.image Set.Nonempty.imageₓ'. -/
theorem Nonempty.image (f : α → β) {s : Set α} : s.Nonempty → (f '' s).Nonempty
  | ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩
#align set.nonempty.image Set.Nonempty.image

/- warning: set.nonempty.of_image -> Set.Nonempty.of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, (Set.Nonempty.{u2} β (Set.image.{u1, u2} α β f s)) -> (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, (Set.Nonempty.{u1} β (Set.image.{u2, u1} α β f s)) -> (Set.Nonempty.{u2} α s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.of_image Set.Nonempty.of_imageₓ'. -/
theorem Nonempty.of_image {f : α → β} {s : Set α} : (f '' s).Nonempty → s.Nonempty
  | ⟨y, x, hx, _⟩ => ⟨x, hx⟩
#align set.nonempty.of_image Set.Nonempty.of_image

/- warning: set.nonempty_image_iff -> Set.nonempty_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, Iff (Set.Nonempty.{u2} β (Set.image.{u1, u2} α β f s)) (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, Iff (Set.Nonempty.{u1} β (Set.image.{u2, u1} α β f s)) (Set.Nonempty.{u2} α s)
Case conversion may be inaccurate. Consider using '#align set.nonempty_image_iff Set.nonempty_image_iffₓ'. -/
@[simp]
theorem nonempty_image_iff {f : α → β} {s : Set α} : (f '' s).Nonempty ↔ s.Nonempty :=
  ⟨Nonempty.of_image, fun h => h.image f⟩
#align set.nonempty_image_iff Set.nonempty_image_iff

#print Set.Nonempty.preimage /-
theorem Nonempty.preimage {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : Surjective f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, mem_preimage.2 <| hx.symm ▸ hy⟩
#align set.nonempty.preimage Set.Nonempty.preimage
-/

instance (f : α → β) (s : Set α) [Nonempty s] : Nonempty (f '' s) :=
  (Set.Nonempty.image f nonempty_of_nonempty_subtype).to_subtype

/- warning: set.image_subset_iff -> Set.image_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f s) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {f : α -> β}, Iff (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f s) t) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.preimage.{u2, u1} α β f t))
Case conversion may be inaccurate. Consider using '#align set.image_subset_iff Set.image_subset_iffₓ'. -/
/-- image and preimage are a Galois connection -/
@[simp]
theorem image_subset_iff {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  ball_image_iff
#align set.image_subset_iff Set.image_subset_iff

#print Set.image_preimage_subset /-
theorem image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s :=
  image_subset_iff.2 Subset.rfl
#align set.image_preimage_subset Set.image_preimage_subset
-/

/- warning: set.subset_preimage_image -> Set.subset_preimage_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.preimage.{u1, u2} α β f (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.preimage.{u2, u1} α β f (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.subset_preimage_image Set.subset_preimage_imageₓ'. -/
theorem subset_preimage_image (f : α → β) (s : Set α) : s ⊆ f ⁻¹' (f '' s) := fun x =>
  mem_image_of_mem f
#align set.subset_preimage_image Set.subset_preimage_image

/- warning: set.preimage_image_eq -> Set.preimage_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} (s : Set.{u1} α), (Function.Injective.{succ u1, succ u2} α β f) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.image.{u1, u2} α β f s)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} (s : Set.{u2} α), (Function.Injective.{succ u2, succ u1} α β f) -> (Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β f (Set.image.{u2, u1} α β f s)) s)
Case conversion may be inaccurate. Consider using '#align set.preimage_image_eq Set.preimage_image_eqₓ'. -/
theorem preimage_image_eq {f : α → β} (s : Set α) (h : Injective f) : f ⁻¹' (f '' s) = s :=
  Subset.antisymm (fun x ⟨y, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)
#align set.preimage_image_eq Set.preimage_image_eq

#print Set.image_preimage_eq /-
theorem image_preimage_eq {f : α → β} (s : Set β) (h : Surjective f) : f '' (f ⁻¹' s) = s :=
  Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩
#align set.image_preimage_eq Set.image_preimage_eq
-/

#print Set.preimage_eq_preimage /-
theorem preimage_eq_preimage {f : β → α} (hf : Surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  Iff.intro (fun eq => by rw [← image_preimage_eq s hf, ← image_preimage_eq t hf, Eq]) fun eq =>
    Eq ▸ rfl
#align set.preimage_eq_preimage Set.preimage_eq_preimage
-/

/- warning: set.image_inter_preimage -> Set.image_inter_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f t))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.image.{u1, u2} α β f s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β f t))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.image.{u2, u1} α β f s) t)
Case conversion may be inaccurate. Consider using '#align set.image_inter_preimage Set.image_inter_preimageₓ'. -/
theorem image_inter_preimage (f : α → β) (s : Set α) (t : Set β) :
    f '' (s ∩ f ⁻¹' t) = f '' s ∩ t := by
  apply subset.antisymm
  ·
    calc
      f '' (s ∩ f ⁻¹' t) ⊆ f '' s ∩ f '' (f ⁻¹' t) := image_inter_subset _ _ _
      _ ⊆ f '' s ∩ t := inter_subset_inter_right _ (image_preimage_subset f t)
      
  · rintro _ ⟨⟨x, h', rfl⟩, h⟩
    exact ⟨x, ⟨h', h⟩, rfl⟩
#align set.image_inter_preimage Set.image_inter_preimage

/- warning: set.image_preimage_inter -> Set.image_preimage_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, u2} α β f t) s)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Set.preimage.{u2, u1} α β f t) s)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) t (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.image_preimage_inter Set.image_preimage_interₓ'. -/
theorem image_preimage_inter (f : α → β) (s : Set α) (t : Set β) :
    f '' (f ⁻¹' t ∩ s) = t ∩ f '' s := by simp only [inter_comm, image_inter_preimage]
#align set.image_preimage_inter Set.image_preimage_inter

/- warning: set.image_inter_nonempty_iff -> Set.image_inter_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (Set.Nonempty.{u2} β (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.image.{u1, u2} α β f s) t)) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (Set.Nonempty.{u1} β (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.image.{u2, u1} α β f s) t)) (Set.Nonempty.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align set.image_inter_nonempty_iff Set.image_inter_nonempty_iffₓ'. -/
@[simp]
theorem image_inter_nonempty_iff {f : α → β} {s : Set α} {t : Set β} :
    (f '' s ∩ t).Nonempty ↔ (s ∩ f ⁻¹' t).Nonempty := by
  rw [← image_inter_preimage, nonempty_image_iff]
#align set.image_inter_nonempty_iff Set.image_inter_nonempty_iff

/- warning: set.image_diff_preimage -> Set.image_diff_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Set.preimage.{u1, u2} α β f t))) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {t : Set.{u1} β}, Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s (Set.preimage.{u2, u1} α β f t))) (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) (Set.image.{u2, u1} α β f s) t)
Case conversion may be inaccurate. Consider using '#align set.image_diff_preimage Set.image_diff_preimageₓ'. -/
theorem image_diff_preimage {f : α → β} {s : Set α} {t : Set β} : f '' (s \ f ⁻¹' t) = f '' s \ t :=
  by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]
#align set.image_diff_preimage Set.image_diff_preimage

/- warning: set.compl_image -> Set.compl_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} (Set.{u1} α)) -> (Set.{u1} (Set.{u1} α))) (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) (Set.preimage.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} (Set.{u1} α)) -> (Set.{u1} (Set.{u1} α))) (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))) (Set.preimage.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))
Case conversion may be inaccurate. Consider using '#align set.compl_image Set.compl_imageₓ'. -/
theorem compl_image : image (compl : Set α → Set α) = preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl
#align set.compl_image Set.compl_image

/- warning: set.compl_image_set_of -> Set.compl_image_set_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : (Set.{u1} α) -> Prop}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => p s))) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => p (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))
but is expected to have type
  forall {α : Type.{u1}} {p : (Set.{u1} α) -> Prop}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Set.image.{u1, u1} (Set.{u1} α) (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => p s))) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => p (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)))
Case conversion may be inaccurate. Consider using '#align set.compl_image_set_of Set.compl_image_set_ofₓ'. -/
theorem compl_image_set_of {p : Set α → Prop} : compl '' { s | p s } = { s | p (sᶜ) } :=
  congr_fun compl_image p
#align set.compl_image_set_of Set.compl_image_set_of

/- warning: set.inter_preimage_subset -> Set.inter_preimage_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β) (f : α -> β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β f t)) (Set.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.image.{u1, u2} α β f s) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β) (f : α -> β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β f t)) (Set.preimage.{u2, u1} α β f (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.image.{u2, u1} α β f s) t))
Case conversion may be inaccurate. Consider using '#align set.inter_preimage_subset Set.inter_preimage_subsetₓ'. -/
theorem inter_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∩ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∩ t) := fun x h => ⟨mem_image_of_mem _ h.left, h.right⟩
#align set.inter_preimage_subset Set.inter_preimage_subset

/- warning: set.union_preimage_subset -> Set.union_preimage_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β) (f : α -> β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Set.preimage.{u1, u2} α β f t)) (Set.preimage.{u1, u2} α β f (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.image.{u1, u2} α β f s) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β) (f : α -> β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s (Set.preimage.{u2, u1} α β f t)) (Set.preimage.{u2, u1} α β f (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.image.{u2, u1} α β f s) t))
Case conversion may be inaccurate. Consider using '#align set.union_preimage_subset Set.union_preimage_subsetₓ'. -/
theorem union_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∪ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∪ t) := fun x h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r
#align set.union_preimage_subset Set.union_preimage_subset

/- warning: set.subset_image_union -> Set.subset_image_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) (t : Set.{u2} β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Set.preimage.{u1, u2} α β f t))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.image.{u1, u2} α β f s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) (t : Set.{u1} β), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s (Set.preimage.{u2, u1} α β f t))) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.image.{u2, u1} α β f s) t)
Case conversion may be inaccurate. Consider using '#align set.subset_image_union Set.subset_image_unionₓ'. -/
theorem subset_image_union (f : α → β) (s : Set α) (t : Set β) : f '' (s ∪ f ⁻¹' t) ⊆ f '' s ∪ t :=
  image_subset_iff.2 (union_preimage_subset _ _ _)
#align set.subset_image_union Set.subset_image_union

/- warning: set.preimage_subset_iff -> Set.preimage_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {A : Set.{u1} α} {B : Set.{u2} β} {f : α -> β}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.preimage.{u1, u2} α β f B) A) (forall (a : α), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f a) B) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a A))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {A : Set.{u2} α} {B : Set.{u1} β} {f : α -> β}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.preimage.{u2, u1} α β f B) A) (forall (a : α), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f a) B) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a A))
Case conversion may be inaccurate. Consider using '#align set.preimage_subset_iff Set.preimage_subset_iffₓ'. -/
theorem preimage_subset_iff {A : Set α} {B : Set β} {f : α → β} :
    f ⁻¹' B ⊆ A ↔ ∀ a : α, f a ∈ B → a ∈ A :=
  Iff.rfl
#align set.preimage_subset_iff Set.preimage_subset_iff

/- warning: set.image_eq_image -> Set.image_eq_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Iff (Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)) (Eq.{succ u1} (Set.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u2} α} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Iff (Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)) (Eq.{succ u2} (Set.{u2} α) s t))
Case conversion may be inaccurate. Consider using '#align set.image_eq_image Set.image_eq_imageₓ'. -/
theorem image_eq_image {f : α → β} (hf : Injective f) : f '' s = f '' t ↔ s = t :=
  Iff.symm <|
    Iff.intro (fun eq => Eq ▸ rfl) fun eq => by
      rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, Eq]
#align set.image_eq_image Set.image_eq_image

/- warning: set.image_subset_image_iff -> Set.image_subset_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u2} α} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Iff (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t))
Case conversion may be inaccurate. Consider using '#align set.image_subset_image_iff Set.image_subset_image_iffₓ'. -/
theorem image_subset_image_iff {f : α → β} (hf : Injective f) : f '' s ⊆ f '' t ↔ s ⊆ t :=
  by
  refine' Iff.symm <| Iff.intro (image_subset f) fun h => _
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf]
  exact preimage_mono h
#align set.image_subset_image_iff Set.image_subset_image_iff

/- warning: set.prod_quotient_preimage_eq_image -> Set.prod_quotient_preimage_eq_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [s : Setoid.{succ u1} α] (g : (Quotient.{succ u1} α s) -> β) {h : α -> β}, (Eq.{max (succ u1) (succ u2)} (α -> β) h (Function.comp.{succ u1, succ u1, succ u2} α (Quotient.{succ u1} α s) β g (Quotient.mk''.{succ u1} α s))) -> (forall (r : Set.{u2} (Prod.{u2, u2} β β)), Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} (Quotient.{succ u1} α s) (Quotient.{succ u1} α s))) (setOf.{u1} (Prod.{u1, u1} (Quotient.{succ u1} α s) (Quotient.{succ u1} α s)) (fun (x : Prod.{u1, u1} (Quotient.{succ u1} α s) (Quotient.{succ u1} α s)) => Membership.Mem.{u2, u2} (Prod.{u2, u2} β β) (Set.{u2} (Prod.{u2, u2} β β)) (Set.hasMem.{u2} (Prod.{u2, u2} β β)) (Prod.mk.{u2, u2} β β (g (Prod.fst.{u1, u1} (Quotient.{succ u1} α s) (Quotient.{succ u1} α s) x)) (g (Prod.snd.{u1, u1} (Quotient.{succ u1} α s) (Quotient.{succ u1} α s) x))) r)) (Set.image.{u1, u1} (Prod.{u1, u1} α α) (Prod.{u1, u1} (Quotient.{succ u1} α s) (Quotient.{succ u1} α s)) (fun (a : Prod.{u1, u1} α α) => Prod.mk.{u1, u1} (Quotient.{succ u1} α s) (Quotient.{succ u1} α s) (Quotient.mk''.{succ u1} α s (Prod.fst.{u1, u1} α α a)) (Quotient.mk''.{succ u1} α s (Prod.snd.{u1, u1} α α a))) (Set.preimage.{u1, u2} (Prod.{u1, u1} α α) (Prod.{u2, u2} β β) (fun (a : Prod.{u1, u1} α α) => Prod.mk.{u2, u2} β β (h (Prod.fst.{u1, u1} α α a)) (h (Prod.snd.{u1, u1} α α a))) r)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [s : Setoid.{succ u2} α] (g : (Quotient.{succ u2} α s) -> β) {h : α -> β}, (Eq.{max (succ u2) (succ u1)} (α -> β) h (Function.comp.{succ u2, succ u2, succ u1} α (Quotient.{succ u2} α s) β g (Quotient.mk''.{succ u2} α s))) -> (forall (r : Set.{u1} (Prod.{u1, u1} β β)), Eq.{succ u2} (Set.{u2} (Prod.{u2, u2} (Quotient.{succ u2} α s) (Quotient.{succ u2} α s))) (setOf.{u2} (Prod.{u2, u2} (Quotient.{succ u2} α s) (Quotient.{succ u2} α s)) (fun (x : Prod.{u2, u2} (Quotient.{succ u2} α s) (Quotient.{succ u2} α s)) => Membership.mem.{u1, u1} (Prod.{u1, u1} β β) (Set.{u1} (Prod.{u1, u1} β β)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} β β)) (Prod.mk.{u1, u1} β β (g (Prod.fst.{u2, u2} (Quotient.{succ u2} α s) (Quotient.{succ u2} α s) x)) (g (Prod.snd.{u2, u2} (Quotient.{succ u2} α s) (Quotient.{succ u2} α s) x))) r)) (Set.image.{u2, u2} (Prod.{u2, u2} α α) (Prod.{u2, u2} (Quotient.{succ u2} α s) (Quotient.{succ u2} α s)) (fun (a : Prod.{u2, u2} α α) => Prod.mk.{u2, u2} (Quotient.{succ u2} α s) (Quotient.{succ u2} α s) (Quotient.mk.{succ u2} α s (Prod.fst.{u2, u2} α α a)) (Quotient.mk.{succ u2} α s (Prod.snd.{u2, u2} α α a))) (Set.preimage.{u2, u1} (Prod.{u2, u2} α α) (Prod.{u1, u1} β β) (fun (a : Prod.{u2, u2} α α) => Prod.mk.{u1, u1} β β (h (Prod.fst.{u2, u2} α α a)) (h (Prod.snd.{u2, u2} α α a))) r)))
Case conversion may be inaccurate. Consider using '#align set.prod_quotient_preimage_eq_image Set.prod_quotient_preimage_eq_imageₓ'. -/
theorem prod_quotient_preimage_eq_image [s : Setoid α] (g : Quotient s → β) {h : α → β}
    (Hh : h = g ∘ Quotient.mk'') (r : Set (β × β)) :
    { x : Quotient s × Quotient s | (g x.1, g x.2) ∈ r } =
      (fun a : α × α => (⟦a.1⟧, ⟦a.2⟧)) '' ((fun a : α × α => (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quotient.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) ∈ r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩
#align set.prod_quotient_preimage_eq_image Set.prod_quotient_preimage_eq_image

/- warning: set.exists_image_iff -> Set.exists_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (x : Set.{u1} α) (P : β -> Prop), Iff (Exists.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β f x)) (fun (a : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β f x)) => P ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β f x)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β f x)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β f x)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β f x)) β (coeSubtype.{succ u2} β (fun (x_1 : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x_1 (Set.image.{u1, u2} α β f x)))))) a))) (Exists.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) x) (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) x) => P (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) x) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) x) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) x) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) x) α (coeSubtype.{succ u1} α (fun (x_1 : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x_1 x))))) a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (x : Set.{u2} α) (P : β -> Prop), Iff (Exists.{succ u1} (Set.Elem.{u1} β (Set.image.{u2, u1} α β f x)) (fun (a : Set.Elem.{u1} β (Set.image.{u2, u1} α β f x)) => P (Subtype.val.{succ u1} β (fun (x_1 : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x_1 (Set.image.{u2, u1} α β f x)) a))) (Exists.{succ u2} (Set.Elem.{u2} α x) (fun (a : Set.Elem.{u2} α x) => P (f (Subtype.val.{succ u2} α (fun (x_1 : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x_1 x) a))))
Case conversion may be inaccurate. Consider using '#align set.exists_image_iff Set.exists_image_iffₓ'. -/
theorem exists_image_iff (f : α → β) (x : Set α) (P : β → Prop) :
    (∃ a : f '' x, P a) ↔ ∃ a : x, P (f a) :=
  ⟨fun ⟨a, h⟩ => ⟨⟨_, a.Prop.some_spec.1⟩, a.Prop.some_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨⟨_, _, a.Prop, rfl⟩, h⟩⟩
#align set.exists_image_iff Set.exists_image_iff

#print Set.imageFactorization /-
/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f '' s`. -/
def imageFactorization (f : α → β) (s : Set α) : s → f '' s := fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩
#align set.image_factorization Set.imageFactorization
-/

/- warning: set.image_factorization_eq -> Set.imageFactorization_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, Eq.{max (succ u1) (succ u2)} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Function.comp.{succ u1, succ u2, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.image.{u1, u2} α β f s))) β (Subtype.val.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.image.{u1, u2} α β f s))) (Set.imageFactorization.{u1, u2} α β f s)) (Function.comp.{succ u1, succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α β f (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u2} α s) -> β) (Function.comp.{succ u2, succ u1, succ u1} (Set.Elem.{u2} α s) (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.image.{u2, u1} α β f s))) β (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.image.{u2, u1} α β f s))) (Set.imageFactorization.{u2, u1} α β f s)) (Function.comp.{succ u2, succ u2, succ u1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) α β f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)))
Case conversion may be inaccurate. Consider using '#align set.image_factorization_eq Set.imageFactorization_eqₓ'. -/
theorem imageFactorization_eq {f : α → β} {s : Set α} :
    Subtype.val ∘ imageFactorization f s = f ∘ Subtype.val :=
  funext fun p => rfl
#align set.image_factorization_eq Set.imageFactorization_eq

/- warning: set.surjective_onto_image -> Set.surjective_onto_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α}, Function.Surjective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β f s)) (Set.imageFactorization.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α}, Function.Surjective.{succ u2, succ u1} (Set.Elem.{u2} α s) (Set.Elem.{u1} β (Set.image.{u2, u1} α β f s)) (Set.imageFactorization.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align set.surjective_onto_image Set.surjective_onto_imageₓ'. -/
theorem surjective_onto_image {f : α → β} {s : Set α} : Surjective (imageFactorization f s) :=
  fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩
#align set.surjective_onto_image Set.surjective_onto_image

#print Set.image_perm /-
/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a ≠ a } ⊆ s) : σ '' s = s :=
  by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine' ⟨_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
  · refine' iff_of_true ⟨σ.symm i, hs fun h => hi _, σ.apply_symm_apply _⟩ (hs hi)
    convert congr_arg σ h <;> exact (σ.apply_symm_apply _).symm
#align set.image_perm Set.image_perm
-/

end Image

/-! ### Lemmas about range of a function. -/


section Range

variable {f : ι → α} {s t : Set α}

#print Set.range /-
/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : Set α :=
  { x | ∃ y, f y = x }
#align set.range Set.range
-/

/- warning: set.mem_range -> Set.mem_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.range.{u1, u2} α ι f)) (Exists.{u2} ι (fun (y : ι) => Eq.{succ u1} α (f y) x))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {x : α}, Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.range.{u2, u1} α ι f)) (Exists.{u1} ι (fun (y : ι) => Eq.{succ u2} α (f y) x))
Case conversion may be inaccurate. Consider using '#align set.mem_range Set.mem_rangeₓ'. -/
@[simp]
theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl
#align set.mem_range Set.mem_range

/- warning: set.mem_range_self -> Set.mem_range_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} (i : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f i) (Set.range.{u1, u2} α ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} (i : ι), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (f i) (Set.range.{u2, u1} α ι f)
Case conversion may be inaccurate. Consider using '#align set.mem_range_self Set.mem_range_selfₓ'. -/
@[simp]
theorem mem_range_self (i : ι) : f i ∈ range f :=
  ⟨i, rfl⟩
#align set.mem_range_self Set.mem_range_self

/- warning: set.forall_range_iff -> Set.forall_range_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {p : α -> Prop}, Iff (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.range.{u1, u2} α ι f)) -> (p a)) (forall (i : ι), p (f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {p : α -> Prop}, Iff (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.range.{u2, u1} α ι f)) -> (p a)) (forall (i : ι), p (f i))
Case conversion may be inaccurate. Consider using '#align set.forall_range_iff Set.forall_range_iffₓ'. -/
theorem forall_range_iff {p : α → Prop} : (∀ a ∈ range f, p a) ↔ ∀ i, p (f i) := by simp
#align set.forall_range_iff Set.forall_range_iff

/- warning: set.forall_subtype_range_iff -> Set.forall_subtype_range_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {p : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.range.{u1, u2} α ι f)) -> Prop}, Iff (forall (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.range.{u1, u2} α ι f)), p a) (forall (i : ι), p (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.range.{u1, u2} α ι f)) (f i) (Set.mem_range_self.{u1, u2} α ι f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {p : (Set.Elem.{u2} α (Set.range.{u2, u1} α ι f)) -> Prop}, Iff (forall (a : Set.Elem.{u2} α (Set.range.{u2, u1} α ι f)), p a) (forall (i : ι), p (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.range.{u2, u1} α ι f)) (f i) (Set.mem_range_self.{u1, u2} α ι f i)))
Case conversion may be inaccurate. Consider using '#align set.forall_subtype_range_iff Set.forall_subtype_range_iffₓ'. -/
theorem forall_subtype_range_iff {p : range f → Prop} :
    (∀ a : range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun H i => H _, fun H ⟨y, i, hi⟩ => by
    subst hi
    apply H⟩
#align set.forall_subtype_range_iff Set.forall_subtype_range_iff

/- warning: set.exists_range_iff -> Set.exists_range_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {p : α -> Prop}, Iff (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.range.{u1, u2} α ι f)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.range.{u1, u2} α ι f)) => p a))) (Exists.{u2} ι (fun (i : ι) => p (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {p : α -> Prop}, Iff (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.range.{u2, u1} α ι f)) (p a))) (Exists.{u1} ι (fun (i : ι) => p (f i)))
Case conversion may be inaccurate. Consider using '#align set.exists_range_iff Set.exists_range_iffₓ'. -/
theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ ∃ i, p (f i) := by simp
#align set.exists_range_iff Set.exists_range_iff

/- warning: set.exists_range_iff' -> Set.exists_range_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {p : α -> Prop}, Iff (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.range.{u1, u2} α ι f)) (p a))) (Exists.{u2} ι (fun (i : ι) => p (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {p : α -> Prop}, Iff (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.range.{u2, u1} α ι f)) (p a))) (Exists.{u1} ι (fun (i : ι) => p (f i)))
Case conversion may be inaccurate. Consider using '#align set.exists_range_iff' Set.exists_range_iff'ₓ'. -/
theorem exists_range_iff' {p : α → Prop} : (∃ a, a ∈ range f ∧ p a) ↔ ∃ i, p (f i) := by
  simpa only [exists_prop] using exists_range_iff
#align set.exists_range_iff' Set.exists_range_iff'

/- warning: set.exists_subtype_range_iff -> Set.exists_subtype_range_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {p : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.range.{u1, u2} α ι f)) -> Prop}, Iff (Exists.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.range.{u1, u2} α ι f)) (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.range.{u1, u2} α ι f)) => p a)) (Exists.{u2} ι (fun (i : ι) => p (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.range.{u1, u2} α ι f)) (f i) (Set.mem_range_self.{u1, u2} α ι f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {p : (Set.Elem.{u2} α (Set.range.{u2, u1} α ι f)) -> Prop}, Iff (Exists.{succ u2} (Set.Elem.{u2} α (Set.range.{u2, u1} α ι f)) (fun (a : Set.Elem.{u2} α (Set.range.{u2, u1} α ι f)) => p a)) (Exists.{u1} ι (fun (i : ι) => p (Subtype.mk.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.range.{u2, u1} α ι f)) (f i) (Set.mem_range_self.{u1, u2} α ι f i))))
Case conversion may be inaccurate. Consider using '#align set.exists_subtype_range_iff Set.exists_subtype_range_iffₓ'. -/
theorem exists_subtype_range_iff {p : range f → Prop} :
    (∃ a : range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun ⟨⟨a, i, hi⟩, ha⟩ => by
    subst a
    exact ⟨i, ha⟩, fun ⟨i, hi⟩ => ⟨_, hi⟩⟩
#align set.exists_subtype_range_iff Set.exists_subtype_range_iff

/- warning: set.range_iff_surjective -> Set.range_iff_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, u2} α ι f) (Set.univ.{u1} α)) (Function.Surjective.{u2, succ u1} ι α f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α}, Iff (Eq.{succ u2} (Set.{u2} α) (Set.range.{u2, u1} α ι f) (Set.univ.{u2} α)) (Function.Surjective.{u1, succ u2} ι α f)
Case conversion may be inaccurate. Consider using '#align set.range_iff_surjective Set.range_iff_surjectiveₓ'. -/
theorem range_iff_surjective : range f = univ ↔ Surjective f :=
  eq_univ_iff_forall
#align set.range_iff_surjective Set.range_iff_surjective

/- warning: function.surjective.range_eq -> Function.Surjective.range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α}, (Function.Surjective.{u2, succ u1} ι α f) -> (Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, u2} α ι f) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α}, (Function.Surjective.{u1, succ u2} ι α f) -> (Eq.{succ u2} (Set.{u2} α) (Set.range.{u2, u1} α ι f) (Set.univ.{u2} α))
Case conversion may be inaccurate. Consider using '#align function.surjective.range_eq Function.Surjective.range_eqₓ'. -/
alias range_iff_surjective ↔ _ _root_.function.surjective.range_eq
#align function.surjective.range_eq Function.Surjective.range_eq

#print Set.image_univ /-
@[simp]
theorem image_univ {f : α → β} : f '' univ = range f :=
  by
  ext
  simp [image, range]
#align set.image_univ Set.image_univ
-/

/- warning: set.image_subset_range -> Set.image_subset_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β f s) (Set.range.{u2, succ u1} β α f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β f s) (Set.range.{u1, succ u2} β α f)
Case conversion may be inaccurate. Consider using '#align set.image_subset_range Set.image_subset_rangeₓ'. -/
theorem image_subset_range (f : α → β) (s) : f '' s ⊆ range f := by
  rw [← image_univ] <;> exact image_subset _ (subset_univ _)
#align set.image_subset_range Set.image_subset_range

/- warning: set.mem_range_of_mem_image -> Set.mem_range_of_mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α) {x : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.image.{u1, u2} α β f s)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α) {x : β}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.image.{u2, u1} α β f s)) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align set.mem_range_of_mem_image Set.mem_range_of_mem_imageₓ'. -/
theorem mem_range_of_mem_image (f : α → β) (s) {x : β} (h : x ∈ f '' s) : x ∈ range f :=
  image_subset_range f s h
#align set.mem_range_of_mem_image Set.mem_range_of_mem_image

#print Nat.mem_range_succ /-
theorem Nat.mem_range_succ (i : ℕ) : i ∈ range Nat.succ ↔ 0 < i :=
  ⟨by
    rintro ⟨n, rfl⟩
    exact Nat.succ_pos n, fun h => ⟨_, Nat.succ_pred_eq_of_pos h⟩⟩
#align nat.mem_range_succ Nat.mem_range_succ
-/

#print Set.Nonempty.preimage' /-
theorem Nonempty.preimage' {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : s ⊆ Set.range f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, Set.mem_preimage.2 <| hx.symm ▸ hy⟩
#align set.nonempty.preimage' Set.Nonempty.preimage'
-/

/- warning: set.range_comp -> Set.range_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} (g : α -> β) (f : ι -> α), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, u3} β ι (Function.comp.{u3, succ u1, succ u2} ι α β g f)) (Set.image.{u1, u2} α β g (Set.range.{u1, u3} α ι f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {ι : Sort.{u2}} (g : α -> β) (f : ι -> α), Eq.{succ u3} (Set.{u3} β) (Set.range.{u3, u2} β ι (Function.comp.{u2, succ u1, succ u3} ι α β g f)) (Set.image.{u1, u3} α β g (Set.range.{u1, u2} α ι f))
Case conversion may be inaccurate. Consider using '#align set.range_comp Set.range_compₓ'. -/
theorem range_comp (g : α → β) (f : ι → α) : range (g ∘ f) = g '' range f :=
  Subset.antisymm (forall_range_iff.mpr fun i => mem_image_of_mem g (mem_range_self _))
    (ball_image_iff.mpr <| forall_range_iff.mpr mem_range_self)
#align set.range_comp Set.range_comp

/- warning: set.range_subset_iff -> Set.range_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {s : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.range.{u1, u2} α ι f) s) (forall (y : ι), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f y) s)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {s : Set.{u2} α}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.range.{u2, u1} α ι f) s) (forall (y : ι), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (f y) s)
Case conversion may be inaccurate. Consider using '#align set.range_subset_iff Set.range_subset_iffₓ'. -/
theorem range_subset_iff : range f ⊆ s ↔ ∀ y, f y ∈ s :=
  forall_range_iff
#align set.range_subset_iff Set.range_subset_iff

#print Set.range_eq_iff /-
theorem range_eq_iff (f : α → β) (s : Set β) :
    range f = s ↔ (∀ a, f a ∈ s) ∧ ∀ b ∈ s, ∃ a, f a = b :=
  by
  rw [← range_subset_iff]
  exact le_antisymm_iff
#align set.range_eq_iff Set.range_eq_iff
-/

/- warning: set.range_comp_subset_range -> Set.range_comp_subset_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : β -> γ), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.range.{u3, succ u1} γ α (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Set.range.{u3, succ u2} γ β g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (f : α -> β) (g : β -> γ), HasSubset.Subset.{u3} (Set.{u3} γ) (Set.instHasSubsetSet.{u3} γ) (Set.range.{u3, succ u2} γ α (Function.comp.{succ u2, succ u1, succ u3} α β γ g f)) (Set.range.{u3, succ u1} γ β g)
Case conversion may be inaccurate. Consider using '#align set.range_comp_subset_range Set.range_comp_subset_rangeₓ'. -/
theorem range_comp_subset_range (f : α → β) (g : β → γ) : range (g ∘ f) ⊆ range g := by
  rw [range_comp] <;> apply image_subset_range
#align set.range_comp_subset_range Set.range_comp_subset_range

/- warning: set.range_nonempty_iff_nonempty -> Set.range_nonempty_iff_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α}, Iff (Set.Nonempty.{u1} α (Set.range.{u1, u2} α ι f)) (Nonempty.{u2} ι)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α}, Iff (Set.Nonempty.{u2} α (Set.range.{u2, u1} α ι f)) (Nonempty.{u1} ι)
Case conversion may be inaccurate. Consider using '#align set.range_nonempty_iff_nonempty Set.range_nonempty_iff_nonemptyₓ'. -/
theorem range_nonempty_iff_nonempty : (range f).Nonempty ↔ Nonempty ι :=
  ⟨fun ⟨y, x, hxy⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩
#align set.range_nonempty_iff_nonempty Set.range_nonempty_iff_nonempty

#print Set.range_nonempty /-
theorem range_nonempty [h : Nonempty ι] (f : ι → α) : (range f).Nonempty :=
  range_nonempty_iff_nonempty.2 h
#align set.range_nonempty Set.range_nonempty
-/

/- warning: set.range_eq_empty_iff -> Set.range_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, u2} α ι f) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (IsEmpty.{u2} ι)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α}, Iff (Eq.{succ u2} (Set.{u2} α) (Set.range.{u2, u1} α ι f) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (IsEmpty.{u1} ι)
Case conversion may be inaccurate. Consider using '#align set.range_eq_empty_iff Set.range_eq_empty_iffₓ'. -/
@[simp]
theorem range_eq_empty_iff {f : ι → α} : range f = ∅ ↔ IsEmpty ι := by
  rw [← not_nonempty_iff, ← range_nonempty_iff_nonempty, not_nonempty_iff_eq_empty]
#align set.range_eq_empty_iff Set.range_eq_empty_iff

#print Set.range_eq_empty /-
theorem range_eq_empty [IsEmpty ι] (f : ι → α) : range f = ∅ :=
  range_eq_empty_iff.2 ‹_›
#align set.range_eq_empty Set.range_eq_empty
-/

instance [Nonempty ι] (f : ι → α) : Nonempty (range f) :=
  (range_nonempty f).to_subtype

/- warning: set.image_union_image_compl_eq_range -> Set.image_union_image_compl_eq_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} (f : α -> β), Eq.{succ u2} (Set.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Set.range.{u2, succ u1} β α f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} (f : α -> β), Eq.{succ u2} (Set.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Set.range.{u2, succ u1} β α f)
Case conversion may be inaccurate. Consider using '#align set.image_union_image_compl_eq_range Set.image_union_image_compl_eq_rangeₓ'. -/
@[simp]
theorem image_union_image_compl_eq_range (f : α → β) : f '' s ∪ f '' sᶜ = range f := by
  rw [← image_union, ← image_univ, ← union_compl_self]
#align set.image_union_image_compl_eq_range Set.image_union_image_compl_eq_range

/- warning: set.insert_image_compl_eq_range -> Set.insert_image_compl_eq_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (x : α), Eq.{succ u2} (Set.{u2} β) (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) (f x) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))) (Set.range.{u2, succ u1} β α f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (x : α), Eq.{succ u2} (Set.{u2} β) (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) (f x) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))) (Set.range.{u2, succ u1} β α f)
Case conversion may be inaccurate. Consider using '#align set.insert_image_compl_eq_range Set.insert_image_compl_eq_rangeₓ'. -/
theorem insert_image_compl_eq_range (f : α → β) (x : α) : insert (f x) (f '' {x}ᶜ) = range f :=
  by
  ext y; rw [mem_range, mem_insert_iff, mem_image]
  constructor
  · rintro (h | ⟨x', hx', h⟩)
    · exact ⟨x, h.symm⟩
    · exact ⟨x', h⟩
  · rintro ⟨x', h⟩
    by_cases hx : x' = x
    · left
      rw [← h, hx]
    · right
      refine' ⟨_, _, h⟩
      rw [mem_compl_singleton_iff]
      exact hx
#align set.insert_image_compl_eq_range Set.insert_image_compl_eq_range

/- warning: set.image_preimage_eq_inter_range -> Set.image_preimage_eq_inter_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.preimage.{u1, u2} α β f t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.preimage.{u1, u2} α β f t)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) t (Set.range.{u2, succ u1} β α f))
Case conversion may be inaccurate. Consider using '#align set.image_preimage_eq_inter_range Set.image_preimage_eq_inter_rangeₓ'. -/
theorem image_preimage_eq_inter_range {f : α → β} {t : Set β} : f '' (f ⁻¹' t) = t ∩ range f :=
  ext fun x =>
    ⟨fun ⟨x, hx, HEq⟩ => HEq ▸ ⟨hx, mem_range_self _⟩, fun ⟨hx, ⟨y, h_eq⟩⟩ =>
      h_eq ▸ mem_image_of_mem f <| show y ∈ f ⁻¹' t by simp [preimage, h_eq, hx]⟩
#align set.image_preimage_eq_inter_range Set.image_preimage_eq_inter_range

#print Set.image_preimage_eq_of_subset /-
theorem image_preimage_eq_of_subset {f : α → β} {s : Set β} (hs : s ⊆ range f) :
    f '' (f ⁻¹' s) = s := by rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]
#align set.image_preimage_eq_of_subset Set.image_preimage_eq_of_subset
-/

#print Set.image_preimage_eq_iff /-
theorem image_preimage_eq_iff {f : α → β} {s : Set β} : f '' (f ⁻¹' s) = s ↔ s ⊆ range f :=
  ⟨by
    intro h
    rw [← h]
    apply image_subset_range, image_preimage_eq_of_subset⟩
#align set.image_preimage_eq_iff Set.image_preimage_eq_iff
-/

#print Set.subset_range_iff_exists_image_eq /-
theorem subset_range_iff_exists_image_eq {f : α → β} {s : Set β} : s ⊆ range f ↔ ∃ t, f '' t = s :=
  ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨t, ht⟩ => ht ▸ image_subset_range _ _⟩
#align set.subset_range_iff_exists_image_eq Set.subset_range_iff_exists_image_eq
-/

#print Set.exists_subset_range_and_iff /-
@[simp]
theorem exists_subset_range_and_iff {f : α → β} {p : Set β → Prop} :
    (∃ s, s ⊆ range f ∧ p s) ↔ ∃ s, p (f '' s) :=
  ⟨fun ⟨s, hsf, hps⟩ => ⟨f ⁻¹' s, (image_preimage_eq_of_subset hsf).symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨f '' s, image_subset_range _ _, hs⟩⟩
#align set.exists_subset_range_and_iff Set.exists_subset_range_and_iff
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (s «expr ⊆ » range[set.range] f) -/
#print Set.exists_subset_range_iff /-
theorem exists_subset_range_iff {f : α → β} {p : Set β → Prop} :
    (∃ (s : _)(_ : s ⊆ range f), p s) ↔ ∃ s, p (f '' s) := by
  simp only [exists_prop, exists_subset_range_and_iff]
#align set.exists_subset_range_iff Set.exists_subset_range_iff
-/

#print Set.range_image /-
theorem range_image (f : α → β) : range (image f) = 𝒫 range f :=
  ext fun s => subset_range_iff_exists_image_eq.symm
#align set.range_image Set.range_image
-/

/- warning: set.preimage_subset_preimage_iff -> Set.preimage_subset_preimage_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u1} α} {f : β -> α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.range.{u1, succ u2} α β f)) -> (Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.preimage.{u2, u1} β α f s) (Set.preimage.{u2, u1} β α f t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u2} α} {f : β -> α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.range.{u2, succ u1} α β f)) -> (Iff (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.preimage.{u1, u2} β α f s) (Set.preimage.{u1, u2} β α f t)) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t))
Case conversion may be inaccurate. Consider using '#align set.preimage_subset_preimage_iff Set.preimage_subset_preimage_iffₓ'. -/
theorem preimage_subset_preimage_iff {s t : Set α} {f : β → α} (hs : s ⊆ range f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
  intro h x; apply h
#align set.preimage_subset_preimage_iff Set.preimage_subset_preimage_iff

/- warning: set.preimage_eq_preimage' -> Set.preimage_eq_preimage' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u1} α} {f : β -> α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.range.{u1, succ u2} α β f)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (Set.range.{u1, succ u2} α β f)) -> (Iff (Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u1} β α f s) (Set.preimage.{u2, u1} β α f t)) (Eq.{succ u1} (Set.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u2} α} {f : β -> α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.range.{u2, succ u1} α β f)) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) t (Set.range.{u2, succ u1} α β f)) -> (Iff (Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, u2} β α f s) (Set.preimage.{u1, u2} β α f t)) (Eq.{succ u2} (Set.{u2} α) s t))
Case conversion may be inaccurate. Consider using '#align set.preimage_eq_preimage' Set.preimage_eq_preimage'ₓ'. -/
theorem preimage_eq_preimage' {s t : Set α} {f : β → α} (hs : s ⊆ range f) (ht : t ⊆ range f) :
    f ⁻¹' s = f ⁻¹' t ↔ s = t := by
  constructor
  · intro h
    apply subset.antisymm
    rw [← preimage_subset_preimage_iff hs, h]
    rw [← preimage_subset_preimage_iff ht, h]
  rintro rfl; rfl
#align set.preimage_eq_preimage' Set.preimage_eq_preimage'

/- warning: set.preimage_inter_range -> Set.preimage_inter_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s (Set.range.{u2, succ u1} β α f))) (Set.preimage.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s (Set.range.{u2, succ u1} β α f))) (Set.preimage.{u1, u2} α β f s)
Case conversion may be inaccurate. Consider using '#align set.preimage_inter_range Set.preimage_inter_rangeₓ'. -/
@[simp]
theorem preimage_inter_range {f : α → β} {s : Set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
  Set.ext fun x => and_iff_left ⟨x, rfl⟩
#align set.preimage_inter_range Set.preimage_inter_range

/- warning: set.preimage_range_inter -> Set.preimage_range_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.range.{u2, succ u1} β α f) s)) (Set.preimage.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (Set.range.{u2, succ u1} β α f) s)) (Set.preimage.{u1, u2} α β f s)
Case conversion may be inaccurate. Consider using '#align set.preimage_range_inter Set.preimage_range_interₓ'. -/
@[simp]
theorem preimage_range_inter {f : α → β} {s : Set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s := by
  rw [inter_comm, preimage_inter_range]
#align set.preimage_range_inter Set.preimage_range_inter

#print Set.preimage_image_preimage /-
theorem preimage_image_preimage {f : α → β} {s : Set β} : f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s := by
  rw [image_preimage_eq_inter_range, preimage_inter_range]
#align set.preimage_image_preimage Set.preimage_image_preimage
-/

#print Set.range_id /-
@[simp]
theorem range_id : range (@id α) = univ :=
  range_iff_surjective.2 surjective_id
#align set.range_id Set.range_id
-/

#print Set.range_id' /-
@[simp]
theorem range_id' : (range fun x : α => x) = univ :=
  range_id
#align set.range_id' Set.range_id'
-/

#print Prod.range_fst /-
@[simp]
theorem Prod.range_fst [Nonempty β] : range (Prod.fst : α × β → α) = univ :=
  Prod.fst_surjective.range_eq
#align prod.range_fst Prod.range_fst
-/

/- warning: prod.range_snd -> Prod.range_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Nonempty.{succ u1} α], Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, max (succ u1) (succ u2)} β (Prod.{u1, u2} α β) (Prod.snd.{u1, u2} α β)) (Set.univ.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Nonempty.{succ u2} α], Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, max (succ u2) (succ u1)} β (Prod.{u2, u1} α β) (Prod.snd.{u2, u1} α β)) (Set.univ.{u1} β)
Case conversion may be inaccurate. Consider using '#align prod.range_snd Prod.range_sndₓ'. -/
@[simp]
theorem Prod.range_snd [Nonempty α] : range (Prod.snd : α × β → β) = univ :=
  Prod.snd_surjective.range_eq
#align prod.range_snd Prod.range_snd

/- warning: set.range_eval -> Set.range_eval is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Nonempty.{succ u2} (α i)] (i : ι), Eq.{succ u2} (Set.{u2} (α i)) (Set.range.{u2, max (succ u1) (succ u2)} (α i) (forall (x : ι), α x) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i)) (Set.univ.{u2} (α i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Nonempty.{succ u1} (α i)] (i : ι), Eq.{succ u1} (Set.{u1} (α i)) (Set.range.{u1, max (succ u2) (succ u1)} (α i) (forall (x : ι), α x) (Function.eval.{succ u2, succ u1} ι (fun (i : ι) => α i) i)) (Set.univ.{u1} (α i))
Case conversion may be inaccurate. Consider using '#align set.range_eval Set.range_evalₓ'. -/
@[simp]
theorem range_eval {ι : Type _} {α : ι → Sort _} [∀ i, Nonempty (α i)] (i : ι) :
    range (eval i : (∀ i, α i) → α i) = univ :=
  (surjective_eval i).range_eq
#align set.range_eval Set.range_eval

/- warning: set.is_compl_range_inl_range_inr -> Set.isCompl_range_inl_range_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, IsCompl.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (SemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Lattice.toSemilatticeInf.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (GeneralizedCoheytingAlgebra.toLattice.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.booleanAlgebra.{max u1 u2} (Sum.{u1, u2} α β))))))) (BooleanAlgebra.toBoundedOrder.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.booleanAlgebra.{max u1 u2} (Sum.{u1, u2} α β))) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β)) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, IsCompl.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (SemilatticeInf.toPartialOrder.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Lattice.toSemilatticeInf.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (BiheytingAlgebra.toCoheytingAlgebra.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (BooleanAlgebra.toBiheytingAlgebra.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instBooleanAlgebraSet.{max u2 u1} (Sum.{u2, u1} α β)))))))) (BooleanAlgebra.toBoundedOrder.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instBooleanAlgebraSet.{max u2 u1} (Sum.{u2, u1} α β))) (Set.range.{max u2 u1, succ u2} (Sum.{u2, u1} α β) α (Sum.inl.{u2, u1} α β)) (Set.range.{max u2 u1, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align set.is_compl_range_inl_range_inr Set.isCompl_range_inl_range_inrₓ'. -/
theorem isCompl_range_inl_range_inr : IsCompl (range <| @Sum.inl α β) (range Sum.inr) :=
  IsCompl.of_le
    (by
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, _⟩⟩
      cc)
    (by rintro (x | y) - <;> [left, right] <;> exact mem_range_self _)
#align set.is_compl_range_inl_range_inr Set.isCompl_range_inl_range_inr

/- warning: set.range_inl_union_range_inr -> Set.range_inl_union_range_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Sum.{u1, u2} α β)) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β)) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))) (Set.univ.{max u1 u2} (Sum.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Union.union.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instUnionSet.{max u2 u1} (Sum.{u2, u1} α β)) (Set.range.{max u2 u1, succ u2} (Sum.{u2, u1} α β) α (Sum.inl.{u2, u1} α β)) (Set.range.{max u2 u1, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β))) (Set.univ.{max u2 u1} (Sum.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align set.range_inl_union_range_inr Set.range_inl_union_range_inrₓ'. -/
@[simp]
theorem range_inl_union_range_inr : range (Sum.inl : α → Sum α β) ∪ range Sum.inr = univ :=
  isCompl_range_inl_range_inr.sup_eq_top
#align set.range_inl_union_range_inr Set.range_inl_union_range_inr

/- warning: set.range_inl_inter_range_inr -> Set.range_inl_inter_range_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasInter.{max u1 u2} (Sum.{u1, u2} α β)) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β)) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Inter.inter.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instInterSet.{max u2 u1} (Sum.{u2, u1} α β)) (Set.range.{max u2 u1, succ u2} (Sum.{u2, u1} α β) α (Sum.inl.{u2, u1} α β)) (Set.range.{max u2 u1, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β))) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instEmptyCollectionSet.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align set.range_inl_inter_range_inr Set.range_inl_inter_range_inrₓ'. -/
@[simp]
theorem range_inl_inter_range_inr : range (Sum.inl : α → Sum α β) ∩ range Sum.inr = ∅ :=
  isCompl_range_inl_range_inr.inf_eq_bot
#align set.range_inl_inter_range_inr Set.range_inl_inter_range_inr

/- warning: set.range_inr_union_range_inl -> Set.range_inr_union_range_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Sum.{u1, u2} α β)) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β)) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))) (Set.univ.{max u1 u2} (Sum.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Union.union.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instUnionSet.{max u2 u1} (Sum.{u2, u1} α β)) (Set.range.{max u2 u1, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β)) (Set.range.{max u2 u1, succ u2} (Sum.{u2, u1} α β) α (Sum.inl.{u2, u1} α β))) (Set.univ.{max u2 u1} (Sum.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align set.range_inr_union_range_inl Set.range_inr_union_range_inlₓ'. -/
@[simp]
theorem range_inr_union_range_inl : range (Sum.inr : β → Sum α β) ∪ range Sum.inl = univ :=
  isCompl_range_inl_range_inr.symm.sup_eq_top
#align set.range_inr_union_range_inl Set.range_inr_union_range_inl

/- warning: set.range_inr_inter_range_inl -> Set.range_inr_inter_range_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasInter.{max u1 u2} (Sum.{u1, u2} α β)) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β)) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasEmptyc.{max u1 u2} (Sum.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Inter.inter.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instInterSet.{max u2 u1} (Sum.{u2, u1} α β)) (Set.range.{max u2 u1, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β)) (Set.range.{max u2 u1, succ u2} (Sum.{u2, u1} α β) α (Sum.inl.{u2, u1} α β))) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instEmptyCollectionSet.{max u2 u1} (Sum.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align set.range_inr_inter_range_inl Set.range_inr_inter_range_inlₓ'. -/
@[simp]
theorem range_inr_inter_range_inl : range (Sum.inr : β → Sum α β) ∩ range Sum.inl = ∅ :=
  isCompl_range_inl_range_inr.symm.inf_eq_bot
#align set.range_inr_inter_range_inl Set.range_inr_inter_range_inl

#print Set.preimage_inl_image_inr /-
@[simp]
theorem preimage_inl_image_inr (s : Set β) : Sum.inl ⁻¹' (@Sum.inr α β '' s) = ∅ :=
  by
  ext
  simp
#align set.preimage_inl_image_inr Set.preimage_inl_image_inr
-/

/- warning: set.preimage_inr_image_inl -> Set.preimage_inr_image_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) (Set.image.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) s)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, max u1 u2} β (Sum.{u2, u1} α β) (Sum.inr.{u2, u1} α β) (Set.image.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Sum.inl.{u2, u1} α β) s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.preimage_inr_image_inl Set.preimage_inr_image_inlₓ'. -/
@[simp]
theorem preimage_inr_image_inl (s : Set α) : Sum.inr ⁻¹' (@Sum.inl α β '' s) = ∅ :=
  by
  ext
  simp
#align set.preimage_inr_image_inl Set.preimage_inr_image_inl

/- warning: set.preimage_inl_range_inr -> Set.preimage_inl_range_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, max u1 u2} α (Sum.{u2, u1} α β) (Sum.inl.{u2, u1} α β) (Set.range.{max u1 u2, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))
Case conversion may be inaccurate. Consider using '#align set.preimage_inl_range_inr Set.preimage_inl_range_inrₓ'. -/
@[simp]
theorem preimage_inl_range_inr : Sum.inl ⁻¹' range (Sum.inr : β → Sum α β) = ∅ := by
  rw [← image_univ, preimage_inl_image_inr]
#align set.preimage_inl_range_inr Set.preimage_inl_range_inr

#print Set.preimage_inr_range_inl /-
@[simp]
theorem preimage_inr_range_inl : Sum.inr ⁻¹' range (Sum.inl : α → Sum α β) = ∅ := by
  rw [← image_univ, preimage_inr_image_inl]
#align set.preimage_inr_range_inl Set.preimage_inr_range_inl
-/

/- warning: set.compl_range_inl -> Set.compl_range_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (HasCompl.compl.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (BooleanAlgebra.toHasCompl.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.booleanAlgebra.{max u1 u2} (Sum.{u1, u2} α β))) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (HasCompl.compl.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (BooleanAlgebra.toHasCompl.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instBooleanAlgebraSet.{max u2 u1} (Sum.{u2, u1} α β))) (Set.range.{max u2 u1, succ u2} (Sum.{u2, u1} α β) α (Sum.inl.{u2, u1} α β))) (Set.range.{max u2 u1, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align set.compl_range_inl Set.compl_range_inlₓ'. -/
@[simp]
theorem compl_range_inl : range (Sum.inl : α → Sum α β)ᶜ = range (Sum.inr : β → Sum α β) :=
  IsCompl.compl_eq isCompl_range_inl_range_inr
#align set.compl_range_inl Set.compl_range_inl

/- warning: set.compl_range_inr -> Set.compl_range_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (HasCompl.compl.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (BooleanAlgebra.toHasCompl.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.booleanAlgebra.{max u1 u2} (Sum.{u1, u2} α β))) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (HasCompl.compl.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (BooleanAlgebra.toHasCompl.{max u2 u1} (Set.{max u2 u1} (Sum.{u2, u1} α β)) (Set.instBooleanAlgebraSet.{max u2 u1} (Sum.{u2, u1} α β))) (Set.range.{max u2 u1, succ u1} (Sum.{u2, u1} α β) β (Sum.inr.{u2, u1} α β))) (Set.range.{max u2 u1, succ u2} (Sum.{u2, u1} α β) α (Sum.inl.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align set.compl_range_inr Set.compl_range_inrₓ'. -/
@[simp]
theorem compl_range_inr : range (Sum.inr : β → Sum α β)ᶜ = range (Sum.inl : α → Sum α β) :=
  IsCompl.compl_eq isCompl_range_inl_range_inr.symm
#align set.compl_range_inr Set.compl_range_inr

/- warning: set.image_preimage_inl_union_image_preimage_inr -> Set.image_preimage_inl_union_image_preimage_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{max u1 u2} (Sum.{u1, u2} α β)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Sum.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Sum.{u1, u2} α β)) (Set.image.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) (Set.preimage.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) s)) (Set.image.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) (Set.preimage.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) s))) s
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{max u2 u1} (Sum.{u1, u2} α β)), Eq.{max (succ u1) (succ u2)} (Set.{max u2 u1} (Sum.{u1, u2} α β)) (Union.union.{max u2 u1} (Set.{max u2 u1} (Sum.{u1, u2} α β)) (Set.instUnionSet.{max u1 u2} (Sum.{u1, u2} α β)) (Set.image.{u1, max u2 u1} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) (Set.preimage.{u1, max u2 u1} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) s)) (Set.image.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) (Set.preimage.{u2, max u2 u1} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) s))) s
Case conversion may be inaccurate. Consider using '#align set.image_preimage_inl_union_image_preimage_inr Set.image_preimage_inl_union_image_preimage_inrₓ'. -/
theorem image_preimage_inl_union_image_preimage_inr (s : Set (Sum α β)) :
    Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) = s := by
  rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, ← inter_distrib_left,
    range_inl_union_range_inr, inter_univ]
#align set.image_preimage_inl_union_image_preimage_inr Set.image_preimage_inl_union_image_preimage_inr

#print Set.range_quot_mk /-
@[simp]
theorem range_quot_mk (r : α → α → Prop) : range (Quot.mk r) = univ :=
  (surjective_quot_mk r).range_eq
#align set.range_quot_mk Set.range_quot_mk
-/

/- warning: set.range_quot_lift -> Set.range_quot_lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {r : ι -> ι -> Prop} (hf : forall (x : ι) (y : ι), (r x y) -> (Eq.{succ u1} α (f x) (f y))), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, u2} α (Quot.{u2} ι (fun (x : ι) (y : ι) => r x y)) (Quot.lift.{u2, succ u1} ι (fun (x : ι) (y : ι) => r x y) α f hf)) (Set.range.{u1, u2} α ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {r : ι -> ι -> Prop} (hf : forall (x : ι) (y : ι), (r x y) -> (Eq.{succ u2} α (f x) (f y))), Eq.{succ u2} (Set.{u2} α) (Set.range.{u2, u1} α (Quot.{u1} ι (fun (x : ι) (y : ι) => r x y)) (Quot.lift.{u1, succ u2} ι (fun (x : ι) (y : ι) => r x y) α f hf)) (Set.range.{u2, u1} α ι f)
Case conversion may be inaccurate. Consider using '#align set.range_quot_lift Set.range_quot_liftₓ'. -/
@[simp]
theorem range_quot_lift {r : ι → ι → Prop} (hf : ∀ x y, r x y → f x = f y) :
    range (Quot.lift f hf) = range f :=
  ext fun y => (surjective_quot_mk _).exists
#align set.range_quot_lift Set.range_quot_lift

#print Set.range_quotient_mk /-
@[simp]
theorem range_quotient_mk [Setoid α] : (range fun x : α => ⟦x⟧) = univ :=
  range_quot_mk _
#align set.range_quotient_mk Set.range_quotient_mk
-/

#print Set.range_quotient_lift /-
@[simp]
theorem range_quotient_lift [s : Setoid ι] (hf) :
    range (Quotient.lift f hf : Quotient s → α) = range f :=
  range_quot_lift _
#align set.range_quotient_lift Set.range_quotient_lift
-/

#print Set.range_quotient_mk' /-
@[simp]
theorem range_quotient_mk' {s : Setoid α} : range (Quotient.mk' : α → Quotient s) = univ :=
  range_quot_mk _
#align set.range_quotient_mk' Set.range_quotient_mk'
-/

#print Set.range_quotient_lift_on' /-
@[simp]
theorem range_quotient_lift_on' {s : Setoid ι} (hf) :
    (range fun x : Quotient s => Quotient.liftOn' x f hf) = range f :=
  range_quot_lift _
#align set.range_quotient_lift_on' Set.range_quotient_lift_on'
-/

#print Set.canLift /-
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Set α) (Set β) ((· '' ·) c) fun s => ∀ x ∈ s, p x
    where prf s hs := subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)
#align set.can_lift Set.canLift
-/

/- warning: set.range_const_subset -> Set.range_const_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {c : α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.range.{u1, u2} α ι (fun (x : ι) => c)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) c)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {c : α}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.range.{u2, u1} α ι (fun (x : ι) => c)) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) c)
Case conversion may be inaccurate. Consider using '#align set.range_const_subset Set.range_const_subsetₓ'. -/
theorem range_const_subset {c : α} : (range fun x : ι => c) ⊆ {c} :=
  range_subset_iff.2 fun x => rfl
#align set.range_const_subset Set.range_const_subset

#print Set.range_const /-
@[simp]
theorem range_const : ∀ [Nonempty ι] {c : α}, (range fun x : ι => c) = {c}
  | ⟨x⟩, c =>
    Subset.antisymm range_const_subset fun y hy => (mem_singleton_iff.1 hy).symm ▸ mem_range_self x
#align set.range_const Set.range_const
-/

#print Set.range_subtype_map /-
theorem range_subtype_map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ x, p x → q (f x)) :
    range (Subtype.map f h) = coe ⁻¹' (f '' { x | p x }) :=
  by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map, Subtype.coe_mk,
    mem_set_of, exists_prop]
#align set.range_subtype_map Set.range_subtype_map
-/

/- warning: set.image_swap_eq_preimage_swap -> Set.image_swap_eq_preimage_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max (succ (max u1 u2)) (succ (max u2 u1))} ((Set.{max u1 u2} (Prod.{u1, u2} α β)) -> (Set.{max u2 u1} (Prod.{u2, u1} β α))) (Set.image.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β)) (Set.preimage.{max u2 u1, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (Prod.swap.{u2, u1} β α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} ((Set.{max u2 u1} (Prod.{u2, u1} α β)) -> (Set.{max u2 u1} (Prod.{u1, u2} β α))) (Set.image.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β)) (Set.preimage.{max u2 u1, max u2 u1} (Prod.{u1, u2} β α) (Prod.{u2, u1} α β) (Prod.swap.{u1, u2} β α))
Case conversion may be inaccurate. Consider using '#align set.image_swap_eq_preimage_swap Set.image_swap_eq_preimage_swapₓ'. -/
theorem image_swap_eq_preimage_swap : image (@Prod.swap α β) = preimage Prod.swap :=
  image_eq_preimage_of_inverse Prod.swap_leftInverse Prod.swap_rightInverse
#align set.image_swap_eq_preimage_swap Set.image_swap_eq_preimage_swap

/- warning: set.preimage_singleton_nonempty -> Set.preimage_singleton_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {y : β}, Iff (Set.Nonempty.{u1} α (Set.preimage.{u1, u2} α β f (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y))) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {y : β}, Iff (Set.Nonempty.{u2} α (Set.preimage.{u2, u1} α β f (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y))) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align set.preimage_singleton_nonempty Set.preimage_singleton_nonemptyₓ'. -/
theorem preimage_singleton_nonempty {f : α → β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y ∈ range f :=
  Iff.rfl
#align set.preimage_singleton_nonempty Set.preimage_singleton_nonempty

/- warning: set.preimage_singleton_eq_empty -> Set.preimage_singleton_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {y : β}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Set.range.{u2, succ u1} β α f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {y : β}, Iff (Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β f (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Not (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Set.range.{u1, succ u2} β α f)))
Case conversion may be inaccurate. Consider using '#align set.preimage_singleton_eq_empty Set.preimage_singleton_eq_emptyₓ'. -/
theorem preimage_singleton_eq_empty {f : α → β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
  not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.Not
#align set.preimage_singleton_eq_empty Set.preimage_singleton_eq_empty

/- warning: set.range_subset_singleton -> Set.range_subset_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> α} {x : α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.range.{u1, u2} α ι f) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Eq.{max u2 (succ u1)} (ι -> α) f (Function.const.{succ u1, u2} α ι x))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {f : ι -> α} {x : α}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.range.{u2, u1} α ι f) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) x)) (Eq.{max (succ u2) u1} (ι -> α) f (Function.const.{succ u2, u1} α ι x))
Case conversion may be inaccurate. Consider using '#align set.range_subset_singleton Set.range_subset_singletonₓ'. -/
theorem range_subset_singleton {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = const ι x := by
  simp [range_subset_iff, funext_iff, mem_singleton]
#align set.range_subset_singleton Set.range_subset_singleton

/- warning: set.image_compl_preimage -> Set.image_compl_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.preimage.{u1, u2} α β f s))) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Set.preimage.{u1, u2} α β f s))) (SDiff.sdiff.{u2} (Set.{u2} β) (Set.instSDiffSet.{u2} β) (Set.range.{u2, succ u1} β α f) s)
Case conversion may be inaccurate. Consider using '#align set.image_compl_preimage Set.image_compl_preimageₓ'. -/
theorem image_compl_preimage {f : α → β} {s : Set β} : f '' (f ⁻¹' s)ᶜ = range f \ s := by
  rw [compl_eq_univ_diff, image_diff_preimage, image_univ]
#align set.image_compl_preimage Set.image_compl_preimage

#print Set.rangeFactorization /-
/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def rangeFactorization (f : ι → β) : ι → range f := fun i => ⟨f i, mem_range_self i⟩
#align set.range_factorization Set.rangeFactorization
-/

/- warning: set.range_factorization_eq -> Set.rangeFactorization_eq is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} {f : ι -> β}, Eq.{max u2 (succ u1)} (ι -> β) (Function.comp.{u2, succ u1, succ u1} ι (Subtype.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) x (Set.range.{u1, u2} β ι f))) β (Subtype.val.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) x (Set.range.{u1, u2} β ι f))) (Set.rangeFactorization.{u1, u2} β ι f)) f
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} {f : ι -> β}, Eq.{max (succ u2) u1} (ι -> β) (Function.comp.{u1, succ u2, succ u2} ι (Subtype.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, u1} β ι f))) β (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, u1} β ι f))) (Set.rangeFactorization.{u2, u1} β ι f)) f
Case conversion may be inaccurate. Consider using '#align set.range_factorization_eq Set.rangeFactorization_eqₓ'. -/
theorem rangeFactorization_eq {f : ι → β} : Subtype.val ∘ rangeFactorization f = f :=
  funext fun i => rfl
#align set.range_factorization_eq Set.rangeFactorization_eq

/- warning: set.range_factorization_coe -> Set.rangeFactorization_coe is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (f : ι -> β) (a : ι), Eq.{succ u1} β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β (coeSubtype.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) x (Set.range.{u1, u2} β ι f)))))) (Set.rangeFactorization.{u1, u2} β ι f a)) (f a)
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (f : ι -> β) (a : ι), Eq.{succ u2} β (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, u1} β ι f)) (Set.rangeFactorization.{u2, u1} β ι f a)) (f a)
Case conversion may be inaccurate. Consider using '#align set.range_factorization_coe Set.rangeFactorization_coeₓ'. -/
@[simp]
theorem rangeFactorization_coe (f : ι → β) (a : ι) : (rangeFactorization f a : β) = f a :=
  rfl
#align set.range_factorization_coe Set.rangeFactorization_coe

/- warning: set.coe_comp_range_factorization -> Set.coe_comp_rangeFactorization is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Sort.{u2}} (f : ι -> β), Eq.{max u2 (succ u1)} (ι -> β) (Function.comp.{u2, succ u1, succ u1} ι (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} β) Type.{u1} (Set.hasCoeToSort.{u1} β) (Set.range.{u1, u2} β ι f)) β (coeSubtype.{succ u1} β (fun (x : β) => Membership.Mem.{u1, u1} β (Set.{u1} β) (Set.hasMem.{u1} β) x (Set.range.{u1, u2} β ι f))))))) (Set.rangeFactorization.{u1, u2} β ι f)) f
but is expected to have type
  forall {β : Type.{u2}} {ι : Sort.{u1}} (f : ι -> β), Eq.{max (succ u2) u1} (ι -> β) (Function.comp.{u1, succ u2, succ u2} ι (Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) β (fun (x : Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) => Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, u1} β ι f)) x) (Set.rangeFactorization.{u2, u1} β ι f)) f
Case conversion may be inaccurate. Consider using '#align set.coe_comp_range_factorization Set.coe_comp_rangeFactorizationₓ'. -/
@[simp]
theorem coe_comp_rangeFactorization (f : ι → β) : coe ∘ rangeFactorization f = f :=
  rfl
#align set.coe_comp_range_factorization Set.coe_comp_rangeFactorization

#print Set.surjective_onto_range /-
theorem surjective_onto_range : Surjective (rangeFactorization f) := fun ⟨_, ⟨i, rfl⟩⟩ => ⟨i, rfl⟩
#align set.surjective_onto_range Set.surjective_onto_range
-/

/- warning: set.image_eq_range -> Set.image_eq_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) (Set.range.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (fun (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) (Set.range.{u1, succ u2} β (Set.Elem.{u2} α s) (fun (x : Set.Elem.{u2} α s) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)))
Case conversion may be inaccurate. Consider using '#align set.image_eq_range Set.image_eq_rangeₓ'. -/
theorem image_eq_range (f : α → β) (s : Set α) : f '' s = range fun x : s => f x :=
  by
  ext
  constructor
  rintro ⟨x, h1, h2⟩
  exact ⟨⟨x, h1⟩, h2⟩
  rintro ⟨⟨x, h1⟩, h2⟩
  exact ⟨x, h1, h2⟩
#align set.image_eq_range Set.image_eq_range

/- warning: sum.range_eq -> Sum.range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : (Sum.{u1, u2} α β) -> γ), Eq.{succ u3} (Set.{u3} γ) (Set.range.{u3, max (succ u1) (succ u2)} γ (Sum.{u1, u2} α β) f) (Union.union.{u3} (Set.{u3} γ) (Set.hasUnion.{u3} γ) (Set.range.{u3, succ u1} γ α (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} α (Sum.{u1, u2} α β) γ f (Sum.inl.{u1, u2} α β))) (Set.range.{u3, succ u2} γ β (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} β (Sum.{u1, u2} α β) γ f (Sum.inr.{u1, u2} α β))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : (Sum.{u3, u2} α β) -> γ), Eq.{succ u1} (Set.{u1} γ) (Set.range.{u1, max (succ u3) (succ u2)} γ (Sum.{u3, u2} α β) f) (Union.union.{u1} (Set.{u1} γ) (Set.instUnionSet.{u1} γ) (Set.range.{u1, succ u3} γ α (Function.comp.{succ u3, max (succ u3) (succ u2), succ u1} α (Sum.{u3, u2} α β) γ f (Sum.inl.{u3, u2} α β))) (Set.range.{u1, succ u2} γ β (Function.comp.{succ u2, max (succ u3) (succ u2), succ u1} β (Sum.{u3, u2} α β) γ f (Sum.inr.{u3, u2} α β))))
Case conversion may be inaccurate. Consider using '#align sum.range_eq Sum.range_eqₓ'. -/
theorem Sum.range_eq (f : Sum α β → γ) : range f = range (f ∘ Sum.inl) ∪ range (f ∘ Sum.inr) :=
  ext fun x => Sum.exists
#align sum.range_eq Sum.range_eq

/- warning: set.sum.elim_range -> Set.Sum.elim_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> γ) (g : β -> γ), Eq.{succ u3} (Set.{u3} γ) (Set.range.{u3, max (succ u1) (succ u2)} γ (Sum.{u1, u2} α β) (Sum.elim.{u1, u2, succ u3} α β γ f g)) (Union.union.{u3} (Set.{u3} γ) (Set.hasUnion.{u3} γ) (Set.range.{u3, succ u1} γ α f) (Set.range.{u3, succ u2} γ β g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> γ) (g : β -> γ), Eq.{succ u3} (Set.{u3} γ) (Set.range.{u3, max (succ u2) (succ u1)} γ (Sum.{u1, u2} α β) (Sum.elim.{u1, u2, succ u3} α β γ f g)) (Union.union.{u3} (Set.{u3} γ) (Set.instUnionSet.{u3} γ) (Set.range.{u3, succ u1} γ α f) (Set.range.{u3, succ u2} γ β g))
Case conversion may be inaccurate. Consider using '#align set.sum.elim_range Set.Sum.elim_rangeₓ'. -/
@[simp]
theorem Sum.elim_range (f : α → γ) (g : β → γ) : range (Sum.elim f g) = range f ∪ range g :=
  Sum.range_eq _
#align set.sum.elim_range Set.Sum.elim_range

/- warning: set.range_ite_subset' -> Set.range_ite_subset' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Prop} [_inst_1 : Decidable p] {f : α -> β} {g : α -> β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.range.{u2, succ u1} β α (ite.{max (succ u1) (succ u2)} (α -> β) p _inst_1 f g)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.range.{u2, succ u1} β α f) (Set.range.{u2, succ u1} β α g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Prop} [_inst_1 : Decidable p] {f : α -> β} {g : α -> β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Set.range.{u2, succ u1} β α (ite.{max (succ u1) (succ u2)} (α -> β) p _inst_1 f g)) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (Set.range.{u2, succ u1} β α f) (Set.range.{u2, succ u1} β α g))
Case conversion may be inaccurate. Consider using '#align set.range_ite_subset' Set.range_ite_subset'ₓ'. -/
theorem range_ite_subset' {p : Prop} [Decidable p] {f g : α → β} :
    range (if p then f else g) ⊆ range f ∪ range g :=
  by
  by_cases h : p;
  · rw [if_pos h]
    exact subset_union_left _ _
  · rw [if_neg h]
    exact subset_union_right _ _
#align set.range_ite_subset' Set.range_ite_subset'

/- warning: set.range_ite_subset -> Set.range_ite_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {f : α -> β} {g : α -> β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.range.{u2, succ u1} β α (fun (x : α) => ite.{succ u2} β (p x) (_inst_1 x) (f x) (g x))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.range.{u2, succ u1} β α f) (Set.range.{u2, succ u1} β α g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u2} α p] {f : α -> β} {g : α -> β}, HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.range.{u1, succ u2} β α (fun (x : α) => ite.{succ u1} β (p x) (_inst_1 x) (f x) (g x))) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.range.{u1, succ u2} β α f) (Set.range.{u1, succ u2} β α g))
Case conversion may be inaccurate. Consider using '#align set.range_ite_subset Set.range_ite_subsetₓ'. -/
theorem range_ite_subset {p : α → Prop} [DecidablePred p] {f g : α → β} :
    (range fun x => if p x then f x else g x) ⊆ range f ∪ range g :=
  by
  rw [range_subset_iff]; intro x; by_cases h : p x
  simp [if_pos h, mem_union, mem_range_self]
  simp [if_neg h, mem_union, mem_range_self]
#align set.range_ite_subset Set.range_ite_subset

/- warning: set.preimage_range -> Set.preimage_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.range.{u2, succ u1} β α f)) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β f (Set.range.{u1, succ u2} β α f)) (Set.univ.{u2} α)
Case conversion may be inaccurate. Consider using '#align set.preimage_range Set.preimage_rangeₓ'. -/
@[simp]
theorem preimage_range (f : α → β) : f ⁻¹' range f = univ :=
  eq_univ_of_forall mem_range_self
#align set.preimage_range Set.preimage_range

#print Set.range_unique /-
/-- The range of a function from a `unique` type contains just the
function applied to its single value. -/
theorem range_unique [h : Unique ι] : range f = {f default} :=
  by
  ext x
  rw [mem_range]
  constructor
  · rintro ⟨i, hi⟩
    rw [h.uniq i] at hi
    exact hi ▸ mem_singleton _
  · exact fun h => ⟨default, h.symm⟩
#align set.range_unique Set.range_unique
-/

/- warning: set.range_diff_image_subset -> Set.range_diff_image_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f) (Set.image.{u1, u2} α β f s)) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) (Set.range.{u1, succ u2} β α f) (Set.image.{u2, u1} α β f s)) (Set.image.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s))
Case conversion may be inaccurate. Consider using '#align set.range_diff_image_subset Set.range_diff_image_subsetₓ'. -/
theorem range_diff_image_subset (f : α → β) (s : Set α) : range f \ f '' s ⊆ f '' sᶜ :=
  fun y ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩
#align set.range_diff_image_subset Set.range_diff_image_subset

/- warning: set.range_diff_image -> Set.range_diff_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f) (Set.image.{u1, u2} α β f s)) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) (Set.range.{u1, succ u2} β α f) (Set.image.{u2, u1} α β f s)) (Set.image.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)))
Case conversion may be inaccurate. Consider using '#align set.range_diff_image Set.range_diff_imageₓ'. -/
theorem range_diff_image {f : α → β} (H : Injective f) (s : Set α) : range f \ f '' s = f '' sᶜ :=
  Subset.antisymm (range_diff_image_subset f s) fun y ⟨x, hx, hy⟩ =>
    hy ▸ ⟨mem_range_self _, fun ⟨x', hx', Eq⟩ => hx <| H Eq ▸ hx'⟩
#align set.range_diff_image Set.range_diff_image

#print Set.range_inclusion /-
@[simp]
theorem range_inclusion (h : s ⊆ t) : range (inclusion h) = { x : t | (x : α) ∈ s } :=
  by
  ext ⟨x, hx⟩
  simp [inclusion]
#align set.range_inclusion Set.range_inclusion
-/

#print Set.rangeSplitting /-
/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
noncomputable def rangeSplitting (f : α → β) : range f → α := fun x => x.2.some
#align set.range_splitting Set.rangeSplitting
-/

#print Set.apply_rangeSplitting /-
-- This can not be a `@[simp]` lemma because the head of the left hand side is a variable.
theorem apply_rangeSplitting (f : α → β) (x : range f) : f (rangeSplitting f x) = x :=
  x.2.some_spec
#align set.apply_range_splitting Set.apply_rangeSplitting
-/

#print Set.comp_rangeSplitting /-
@[simp]
theorem comp_rangeSplitting (f : α → β) : f ∘ rangeSplitting f = coe :=
  by
  ext
  simp only [Function.comp_apply]
  apply apply_range_splitting
#align set.comp_range_splitting Set.comp_rangeSplitting
-/

#print Set.leftInverse_rangeSplitting /-
-- When `f` is injective, see also `equiv.of_injective`.
theorem leftInverse_rangeSplitting (f : α → β) :
    LeftInverse (rangeFactorization f) (rangeSplitting f) := fun x =>
  by
  ext
  simp only [range_factorization_coe]
  apply apply_range_splitting
#align set.left_inverse_range_splitting Set.leftInverse_rangeSplitting
-/

#print Set.rangeSplitting_injective /-
theorem rangeSplitting_injective (f : α → β) : Injective (rangeSplitting f) :=
  (leftInverse_rangeSplitting f).Injective
#align set.range_splitting_injective Set.rangeSplitting_injective
-/

/- warning: set.right_inverse_range_splitting -> Set.rightInverse_rangeSplitting is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Function.RightInverse.{succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) α (Set.rangeFactorization.{u2, succ u1} β α f) (Set.rangeSplitting.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Function.RightInverse.{succ u1, succ u2} (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f)) α (Set.rangeFactorization.{u1, succ u2} β α f) (Set.rangeSplitting.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align set.right_inverse_range_splitting Set.rightInverse_rangeSplittingₓ'. -/
theorem rightInverse_rangeSplitting {f : α → β} (h : Injective f) :
    RightInverse (rangeFactorization f) (rangeSplitting f) :=
  (leftInverse_rangeSplitting f).right_inverse_of_injective fun x y hxy =>
    h <| Subtype.ext_iff.1 hxy
#align set.right_inverse_range_splitting Set.rightInverse_rangeSplitting

/- warning: set.preimage_range_splitting -> Set.preimage_rangeSplitting is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Eq.{max (succ u1) (succ u2)} ((Set.{u1} α) -> (Set.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)))) (Set.preimage.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) α (Set.rangeSplitting.{u1, u2} α β f)) (Set.image.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) (Set.rangeFactorization.{u2, succ u1} β α f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Eq.{max (succ u2) (succ u1)} ((Set.{u2} α) -> (Set.{u1} (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f)))) (Set.preimage.{u1, u2} (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f)) α (Set.rangeSplitting.{u2, u1} α β f)) (Set.image.{u2, u1} α (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f)) (Set.rangeFactorization.{u1, succ u2} β α f)))
Case conversion may be inaccurate. Consider using '#align set.preimage_range_splitting Set.preimage_rangeSplittingₓ'. -/
theorem preimage_rangeSplitting {f : α → β} (hf : Injective f) :
    preimage (rangeSplitting f) = image (rangeFactorization f) :=
  (image_eq_preimage_of_inverse (rightInverse_rangeSplitting hf)
      (leftInverse_rangeSplitting f)).symm
#align set.preimage_range_splitting Set.preimage_rangeSplitting

/- warning: set.is_compl_range_some_none -> Set.isCompl_range_some_none is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), IsCompl.{u1} (Set.{u1} (Option.{u1} α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Option.{u1} α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Option.{u1} α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Option.{u1} α)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Option.{u1} α)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (Option.{u1} α)) (Set.booleanAlgebra.{u1} (Option.{u1} α))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} (Option.{u1} α)) (Set.booleanAlgebra.{u1} (Option.{u1} α))) (Set.range.{u1, succ u1} (Option.{u1} α) α (Option.some.{u1} α)) (Singleton.singleton.{u1, u1} (Option.{u1} α) (Set.{u1} (Option.{u1} α)) (Set.hasSingleton.{u1} (Option.{u1} α)) (Option.none.{u1} α))
but is expected to have type
  forall (α : Type.{u1}), IsCompl.{u1} (Set.{u1} (Option.{u1} α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Option.{u1} α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Option.{u1} α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Option.{u1} α)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Option.{u1} α)) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} (Option.{u1} α)) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} (Option.{u1} α)) (Set.instBooleanAlgebraSet.{u1} (Option.{u1} α)))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} (Option.{u1} α)) (Set.instBooleanAlgebraSet.{u1} (Option.{u1} α))) (Set.range.{u1, succ u1} (Option.{u1} α) α (Option.some.{u1} α)) (Singleton.singleton.{u1, u1} (Option.{u1} α) (Set.{u1} (Option.{u1} α)) (Set.instSingletonSet.{u1} (Option.{u1} α)) (Option.none.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.is_compl_range_some_none Set.isCompl_range_some_noneₓ'. -/
theorem isCompl_range_some_none (α : Type _) : IsCompl (range (some : α → Option α)) {none} :=
  IsCompl.of_le (fun x ⟨⟨a, ha⟩, (hn : x = none)⟩ => Option.some_ne_none _ (ha.trans hn))
    fun x hx => Option.casesOn x (Or.inr rfl) fun x => Or.inl <| mem_range_self _
#align set.is_compl_range_some_none Set.isCompl_range_some_none

/- warning: set.compl_range_some -> Set.compl_range_some is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), Eq.{succ u1} (Set.{u1} (Option.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} (Option.{u1} α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Option.{u1} α)) (Set.booleanAlgebra.{u1} (Option.{u1} α))) (Set.range.{u1, succ u1} (Option.{u1} α) α (Option.some.{u1} α))) (Singleton.singleton.{u1, u1} (Option.{u1} α) (Set.{u1} (Option.{u1} α)) (Set.hasSingleton.{u1} (Option.{u1} α)) (Option.none.{u1} α))
but is expected to have type
  forall (α : Type.{u1}), Eq.{succ u1} (Set.{u1} (Option.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} (Option.{u1} α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Option.{u1} α)) (Set.instBooleanAlgebraSet.{u1} (Option.{u1} α))) (Set.range.{u1, succ u1} (Option.{u1} α) α (Option.some.{u1} α))) (Singleton.singleton.{u1, u1} (Option.{u1} α) (Set.{u1} (Option.{u1} α)) (Set.instSingletonSet.{u1} (Option.{u1} α)) (Option.none.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.compl_range_some Set.compl_range_someₓ'. -/
@[simp]
theorem compl_range_some (α : Type _) : range (some : α → Option α)ᶜ = {none} :=
  (isCompl_range_some_none α).compl_eq
#align set.compl_range_some Set.compl_range_some

/- warning: set.range_some_inter_none -> Set.range_some_inter_none is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), Eq.{succ u1} (Set.{u1} (Option.{u1} α)) (Inter.inter.{u1} (Set.{u1} (Option.{u1} α)) (Set.hasInter.{u1} (Option.{u1} α)) (Set.range.{u1, succ u1} (Option.{u1} α) α (Option.some.{u1} α)) (Singleton.singleton.{u1, u1} (Option.{u1} α) (Set.{u1} (Option.{u1} α)) (Set.hasSingleton.{u1} (Option.{u1} α)) (Option.none.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Option.{u1} α)) (Set.hasEmptyc.{u1} (Option.{u1} α)))
but is expected to have type
  forall (α : Type.{u1}), Eq.{succ u1} (Set.{u1} (Option.{u1} α)) (Inter.inter.{u1} (Set.{u1} (Option.{u1} α)) (Set.instInterSet.{u1} (Option.{u1} α)) (Set.range.{u1, succ u1} (Option.{u1} α) α (Option.some.{u1} α)) (Singleton.singleton.{u1, u1} (Option.{u1} α) (Set.{u1} (Option.{u1} α)) (Set.instSingletonSet.{u1} (Option.{u1} α)) (Option.none.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Option.{u1} α)) (Set.instEmptyCollectionSet.{u1} (Option.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.range_some_inter_none Set.range_some_inter_noneₓ'. -/
@[simp]
theorem range_some_inter_none (α : Type _) : range (some : α → Option α) ∩ {none} = ∅ :=
  (isCompl_range_some_none α).inf_eq_bot
#align set.range_some_inter_none Set.range_some_inter_none

/- warning: set.range_some_union_none -> Set.range_some_union_none is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), Eq.{succ u1} (Set.{u1} (Option.{u1} α)) (Union.union.{u1} (Set.{u1} (Option.{u1} α)) (Set.hasUnion.{u1} (Option.{u1} α)) (Set.range.{u1, succ u1} (Option.{u1} α) α (Option.some.{u1} α)) (Singleton.singleton.{u1, u1} (Option.{u1} α) (Set.{u1} (Option.{u1} α)) (Set.hasSingleton.{u1} (Option.{u1} α)) (Option.none.{u1} α))) (Set.univ.{u1} (Option.{u1} α))
but is expected to have type
  forall (α : Type.{u1}), Eq.{succ u1} (Set.{u1} (Option.{u1} α)) (Union.union.{u1} (Set.{u1} (Option.{u1} α)) (Set.instUnionSet.{u1} (Option.{u1} α)) (Set.range.{u1, succ u1} (Option.{u1} α) α (Option.some.{u1} α)) (Singleton.singleton.{u1, u1} (Option.{u1} α) (Set.{u1} (Option.{u1} α)) (Set.instSingletonSet.{u1} (Option.{u1} α)) (Option.none.{u1} α))) (Set.univ.{u1} (Option.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.range_some_union_none Set.range_some_union_noneₓ'. -/
@[simp]
theorem range_some_union_none (α : Type _) : range (some : α → Option α) ∪ {none} = univ :=
  (isCompl_range_some_none α).sup_eq_top
#align set.range_some_union_none Set.range_some_union_none

#print Set.insert_none_range_some /-
@[simp]
theorem insert_none_range_some (α : Type _) : insert none (range (some : α → Option α)) = univ :=
  (isCompl_range_some_none α).symm.sup_eq_top
#align set.insert_none_range_some Set.insert_none_range_some
-/

end Range

section Subsingleton

variable {s : Set α}

/- warning: set.subsingleton.image -> Set.Subsingleton.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (forall (f : α -> β), Set.Subsingleton.{u2} β (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α}, (Set.Subsingleton.{u2} α s) -> (forall (f : α -> β), Set.Subsingleton.{u1} β (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align set.subsingleton.image Set.Subsingleton.imageₓ'. -/
/-- The image of a subsingleton is a subsingleton. -/
theorem Subsingleton.image (hs : s.Subsingleton) (f : α → β) : (f '' s).Subsingleton :=
  fun _ ⟨x, hx, Hx⟩ _ ⟨y, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)
#align set.subsingleton.image Set.Subsingleton.image

#print Set.Subsingleton.preimage /-
/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
theorem Subsingleton.preimage {s : Set β} (hs : s.Subsingleton) {f : α → β}
    (hf : Function.Injective f) : (f ⁻¹' s).Subsingleton := fun a ha b hb => hf <| hs ha hb
#align set.subsingleton.preimage Set.Subsingleton.preimage
-/

/- warning: set.subsingleton_of_image -> Set.subsingleton_of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u1} α), (Set.Subsingleton.{u2} β (Set.image.{u1, u2} α β f s)) -> (Set.Subsingleton.{u1} α s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u2} α), (Set.Subsingleton.{u1} β (Set.image.{u2, u1} α β f s)) -> (Set.Subsingleton.{u2} α s))
Case conversion may be inaccurate. Consider using '#align set.subsingleton_of_image Set.subsingleton_of_imageₓ'. -/
/-- If the image of a set under an injective map is a subsingleton, the set is a subsingleton. -/
theorem subsingleton_of_image {α β : Type _} {f : α → β} (hf : Function.Injective f) (s : Set α)
    (hs : (f '' s).Subsingleton) : s.Subsingleton :=
  (hs.Preimage hf).anti <| subset_preimage_image _ _
#align set.subsingleton_of_image Set.subsingleton_of_image

/- warning: set.subsingleton_of_preimage -> Set.subsingleton_of_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u2} β), (Set.Subsingleton.{u1} α (Set.preimage.{u1, u2} α β f s)) -> (Set.Subsingleton.{u2} β s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u1} β), (Set.Subsingleton.{u2} α (Set.preimage.{u2, u1} α β f s)) -> (Set.Subsingleton.{u1} β s))
Case conversion may be inaccurate. Consider using '#align set.subsingleton_of_preimage Set.subsingleton_of_preimageₓ'. -/
/-- If the preimage of a set under an surjective map is a subsingleton,
the set is a subsingleton. -/
theorem subsingleton_of_preimage {α β : Type _} {f : α → β} (hf : Function.Surjective f) (s : Set β)
    (hs : (f ⁻¹' s).Subsingleton) : s.Subsingleton := fun fx hx fy hy =>
  by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)
#align set.subsingleton_of_preimage Set.subsingleton_of_preimage

#print Set.subsingleton_range /-
theorem subsingleton_range {α : Sort _} [Subsingleton α] (f : α → β) : (range f).Subsingleton :=
  forall_range_iff.2 fun x => forall_range_iff.2 fun y => congr_arg f (Subsingleton.elim x y)
#align set.subsingleton_range Set.subsingleton_range
-/

#print Set.Nontrivial.preimage /-
/-- The preimage of a nontrivial set under a surjective map is nontrivial. -/
theorem Nontrivial.preimage {s : Set β} (hs : s.Nontrivial) {f : α → β}
    (hf : Function.Surjective f) : (f ⁻¹' s).Nontrivial :=
  by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩
#align set.nontrivial.preimage Set.Nontrivial.preimage
-/

/- warning: set.nontrivial.image -> Set.Nontrivial.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (forall {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Set.Nontrivial.{u2} β (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α}, (Set.Nontrivial.{u2} α s) -> (forall {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Set.Nontrivial.{u1} β (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.image Set.Nontrivial.imageₓ'. -/
/-- The image of a nontrivial set under an injective map is nontrivial. -/
theorem Nontrivial.image (hs : s.Nontrivial) {f : α → β} (hf : Function.Injective f) :
    (f '' s).Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.Ne hxy⟩
#align set.nontrivial.image Set.Nontrivial.image

/- warning: set.nontrivial_of_image -> Set.nontrivial_of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), (Set.Nontrivial.{u2} β (Set.image.{u1, u2} α β f s)) -> (Set.Nontrivial.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), (Set.Nontrivial.{u1} β (Set.image.{u2, u1} α β f s)) -> (Set.Nontrivial.{u2} α s)
Case conversion may be inaccurate. Consider using '#align set.nontrivial_of_image Set.nontrivial_of_imageₓ'. -/
/-- If the image of a set is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_image (f : α → β) (s : Set α) (hs : (f '' s).Nontrivial) : s.Nontrivial :=
  let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩
#align set.nontrivial_of_image Set.nontrivial_of_image

/- warning: set.nontrivial_of_preimage -> Set.nontrivial_of_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u2} β), (Set.Nontrivial.{u1} α (Set.preimage.{u1, u2} α β f s)) -> (Set.Nontrivial.{u2} β s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u1} β), (Set.Nontrivial.{u2} α (Set.preimage.{u2, u1} α β f s)) -> (Set.Nontrivial.{u1} β s))
Case conversion may be inaccurate. Consider using '#align set.nontrivial_of_preimage Set.nontrivial_of_preimageₓ'. -/
/-- If the preimage of a set under an injective map is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_preimage {f : α → β} (hf : Function.Injective f) (s : Set β)
    (hs : (f ⁻¹' s).Nontrivial) : s.Nontrivial :=
  (hs.image hf).mono <| image_preimage_subset _ _
#align set.nontrivial_of_preimage Set.nontrivial_of_preimage

end Subsingleton

end Set

namespace Function

variable {ι : Sort _} {α : Type _} {β : Type _} {f : α → β}

open Set

/- warning: function.surjective.preimage_injective -> Function.Surjective.preimage_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (Function.Injective.{succ u2, succ u1} (Set.{u2} β) (Set.{u1} α) (Set.preimage.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (Function.Injective.{succ u1, succ u2} (Set.{u1} β) (Set.{u2} α) (Set.preimage.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align function.surjective.preimage_injective Function.Surjective.preimage_injectiveₓ'. -/
theorem Surjective.preimage_injective (hf : Surjective f) : Injective (preimage f) := fun s t =>
  (preimage_eq_preimage hf).1
#align function.surjective.preimage_injective Function.Surjective.preimage_injective

/- warning: function.injective.preimage_image -> Function.Injective.preimage_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.image.{u1, u2} α β f s)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β f (Set.image.{u2, u1} α β f s)) s)
Case conversion may be inaccurate. Consider using '#align function.injective.preimage_image Function.Injective.preimage_imageₓ'. -/
theorem Injective.preimage_image (hf : Injective f) (s : Set α) : f ⁻¹' (f '' s) = s :=
  preimage_image_eq s hf
#align function.injective.preimage_image Function.Injective.preimage_image

/- warning: function.injective.preimage_surjective -> Function.Injective.preimage_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Function.Surjective.{succ u2, succ u1} (Set.{u2} β) (Set.{u1} α) (Set.preimage.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Function.Surjective.{succ u1, succ u2} (Set.{u1} β) (Set.{u2} α) (Set.preimage.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align function.injective.preimage_surjective Function.Injective.preimage_surjectiveₓ'. -/
theorem Injective.preimage_surjective (hf : Injective f) : Surjective (preimage f) :=
  by
  intro s
  use f '' s
  rw [hf.preimage_image]
#align function.injective.preimage_surjective Function.Injective.preimage_surjective

/- warning: function.injective.subsingleton_image_iff -> Function.Injective.subsingleton_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {s : Set.{u1} α}, Iff (Set.Subsingleton.{u2} β (Set.image.{u1, u2} α β f s)) (Set.Subsingleton.{u1} α s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {s : Set.{u2} α}, Iff (Set.Subsingleton.{u1} β (Set.image.{u2, u1} α β f s)) (Set.Subsingleton.{u2} α s))
Case conversion may be inaccurate. Consider using '#align function.injective.subsingleton_image_iff Function.Injective.subsingleton_image_iffₓ'. -/
theorem Injective.subsingleton_image_iff (hf : Injective f) {s : Set α} :
    (f '' s).Subsingleton ↔ s.Subsingleton :=
  ⟨subsingleton_of_image hf s, fun h => h.image f⟩
#align function.injective.subsingleton_image_iff Function.Injective.subsingleton_image_iff

/- warning: function.surjective.image_preimage -> Function.Surjective.image_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (Set.preimage.{u1, u2} α β f s)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (Set.preimage.{u2, u1} α β f s)) s)
Case conversion may be inaccurate. Consider using '#align function.surjective.image_preimage Function.Surjective.image_preimageₓ'. -/
theorem Surjective.image_preimage (hf : Surjective f) (s : Set β) : f '' (f ⁻¹' s) = s :=
  image_preimage_eq s hf
#align function.surjective.image_preimage Function.Surjective.image_preimage

/- warning: function.surjective.image_surjective -> Function.Surjective.image_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (Function.Surjective.{succ u1, succ u2} (Set.{u1} α) (Set.{u2} β) (Set.image.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (Function.Surjective.{succ u2, succ u1} (Set.{u2} α) (Set.{u1} β) (Set.image.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align function.surjective.image_surjective Function.Surjective.image_surjectiveₓ'. -/
theorem Surjective.image_surjective (hf : Surjective f) : Surjective (image f) :=
  by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]
#align function.surjective.image_surjective Function.Surjective.image_surjective

/- warning: function.surjective.nonempty_preimage -> Function.Surjective.nonempty_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (forall {s : Set.{u2} β}, Iff (Set.Nonempty.{u1} α (Set.preimage.{u1, u2} α β f s)) (Set.Nonempty.{u2} β s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (forall {s : Set.{u1} β}, Iff (Set.Nonempty.{u2} α (Set.preimage.{u2, u1} α β f s)) (Set.Nonempty.{u1} β s))
Case conversion may be inaccurate. Consider using '#align function.surjective.nonempty_preimage Function.Surjective.nonempty_preimageₓ'. -/
theorem Surjective.nonempty_preimage (hf : Surjective f) {s : Set β} :
    (f ⁻¹' s).Nonempty ↔ s.Nonempty := by rw [← nonempty_image_iff, hf.image_preimage]
#align function.surjective.nonempty_preimage Function.Surjective.nonempty_preimage

/- warning: function.injective.image_injective -> Function.Injective.image_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Function.Injective.{succ u1, succ u2} (Set.{u1} α) (Set.{u2} β) (Set.image.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Function.Injective.{succ u2, succ u1} (Set.{u2} α) (Set.{u1} β) (Set.image.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align function.injective.image_injective Function.Injective.image_injectiveₓ'. -/
theorem Injective.image_injective (hf : Injective f) : Injective (image f) :=
  by
  intro s t h
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, h]
#align function.injective.image_injective Function.Injective.image_injective

#print Function.Surjective.preimage_subset_preimage_iff /-
theorem Surjective.preimage_subset_preimage_iff {s t : Set β} (hf : Surjective f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
  by
  apply preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ
#align function.surjective.preimage_subset_preimage_iff Function.Surjective.preimage_subset_preimage_iff
-/

/- warning: function.surjective.range_comp -> Function.Surjective.range_comp is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {ι' : Sort.{u3}} {f : ι -> ι'}, (Function.Surjective.{u1, u3} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u2} (Set.{u2} α) (Set.range.{u2, u1} α ι (Function.comp.{u1, u3, succ u2} ι ι' α g f)) (Set.range.{u2, u3} α ι' g))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} {ι' : Sort.{u3}} {f : ι -> ι'}, (Function.Surjective.{u2, u3} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, u2} α ι (Function.comp.{u2, u3, succ u1} ι ι' α g f)) (Set.range.{u1, u3} α ι' g))
Case conversion may be inaccurate. Consider using '#align function.surjective.range_comp Function.Surjective.range_compₓ'. -/
theorem Surjective.range_comp {ι' : Sort _} {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    range (g ∘ f) = range g :=
  ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm
#align function.surjective.range_comp Function.Surjective.range_comp

/- warning: function.injective.mem_range_iff_exists_unique -> Function.Injective.mem_range_iff_exists_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {b : β}, Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α f)) (ExistsUnique.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {b : β}, Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b (Set.range.{u1, succ u2} β α f)) (ExistsUnique.{succ u2} α (fun (a : α) => Eq.{succ u1} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align function.injective.mem_range_iff_exists_unique Function.Injective.mem_range_iff_exists_uniqueₓ'. -/
theorem Injective.mem_range_iff_exists_unique (hf : Injective f) {b : β} :
    b ∈ range f ↔ ∃! a, f a = b :=
  ⟨fun ⟨a, h⟩ => ⟨a, h, fun a' ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩
#align function.injective.mem_range_iff_exists_unique Function.Injective.mem_range_iff_exists_unique

/- warning: function.injective.exists_unique_of_mem_range -> Function.Injective.exists_unique_of_mem_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {b : β}, (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α f)) -> (ExistsUnique.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {b : β}, (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b (Set.range.{u1, succ u2} β α f)) -> (ExistsUnique.{succ u2} α (fun (a : α) => Eq.{succ u1} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align function.injective.exists_unique_of_mem_range Function.Injective.exists_unique_of_mem_rangeₓ'. -/
theorem Injective.exists_unique_of_mem_range (hf : Injective f) {b : β} (hb : b ∈ range f) :
    ∃! a, f a = b :=
  hf.mem_range_iff_exists_unique.mp hb
#align function.injective.exists_unique_of_mem_range Function.Injective.exists_unique_of_mem_range

/- warning: function.injective.compl_image_eq -> Function.Injective.compl_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.image.{u1, u2} α β f s)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.image.{u1, u2} α β f (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β α f))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) (Set.image.{u2, u1} α β f s)) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.image.{u2, u1} α β f (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) (Set.range.{u1, succ u2} β α f))))
Case conversion may be inaccurate. Consider using '#align function.injective.compl_image_eq Function.Injective.compl_image_eqₓ'. -/
theorem Injective.compl_image_eq (hf : Injective f) (s : Set α) : (f '' s)ᶜ = f '' sᶜ ∪ range fᶜ :=
  by
  ext y
  rcases em (y ∈ range f) with (⟨x, rfl⟩ | hx)
  · simp [hf.eq_iff]
  · rw [mem_range, not_exists] at hx
    simp [hx]
#align function.injective.compl_image_eq Function.Injective.compl_image_eq

/- warning: function.left_inverse.image_image -> Function.LeftInverse.image_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u1, succ u2} α β g f) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α g (Set.image.{u1, u2} α β f s)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u2, succ u1} α β g f) -> (forall (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α g (Set.image.{u2, u1} α β f s)) s)
Case conversion may be inaccurate. Consider using '#align function.left_inverse.image_image Function.LeftInverse.image_imageₓ'. -/
theorem LeftInverse.image_image {g : β → α} (h : LeftInverse g f) (s : Set α) : g '' (f '' s) = s :=
  by rw [← image_comp, h.comp_eq_id, image_id]
#align function.left_inverse.image_image Function.LeftInverse.image_image

/- warning: function.left_inverse.preimage_preimage -> Function.LeftInverse.preimage_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u1, succ u2} α β g f) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f (Set.preimage.{u2, u1} β α g s)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : β -> α}, (Function.LeftInverse.{succ u2, succ u1} α β g f) -> (forall (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β f (Set.preimage.{u1, u2} β α g s)) s)
Case conversion may be inaccurate. Consider using '#align function.left_inverse.preimage_preimage Function.LeftInverse.preimage_preimageₓ'. -/
theorem LeftInverse.preimage_preimage {g : β → α} (h : LeftInverse g f) (s : Set α) :
    f ⁻¹' (g ⁻¹' s) = s := by rw [← preimage_comp, h.comp_eq_id, preimage_id]
#align function.left_inverse.preimage_preimage Function.LeftInverse.preimage_preimage

end Function

/-! ### Image and preimage on subtypes -/


namespace Subtype

open Set

variable {α : Type _}

#print Subtype.coe_image /-
theorem coe_image {p : α → Prop} {s : Set (Subtype p)} :
    coe '' s = { x | ∃ h : p x, (⟨x, h⟩ : Subtype p) ∈ s } :=
  Set.ext fun a =>
    ⟨fun ⟨⟨a', ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩
#align subtype.coe_image Subtype.coe_image
-/

#print Subtype.coe_image_of_subset /-
@[simp]
theorem coe_image_of_subset {s t : Set α} (h : t ⊆ s) : coe '' { x : ↥s | ↑x ∈ t } = t :=
  by
  ext x
  rw [Set.mem_image]
  exact ⟨fun ⟨x', hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩
#align subtype.coe_image_of_subset Subtype.coe_image_of_subset
-/

#print Subtype.range_coe /-
theorem range_coe {s : Set α} : range (coe : s → α) = s :=
  by
  rw [← Set.image_univ]
  simp [-Set.image_univ, coe_image]
#align subtype.range_coe Subtype.range_coe
-/

#print Subtype.range_val /-
/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
theorem range_val {s : Set α} : range (Subtype.val : s → α) = s :=
  range_coe
#align subtype.range_val Subtype.range_val
-/

#print Subtype.range_coe_subtype /-
/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : set α` the function `coe : s → α`, then the inferred implicit arguments of `coe` are
  `coe α (λ x, x ∈ s)`. -/
@[simp]
theorem range_coe_subtype {p : α → Prop} : range (coe : Subtype p → α) = { x | p x } :=
  range_coe
#align subtype.range_coe_subtype Subtype.range_coe_subtype
-/

#print Subtype.coe_preimage_self /-
@[simp]
theorem coe_preimage_self (s : Set α) : (coe : s → α) ⁻¹' s = univ := by
  rw [← preimage_range (coe : s → α), range_coe]
#align subtype.coe_preimage_self Subtype.coe_preimage_self
-/

#print Subtype.range_val_subtype /-
theorem range_val_subtype {p : α → Prop} : range (Subtype.val : Subtype p → α) = { x | p x } :=
  range_coe
#align subtype.range_val_subtype Subtype.range_val_subtype
-/

#print Subtype.coe_image_subset /-
theorem coe_image_subset (s : Set α) (t : Set s) : coe '' t ⊆ s := fun x ⟨y, yt, yvaleq⟩ => by
  rw [← yvaleq] <;> exact y.property
#align subtype.coe_image_subset Subtype.coe_image_subset
-/

#print Subtype.coe_image_univ /-
theorem coe_image_univ (s : Set α) : (coe : s → α) '' Set.univ = s :=
  image_univ.trans range_coe
#align subtype.coe_image_univ Subtype.coe_image_univ
-/

/- warning: subtype.image_preimage_coe -> Subtype.image_preimage_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align subtype.image_preimage_coe Subtype.image_preimage_coeₓ'. -/
@[simp]
theorem image_preimage_coe (s t : Set α) : (coe : s → α) '' (coe ⁻¹' t) = t ∩ s :=
  image_preimage_eq_inter_range.trans <| congr_arg _ range_coe
#align subtype.image_preimage_coe Subtype.image_preimage_coe

/- warning: subtype.image_preimage_val -> Subtype.image_preimage_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) (Set.preimage.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) (Set.preimage.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align subtype.image_preimage_val Subtype.image_preimage_valₓ'. -/
theorem image_preimage_val (s t : Set α) : (Subtype.val : s → α) '' (Subtype.val ⁻¹' t) = t ∩ s :=
  image_preimage_coe s t
#align subtype.image_preimage_val Subtype.image_preimage_val

/- warning: subtype.preimage_coe_eq_preimage_coe_iff -> Subtype.preimage_coe_eq_preimage_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) u)) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} (Set.Elem.{u1} α s)) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) t) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) u)) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u s))
Case conversion may be inaccurate. Consider using '#align subtype.preimage_coe_eq_preimage_coe_iff Subtype.preimage_coe_eq_preimage_coe_iffₓ'. -/
theorem preimage_coe_eq_preimage_coe_iff {s t u : Set α} :
    (coe : s → α) ⁻¹' t = coe ⁻¹' u ↔ t ∩ s = u ∩ s := by
  rw [← image_preimage_coe, ← image_preimage_coe, coe_injective.image_injective.eq_iff]
#align subtype.preimage_coe_eq_preimage_coe_iff Subtype.preimage_coe_eq_preimage_coe_iff

/- warning: subtype.preimage_coe_inter_self -> Subtype.preimage_coe_inter_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Set.Elem.{u1} α s)) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) t)
Case conversion may be inaccurate. Consider using '#align subtype.preimage_coe_inter_self Subtype.preimage_coe_inter_selfₓ'. -/
@[simp]
theorem preimage_coe_inter_self (s t : Set α) : (coe : s → α) ⁻¹' (t ∩ s) = coe ⁻¹' t := by
  rw [preimage_coe_eq_preimage_coe_iff, inter_assoc, inter_self]
#align subtype.preimage_coe_inter_self Subtype.preimage_coe_inter_self

/- warning: subtype.preimage_val_eq_preimage_val_iff -> Subtype.preimage_val_eq_preimage_val_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Iff (Eq.{succ u1} (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))) (Set.preimage.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) t) (Set.preimage.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) u)) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Iff (Eq.{succ u1} (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (Set.preimage.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t) (Set.preimage.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) u)) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u s))
Case conversion may be inaccurate. Consider using '#align subtype.preimage_val_eq_preimage_val_iff Subtype.preimage_val_eq_preimage_val_iffₓ'. -/
theorem preimage_val_eq_preimage_val_iff (s t u : Set α) :
    (Subtype.val : s → α) ⁻¹' t = Subtype.val ⁻¹' u ↔ t ∩ s = u ∩ s :=
  preimage_coe_eq_preimage_coe_iff
#align subtype.preimage_val_eq_preimage_val_iff Subtype.preimage_val_eq_preimage_val_iff

#print Subtype.exists_set_subtype /-
theorem exists_set_subtype {t : Set α} (p : Set α → Prop) :
    (∃ s : Set t, p (coe '' s)) ↔ ∃ s : Set α, s ⊆ t ∧ p s :=
  by
  constructor
  · rintro ⟨s, hs⟩
    refine' ⟨coe '' s, _, hs⟩
    convert image_subset_range _ _
    rw [range_coe]
  rintro ⟨s, hs₁, hs₂⟩; refine' ⟨coe ⁻¹' s, _⟩
  rw [image_preimage_eq_of_subset]; exact hs₂; rw [range_coe]; exact hs₁
#align subtype.exists_set_subtype Subtype.exists_set_subtype
-/

/- warning: subtype.preimage_coe_nonempty -> Subtype.preimage_coe_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} (Set.Elem.{u1} α s) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) t)) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align subtype.preimage_coe_nonempty Subtype.preimage_coe_nonemptyₓ'. -/
theorem preimage_coe_nonempty {s t : Set α} : ((coe : s → α) ⁻¹' t).Nonempty ↔ (s ∩ t).Nonempty :=
  by rw [inter_comm, ← image_preimage_coe, nonempty_image_iff]
#align subtype.preimage_coe_nonempty Subtype.preimage_coe_nonempty

/- warning: subtype.preimage_coe_eq_empty -> Subtype.preimage_coe_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.hasEmptyc.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)))) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} (Set.Elem.{u1} α s)) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Set.Elem.{u1} α s)) (Set.instEmptyCollectionSet.{u1} (Set.Elem.{u1} α s)))) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align subtype.preimage_coe_eq_empty Subtype.preimage_coe_eq_emptyₓ'. -/
theorem preimage_coe_eq_empty {s t : Set α} : (coe : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ := by
  simp only [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]
#align subtype.preimage_coe_eq_empty Subtype.preimage_coe_eq_empty

/- warning: subtype.preimage_coe_compl -> Subtype.preimage_coe_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Set.hasEmptyc.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Set.Elem.{u1} α s)) (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (fun (x : Set.Elem.{u1} α s) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Set.Elem.{u1} α s)) (Set.instEmptyCollectionSet.{u1} (Set.Elem.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align subtype.preimage_coe_compl Subtype.preimage_coe_complₓ'. -/
@[simp]
theorem preimage_coe_compl (s : Set α) : (coe : s → α) ⁻¹' sᶜ = ∅ :=
  preimage_coe_eq_empty.2 (inter_compl_self s)
#align subtype.preimage_coe_compl Subtype.preimage_coe_compl

/- warning: subtype.preimage_coe_compl' -> Subtype.preimage_coe_compl' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))))))) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Set.hasEmptyc.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Set.preimage.{u1, u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) α (fun (x : Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) x) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Set.instEmptyCollectionSet.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))))
Case conversion may be inaccurate. Consider using '#align subtype.preimage_coe_compl' Subtype.preimage_coe_compl'ₓ'. -/
@[simp]
theorem preimage_coe_compl' (s : Set α) : (coe : sᶜ → α) ⁻¹' s = ∅ :=
  preimage_coe_eq_empty.2 (compl_inter_self s)
#align subtype.preimage_coe_compl' Subtype.preimage_coe_compl'

end Subtype

/-! ### Images and preimages on `option` -/


open Set

namespace Option

/- warning: option.injective_iff -> Option.injective_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : (Option.{u1} α) -> β}, Iff (Function.Injective.{succ u1, succ u2} (Option.{u1} α) β f) (And (Function.Injective.{succ u1, succ u2} α β (Function.comp.{succ u1, succ u1, succ u2} α (Option.{u1} α) β f (Option.some.{u1} α))) (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f (Option.none.{u1} α)) (Set.range.{u2, succ u1} β α (Function.comp.{succ u1, succ u1, succ u2} α (Option.{u1} α) β f (Option.some.{u1} α))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : (Option.{u2} α) -> β}, Iff (Function.Injective.{succ u2, succ u1} (Option.{u2} α) β f) (And (Function.Injective.{succ u2, succ u1} α β (Function.comp.{succ u2, succ u2, succ u1} α (Option.{u2} α) β f (Option.some.{u2} α))) (Not (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f (Option.none.{u2} α)) (Set.range.{u1, succ u2} β α (Function.comp.{succ u2, succ u2, succ u1} α (Option.{u2} α) β f (Option.some.{u2} α))))))
Case conversion may be inaccurate. Consider using '#align option.injective_iff Option.injective_iffₓ'. -/
theorem injective_iff {α β} {f : Option α → β} :
    Injective f ↔ Injective (f ∘ some) ∧ f none ∉ range (f ∘ some) :=
  by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine'
    ⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.Ne <| Option.some_ne_none _⟩, _⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts[rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]
#align option.injective_iff Option.injective_iff

/- warning: option.range_eq -> Option.range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : (Option.{u1} α) -> β), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β (Option.{u1} α) f) (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) (f (Option.none.{u1} α)) (Set.range.{u2, succ u1} β α (Function.comp.{succ u1, succ u1, succ u2} α (Option.{u1} α) β f (Option.some.{u1} α))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : (Option.{u2} α) -> β), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, succ u2} β (Option.{u2} α) f) (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) (f (Option.none.{u2} α)) (Set.range.{u1, succ u2} β α (Function.comp.{succ u2, succ u2, succ u1} α (Option.{u2} α) β f (Option.some.{u2} α))))
Case conversion may be inaccurate. Consider using '#align option.range_eq Option.range_eqₓ'. -/
theorem range_eq {α β} (f : Option α → β) : range f = insert (f none) (range (f ∘ some)) :=
  Set.ext fun y => Option.exists.trans <| eq_comm.Or Iff.rfl
#align option.range_eq Option.range_eq

end Option

/- warning: with_bot.range_eq -> WithBot.range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : (WithBot.{u1} α) -> β), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β (WithBot.{u1} α) f) (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) (f (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Set.range.{u2, succ u1} β α (Function.comp.{succ u1, succ u1, succ u2} α (WithBot.{u1} α) β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : (WithBot.{u2} α) -> β), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, succ u2} β (WithBot.{u2} α) f) (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) (f (Bot.bot.{u2} (WithBot.{u2} α) (WithBot.bot.{u2} α))) (Set.range.{u1, succ u2} β α (Function.comp.{succ u2, succ u2, succ u1} α (WithBot.{u2} α) β f (WithBot.some.{u2} α))))
Case conversion may be inaccurate. Consider using '#align with_bot.range_eq WithBot.range_eqₓ'. -/
theorem WithBot.range_eq {α β} (f : WithBot α → β) :
    range f = insert (f ⊥) (range (f ∘ coe : α → β)) :=
  Option.range_eq f
#align with_bot.range_eq WithBot.range_eq

/- warning: with_top.range_eq -> WithTop.range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : (WithTop.{u1} α) -> β), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β (WithTop.{u1} α) f) (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) (f (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Set.range.{u2, succ u1} β α (Function.comp.{succ u1, succ u1, succ u2} α (WithTop.{u1} α) β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : (WithTop.{u2} α) -> β), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, succ u2} β (WithTop.{u2} α) f) (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) (f (Top.top.{u2} (WithTop.{u2} α) (WithTop.top.{u2} α))) (Set.range.{u1, succ u2} β α (Function.comp.{succ u2, succ u2, succ u1} α (WithTop.{u2} α) β f (WithBot.some.{u2} α))))
Case conversion may be inaccurate. Consider using '#align with_top.range_eq WithTop.range_eqₓ'. -/
theorem WithTop.range_eq {α β} (f : WithTop α → β) :
    range f = insert (f ⊤) (range (f ∘ coe : α → β)) :=
  Option.range_eq f
#align with_top.range_eq WithTop.range_eq

namespace Set

open Function

/-! ### Injectivity and surjectivity lemmas for image and preimage -/


section ImagePreimage

variable {α : Type u} {β : Type v} {f : α → β}

#print Set.preimage_injective /-
@[simp]
theorem preimage_injective : Injective (preimage f) ↔ Surjective f :=
  by
  refine' ⟨fun h y => _, surjective.preimage_injective⟩
  obtain ⟨x, hx⟩ : (f ⁻¹' {y}).Nonempty :=
    by
    rw [h.nonempty_apply_iff preimage_empty]
    apply singleton_nonempty
  exact ⟨x, hx⟩
#align set.preimage_injective Set.preimage_injective
-/

#print Set.preimage_surjective /-
@[simp]
theorem preimage_surjective : Surjective (preimage f) ↔ Injective f :=
  by
  refine' ⟨fun h x x' hx => _, injective.preimage_surjective⟩
  cases' h {x} with s hs; have := mem_singleton x
  rwa [← hs, mem_preimage, hx, ← mem_preimage, hs, mem_singleton_iff, eq_comm] at this
#align set.preimage_surjective Set.preimage_surjective
-/

#print Set.image_surjective /-
@[simp]
theorem image_surjective : Surjective (image f) ↔ Surjective f :=
  by
  refine' ⟨fun h y => _, surjective.image_surjective⟩
  cases' h {y} with s hs
  have := mem_singleton y; rw [← hs] at this; rcases this with ⟨x, h1x, h2x⟩
  exact ⟨x, h2x⟩
#align set.image_surjective Set.image_surjective
-/

#print Set.image_injective /-
@[simp]
theorem image_injective : Injective (image f) ↔ Injective f :=
  by
  refine' ⟨fun h x x' hx => _, injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]; apply h
  rw [image_singleton, image_singleton, hx]
#align set.image_injective Set.image_injective
-/

#print Set.preimage_eq_iff_eq_image /-
theorem preimage_eq_iff_eq_image {f : α → β} (hf : Bijective f) {s t} : f ⁻¹' s = t ↔ s = f '' t :=
  by rw [← image_eq_image hf.1, hf.2.image_preimage]
#align set.preimage_eq_iff_eq_image Set.preimage_eq_iff_eq_image
-/

#print Set.eq_preimage_iff_image_eq /-
theorem eq_preimage_iff_image_eq {f : α → β} (hf : Bijective f) {s t} : s = f ⁻¹' t ↔ f '' s = t :=
  by rw [← image_eq_image hf.1, hf.2.image_preimage]
#align set.eq_preimage_iff_image_eq Set.eq_preimage_iff_image_eq
-/

end ImagePreimage

end Set

/-! ### Disjoint lemmas for image and preimage -/


section Disjoint

variable {α β γ : Type _} {f : α → β} {s t : Set α}

/- warning: disjoint.preimage -> Disjoint.preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) {s : Set.{u2} β} {t : Set.{u2} β}, (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) {s : Set.{u2} β} {t : Set.{u2} β}, (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t))
Case conversion may be inaccurate. Consider using '#align disjoint.preimage Disjoint.preimageₓ'. -/
theorem Disjoint.preimage (f : α → β) {s t : Set β} (h : Disjoint s t) :
    Disjoint (f ⁻¹' s) (f ⁻¹' t) :=
  disjoint_iff_inf_le.mpr fun x hx => h.le_bot hx
#align disjoint.preimage Disjoint.preimage

namespace Set

/- warning: set.disjoint_image_image -> Set.disjoint_image_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : β -> α} {g : γ -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, (forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s) -> (forall (c : γ), (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c t) -> (Ne.{succ u1} α (f b) (g c)))) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.image.{u2, u1} β α f s) (Set.image.{u3, u1} γ α g t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {f : β -> α} {g : γ -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, (forall (b : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b s) -> (forall (c : γ), (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) c t) -> (Ne.{succ u1} α (f b) (g c)))) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Set.image.{u3, u1} β α f s) (Set.image.{u2, u1} γ α g t))
Case conversion may be inaccurate. Consider using '#align set.disjoint_image_image Set.disjoint_image_imageₓ'. -/
theorem disjoint_image_image {f : β → α} {g : γ → α} {s : Set β} {t : Set γ}
    (h : ∀ b ∈ s, ∀ c ∈ t, f b ≠ g c) : Disjoint (f '' s) (g '' t) :=
  disjoint_iff_inf_le.mpr <| by rintro a ⟨⟨b, hb, eq⟩, c, hc, rfl⟩ <;> exact h b hb c hc Eq
#align set.disjoint_image_image Set.disjoint_image_image

/- warning: set.disjoint_image_of_injective -> Set.disjoint_image_of_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall {s : Set.{u2} α} {t : Set.{u2} α}, (Disjoint.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) s t) -> (Disjoint.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_image_of_injective Set.disjoint_image_of_injectiveₓ'. -/
theorem disjoint_image_of_injective {f : α → β} (hf : Injective f) {s t : Set α}
    (hd : Disjoint s t) : Disjoint (f '' s) (f '' t) :=
  disjoint_image_image fun x hx y hy => hf.Ne fun H => Set.disjoint_iff.1 hd ⟨hx, H.symm ▸ hy⟩
#align set.disjoint_image_of_injective Set.disjoint_image_of_injective

/- warning: disjoint.of_image -> Disjoint.of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t)
Case conversion may be inaccurate. Consider using '#align disjoint.of_image Disjoint.of_imageₓ'. -/
theorem Disjoint.of_image (h : Disjoint (f '' s) (f '' t)) : Disjoint s t :=
  disjoint_iff_inf_le.mpr fun x hx =>
    disjoint_left.1 h (mem_image_of_mem _ hx.1) (mem_image_of_mem _ hx.2)
#align disjoint.of_image Disjoint.of_image

/- warning: set.disjoint_image_iff -> Set.disjoint_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (Function.Injective.{succ u1, succ u2} α β f) -> (Iff (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) (Set.image.{u1, u2} α β f s) (Set.image.{u1, u2} α β f t)) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (Function.Injective.{succ u2, succ u1} α β f) -> (Iff (Disjoint.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))) (Set.image.{u2, u1} α β f s) (Set.image.{u2, u1} α β f t)) (Disjoint.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) s t))
Case conversion may be inaccurate. Consider using '#align set.disjoint_image_iff Set.disjoint_image_iffₓ'. -/
theorem disjoint_image_iff (hf : Injective f) : Disjoint (f '' s) (f '' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_image, disjoint_image_of_injective hf⟩
#align set.disjoint_image_iff Set.disjoint_image_iff

/- warning: disjoint.of_preimage -> Disjoint.of_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (forall {s : Set.{u2} β} {t : Set.{u2} β}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t)) -> (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (forall {s : Set.{u1} β} {t : Set.{u1} β}, (Disjoint.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) (Set.preimage.{u2, u1} α β f s) (Set.preimage.{u2, u1} α β f t)) -> (Disjoint.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))) s t))
Case conversion may be inaccurate. Consider using '#align disjoint.of_preimage Disjoint.of_preimageₓ'. -/
theorem Disjoint.of_preimage (hf : Surjective f) {s t : Set β} (h : Disjoint (f ⁻¹' s) (f ⁻¹' t)) :
    Disjoint s t := by
  rw [disjoint_iff_inter_eq_empty, ← image_preimage_eq (_ ∩ _) hf, preimage_inter, h.inter_eq,
    image_empty]
#align disjoint.of_preimage Disjoint.of_preimage

/- warning: set.disjoint_preimage_iff -> Set.disjoint_preimage_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (forall {s : Set.{u2} β} {t : Set.{u2} β}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u1, u2} α β f t)) (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (forall {s : Set.{u1} β} {t : Set.{u1} β}, Iff (Disjoint.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α))) (Set.preimage.{u2, u1} α β f s) (Set.preimage.{u2, u1} α β f t)) (Disjoint.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β))) s t))
Case conversion may be inaccurate. Consider using '#align set.disjoint_preimage_iff Set.disjoint_preimage_iffₓ'. -/
theorem disjoint_preimage_iff (hf : Surjective f) {s t : Set β} :
    Disjoint (f ⁻¹' s) (f ⁻¹' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_preimage hf, Disjoint.preimage _⟩
#align set.disjoint_preimage_iff Set.disjoint_preimage_iff

/- warning: set.preimage_eq_empty -> Set.preimage_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) s (Set.range.{u2, succ u1} β α f)) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))) s (Set.range.{u2, succ u1} β α f)) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.preimage_eq_empty Set.preimage_eq_emptyₓ'. -/
theorem preimage_eq_empty {f : α → β} {s : Set β} (h : Disjoint s (range f)) : f ⁻¹' s = ∅ := by
  simpa using h.preimage f
#align set.preimage_eq_empty Set.preimage_eq_empty

/- warning: set.preimage_eq_empty_iff -> Set.preimage_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) s (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {s : Set.{u2} β}, Iff (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β f s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))) s (Set.range.{u2, succ u1} β α f))
Case conversion may be inaccurate. Consider using '#align set.preimage_eq_empty_iff Set.preimage_eq_empty_iffₓ'. -/
theorem preimage_eq_empty_iff {s : Set β} : f ⁻¹' s = ∅ ↔ Disjoint s (range f) :=
  ⟨fun h =>
    by
    simp only [eq_empty_iff_forall_not_mem, disjoint_iff_inter_eq_empty, not_exists, mem_inter_iff,
      not_and, mem_range, mem_preimage] at h⊢
    intro y hy x hx
    rw [← hx] at hy
    exact h x hy, preimage_eq_empty⟩
#align set.preimage_eq_empty_iff Set.preimage_eq_empty_iff

end Set

end Disjoint

