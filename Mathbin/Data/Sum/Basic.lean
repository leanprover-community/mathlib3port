/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov

! This file was ported from Lean 3 source module data.sum.basic
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Function.Basic
import Mathbin.Tactic.Basic

/-!
# Disjoint union of types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic results about the sum type `α ⊕ β`.

`α ⊕ β` is the type made of a copy of `α` and a copy of `β`. It is also called *disjoint union*.

## Main declarations

* `sum.get_left`: Retrieves the left content of `x : α ⊕ β` or returns `none` if it's coming from
  the right.
* `sum.get_right`: Retrieves the right content of `x : α ⊕ β` or returns `none` if it's coming from
  the left.
* `sum.is_left`: Returns whether `x : α ⊕ β` comes from the left component or not.
* `sum.is_right`: Returns whether `x : α ⊕ β` comes from the right component or not.
* `sum.map`: Maps `α ⊕ β` to `γ ⊕ δ` component-wise.
* `sum.elim`: Nondependent eliminator/induction principle for `α ⊕ β`.
* `sum.swap`: Maps `α ⊕ β` to `β ⊕ α` by swapping components.
* `sum.lex`: Lexicographic order on `α ⊕ β` induced by a relation on `α` and a relation on `β`.

## Notes

The definition of `sum` takes values in `Type*`. This effectively forbids `Prop`- valued sum types.
To this effect, we have `psum`, which takes value in `Sort*` and carries a more complicated
universe signature in consequence. The `Prop` version is `or`.
-/


universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type _}

namespace Sum

deriving instance DecidableEq for Sum

#print Sum.forall /-
@[simp]
theorem forall {p : Sum α β → Prop} : (∀ x, p x) ↔ (∀ a, p (inl a)) ∧ ∀ b, p (inr b) :=
  ⟨fun h => ⟨fun a => h _, fun b => h _⟩, fun ⟨h₁, h₂⟩ => Sum.rec h₁ h₂⟩
#align sum.forall Sum.forall
-/

#print Sum.exists /-
@[simp]
theorem exists {p : Sum α β → Prop} : (∃ x, p x) ↔ (∃ a, p (inl a)) ∨ ∃ b, p (inr b) :=
  ⟨fun h =>
    match h with
    | ⟨inl a, h⟩ => Or.inl ⟨a, h⟩
    | ⟨inr b, h⟩ => Or.inr ⟨b, h⟩,
    fun h =>
    match h with
    | Or.inl ⟨a, h⟩ => ⟨inl a, h⟩
    | Or.inr ⟨b, h⟩ => ⟨inr b, h⟩⟩
#align sum.exists Sum.exists
-/

#print Sum.inl_injective /-
theorem inl_injective : Function.Injective (inl : α → Sum α β) := fun x y => inl.inj
#align sum.inl_injective Sum.inl_injective
-/

#print Sum.inr_injective /-
theorem inr_injective : Function.Injective (inr : β → Sum α β) := fun x y => inr.inj
#align sum.inr_injective Sum.inr_injective
-/

section get

#print Sum.getLeft /-
/-- Check if a sum is `inl` and if so, retrieve its contents. -/
@[simp]
def getLeft : Sum α β → Option α
  | inl a => some a
  | inr _ => none
#align sum.get_left Sum.getLeft
-/

#print Sum.getRight /-
/-- Check if a sum is `inr` and if so, retrieve its contents. -/
@[simp]
def getRight : Sum α β → Option β
  | inr b => some b
  | inl _ => none
#align sum.get_right Sum.getRight
-/

#print Sum.isLeft /-
/-- Check if a sum is `inl`. -/
@[simp]
def isLeft : Sum α β → Bool
  | inl _ => true
  | inr _ => false
#align sum.is_left Sum.isLeft
-/

#print Sum.isRight /-
/-- Check if a sum is `inr`. -/
@[simp]
def isRight : Sum α β → Bool
  | inl _ => false
  | inr _ => true
#align sum.is_right Sum.isRight
-/

variable {x y : Sum α β}

#print Sum.getLeft_eq_none_iff /-
@[simp]
theorem getLeft_eq_none_iff : x.getLeft = none ↔ x.isRight := by
  cases x <;>
    simp only [get_left, is_right, Bool.coe_sort_true, Bool.coe_sort_false, eq_self_iff_true]
#align sum.get_left_eq_none_iff Sum.getLeft_eq_none_iff
-/

#print Sum.getRight_eq_none_iff /-
@[simp]
theorem getRight_eq_none_iff : x.getRight = none ↔ x.isLeft := by
  cases x <;>
    simp only [get_right, is_left, Bool.coe_sort_true, Bool.coe_sort_false, eq_self_iff_true]
#align sum.get_right_eq_none_iff Sum.getRight_eq_none_iff
-/

#print Sum.getLeft_eq_some_iff /-
@[simp]
theorem getLeft_eq_some_iff {a} : x.getLeft = some a ↔ x = inl a := by
  cases x <;> simp only [get_left]
#align sum.get_left_eq_some_iff Sum.getLeft_eq_some_iff
-/

#print Sum.getRight_eq_some_iff /-
@[simp]
theorem getRight_eq_some_iff {b} : x.getRight = some b ↔ x = inr b := by
  cases x <;> simp only [get_right]
#align sum.get_right_eq_some_iff Sum.getRight_eq_some_iff
-/

#print Sum.not_isLeft /-
@[simp]
theorem not_isLeft (x : Sum α β) : not x.isLeft = x.isRight := by cases x <;> rfl
#align sum.bnot_is_left Sum.not_isLeft
-/

#print Sum.isLeft_eq_false /-
@[simp]
theorem isLeft_eq_false : x.isLeft = false ↔ x.isRight := by cases x <;> simp
#align sum.is_left_eq_ff Sum.isLeft_eq_false
-/

#print Sum.Not_isLeft /-
theorem Not_isLeft : ¬x.isLeft ↔ x.isRight := by simp
#align sum.not_is_left Sum.Not_isLeft
-/

/- warning: sum.bnot_is_right -> Sum.not_isRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (x : Sum.{u1, u2} α β), Eq.{1} Bool (not (Sum.isRight.{u1, u2} α β x)) (Sum.isLeft.{u1, u2} α β x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (x : Sum.{u1, u2} α β), Eq.{1} Bool (not (Decidable.decide (Eq.{1} Bool (Sum.isRight.{u1, u2} α β x) (Sum.isLeft.{u1, u2} α β x)) (instDecidableEqBool (Sum.isRight.{u1, u2} α β x) (Sum.isLeft.{u1, u2} α β x)))) Bool.true
Case conversion may be inaccurate. Consider using '#align sum.bnot_is_right Sum.not_isRightₓ'. -/
@[simp]
theorem not_isRight (x : Sum α β) : not x.isRight = x.isLeft := by cases x <;> rfl
#align sum.bnot_is_right Sum.not_isRight

#print Sum.isRight_eq_false /-
@[simp]
theorem isRight_eq_false : x.isRight = false ↔ x.isLeft := by cases x <;> simp
#align sum.is_right_eq_ff Sum.isRight_eq_false
-/

#print Sum.Not_isRight /-
theorem Not_isRight : ¬x.isRight ↔ x.isLeft := by simp
#align sum.not_is_right Sum.Not_isRight
-/

#print Sum.isLeft_iff /-
theorem isLeft_iff : x.isLeft ↔ ∃ y, x = Sum.inl y := by cases x <;> simp
#align sum.is_left_iff Sum.isLeft_iff
-/

#print Sum.isRight_iff /-
theorem isRight_iff : x.isRight ↔ ∃ y, x = Sum.inr y := by cases x <;> simp
#align sum.is_right_iff Sum.isRight_iff
-/

end get

#print Sum.inl.inj_iff /-
theorem inl.inj_iff {a b} : (inl a : Sum α β) = inl b ↔ a = b :=
  ⟨inl.inj, congr_arg _⟩
#align sum.inl.inj_iff Sum.inl.inj_iff
-/

#print Sum.inr.inj_iff /-
theorem inr.inj_iff {a b} : (inr a : Sum α β) = inr b ↔ a = b :=
  ⟨inr.inj, congr_arg _⟩
#align sum.inr.inj_iff Sum.inr.inj_iff
-/

#print Sum.inl_ne_inr /-
theorem inl_ne_inr {a : α} {b : β} : inl a ≠ inr b :=
  fun.
#align sum.inl_ne_inr Sum.inl_ne_inr
-/

#print Sum.inr_ne_inl /-
theorem inr_ne_inl {a : α} {b : β} : inr b ≠ inl a :=
  fun.
#align sum.inr_ne_inl Sum.inr_ne_inl
-/

#print Sum.elim /-
/-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`. -/
protected def elim {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum α β → γ := fun x =>
  Sum.recOn x f g
#align sum.elim Sum.elim
-/

/- warning: sum.elim_inl -> Sum.elim_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Sort.{u3}} (f : α -> γ) (g : β -> γ) (x : α), Eq.{u3} γ (Sum.elim.{u1, u2, u3} α β γ f g (Sum.inl.{u1, u2} α β x)) (f x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Sort.{u1}} (f : α -> γ) (g : β -> γ) (x : α), Eq.{u1} γ (Sum.elim.{u3, u2, u1} α β γ f g (Sum.inl.{u3, u2} α β x)) (f x)
Case conversion may be inaccurate. Consider using '#align sum.elim_inl Sum.elim_inlₓ'. -/
@[simp]
theorem elim_inl {α β γ : Sort _} (f : α → γ) (g : β → γ) (x : α) : Sum.elim f g (inl x) = f x :=
  rfl
#align sum.elim_inl Sum.elim_inl

/- warning: sum.elim_inr -> Sum.elim_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Sort.{u3}} (f : α -> γ) (g : β -> γ) (x : β), Eq.{u3} γ (Sum.elim.{u1, u2, u3} α β γ f g (Sum.inr.{u1, u2} α β x)) (g x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Sort.{u1}} (f : α -> γ) (g : β -> γ) (x : β), Eq.{u1} γ (Sum.elim.{u3, u2, u1} α β γ f g (Sum.inr.{u3, u2} α β x)) (g x)
Case conversion may be inaccurate. Consider using '#align sum.elim_inr Sum.elim_inrₓ'. -/
@[simp]
theorem elim_inr {α β γ : Sort _} (f : α → γ) (g : β → γ) (x : β) : Sum.elim f g (inr x) = g x :=
  rfl
#align sum.elim_inr Sum.elim_inr

/- warning: sum.elim_comp_inl -> Sum.elim_comp_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Sort.{u3}} (f : α -> γ) (g : β -> γ), Eq.{imax (succ u1) u3} (α -> γ) (Function.comp.{succ u1, max (succ u1) (succ u2), u3} α (Sum.{u1, u2} α β) γ (Sum.elim.{u1, u2, u3} α β γ f g) (Sum.inl.{u1, u2} α β)) f
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Sort.{u1}} (f : α -> γ) (g : β -> γ), Eq.{imax (succ u3) u1} (α -> γ) (Function.comp.{succ u3, max (succ u2) (succ u3), u1} α (Sum.{u3, u2} α β) γ (Sum.elim.{u3, u2, u1} α β γ f g) (Sum.inl.{u3, u2} α β)) f
Case conversion may be inaccurate. Consider using '#align sum.elim_comp_inl Sum.elim_comp_inlₓ'. -/
@[simp]
theorem elim_comp_inl {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum.elim f g ∘ inl = f :=
  rfl
#align sum.elim_comp_inl Sum.elim_comp_inl

/- warning: sum.elim_comp_inr -> Sum.elim_comp_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Sort.{u3}} (f : α -> γ) (g : β -> γ), Eq.{imax (succ u2) u3} (β -> γ) (Function.comp.{succ u2, max (succ u1) (succ u2), u3} β (Sum.{u1, u2} α β) γ (Sum.elim.{u1, u2, u3} α β γ f g) (Sum.inr.{u1, u2} α β)) g
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Sort.{u1}} (f : α -> γ) (g : β -> γ), Eq.{imax (succ u2) u1} (β -> γ) (Function.comp.{succ u2, max (succ u2) (succ u3), u1} β (Sum.{u3, u2} α β) γ (Sum.elim.{u3, u2, u1} α β γ f g) (Sum.inr.{u3, u2} α β)) g
Case conversion may be inaccurate. Consider using '#align sum.elim_comp_inr Sum.elim_comp_inrₓ'. -/
@[simp]
theorem elim_comp_inr {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum.elim f g ∘ inr = g :=
  rfl
#align sum.elim_comp_inr Sum.elim_comp_inr

/- warning: sum.elim_inl_inr -> Sum.elim_inl_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max (succ u1) (succ u2)} ((Sum.{u1, u2} α β) -> (Sum.{u1, u2} α β)) (Sum.elim.{u1, u2, max (succ u1) (succ u2)} α β (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) (Sum.inr.{u1, u2} α β)) (id.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u1) (succ u2)} ((Sum.{u2, u1} α β) -> (Sum.{u2, u1} α β)) (Sum.elim.{u2, u1, max (succ u2) (succ u1)} α β (Sum.{u2, u1} α β) (Sum.inl.{u2, u1} α β) (Sum.inr.{u2, u1} α β)) (id.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align sum.elim_inl_inr Sum.elim_inl_inrₓ'. -/
@[simp]
theorem elim_inl_inr {α β : Sort _} : @Sum.elim α β _ inl inr = id :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl
#align sum.elim_inl_inr Sum.elim_inl_inr

/- warning: sum.comp_elim -> Sum.comp_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Sort.{u3}} {δ : Sort.{u4}} (f : γ -> δ) (g : α -> γ) (h : β -> γ), Eq.{imax (max (succ u1) (succ u2)) u4} ((Sum.{u1, u2} α β) -> δ) (Function.comp.{max (succ u1) (succ u2), u3, u4} (Sum.{u1, u2} α β) γ δ f (Sum.elim.{u1, u2, u3} α β γ g h)) (Sum.elim.{u1, u2, u4} α β δ (Function.comp.{succ u1, u3, u4} α γ δ f g) (Function.comp.{succ u2, u3, u4} β γ δ f h))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Sort.{u2}} {δ : Sort.{u1}} (f : γ -> δ) (g : α -> γ) (h : β -> γ), Eq.{imax (max (succ u3) (succ u4)) u1} ((Sum.{u4, u3} α β) -> δ) (Function.comp.{max (succ u3) (succ u4), u2, u1} (Sum.{u4, u3} α β) γ δ f (Sum.elim.{u4, u3, u2} α β γ g h)) (Sum.elim.{u4, u3, u1} α β δ (Function.comp.{succ u4, u2, u1} α γ δ f g) (Function.comp.{succ u3, u2, u1} β γ δ f h))
Case conversion may be inaccurate. Consider using '#align sum.comp_elim Sum.comp_elimₓ'. -/
theorem comp_elim {α β γ δ : Sort _} (f : γ → δ) (g : α → γ) (h : β → γ) :
    f ∘ Sum.elim g h = Sum.elim (f ∘ g) (f ∘ h) :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl
#align sum.comp_elim Sum.comp_elim

/- warning: sum.elim_comp_inl_inr -> Sum.elim_comp_inl_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Sort.{u3}} (f : (Sum.{u1, u2} α β) -> γ), Eq.{imax (max (succ u1) (succ u2)) u3} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, u3} α β γ (Function.comp.{succ u1, max (succ u1) (succ u2), u3} α (Sum.{u1, u2} α β) γ f (Sum.inl.{u1, u2} α β)) (Function.comp.{succ u2, max (succ u1) (succ u2), u3} β (Sum.{u1, u2} α β) γ f (Sum.inr.{u1, u2} α β))) f
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Sort.{u1}} (f : (Sum.{u3, u2} α β) -> γ), Eq.{imax (max (succ u2) (succ u3)) u1} ((Sum.{u3, u2} α β) -> γ) (Sum.elim.{u3, u2, u1} α β γ (Function.comp.{succ u3, max (succ u2) (succ u3), u1} α (Sum.{u3, u2} α β) γ f (Sum.inl.{u3, u2} α β)) (Function.comp.{succ u2, max (succ u2) (succ u3), u1} β (Sum.{u3, u2} α β) γ f (Sum.inr.{u3, u2} α β))) f
Case conversion may be inaccurate. Consider using '#align sum.elim_comp_inl_inr Sum.elim_comp_inl_inrₓ'. -/
@[simp]
theorem elim_comp_inl_inr {α β γ : Sort _} (f : Sum α β → γ) : Sum.elim (f ∘ inl) (f ∘ inr) = f :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl
#align sum.elim_comp_inl_inr Sum.elim_comp_inl_inr

#print Sum.map /-
/-- Map `α ⊕ β` to `α' ⊕ β'` sending `α` to `α'` and `β` to `β'`. -/
protected def map (f : α → α') (g : β → β') : Sum α β → Sum α' β' :=
  Sum.elim (inl ∘ f) (inr ∘ g)
#align sum.map Sum.map
-/

#print Sum.map_inl /-
@[simp]
theorem map_inl (f : α → α') (g : β → β') (x : α) : (inl x).map f g = inl (f x) :=
  rfl
#align sum.map_inl Sum.map_inl
-/

#print Sum.map_inr /-
@[simp]
theorem map_inr (f : α → α') (g : β → β') (x : β) : (inr x).map f g = inr (g x) :=
  rfl
#align sum.map_inr Sum.map_inr
-/

/- warning: sum.map_map -> Sum.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u3}} {β : Type.{u2}} {β' : Type.{u4}} {α'' : Type.{u5}} {β'' : Type.{u6}} (f' : α' -> α'') (g' : β' -> β'') (f : α -> α') (g : β -> β') (x : Sum.{u1, u2} α β), Eq.{max (succ u5) (succ u6)} (Sum.{u5, u6} α'' β'') (Sum.map.{u3, u4, u5, u6} α' α'' β' β'' f' g' (Sum.map.{u1, u2, u3, u4} α α' β β' f g x)) (Sum.map.{u1, u2, u5, u6} α α'' β β'' (Function.comp.{succ u1, succ u3, succ u5} α α' α'' f' f) (Function.comp.{succ u2, succ u4, succ u6} β β' β'' g' g) x)
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u5}} {β : Type.{u4}} {β' : Type.{u6}} {α'' : Type.{u2}} {β'' : Type.{u1}} (f' : α' -> α'') (g' : β' -> β'') (f : α -> α') (g : β -> β') (x : Sum.{u3, u4} α β), Eq.{max (succ u1) (succ u2)} (Sum.{u2, u1} α'' β'') (Sum.map.{u5, u6, u2, u1} α' α'' β' β'' f' g' (Sum.map.{u3, u4, u5, u6} α α' β β' f g x)) (Sum.map.{u3, u4, u2, u1} α α'' β β'' (Function.comp.{succ u3, succ u5, succ u2} α α' α'' f' f) (Function.comp.{succ u4, succ u6, succ u1} β β' β'' g' g) x)
Case conversion may be inaccurate. Consider using '#align sum.map_map Sum.map_mapₓ'. -/
@[simp]
theorem map_map {α'' β''} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
    ∀ x : Sum α β, (x.map f g).map f' g' = x.map (f' ∘ f) (g' ∘ g)
  | inl a => rfl
  | inr b => rfl
#align sum.map_map Sum.map_map

/- warning: sum.map_comp_map -> Sum.map_comp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u3}} {β : Type.{u2}} {β' : Type.{u4}} {α'' : Type.{u5}} {β'' : Type.{u6}} (f' : α' -> α'') (g' : β' -> β'') (f : α -> α') (g : β -> β'), Eq.{max (max (succ u1) (succ u2)) (succ u5) (succ u6)} ((Sum.{u1, u2} α β) -> (Sum.{u5, u6} α'' β'')) (Function.comp.{max (succ u1) (succ u2), max (succ u3) (succ u4), max (succ u5) (succ u6)} (Sum.{u1, u2} α β) (Sum.{u3, u4} α' β') (Sum.{u5, u6} α'' β'') (Sum.map.{u3, u4, u5, u6} α' α'' β' β'' f' g') (Sum.map.{u1, u2, u3, u4} α α' β β' f g)) (Sum.map.{u1, u2, u5, u6} α α'' β β'' (Function.comp.{succ u1, succ u3, succ u5} α α' α'' f' f) (Function.comp.{succ u2, succ u4, succ u6} β β' β'' g' g))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u5}} {β : Type.{u4}} {β' : Type.{u6}} {α'' : Type.{u2}} {β'' : Type.{u1}} (f' : α' -> α'') (g' : β' -> β'') (f : α -> α') (g : β -> β'), Eq.{max (max (max (succ u3) (succ u4)) (succ u1)) (succ u2)} ((Sum.{u3, u4} α β) -> (Sum.{u2, u1} α'' β'')) (Function.comp.{max (succ u4) (succ u3), max (succ u6) (succ u5), max (succ u1) (succ u2)} (Sum.{u3, u4} α β) (Sum.{u5, u6} α' β') (Sum.{u2, u1} α'' β'') (Sum.map.{u5, u6, u2, u1} α' α'' β' β'' f' g') (Sum.map.{u3, u4, u5, u6} α α' β β' f g)) (Sum.map.{u3, u4, u2, u1} α α'' β β'' (Function.comp.{succ u3, succ u5, succ u2} α α' α'' f' f) (Function.comp.{succ u4, succ u6, succ u1} β β' β'' g' g))
Case conversion may be inaccurate. Consider using '#align sum.map_comp_map Sum.map_comp_mapₓ'. -/
@[simp]
theorem map_comp_map {α'' β''} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
    Sum.map f' g' ∘ Sum.map f g = Sum.map (f' ∘ f) (g' ∘ g) :=
  funext <| map_map f' g' f g
#align sum.map_comp_map Sum.map_comp_map

/- warning: sum.map_id_id -> Sum.map_id_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{max (succ u1) (succ u2)} ((Sum.{u1, u2} α β) -> (Sum.{u1, u2} α β)) (Sum.map.{u1, u2, u1, u2} α α β β (id.{succ u1} α) (id.{succ u2} β)) (id.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β))
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}), Eq.{max (succ u1) (succ u2)} ((Sum.{u2, u1} α β) -> (Sum.{u2, u1} α β)) (Sum.map.{u2, u1, u2, u1} α α β β (id.{succ u2} α) (id.{succ u1} β)) (id.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align sum.map_id_id Sum.map_id_idₓ'. -/
@[simp]
theorem map_id_id (α β) : Sum.map (@id α) (@id β) = id :=
  funext fun x => Sum.recOn x (fun _ => rfl) fun _ => rfl
#align sum.map_id_id Sum.map_id_id

/- warning: sum.elim_map -> Sum.elim_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Sort.{u5}} {f₁ : α -> β} {f₂ : β -> ε} {g₁ : γ -> δ} {g₂ : δ -> ε} {x : Sum.{u1, u3} α γ}, Eq.{u5} ε (Sum.elim.{u2, u4, u5} β δ ε f₂ g₂ (Sum.map.{u1, u3, u2, u4} α β γ δ f₁ g₁ x)) (Sum.elim.{u1, u3, u5} α γ ε (Function.comp.{succ u1, succ u2, u5} α β ε f₂ f₁) (Function.comp.{succ u3, succ u4, u5} γ δ ε g₂ g₁) x)
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u4}} {γ : Type.{u3}} {δ : Type.{u2}} {ε : Sort.{u1}} {f₁ : α -> β} {f₂ : β -> ε} {g₁ : γ -> δ} {g₂ : δ -> ε} {x : Sum.{u5, u3} α γ}, Eq.{u1} ε (Sum.elim.{u4, u2, u1} β δ ε f₂ g₂ (Sum.map.{u5, u3, u4, u2} α β γ δ f₁ g₁ x)) (Sum.elim.{u5, u3, u1} α γ ε (Function.comp.{succ u5, succ u4, u1} α β ε f₂ f₁) (Function.comp.{succ u3, succ u2, u1} γ δ ε g₂ g₁) x)
Case conversion may be inaccurate. Consider using '#align sum.elim_map Sum.elim_mapₓ'. -/
theorem elim_map {α β γ δ ε : Sort _} {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} {x} :
    Sum.elim f₂ g₂ (Sum.map f₁ g₁ x) = Sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) x := by cases x <;> rfl
#align sum.elim_map Sum.elim_map

/- warning: sum.elim_comp_map -> Sum.elim_comp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Sort.{u5}} {f₁ : α -> β} {f₂ : β -> ε} {g₁ : γ -> δ} {g₂ : δ -> ε}, Eq.{imax (max (succ u1) (succ u3)) u5} ((Sum.{u1, u3} α γ) -> ε) (Function.comp.{max (succ u1) (succ u3), max (succ u2) (succ u4), u5} (Sum.{u1, u3} α γ) (Sum.{u2, u4} β δ) ε (Sum.elim.{u2, u4, u5} β δ ε f₂ g₂) (Sum.map.{u1, u3, u2, u4} α β γ δ f₁ g₁)) (Sum.elim.{u1, u3, u5} α γ ε (Function.comp.{succ u1, succ u2, u5} α β ε f₂ f₁) (Function.comp.{succ u3, succ u4, u5} γ δ ε g₂ g₁))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u4}} {γ : Type.{u3}} {δ : Type.{u2}} {ε : Sort.{u1}} {f₁ : α -> β} {f₂ : β -> ε} {g₁ : γ -> δ} {g₂ : δ -> ε}, Eq.{imax (max (succ u3) (succ u5)) u1} ((Sum.{u5, u3} α γ) -> ε) (Function.comp.{max (succ u3) (succ u5), max (succ u2) (succ u4), u1} (Sum.{u5, u3} α γ) (Sum.{u4, u2} β δ) ε (Sum.elim.{u4, u2, u1} β δ ε f₂ g₂) (Sum.map.{u5, u3, u4, u2} α β γ δ f₁ g₁)) (Sum.elim.{u5, u3, u1} α γ ε (Function.comp.{succ u5, succ u4, u1} α β ε f₂ f₁) (Function.comp.{succ u3, succ u2, u1} γ δ ε g₂ g₁))
Case conversion may be inaccurate. Consider using '#align sum.elim_comp_map Sum.elim_comp_mapₓ'. -/
theorem elim_comp_map {α β γ δ ε : Sort _} {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} :
    Sum.elim f₂ g₂ ∘ Sum.map f₁ g₁ = Sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) :=
  funext fun _ => elim_map
#align sum.elim_comp_map Sum.elim_comp_map

/- warning: sum.is_left_map -> Sum.isLeft_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> β) (g : γ -> δ) (x : Sum.{u1, u3} α γ), Eq.{1} Bool (Sum.isLeft.{u2, u4} β δ (Sum.map.{u1, u3, u2, u4} α β γ δ f g x)) (Sum.isLeft.{u1, u3} α γ x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} (f : α -> β) (g : γ -> δ) (x : Sum.{u3, u2} α γ), Eq.{1} Bool (Sum.isLeft.{u4, u1} β δ (Sum.map.{u3, u2, u4, u1} α β γ δ f g x)) (Sum.isLeft.{u3, u2} α γ x)
Case conversion may be inaccurate. Consider using '#align sum.is_left_map Sum.isLeft_mapₓ'. -/
@[simp]
theorem isLeft_map (f : α → β) (g : γ → δ) (x : Sum α γ) : isLeft (x.map f g) = isLeft x := by
  cases x <;> rfl
#align sum.is_left_map Sum.isLeft_map

/- warning: sum.is_right_map -> Sum.isRight_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> β) (g : γ -> δ) (x : Sum.{u1, u3} α γ), Eq.{1} Bool (Sum.isRight.{u2, u4} β δ (Sum.map.{u1, u3, u2, u4} α β γ δ f g x)) (Sum.isRight.{u1, u3} α γ x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} (f : α -> β) (g : γ -> δ) (x : Sum.{u3, u2} α γ), Eq.{1} Bool (Sum.isRight.{u4, u1} β δ (Sum.map.{u3, u2, u4, u1} α β γ δ f g x)) (Sum.isRight.{u3, u2} α γ x)
Case conversion may be inaccurate. Consider using '#align sum.is_right_map Sum.isRight_mapₓ'. -/
@[simp]
theorem isRight_map (f : α → β) (g : γ → δ) (x : Sum α γ) : isRight (x.map f g) = isRight x := by
  cases x <;> rfl
#align sum.is_right_map Sum.isRight_map

/- warning: sum.get_left_map -> Sum.getLeft_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> β) (g : γ -> δ) (x : Sum.{u1, u3} α γ), Eq.{succ u2} (Option.{u2} β) (Sum.getLeft.{u2, u4} β δ (Sum.map.{u1, u3, u2, u4} α β γ δ f g x)) (Option.map.{u1, u2} α β f (Sum.getLeft.{u1, u3} α γ x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} (f : α -> β) (g : γ -> δ) (x : Sum.{u3, u2} α γ), Eq.{succ u4} (Option.{u4} β) (Sum.getLeft.{u4, u1} β δ (Sum.map.{u3, u2, u4, u1} α β γ δ f g x)) (Option.map.{u3, u4} α β f (Sum.getLeft.{u3, u2} α γ x))
Case conversion may be inaccurate. Consider using '#align sum.get_left_map Sum.getLeft_mapₓ'. -/
@[simp]
theorem getLeft_map (f : α → β) (g : γ → δ) (x : Sum α γ) : (x.map f g).getLeft = x.getLeft.map f :=
  by cases x <;> rfl
#align sum.get_left_map Sum.getLeft_map

/- warning: sum.get_right_map -> Sum.getRight_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> β) (g : γ -> δ) (x : Sum.{u1, u3} α γ), Eq.{succ u4} (Option.{u4} δ) (Sum.getRight.{u2, u4} β δ (Sum.map.{u1, u3, u2, u4} α β γ δ f g x)) (Option.map.{u3, u4} γ δ g (Sum.getRight.{u1, u3} α γ x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} (f : α -> β) (g : γ -> δ) (x : Sum.{u3, u2} α γ), Eq.{succ u1} (Option.{u1} δ) (Sum.getRight.{u4, u1} β δ (Sum.map.{u3, u2, u4, u1} α β γ δ f g x)) (Option.map.{u2, u1} γ δ g (Sum.getRight.{u3, u2} α γ x))
Case conversion may be inaccurate. Consider using '#align sum.get_right_map Sum.getRight_mapₓ'. -/
@[simp]
theorem getRight_map (f : α → β) (g : γ → δ) (x : Sum α γ) :
    (x.map f g).getRight = x.getRight.map g := by cases x <;> rfl
#align sum.get_right_map Sum.getRight_map

open Function (update update_eq_iff update_comp_eq_of_injective update_comp_eq_of_forall_ne)

/- warning: sum.update_elim_inl -> Sum.update_elim_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : α -> γ} {g : β -> γ} {i : α} {x : γ}, Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_2 a b) (Sum.elim.{u1, u2, succ u3} α β γ f g) (Sum.inl.{u1, u2} α β i) x) (Sum.elim.{u1, u2, succ u3} α β γ (Function.update.{succ u1, succ u3} α (fun (ᾰ : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) f i x) g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : α -> γ} {g : β -> γ} {i : α} {x : γ}, Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} α β) -> γ) (Function.update.{max (succ u3) (succ u2), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_2 a b) (Sum.elim.{u2, u3, succ u1} α β γ f g) (Sum.inl.{u2, u3} α β i) x) (Sum.elim.{u2, u3, succ u1} α β γ (Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) f i x) g)
Case conversion may be inaccurate. Consider using '#align sum.update_elim_inl Sum.update_elim_inlₓ'. -/
@[simp]
theorem update_elim_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : α → γ} {g : β → γ} {i : α}
    {x : γ} : update (Sum.elim f g) (inl i) x = Sum.elim (update f i x) g :=
  update_eq_iff.2 ⟨by simp, by simp (config := { contextual := true })⟩
#align sum.update_elim_inl Sum.update_elim_inl

/- warning: sum.update_elim_inr -> Sum.update_elim_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : α -> γ} {g : β -> γ} {i : β} {x : γ}, Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_2 a b) (Sum.elim.{u1, u2, succ u3} α β γ f g) (Sum.inr.{u1, u2} α β i) x) (Sum.elim.{u1, u2, succ u3} α β γ f (Function.update.{succ u2, succ u3} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_1 a b) g i x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} β] [_inst_2 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : α -> γ} {g : β -> γ} {i : β} {x : γ}, Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} α β) -> γ) (Function.update.{max (succ u3) (succ u2), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_2 a b) (Sum.elim.{u2, u3, succ u1} α β γ f g) (Sum.inr.{u2, u3} α β i) x) (Sum.elim.{u2, u3, succ u1} α β γ f (Function.update.{succ u3, succ u1} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_1 a b) g i x))
Case conversion may be inaccurate. Consider using '#align sum.update_elim_inr Sum.update_elim_inrₓ'. -/
@[simp]
theorem update_elim_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : α → γ} {g : β → γ} {i : β}
    {x : γ} : update (Sum.elim f g) (inr i) x = Sum.elim f (update g i x) :=
  update_eq_iff.2 ⟨by simp, by simp (config := { contextual := true })⟩
#align sum.update_elim_inr Sum.update_elim_inr

/- warning: sum.update_inl_comp_inl -> Sum.update_inl_comp_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : (Sum.{u1, u2} α β) -> γ} {i : α} {x : γ}, Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} α (Sum.{u1, u2} α β) γ (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_2 a b) f (Sum.inl.{u1, u2} α β i) x) (Sum.inl.{u1, u2} α β)) (Function.update.{succ u1, succ u3} α (fun (ᾰ : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} α (Sum.{u1, u2} α β) γ f (Sum.inl.{u1, u2} α β)) i x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : (Sum.{u2, u3} α β) -> γ} {i : α} {x : γ}, Eq.{max (succ u2) (succ u1)} (α -> γ) (Function.comp.{succ u2, max (succ u2) (succ u3), succ u1} α (Sum.{u2, u3} α β) γ (Function.update.{max (succ u2) (succ u3), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_2 a b) f (Sum.inl.{u2, u3} α β i) x) (Sum.inl.{u2, u3} α β)) (Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) (Function.comp.{succ u2, max (succ u2) (succ u3), succ u1} α (Sum.{u2, u3} α β) γ f (Sum.inl.{u2, u3} α β)) i x)
Case conversion may be inaccurate. Consider using '#align sum.update_inl_comp_inl Sum.update_inl_comp_inlₓ'. -/
@[simp]
theorem update_inl_comp_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α}
    {x : γ} : update f (inl i) x ∘ inl = update (f ∘ inl) i x :=
  update_comp_eq_of_injective _ inl_injective _ _
#align sum.update_inl_comp_inl Sum.update_inl_comp_inl

/- warning: sum.update_inl_apply_inl -> Sum.update_inl_apply_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : (Sum.{u1, u2} α β) -> γ} {i : α} {j : α} {x : γ}, Eq.{succ u3} γ (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_2 a b) f (Sum.inl.{u1, u2} α β i) x (Sum.inl.{u1, u2} α β j)) (Function.update.{succ u1, succ u3} α (fun (ᾰ : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} α (Sum.{u1, u2} α β) γ f (Sum.inl.{u1, u2} α β)) i x j)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : (Sum.{u2, u3} α β) -> γ} {i : α} {j : α} {x : γ}, Eq.{succ u1} γ (Function.update.{max (succ u2) (succ u3), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_2 a b) f (Sum.inl.{u2, u3} α β i) x (Sum.inl.{u2, u3} α β j)) (Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) (Function.comp.{succ u2, max (succ u2) (succ u3), succ u1} α (Sum.{u2, u3} α β) γ f (Sum.inl.{u2, u3} α β)) i x j)
Case conversion may be inaccurate. Consider using '#align sum.update_inl_apply_inl Sum.update_inl_apply_inlₓ'. -/
@[simp]
theorem update_inl_apply_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i j : α}
    {x : γ} : update f (inl i) x (inl j) = update (f ∘ inl) i x j := by rw [← update_inl_comp_inl]
#align sum.update_inl_apply_inl Sum.update_inl_apply_inl

/- warning: sum.update_inl_comp_inr -> Sum.update_inl_comp_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : (Sum.{u1, u2} α β) -> γ} {i : α} {x : γ}, Eq.{max (succ u2) (succ u3)} (β -> γ) (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} β (Sum.{u1, u2} α β) γ (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_1 a b) f (Sum.inl.{u1, u2} α β i) x) (Sum.inr.{u1, u2} α β)) (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} β (Sum.{u1, u2} α β) γ f (Sum.inr.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : (Sum.{u2, u3} α β) -> γ} {i : α} {x : γ}, Eq.{max (succ u3) (succ u1)} (β -> γ) (Function.comp.{succ u3, max (succ u2) (succ u3), succ u1} β (Sum.{u2, u3} α β) γ (Function.update.{max (succ u2) (succ u3), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_1 a b) f (Sum.inl.{u2, u3} α β i) x) (Sum.inr.{u2, u3} α β)) (Function.comp.{succ u3, max (succ u2) (succ u3), succ u1} β (Sum.{u2, u3} α β) γ f (Sum.inr.{u2, u3} α β))
Case conversion may be inaccurate. Consider using '#align sum.update_inl_comp_inr Sum.update_inl_comp_inrₓ'. -/
@[simp]
theorem update_inl_comp_inr [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {x : γ} :
    update f (inl i) x ∘ inr = f ∘ inr :=
  update_comp_eq_of_forall_ne _ _ fun _ => inr_ne_inl
#align sum.update_inl_comp_inr Sum.update_inl_comp_inr

/- warning: sum.update_inl_apply_inr -> Sum.update_inl_apply_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : (Sum.{u1, u2} α β) -> γ} {i : α} {j : β} {x : γ}, Eq.{succ u3} γ (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_1 a b) f (Sum.inl.{u1, u2} α β i) x (Sum.inr.{u1, u2} α β j)) (f (Sum.inr.{u1, u2} α β j))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : (Sum.{u2, u3} α β) -> γ} {i : α} {j : β} {x : γ}, Eq.{succ u1} γ (Function.update.{max (succ u2) (succ u3), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_1 a b) f (Sum.inl.{u2, u3} α β i) x (Sum.inr.{u2, u3} α β j)) (f (Sum.inr.{u2, u3} α β j))
Case conversion may be inaccurate. Consider using '#align sum.update_inl_apply_inr Sum.update_inl_apply_inrₓ'. -/
@[simp]
theorem update_inl_apply_inr [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {j : β} {x : γ} :
    update f (inl i) x (inr j) = f (inr j) :=
  Function.update_noteq inr_ne_inl _ _
#align sum.update_inl_apply_inr Sum.update_inl_apply_inr

/- warning: sum.update_inr_comp_inl -> Sum.update_inr_comp_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : (Sum.{u1, u2} α β) -> γ} {i : β} {x : γ}, Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} α (Sum.{u1, u2} α β) γ (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_1 a b) f (Sum.inr.{u1, u2} α β i) x) (Sum.inl.{u1, u2} α β)) (Function.comp.{succ u1, max (succ u1) (succ u2), succ u3} α (Sum.{u1, u2} α β) γ f (Sum.inl.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : (Sum.{u2, u3} α β) -> γ} {i : β} {x : γ}, Eq.{max (succ u2) (succ u1)} (α -> γ) (Function.comp.{succ u2, max (succ u2) (succ u3), succ u1} α (Sum.{u2, u3} α β) γ (Function.update.{max (succ u2) (succ u3), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_1 a b) f (Sum.inr.{u2, u3} α β i) x) (Sum.inl.{u2, u3} α β)) (Function.comp.{succ u2, max (succ u2) (succ u3), succ u1} α (Sum.{u2, u3} α β) γ f (Sum.inl.{u2, u3} α β))
Case conversion may be inaccurate. Consider using '#align sum.update_inr_comp_inl Sum.update_inr_comp_inlₓ'. -/
@[simp]
theorem update_inr_comp_inl [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : β} {x : γ} :
    update f (inr i) x ∘ inl = f ∘ inl :=
  update_comp_eq_of_forall_ne _ _ fun _ => inl_ne_inr
#align sum.update_inr_comp_inl Sum.update_inr_comp_inl

/- warning: sum.update_inr_apply_inl -> Sum.update_inr_apply_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : (Sum.{u1, u2} α β) -> γ} {i : α} {j : β} {x : γ}, Eq.{succ u3} γ (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_1 a b) f (Sum.inr.{u1, u2} α β j) x (Sum.inl.{u1, u2} α β i)) (f (Sum.inl.{u1, u2} α β i))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : (Sum.{u2, u3} α β) -> γ} {i : α} {j : β} {x : γ}, Eq.{succ u1} γ (Function.update.{max (succ u2) (succ u3), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_1 a b) f (Sum.inr.{u2, u3} α β j) x (Sum.inl.{u2, u3} α β i)) (f (Sum.inl.{u2, u3} α β i))
Case conversion may be inaccurate. Consider using '#align sum.update_inr_apply_inl Sum.update_inr_apply_inlₓ'. -/
@[simp]
theorem update_inr_apply_inl [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {j : β} {x : γ} :
    update f (inr j) x (inl i) = f (inl i) :=
  Function.update_noteq inl_ne_inr _ _
#align sum.update_inr_apply_inl Sum.update_inr_apply_inl

/- warning: sum.update_inr_comp_inr -> Sum.update_inr_comp_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : (Sum.{u1, u2} α β) -> γ} {i : β} {x : γ}, Eq.{max (succ u2) (succ u3)} (β -> γ) (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} β (Sum.{u1, u2} α β) γ (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_2 a b) f (Sum.inr.{u1, u2} α β i) x) (Sum.inr.{u1, u2} α β)) (Function.update.{succ u2, succ u3} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_1 a b) (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} β (Sum.{u1, u2} α β) γ f (Sum.inr.{u1, u2} α β)) i x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} β] [_inst_2 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : (Sum.{u2, u3} α β) -> γ} {i : β} {x : γ}, Eq.{max (succ u3) (succ u1)} (β -> γ) (Function.comp.{succ u3, max (succ u2) (succ u3), succ u1} β (Sum.{u2, u3} α β) γ (Function.update.{max (succ u2) (succ u3), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_2 a b) f (Sum.inr.{u2, u3} α β i) x) (Sum.inr.{u2, u3} α β)) (Function.update.{succ u3, succ u1} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_1 a b) (Function.comp.{succ u3, max (succ u2) (succ u3), succ u1} β (Sum.{u2, u3} α β) γ f (Sum.inr.{u2, u3} α β)) i x)
Case conversion may be inaccurate. Consider using '#align sum.update_inr_comp_inr Sum.update_inr_comp_inrₓ'. -/
@[simp]
theorem update_inr_comp_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : β}
    {x : γ} : update f (inr i) x ∘ inr = update (f ∘ inr) i x :=
  update_comp_eq_of_injective _ inr_injective _ _
#align sum.update_inr_comp_inr Sum.update_inr_comp_inr

/- warning: sum.update_inr_apply_inr -> Sum.update_inr_apply_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)] {f : (Sum.{u1, u2} α β) -> γ} {i : β} {j : β} {x : γ}, Eq.{succ u3} γ (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => _inst_2 a b) f (Sum.inr.{u1, u2} α β i) x (Sum.inr.{u1, u2} α β j)) (Function.update.{succ u2, succ u3} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_1 a b) (Function.comp.{succ u2, max (succ u1) (succ u2), succ u3} β (Sum.{u1, u2} α β) γ f (Sum.inr.{u1, u2} α β)) i x j)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} β] [_inst_2 : DecidableEq.{max (succ u3) (succ u2)} (Sum.{u2, u3} α β)] {f : (Sum.{u2, u3} α β) -> γ} {i : β} {j : β} {x : γ}, Eq.{succ u1} γ (Function.update.{max (succ u2) (succ u3), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => _inst_2 a b) f (Sum.inr.{u2, u3} α β i) x (Sum.inr.{u2, u3} α β j)) (Function.update.{succ u3, succ u1} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_1 a b) (Function.comp.{succ u3, max (succ u2) (succ u3), succ u1} β (Sum.{u2, u3} α β) γ f (Sum.inr.{u2, u3} α β)) i x j)
Case conversion may be inaccurate. Consider using '#align sum.update_inr_apply_inr Sum.update_inr_apply_inrₓ'. -/
@[simp]
theorem update_inr_apply_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i j : β}
    {x : γ} : update f (inr i) x (inr j) = update (f ∘ inr) i x j := by rw [← update_inr_comp_inr]
#align sum.update_inr_apply_inr Sum.update_inr_apply_inr

#print Sum.swap /-
/-- Swap the factors of a sum type -/
def swap : Sum α β → Sum β α :=
  Sum.elim inr inl
#align sum.swap Sum.swap
-/

#print Sum.swap_inl /-
@[simp]
theorem swap_inl (x : α) : swap (inl x : Sum α β) = inr x :=
  rfl
#align sum.swap_inl Sum.swap_inl
-/

#print Sum.swap_inr /-
@[simp]
theorem swap_inr (x : β) : swap (inr x : Sum α β) = inl x :=
  rfl
#align sum.swap_inr Sum.swap_inr
-/

#print Sum.swap_swap /-
@[simp]
theorem swap_swap (x : Sum α β) : swap (swap x) = x := by cases x <;> rfl
#align sum.swap_swap Sum.swap_swap
-/

#print Sum.swap_swap_eq /-
@[simp]
theorem swap_swap_eq : swap ∘ swap = @id (Sum α β) :=
  funext <| swap_swap
#align sum.swap_swap_eq Sum.swap_swap_eq
-/

#print Sum.swap_leftInverse /-
@[simp]
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap
#align sum.swap_left_inverse Sum.swap_leftInverse
-/

#print Sum.swap_rightInverse /-
@[simp]
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap
#align sum.swap_right_inverse Sum.swap_rightInverse
-/

#print Sum.isLeft_swap /-
@[simp]
theorem isLeft_swap (x : Sum α β) : x.symm.isLeft = x.isRight := by cases x <;> rfl
#align sum.is_left_swap Sum.isLeft_swap
-/

#print Sum.isRight_swap /-
@[simp]
theorem isRight_swap (x : Sum α β) : x.symm.isRight = x.isLeft := by cases x <;> rfl
#align sum.is_right_swap Sum.isRight_swap
-/

#print Sum.getLeft_swap /-
@[simp]
theorem getLeft_swap (x : Sum α β) : x.symm.getLeft = x.getRight := by cases x <;> rfl
#align sum.get_left_swap Sum.getLeft_swap
-/

#print Sum.getRight_swap /-
@[simp]
theorem getRight_swap (x : Sum α β) : x.symm.getRight = x.getLeft := by cases x <;> rfl
#align sum.get_right_swap Sum.getRight_swap
-/

section LiftRel

#print Sum.LiftRel /-
/-- Lifts pointwise two relations between `α` and `γ` and between `β` and `δ` to a relation between
`α ⊕ β` and `γ ⊕ δ`. -/
inductive LiftRel (r : α → γ → Prop) (s : β → δ → Prop) : Sum α β → Sum γ δ → Prop
  | inl {a c} : r a c → lift_rel (inl a) (inl c)
  | inr {b d} : s b d → lift_rel (inr b) (inr d)
#align sum.lift_rel Sum.LiftRel
-/

attribute [protected] lift_rel.inl lift_rel.inr

variable {r r₁ r₂ : α → γ → Prop} {s s₁ s₂ : β → δ → Prop} {a : α} {b : β} {c : γ} {d : δ}
  {x : Sum α β} {y : Sum γ δ}

/- warning: sum.lift_rel_inl_inl -> Sum.liftRel_inl_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {a : α} {c : γ}, Iff (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r s (Sum.inl.{u1, u2} α β a) (Sum.inl.{u3, u4} γ δ c)) (r a c)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {a : α} {c : γ}, Iff (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r s (Sum.inl.{u3, u4} α β a) (Sum.inl.{u2, u1} γ δ c)) (r a c)
Case conversion may be inaccurate. Consider using '#align sum.lift_rel_inl_inl Sum.liftRel_inl_inlₓ'. -/
@[simp]
theorem liftRel_inl_inl : LiftRel r s (inl a) (inl c) ↔ r a c :=
  ⟨fun h => by
    cases h
    assumption, LiftRel.inl⟩
#align sum.lift_rel_inl_inl Sum.liftRel_inl_inl

/- warning: sum.not_lift_rel_inl_inr -> Sum.not_liftRel_inl_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {a : α} {d : δ}, Not (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r s (Sum.inl.{u1, u2} α β a) (Sum.inr.{u3, u4} γ δ d))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {a : α} {d : δ}, Not (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r s (Sum.inl.{u3, u4} α β a) (Sum.inr.{u2, u1} γ δ d))
Case conversion may be inaccurate. Consider using '#align sum.not_lift_rel_inl_inr Sum.not_liftRel_inl_inrₓ'. -/
@[simp]
theorem not_liftRel_inl_inr : ¬LiftRel r s (inl a) (inr d) :=
  fun.
#align sum.not_lift_rel_inl_inr Sum.not_liftRel_inl_inr

/- warning: sum.not_lift_rel_inr_inl -> Sum.not_liftRel_inr_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {b : β} {c : γ}, Not (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r s (Sum.inr.{u1, u2} α β b) (Sum.inl.{u3, u4} γ δ c))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {b : β} {c : γ}, Not (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r s (Sum.inr.{u3, u4} α β b) (Sum.inl.{u2, u1} γ δ c))
Case conversion may be inaccurate. Consider using '#align sum.not_lift_rel_inr_inl Sum.not_liftRel_inr_inlₓ'. -/
@[simp]
theorem not_liftRel_inr_inl : ¬LiftRel r s (inr b) (inl c) :=
  fun.
#align sum.not_lift_rel_inr_inl Sum.not_liftRel_inr_inl

/- warning: sum.lift_rel_inr_inr -> Sum.liftRel_inr_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {b : β} {d : δ}, Iff (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r s (Sum.inr.{u1, u2} α β b) (Sum.inr.{u3, u4} γ δ d)) (s b d)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {b : β} {d : δ}, Iff (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r s (Sum.inr.{u3, u4} α β b) (Sum.inr.{u2, u1} γ δ d)) (s b d)
Case conversion may be inaccurate. Consider using '#align sum.lift_rel_inr_inr Sum.liftRel_inr_inrₓ'. -/
@[simp]
theorem liftRel_inr_inr : LiftRel r s (inr b) (inr d) ↔ s b d :=
  ⟨fun h => by
    cases h
    assumption, LiftRel.inr⟩
#align sum.lift_rel_inr_inr Sum.liftRel_inr_inr

instance [∀ a c, Decidable (r a c)] [∀ b d, Decidable (s b d)] :
    ∀ (ab : Sum α β) (cd : Sum γ δ), Decidable (LiftRel r s ab cd)
  | inl a, inl c => decidable_of_iff' _ liftRel_inl_inl
  | inl a, inr d => Decidable.isFalse not_liftRel_inl_inr
  | inr b, inl c => Decidable.isFalse not_liftRel_inr_inl
  | inr b, inr d => decidable_of_iff' _ liftRel_inr_inr

/- warning: sum.lift_rel.mono -> Sum.LiftRel.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r₁ : α -> γ -> Prop} {r₂ : α -> γ -> Prop} {s₁ : β -> δ -> Prop} {s₂ : β -> δ -> Prop} {x : Sum.{u1, u2} α β} {y : Sum.{u3, u4} γ δ}, (forall (a : α) (b : γ), (r₁ a b) -> (r₂ a b)) -> (forall (a : β) (b : δ), (s₁ a b) -> (s₂ a b)) -> (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r₁ s₁ x y) -> (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r₂ s₂ x y)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} {r₁ : α -> γ -> Prop} {r₂ : α -> γ -> Prop} {s₁ : β -> δ -> Prop} {s₂ : β -> δ -> Prop} {x : Sum.{u3, u4} α β} {y : Sum.{u2, u1} γ δ}, (forall (a : α) (b : γ), (r₁ a b) -> (r₂ a b)) -> (forall (a : β) (b : δ), (s₁ a b) -> (s₂ a b)) -> (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r₁ s₁ x y) -> (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r₂ s₂ x y)
Case conversion may be inaccurate. Consider using '#align sum.lift_rel.mono Sum.LiftRel.monoₓ'. -/
theorem LiftRel.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b)
    (h : LiftRel r₁ s₁ x y) : LiftRel r₂ s₂ x y :=
  by
  cases h
  exacts[lift_rel.inl (hr _ _ ‹_›), lift_rel.inr (hs _ _ ‹_›)]
#align sum.lift_rel.mono Sum.LiftRel.mono

/- warning: sum.lift_rel.mono_left -> Sum.LiftRel.mono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r₁ : α -> γ -> Prop} {r₂ : α -> γ -> Prop} {s : β -> δ -> Prop} {x : Sum.{u1, u2} α β} {y : Sum.{u3, u4} γ δ}, (forall (a : α) (b : γ), (r₁ a b) -> (r₂ a b)) -> (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r₁ s x y) -> (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r₂ s x y)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} {r₁ : α -> γ -> Prop} {r₂ : α -> γ -> Prop} {s : β -> δ -> Prop} {x : Sum.{u3, u4} α β} {y : Sum.{u2, u1} γ δ}, (forall (a : α) (b : γ), (r₁ a b) -> (r₂ a b)) -> (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r₁ s x y) -> (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r₂ s x y)
Case conversion may be inaccurate. Consider using '#align sum.lift_rel.mono_left Sum.LiftRel.mono_leftₓ'. -/
theorem LiftRel.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : LiftRel r₁ s x y) : LiftRel r₂ s x y :=
  h.mono hr fun _ _ => id
#align sum.lift_rel.mono_left Sum.LiftRel.mono_left

/- warning: sum.lift_rel.mono_right -> Sum.LiftRel.mono_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r : α -> γ -> Prop} {s₁ : β -> δ -> Prop} {s₂ : β -> δ -> Prop} {x : Sum.{u1, u2} α β} {y : Sum.{u3, u4} γ δ}, (forall (a : β) (b : δ), (s₁ a b) -> (s₂ a b)) -> (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r s₁ x y) -> (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r s₂ x y)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} {r : α -> γ -> Prop} {s₁ : β -> δ -> Prop} {s₂ : β -> δ -> Prop} {x : Sum.{u3, u4} α β} {y : Sum.{u2, u1} γ δ}, (forall (a : β) (b : δ), (s₁ a b) -> (s₂ a b)) -> (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r s₁ x y) -> (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r s₂ x y)
Case conversion may be inaccurate. Consider using '#align sum.lift_rel.mono_right Sum.LiftRel.mono_rightₓ'. -/
theorem LiftRel.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : LiftRel r s₁ x y) :
    LiftRel r s₂ x y :=
  h.mono (fun _ _ => id) hs
#align sum.lift_rel.mono_right Sum.LiftRel.mono_right

/- warning: sum.lift_rel.swap -> Sum.LiftRel.swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {x : Sum.{u1, u2} α β} {y : Sum.{u3, u4} γ δ}, (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r s x y) -> (Sum.LiftRel.{u2, u1, u4, u3} β α δ γ s r (Sum.swap.{u1, u2} α β x) (Sum.swap.{u3, u4} γ δ y))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {x : Sum.{u3, u4} α β} {y : Sum.{u2, u1} γ δ}, (Sum.LiftRel.{u3, u4, u2, u1} α β γ δ r s x y) -> (Sum.LiftRel.{u4, u3, u1, u2} β α δ γ s r (Sum.swap.{u3, u4} α β x) (Sum.swap.{u2, u1} γ δ y))
Case conversion may be inaccurate. Consider using '#align sum.lift_rel.swap Sum.LiftRel.swapₓ'. -/
protected theorem LiftRel.swap (h : LiftRel r s x y) : LiftRel s r x.symm y.symm :=
  by
  cases h
  exacts[lift_rel.inr ‹_›, lift_rel.inl ‹_›]
#align sum.lift_rel.swap Sum.LiftRel.swap

/- warning: sum.lift_rel_swap_iff -> Sum.liftRel_swap_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {x : Sum.{u1, u2} α β} {y : Sum.{u3, u4} γ δ}, Iff (Sum.LiftRel.{u2, u1, u4, u3} β α δ γ s r (Sum.swap.{u1, u2} α β x) (Sum.swap.{u3, u4} γ δ y)) (Sum.LiftRel.{u1, u2, u3, u4} α β γ δ r s x y)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u1}} {δ : Type.{u2}} {r : α -> γ -> Prop} {s : β -> δ -> Prop} {x : Sum.{u3, u4} α β} {y : Sum.{u1, u2} γ δ}, Iff (Sum.LiftRel.{u4, u3, u2, u1} β α δ γ s r (Sum.swap.{u3, u4} α β x) (Sum.swap.{u1, u2} γ δ y)) (Sum.LiftRel.{u3, u4, u1, u2} α β γ δ r s x y)
Case conversion may be inaccurate. Consider using '#align sum.lift_rel_swap_iff Sum.liftRel_swap_iffₓ'. -/
@[simp]
theorem liftRel_swap_iff : LiftRel s r x.symm y.symm ↔ LiftRel r s x y :=
  ⟨fun h => by
    rw [← swap_swap x, ← swap_swap y]
    exact h.swap, LiftRel.swap⟩
#align sum.lift_rel_swap_iff Sum.liftRel_swap_iff

end LiftRel

section Lex

#print Sum.Lex /-
/-- Lexicographic order for sum. Sort all the `inl a` before the `inr b`, otherwise use the
respective order on `α` or `β`. -/
inductive Lex (r : α → α → Prop) (s : β → β → Prop) : Sum α β → Sum α β → Prop
  | inl {a₁ a₂} (h : r a₁ a₂) : Lex (inl a₁) (inl a₂)
  | inr {b₁ b₂} (h : s b₁ b₂) : Lex (inr b₁) (inr b₂)
  | sep (a b) : Lex (inl a) (inr b)
#align sum.lex Sum.Lex
-/

attribute [protected] Sum.Lex.inl Sum.Lex.inr

attribute [simp] lex.sep

variable {r r₁ r₂ : α → α → Prop} {s s₁ s₂ : β → β → Prop} {a a₁ a₂ : α} {b b₁ b₂ : β}
  {x y : Sum α β}

#print Sum.lex_inl_inl /-
@[simp]
theorem lex_inl_inl : Lex r s (inl a₁) (inl a₂) ↔ r a₁ a₂ :=
  ⟨fun h => by
    cases h
    assumption, Lex.inl⟩
#align sum.lex_inl_inl Sum.lex_inl_inl
-/

#print Sum.lex_inr_inr /-
@[simp]
theorem lex_inr_inr : Lex r s (inr b₁) (inr b₂) ↔ s b₁ b₂ :=
  ⟨fun h => by
    cases h
    assumption, Lex.inr⟩
#align sum.lex_inr_inr Sum.lex_inr_inr
-/

#print Sum.lex_inr_inl /-
@[simp]
theorem lex_inr_inl : ¬Lex r s (inr b) (inl a) :=
  fun.
#align sum.lex_inr_inl Sum.lex_inr_inl
-/

instance [DecidableRel r] [DecidableRel s] : DecidableRel (Lex r s)
  | inl a, inl c => decidable_of_iff' _ lex_inl_inl
  | inl a, inr d => Decidable.isTrue (Lex.sep _ _)
  | inr b, inl c => Decidable.isFalse lex_inr_inl
  | inr b, inr d => decidable_of_iff' _ lex_inr_inr

#print Sum.LiftRel.lex /-
protected theorem LiftRel.lex {a b : Sum α β} (h : LiftRel r s a b) : Lex r s a b :=
  by
  cases h
  exacts[lex.inl ‹_›, lex.inr ‹_›]
#align sum.lift_rel.lex Sum.LiftRel.lex
-/

#print Sum.liftRel_subrelation_lex /-
theorem liftRel_subrelation_lex : Subrelation (LiftRel r s) (Lex r s) := fun a b => LiftRel.lex
#align sum.lift_rel_subrelation_lex Sum.liftRel_subrelation_lex
-/

#print Sum.Lex.mono /-
theorem Lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b) (h : Lex r₁ s₁ x y) :
    Lex r₂ s₂ x y := by
  cases h
  exacts[lex.inl (hr _ _ ‹_›), lex.inr (hs _ _ ‹_›), lex.sep _ _]
#align sum.lex.mono Sum.Lex.mono
-/

#print Sum.Lex.mono_left /-
theorem Lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : Lex r₁ s x y) : Lex r₂ s x y :=
  h.mono hr fun _ _ => id
#align sum.lex.mono_left Sum.Lex.mono_left
-/

#print Sum.Lex.mono_right /-
theorem Lex.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : Lex r s₁ x y) : Lex r s₂ x y :=
  h.mono (fun _ _ => id) hs
#align sum.lex.mono_right Sum.Lex.mono_right
-/

#print Sum.lex_acc_inl /-
theorem lex_acc_inl {a} (aca : Acc r a) : Acc (Lex r s) (inl a) :=
  by
  induction' aca with a H IH
  constructor; intro y h
  cases' h with a' _ h'
  exact IH _ h'
#align sum.lex_acc_inl Sum.lex_acc_inl
-/

#print Sum.lex_acc_inr /-
theorem lex_acc_inr (aca : ∀ a, Acc (Lex r s) (inl a)) {b} (acb : Acc s b) :
    Acc (Lex r s) (inr b) := by
  induction' acb with b H IH
  constructor; intro y h
  cases' h with _ _ _ b' _ h' a
  · exact IH _ h'
  · exact aca _
#align sum.lex_acc_inr Sum.lex_acc_inr
-/

#print Sum.lex_wf /-
theorem lex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (Lex r s) :=
  have aca : ∀ a, Acc (Lex r s) (inl a) := fun a => lex_acc_inl (ha.apply a)
  ⟨fun x => Sum.recOn x aca fun b => lex_acc_inr aca (hb.apply b)⟩
#align sum.lex_wf Sum.lex_wf
-/

end Lex

end Sum

open Sum

namespace Function

/- warning: function.injective.sum_elim -> Function.Injective.sum_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> γ} {g : β -> γ}, (Function.Injective.{succ u1, succ u3} α γ f) -> (Function.Injective.{succ u2, succ u3} β γ g) -> (forall (a : α) (b : β), Ne.{succ u3} γ (f a) (g b)) -> (Function.Injective.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) γ (Sum.elim.{u1, u2, succ u3} α β γ f g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} {f : α -> γ} {g : β -> γ}, (Function.Injective.{succ u2, succ u1} α γ f) -> (Function.Injective.{succ u3, succ u1} β γ g) -> (forall (a : α) (b : β), Ne.{succ u1} γ (f a) (g b)) -> (Function.Injective.{max (succ u3) (succ u2), succ u1} (Sum.{u2, u3} α β) γ (Sum.elim.{u2, u3, succ u1} α β γ f g))
Case conversion may be inaccurate. Consider using '#align function.injective.sum_elim Function.Injective.sum_elimₓ'. -/
theorem Injective.sum_elim {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (hfg : ∀ a b, f a ≠ g b) : Injective (Sum.elim f g)
  | inl x, inl y, h => congr_arg inl <| hf h
  | inl x, inr y, h => (hfg x y h).elim
  | inr x, inl y, h => (hfg y x h.symm).elim
  | inr x, inr y, h => congr_arg inr <| hg h
#align function.injective.sum_elim Function.Injective.sum_elim

#print Function.Injective.sum_map /-
theorem Injective.sum_map {f : α → β} {g : α' → β'} (hf : Injective f) (hg : Injective g) :
    Injective (Sum.map f g)
  | inl x, inl y, h => congr_arg inl <| hf <| inl.inj h
  | inr x, inr y, h => congr_arg inr <| hg <| inr.inj h
#align function.injective.sum_map Function.Injective.sum_map
-/

#print Function.Surjective.sum_map /-
theorem Surjective.sum_map {f : α → β} {g : α' → β'} (hf : Surjective f) (hg : Surjective g) :
    Surjective (Sum.map f g)
  | inl y =>
    let ⟨x, hx⟩ := hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩
#align function.surjective.sum_map Function.Surjective.sum_map
-/

end Function

namespace Sum

open Function

/- warning: sum.elim_const_const -> Sum.elim_const_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (c : γ), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (Function.const.{succ u3, succ u1} γ α c) (Function.const.{succ u3, succ u2} γ β c)) (Function.const.{succ u3, max (succ u1) (succ u2)} γ (Sum.{u1, u2} α β) c)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} (c : γ), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} α β) -> γ) (Sum.elim.{u2, u3, succ u1} α β γ (Function.const.{succ u1, succ u2} γ α c) (Function.const.{succ u1, succ u3} γ β c)) (Function.const.{succ u1, max (succ u2) (succ u3)} γ (Sum.{u2, u3} α β) c)
Case conversion may be inaccurate. Consider using '#align sum.elim_const_const Sum.elim_const_constₓ'. -/
theorem elim_const_const (c : γ) : Sum.elim (const _ c : α → γ) (const _ c : β → γ) = const _ c :=
  by
  ext x
  cases x <;> rfl
#align sum.elim_const_const Sum.elim_const_const

/- warning: sum.elim_lam_const_lam_const -> Sum.elim_lam_const_lam_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (c : γ), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (fun (_x : α) => c) (fun (_x : β) => c)) (fun (_x : Sum.{u1, u2} α β) => c)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} (c : γ), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} α β) -> γ) (Sum.elim.{u2, u3, succ u1} α β γ (fun (_x : α) => c) (fun (_x : β) => c)) (fun (_x : Sum.{u2, u3} α β) => c)
Case conversion may be inaccurate. Consider using '#align sum.elim_lam_const_lam_const Sum.elim_lam_const_lam_constₓ'. -/
@[simp]
theorem elim_lam_const_lam_const (c : γ) :
    (Sum.elim (fun _ : α => c) fun _ : β => c) = fun _ => c :=
  Sum.elim_const_const c
#align sum.elim_lam_const_lam_const Sum.elim_lam_const_lam_const

/- warning: sum.elim_update_left -> Sum.elim_update_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : α -> γ) (g : β -> γ) (i : α) (c : γ), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (Function.update.{succ u1, succ u3} α (fun (ᾰ : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) f i c) g) (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => Sum.decidableEq.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) β (fun (a : β) (b : β) => _inst_2 a b) a b) (Sum.elim.{u1, u2, succ u3} α β γ f g) (Sum.inl.{u1, u2} α β i) c)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u3} β] (f : α -> γ) (g : β -> γ) (i : α) (c : γ), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} α β) -> γ) (Sum.elim.{u2, u3, succ u1} α β γ (Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) f i c) g) (Function.update.{max (succ u3) (succ u2), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => Sum.instDecidableEqSum.{u2, u3} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (Sum.elim.{u2, u3, succ u1} α β γ f g) (Sum.inl.{u2, u3} α β i) c)
Case conversion may be inaccurate. Consider using '#align sum.elim_update_left Sum.elim_update_leftₓ'. -/
theorem elim_update_left [DecidableEq α] [DecidableEq β] (f : α → γ) (g : β → γ) (i : α) (c : γ) :
    Sum.elim (Function.update f i c) g = Function.update (Sum.elim f g) (inl i) c :=
  by
  ext x; cases x
  · by_cases h : x = i
    · subst h
      simp
    · simp [h]
  · simp
#align sum.elim_update_left Sum.elim_update_left

/- warning: sum.elim_update_right -> Sum.elim_update_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : α -> γ) (g : β -> γ) (i : β) (c : γ), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ f (Function.update.{succ u2, succ u3} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_2 a b) g i c)) (Function.update.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => Sum.decidableEq.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) β (fun (a : β) (b : β) => _inst_2 a b) a b) (Sum.elim.{u1, u2, succ u3} α β γ f g) (Sum.inr.{u1, u2} α β i) c)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u3} β] (f : α -> γ) (g : β -> γ) (i : β) (c : γ), Eq.{max (max (succ u2) (succ u3)) (succ u1)} ((Sum.{u2, u3} α β) -> γ) (Sum.elim.{u2, u3, succ u1} α β γ f (Function.update.{succ u3, succ u1} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_2 a b) g i c)) (Function.update.{max (succ u3) (succ u2), succ u1} (Sum.{u2, u3} α β) (fun (ᾰ : Sum.{u2, u3} α β) => γ) (fun (a : Sum.{u2, u3} α β) (b : Sum.{u2, u3} α β) => Sum.instDecidableEqSum.{u2, u3} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (Sum.elim.{u2, u3, succ u1} α β γ f g) (Sum.inr.{u2, u3} α β i) c)
Case conversion may be inaccurate. Consider using '#align sum.elim_update_right Sum.elim_update_rightₓ'. -/
theorem elim_update_right [DecidableEq α] [DecidableEq β] (f : α → γ) (g : β → γ) (i : β) (c : γ) :
    Sum.elim f (Function.update g i c) = Function.update (Sum.elim f g) (inr i) c :=
  by
  ext x; cases x
  · simp
  · by_cases h : x = i
    · subst h
      simp
    · simp [h]
#align sum.elim_update_right Sum.elim_update_right

end Sum

/-!
### Ternary sum

Abbreviations for the maps from the summands to `α ⊕ β ⊕ γ`. This is useful for pattern-matching.
-/


namespace Sum3

#print Sum3.in₀ /-
/-- The map from the first summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₀ (a) : Sum α (Sum β γ) :=
  inl a
#align sum3.in₀ Sum3.in₀
-/

#print Sum3.in₁ /-
/-- The map from the second summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₁ (b) : Sum α (Sum β γ) :=
  inr <| inl b
#align sum3.in₁ Sum3.in₁
-/

#print Sum3.in₂ /-
/-- The map from the third summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₂ (c) : Sum α (Sum β γ) :=
  inr <| inr c
#align sum3.in₂ Sum3.in₂
-/

end Sum3

