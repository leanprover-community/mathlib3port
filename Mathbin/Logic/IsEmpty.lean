/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module logic.is_empty
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Function.Basic
import Mathbin.Tactic.Protected

/-!
# Types that are empty

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a typeclass `is_empty`, which expresses that a type has no elements.

## Main declaration

* `is_empty`: a typeclass that expresses that a type is empty.
-/


variable {α β γ : Sort _}

#print IsEmpty /-
/-- `is_empty α` expresses that `α` is empty. -/
@[protect_proj]
class IsEmpty (α : Sort _) : Prop where
  False : α → False
#align is_empty IsEmpty
-/

instance : IsEmpty Empty :=
  ⟨Empty.elim⟩

instance : IsEmpty PEmpty :=
  ⟨PEmpty.elim⟩

instance : IsEmpty False :=
  ⟨id⟩

instance : IsEmpty (Fin 0) :=
  ⟨fun n => Nat.not_lt_zero n.1 n.2⟩

#print Function.isEmpty /-
protected theorem Function.isEmpty [IsEmpty β] (f : α → β) : IsEmpty α :=
  ⟨fun x => IsEmpty.false (f x)⟩
#align function.is_empty Function.isEmpty
-/

instance {p : α → Sort _} [h : Nonempty α] [∀ x, IsEmpty (p x)] : IsEmpty (∀ x, p x) :=
  h.elim fun x => Function.isEmpty <| Function.eval x

#print PProd.isEmpty_left /-
instance PProd.isEmpty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.fst
#align pprod.is_empty_left PProd.isEmpty_left
-/

#print PProd.isEmpty_right /-
instance PProd.isEmpty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.isEmpty PProd.snd
#align pprod.is_empty_right PProd.isEmpty_right
-/

#print Prod.isEmpty_left /-
instance Prod.isEmpty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.isEmpty Prod.fst
#align prod.is_empty_left Prod.isEmpty_left
-/

#print Prod.isEmpty_right /-
instance Prod.isEmpty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.isEmpty Prod.snd
#align prod.is_empty_right Prod.isEmpty_right
-/

instance [IsEmpty α] [IsEmpty β] : IsEmpty (PSum α β) :=
  ⟨fun x => PSum.rec IsEmpty.false IsEmpty.false x⟩

instance {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (Sum α β) :=
  ⟨fun x => Sum.rec IsEmpty.false IsEmpty.false x⟩

/-- subtypes of an empty type are empty -/
instance [IsEmpty α] (p : α → Prop) : IsEmpty (Subtype p) :=
  ⟨fun x => IsEmpty.false x.1⟩

#print Subtype.isEmpty_of_false /-
/-- subtypes by an all-false predicate are false. -/
theorem Subtype.isEmpty_of_false {p : α → Prop} (hp : ∀ a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x => hp _ x.2⟩
#align subtype.is_empty_of_false Subtype.isEmpty_of_false
-/

#print Subtype.isEmpty_false /-
/-- subtypes by false are false. -/
instance Subtype.isEmpty_false : IsEmpty { a : α // False } :=
  Subtype.isEmpty_of_false fun a => id
#align subtype.is_empty_false Subtype.isEmpty_false
-/

#print Sigma.isEmpty_left /-
instance Sigma.isEmpty_left {α} [IsEmpty α] {E : α → Type _} : IsEmpty (Sigma E) :=
  Function.isEmpty Sigma.fst
#align sigma.is_empty_left Sigma.isEmpty_left
-/

-- Test that `pi.is_empty` finds this instance.
example [h : Nonempty α] [IsEmpty β] : IsEmpty (α → β) := by infer_instance

#print isEmptyElim /-
/-- Eliminate out of a type that `is_empty` (without using projection notation). -/
@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort _} (a : α) : p a :=
  (IsEmpty.false a).elim
#align is_empty_elim isEmptyElim
-/

#print isEmpty_iff /-
theorem isEmpty_iff : IsEmpty α ↔ α → False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩
#align is_empty_iff isEmpty_iff
-/

namespace IsEmpty

open Function

#print IsEmpty.elim /-
/-- Eliminate out of a type that `is_empty` (using projection notation). -/
protected def elim (h : IsEmpty α) {p : α → Sort _} (a : α) : p a :=
  isEmptyElim a
#align is_empty.elim IsEmpty.elim
-/

#print IsEmpty.elim' /-
/-- Non-dependent version of `is_empty.elim`. Helpful if the elaborator cannot elaborate `h.elim a`
  correctly. -/
protected def elim' {β : Sort _} (h : IsEmpty α) (a : α) : β :=
  h.elim a
#align is_empty.elim' IsEmpty.elim'
-/

#print IsEmpty.prop_iff /-
protected theorem prop_iff {p : Prop} : IsEmpty p ↔ ¬p :=
  isEmpty_iff
#align is_empty.prop_iff IsEmpty.prop_iff
-/

variable [IsEmpty α]

#print IsEmpty.forall_iff /-
@[simp]
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro isEmptyElim
#align is_empty.forall_iff IsEmpty.forall_iff
-/

#print IsEmpty.exists_iff /-
@[simp]
theorem exists_iff {p : α → Prop} : (∃ a, p a) ↔ False :=
  iff_false_intro fun ⟨x, hx⟩ => IsEmpty.false x
#align is_empty.exists_iff IsEmpty.exists_iff
-/

-- see Note [lower instance priority]
instance (priority := 100) : Subsingleton α :=
  ⟨isEmptyElim⟩

end IsEmpty

#print not_nonempty_iff /-
@[simp]
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h1 h2 => h2.elim h1.elim⟩
#align not_nonempty_iff not_nonempty_iff
-/

#print not_isEmpty_iff /-
@[simp]
theorem not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α :=
  not_iff_comm.mp not_nonempty_iff
#align not_is_empty_iff not_isEmpty_iff
-/

#print isEmpty_Prop /-
@[simp]
theorem isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by simp only [← not_nonempty_iff, nonempty_Prop]
#align is_empty_Prop isEmpty_Prop
-/

#print isEmpty_pi /-
@[simp]
theorem isEmpty_pi {π : α → Sort _} : IsEmpty (∀ a, π a) ↔ ∃ a, IsEmpty (π a) := by
  simp only [← not_nonempty_iff, Classical.nonempty_pi, not_forall]
#align is_empty_pi isEmpty_pi
-/

/- warning: is_empty_sigma -> isEmpty_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : α -> Type.{u2}}, Iff (IsEmpty.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α E)) (forall (a : α), IsEmpty.{succ u2} (E a))
but is expected to have type
  forall {α : Type.{u2}} {E : α -> Type.{u1}}, Iff (IsEmpty.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α E)) (forall (a : α), IsEmpty.{succ u1} (E a))
Case conversion may be inaccurate. Consider using '#align is_empty_sigma isEmpty_sigmaₓ'. -/
@[simp]
theorem isEmpty_sigma {α} {E : α → Type _} : IsEmpty (Sigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]
#align is_empty_sigma isEmpty_sigma

/- warning: is_empty_psigma -> isEmpty_psigma is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {E : α -> Sort.{u2}}, Iff (IsEmpty.{max 1 u1 u2} (PSigma.{u1, u2} α E)) (forall (a : α), IsEmpty.{u2} (E a))
but is expected to have type
  forall {α : Sort.{u2}} {E : α -> Sort.{u1}}, Iff (IsEmpty.{max (max 1 u1) u2} (PSigma.{u2, u1} α E)) (forall (a : α), IsEmpty.{u1} (E a))
Case conversion may be inaccurate. Consider using '#align is_empty_psigma isEmpty_psigmaₓ'. -/
@[simp]
theorem isEmpty_psigma {α} {E : α → Sort _} : IsEmpty (PSigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]
#align is_empty_psigma isEmpty_psigma

#print isEmpty_subtype /-
@[simp]
theorem isEmpty_subtype (p : α → Prop) : IsEmpty (Subtype p) ↔ ∀ x, ¬p x := by
  simp only [← not_nonempty_iff, nonempty_subtype, not_exists]
#align is_empty_subtype isEmpty_subtype
-/

/- warning: is_empty_prod -> isEmpty_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Iff (IsEmpty.{max (succ u1) (succ u2)} (Prod.{u1, u2} α β)) (Or (IsEmpty.{succ u1} α) (IsEmpty.{succ u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Iff (IsEmpty.{max (succ u1) (succ u2)} (Prod.{u2, u1} α β)) (Or (IsEmpty.{succ u2} α) (IsEmpty.{succ u1} β))
Case conversion may be inaccurate. Consider using '#align is_empty_prod isEmpty_prodₓ'. -/
@[simp]
theorem isEmpty_prod {α β : Type _} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]
#align is_empty_prod isEmpty_prod

#print isEmpty_pprod /-
@[simp]
theorem isEmpty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]
#align is_empty_pprod isEmpty_pprod
-/

/- warning: is_empty_sum -> isEmpty_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Iff (IsEmpty.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (And (IsEmpty.{succ u1} α) (IsEmpty.{succ u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Iff (IsEmpty.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (And (IsEmpty.{succ u2} α) (IsEmpty.{succ u1} β))
Case conversion may be inaccurate. Consider using '#align is_empty_sum isEmpty_sumₓ'. -/
@[simp]
theorem isEmpty_sum {α β} : IsEmpty (Sum α β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]
#align is_empty_sum isEmpty_sum

/- warning: is_empty_psum -> isEmpty_psum is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, Iff (IsEmpty.{max 1 u1 u2} (PSum.{u1, u2} α β)) (And (IsEmpty.{u1} α) (IsEmpty.{u2} β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, Iff (IsEmpty.{max (max 1 u1) u2} (PSum.{u2, u1} α β)) (And (IsEmpty.{u2} α) (IsEmpty.{u1} β))
Case conversion may be inaccurate. Consider using '#align is_empty_psum isEmpty_psumₓ'. -/
@[simp]
theorem isEmpty_psum {α β} : IsEmpty (PSum α β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]
#align is_empty_psum isEmpty_psum

/- warning: is_empty_ulift -> isEmpty_ulift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Iff (IsEmpty.{succ (max u1 u2)} (ULift.{u2, u1} α)) (IsEmpty.{succ u1} α)
but is expected to have type
  forall {α : Type.{u2}}, Iff (IsEmpty.{max (succ u2) (succ u1)} (ULift.{u1, u2} α)) (IsEmpty.{succ u2} α)
Case conversion may be inaccurate. Consider using '#align is_empty_ulift isEmpty_uliftₓ'. -/
@[simp]
theorem isEmpty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_ulift]
#align is_empty_ulift isEmpty_ulift

#print isEmpty_plift /-
@[simp]
theorem isEmpty_plift {α} : IsEmpty (PLift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_plift]
#align is_empty_plift isEmpty_plift
-/

#print wellFounded_of_isEmpty /-
theorem wellFounded_of_isEmpty {α} [IsEmpty α] (r : α → α → Prop) : WellFounded r :=
  ⟨isEmptyElim⟩
#align well_founded_of_empty wellFounded_of_isEmpty
-/

variable (α)

#print isEmpty_or_nonempty /-
theorem isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α :=
  (em <| IsEmpty α).elim Or.inl <| Or.inr ∘ not_isEmpty_iff.mp
#align is_empty_or_nonempty isEmpty_or_nonempty
-/

#print not_isEmpty_of_nonempty /-
@[simp]
theorem not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsEmpty α :=
  not_isEmpty_iff.mpr h
#align not_is_empty_of_nonempty not_isEmpty_of_nonempty
-/

variable {α}

/- warning: function.extend_of_empty -> Function.extend_of_isEmpty is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {γ : Sort.{u3}} [_inst_1 : IsEmpty.{u1} α] (f : α -> β) (g : α -> γ) (h : β -> γ), Eq.{imax u2 u3} (β -> γ) (Function.extend.{u1, u2, u3} α β γ f g h) h
but is expected to have type
  forall {α : Sort.{u3}} {β : Sort.{u2}} {γ : Sort.{u1}} [_inst_1 : IsEmpty.{u3} α] (f : α -> β) (g : α -> γ) (h : β -> γ), Eq.{imax u2 u1} (β -> γ) (Function.extend.{u3, u2, u1} α β γ f g h) h
Case conversion may be inaccurate. Consider using '#align function.extend_of_empty Function.extend_of_isEmptyₓ'. -/
theorem Function.extend_of_isEmpty [IsEmpty α] (f : α → β) (g : α → γ) (h : β → γ) :
    Function.extend f g h = h :=
  funext fun x => Function.extend_apply' _ _ _ fun ⟨a, h⟩ => isEmptyElim a
#align function.extend_of_empty Function.extend_of_isEmpty

