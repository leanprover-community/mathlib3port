/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Logic.Function.Basic
import Mathbin.Tactic.Protected

/-!
# Types that are empty

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
-/

instance : IsEmpty Empty :=
  ⟨Empty.elim⟩

instance : IsEmpty PEmpty :=
  ⟨PEmpty.elim⟩

instance : IsEmpty False :=
  ⟨id⟩

instance : IsEmpty (Fin 0) :=
  ⟨fun n => Nat.not_lt_zero n.1 n.2⟩

#print Function.is_empty /-
protected theorem Function.is_empty [IsEmpty β] (f : α → β) : IsEmpty α :=
  ⟨fun x => IsEmpty.false (f x)⟩
-/

instance {p : α → Sort _} [h : Nonempty α] [∀ x, IsEmpty (p x)] : IsEmpty (∀ x, p x) :=
  h.elim fun x => Function.is_empty <| Function.eval x

#print PProd.is_empty_left /-
instance PProd.is_empty_left [IsEmpty α] : IsEmpty (PProd α β) :=
  Function.is_empty PProd.fst
-/

#print PProd.is_empty_right /-
instance PProd.is_empty_right [IsEmpty β] : IsEmpty (PProd α β) :=
  Function.is_empty PProd.snd
-/

#print Prod.is_empty_left /-
instance Prod.is_empty_left {α β} [IsEmpty α] : IsEmpty (α × β) :=
  Function.is_empty Prod.fst
-/

#print Prod.is_empty_right /-
instance Prod.is_empty_right {α β} [IsEmpty β] : IsEmpty (α × β) :=
  Function.is_empty Prod.snd
-/

instance [IsEmpty α] [IsEmpty β] : IsEmpty (PSum α β) :=
  ⟨fun x => PSum.rec IsEmpty.false IsEmpty.false x⟩

instance {α β} [IsEmpty α] [IsEmpty β] : IsEmpty (Sum α β) :=
  ⟨fun x => Sum.rec IsEmpty.false IsEmpty.false x⟩

/-- subtypes of an empty type are empty -/
instance [IsEmpty α] (p : α → Prop) : IsEmpty (Subtype p) :=
  ⟨fun x => IsEmpty.false x.1⟩

#print Subtype.is_empty_of_false /-
/-- subtypes by an all-false predicate are false. -/
theorem Subtype.is_empty_of_false {p : α → Prop} (hp : ∀ a, ¬p a) : IsEmpty (Subtype p) :=
  ⟨fun x => hp _ x.2⟩
-/

#print Subtype.is_empty_false /-
/-- subtypes by false are false. -/
instance Subtype.is_empty_false : IsEmpty { a : α // False } :=
  Subtype.is_empty_of_false fun a => id
-/

#print Sigma.is_empty_left /-
instance Sigma.is_empty_left {α} [IsEmpty α] {E : α → Type _} : IsEmpty (Sigma E) :=
  Function.is_empty Sigma.fst
-/

-- Test that `pi.is_empty` finds this instance.
example [h : Nonempty α] [IsEmpty β] : IsEmpty (α → β) := by infer_instance

#print isEmptyElim /-
/-- Eliminate out of a type that `is_empty` (without using projection notation). -/
@[elab_as_elim]
def isEmptyElim [IsEmpty α] {p : α → Sort _} (a : α) : p a :=
  (IsEmpty.false a).elim
-/

#print is_empty_iff /-
theorem is_empty_iff : IsEmpty α ↔ α → False :=
  ⟨@IsEmpty.false α, IsEmpty.mk⟩
-/

namespace IsEmpty

open Function

#print IsEmpty.elim /-
/-- Eliminate out of a type that `is_empty` (using projection notation). -/
protected def elim (h : IsEmpty α) {p : α → Sort _} (a : α) : p a :=
  isEmptyElim a
-/

#print IsEmpty.elim' /-
/-- Non-dependent version of `is_empty.elim`. Helpful if the elaborator cannot elaborate `h.elim a`
  correctly. -/
protected def elim' {β : Sort _} (h : IsEmpty α) (a : α) : β :=
  h.elim a
-/

#print IsEmpty.prop_iff /-
protected theorem prop_iff {p : Prop} : IsEmpty p ↔ ¬p :=
  is_empty_iff
-/

variable [IsEmpty α]

#print IsEmpty.forall_iff /-
@[simp]
theorem forall_iff {p : α → Prop} : (∀ a, p a) ↔ True :=
  iff_true_intro isEmptyElim
-/

#print IsEmpty.exists_iff /-
@[simp]
theorem exists_iff {p : α → Prop} : (∃ a, p a) ↔ False :=
  iff_false_intro fun ⟨x, hx⟩ => IsEmpty.false x
-/

-- see Note [lower instance priority]
instance (priority := 100) : Subsingleton α :=
  ⟨isEmptyElim⟩

end IsEmpty

#print not_nonempty_iff /-
@[simp]
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h => ⟨fun x => h ⟨x⟩⟩, fun h1 h2 => h2.elim h1.elim⟩
-/

#print not_is_empty_iff /-
@[simp]
theorem not_is_empty_iff : ¬IsEmpty α ↔ Nonempty α :=
  not_iff_comm.mp not_nonempty_iff
-/

#print is_empty_Prop /-
@[simp]
theorem is_empty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by simp only [← not_nonempty_iff, nonempty_Prop]
-/

#print is_empty_pi /-
@[simp]
theorem is_empty_pi {π : α → Sort _} : IsEmpty (∀ a, π a) ↔ ∃ a, IsEmpty (π a) := by
  simp only [← not_nonempty_iff, Classical.nonempty_pi, not_forall]
-/

/- warning: is_empty_sigma -> is_empty_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {E : α -> Type.{u_2}}, Iff (IsEmpty.{(max (succ u_1) (succ u_2))} (Sigma.{u_1 u_2} α E)) (forall (a : α), IsEmpty.{succ u_2} (E a))
but is expected to have type
  forall {α : Type.{u_1}} {E : α -> Type.{u_2}}, Iff (IsEmpty.{(max (succ u_2) (succ u_1))} (Sigma.{u_1 u_2} α E)) (forall (a : α), IsEmpty.{succ u_2} (E a))
Case conversion may be inaccurate. Consider using '#align is_empty_sigma is_empty_sigmaₓ'. -/
@[simp]
theorem is_empty_sigma {α} {E : α → Type _} : IsEmpty (Sigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

/- warning: is_empty_psigma -> is_empty_psigma is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {E : α -> Sort.{u_2}}, Iff (IsEmpty.{(max 1 u_1 u_2)} (PSigma.{u_1 u_2} α E)) (forall (a : α), IsEmpty.{u_2} (E a))
but is expected to have type
  forall {α : Sort.{u_1}} {E : α -> Sort.{u_2}}, Iff (IsEmpty.{(max (max 1 u_2) u_1)} (PSigma.{u_1 u_2} α E)) (forall (a : α), IsEmpty.{u_2} (E a))
Case conversion may be inaccurate. Consider using '#align is_empty_psigma is_empty_psigmaₓ'. -/
@[simp]
theorem is_empty_psigma {α} {E : α → Sort _} : IsEmpty (PSigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]

#print is_empty_subtype /-
@[simp]
theorem is_empty_subtype (p : α → Prop) : IsEmpty (Subtype p) ↔ ∀ x, ¬p x := by
  simp only [← not_nonempty_iff, nonempty_subtype, not_exists]
-/

/- warning: is_empty_prod -> is_empty_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Iff (IsEmpty.{(max (succ u_1) (succ u_2))} (Prod.{u_1 u_2} α β)) (Or (IsEmpty.{succ u_1} α) (IsEmpty.{succ u_2} β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Iff (IsEmpty.{(max (succ u_2) (succ u_1))} (Prod.{u_1 u_2} α β)) (Or (IsEmpty.{succ u_1} α) (IsEmpty.{succ u_2} β))
Case conversion may be inaccurate. Consider using '#align is_empty_prod is_empty_prodₓ'. -/
@[simp]
theorem is_empty_prod {α β : Type _} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]

#print is_empty_pprod /-
@[simp]
theorem is_empty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]
-/

/- warning: is_empty_sum -> is_empty_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Iff (IsEmpty.{(max (succ u_1) (succ u_2))} (Sum.{u_1 u_2} α β)) (And (IsEmpty.{succ u_1} α) (IsEmpty.{succ u_2} β))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}}, Iff (IsEmpty.{(max (succ u_2) (succ u_1))} (Sum.{u_1 u_2} α β)) (And (IsEmpty.{succ u_1} α) (IsEmpty.{succ u_2} β))
Case conversion may be inaccurate. Consider using '#align is_empty_sum is_empty_sumₓ'. -/
@[simp]
theorem is_empty_sum {α β} : IsEmpty (Sum α β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]

/- warning: is_empty_psum -> is_empty_psum is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Iff (IsEmpty.{(max 1 u_1 u_2)} (PSum.{u_1 u_2} α β)) (And (IsEmpty.{u_1} α) (IsEmpty.{u_2} β))
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}}, Iff (IsEmpty.{(max (max 1 u_2) u_1)} (PSum.{u_1 u_2} α β)) (And (IsEmpty.{u_1} α) (IsEmpty.{u_2} β))
Case conversion may be inaccurate. Consider using '#align is_empty_psum is_empty_psumₓ'. -/
@[simp]
theorem is_empty_psum {α β} : IsEmpty (PSum α β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]

/- warning: is_empty_ulift -> is_empty_ulift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, Iff (IsEmpty.{succ (max u_1 u_2)} (ULift.{u_2 u_1} α)) (IsEmpty.{succ u_1} α)
but is expected to have type
  forall {α : Type.{u_1}}, Iff (IsEmpty.{(max (succ u_1) (succ u_2))} (ULift.{u_2 u_1} α)) (IsEmpty.{succ u_1} α)
Case conversion may be inaccurate. Consider using '#align is_empty_ulift is_empty_uliftₓ'. -/
@[simp]
theorem is_empty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α := by simp only [← not_nonempty_iff, nonempty_ulift]

#print is_empty_plift /-
@[simp]
theorem is_empty_plift {α} : IsEmpty (PLift α) ↔ IsEmpty α := by simp only [← not_nonempty_iff, nonempty_plift]
-/

#print well_founded_of_empty /-
theorem well_founded_of_empty {α} [IsEmpty α] (r : α → α → Prop) : WellFounded r :=
  ⟨isEmptyElim⟩
-/

variable (α)

#print is_empty_or_nonempty /-
theorem is_empty_or_nonempty : IsEmpty α ∨ Nonempty α :=
  (em <| IsEmpty α).elim Or.inl <| Or.inr ∘ not_is_empty_iff.mp
-/

#print not_is_empty_of_nonempty /-
@[simp]
theorem not_is_empty_of_nonempty [h : Nonempty α] : ¬IsEmpty α :=
  not_is_empty_iff.mpr h
-/

variable {α}

/- warning: function.extend_of_empty -> Function.extend_of_empty is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} [_inst_1 : IsEmpty.{u_1} α] (f : α -> β) (g : α -> γ) (h : β -> γ), Eq.{(imax u_2 u_3)} (β -> γ) (Function.extend.{u_1 u_2 u_3} α β γ f g h) h
but is expected to have type
  forall {α : Sort.{u_1}} {β : Sort.{u_2}} {γ : Sort.{u_3}} [inst._@.Mathlib.Logic.IsEmpty._hyg.974 : IsEmpty.{u_1} α] (f : α -> β) (g : α -> γ) (h : β -> γ), Eq.{(imax u_2 u_3)} (β -> γ) (Function.extend.{u_1 u_2 u_3} α β γ f g h) h
Case conversion may be inaccurate. Consider using '#align function.extend_of_empty Function.extend_of_emptyₓ'. -/
theorem Function.extend_of_empty [IsEmpty α] (f : α → β) (g : α → γ) (h : β → γ) : Function.extend f g h = h :=
  funext fun x => (Function.extend_apply' _ _ _) fun ⟨a, h⟩ => isEmptyElim a

