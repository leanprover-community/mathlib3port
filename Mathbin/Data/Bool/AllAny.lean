/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.bool.all_any
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic

/-!
# Boolean quantifiers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This proves a few properties about `list.all` and `list.any`, which are the `bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/


variable {α : Type _} {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

namespace List

#print List.all_nil /-
@[simp]
theorem all_nil (p : α → Bool) : all [] p = tt :=
  rfl
#align list.all_nil List.all_nil
-/

@[simp]
theorem all_cons (p : α → Bool) (a : α) (l : List α) : all (a :: l) p = (p a && all l p) :=
  rfl
#align list.all_cons List.all_consₓ

#print List.all_iff_forall /-
theorem all_iff_forall {p : α → Bool} : all l p ↔ ∀ a ∈ l, p a :=
  by
  induction' l with a l ih
  · exact iff_of_true rfl (forall_mem_nil _)
  simp only [all_cons, Bool.and_coe_iff, ih, forall_mem_cons]
#align list.all_iff_forall List.all_iff_forall
-/

#print List.all_iff_forall_prop /-
theorem all_iff_forall_prop : (all l fun a => p a) ↔ ∀ a ∈ l, p a := by
  simp only [all_iff_forall, Bool.of_decide_iff]
#align list.all_iff_forall_prop List.all_iff_forall_prop
-/

#print List.any_nil /-
@[simp]
theorem any_nil (p : α → Bool) : any [] p = ff :=
  rfl
#align list.any_nil List.any_nil
-/

@[simp]
theorem any_cons (p : α → Bool) (a : α) (l : List α) : any (a :: l) p = (p a || any l p) :=
  rfl
#align list.any_cons List.any_consₓ

/- warning: list.any_iff_exists -> List.any_iff_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {p : α -> Bool}, Iff (coeSort.{1, 1} Bool Prop coeSortBool (List.any.{u1} α l p)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) (fun (H : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) => coeSort.{1, 1} Bool Prop coeSortBool (p a))))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {p : α -> Bool}, Iff (Eq.{1} Bool (List.any.{u1} α l p) Bool.true) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l) (Eq.{1} Bool (p a) Bool.true)))
Case conversion may be inaccurate. Consider using '#align list.any_iff_exists List.any_iff_existsₓ'. -/
theorem any_iff_exists {p : α → Bool} : any l p ↔ ∃ a ∈ l, p a :=
  by
  induction' l with a l ih
  · exact iff_of_false Bool.not_false' (not_exists_mem_nil _)
  simp only [any_cons, Bool.or_coe_iff, ih, exists_mem_cons_iff]
#align list.any_iff_exists List.any_iff_exists

/- warning: list.any_iff_exists_prop -> List.any_iff_exists_prop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (coeSort.{1, 1} Bool Prop coeSortBool (List.any.{u1} α l (fun (a : α) => Decidable.decide (p a) (_inst_1 a)))) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) (fun (H : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) => p a)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{1} Bool (List.any.{u1} α l (fun (a : α) => Decidable.decide (p a) (_inst_1 a))) Bool.true) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l) (p a)))
Case conversion may be inaccurate. Consider using '#align list.any_iff_exists_prop List.any_iff_exists_propₓ'. -/
theorem any_iff_exists_prop : (any l fun a => p a) ↔ ∃ a ∈ l, p a := by simp [any_iff_exists]
#align list.any_iff_exists_prop List.any_iff_exists_prop

#print List.any_of_mem /-
theorem any_of_mem {p : α → Bool} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_iff_exists.2 ⟨_, h₁, h₂⟩
#align list.any_of_mem List.any_of_mem
-/

end List

