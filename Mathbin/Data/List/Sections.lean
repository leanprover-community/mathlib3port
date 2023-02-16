/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.sections
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Forall2

/-!
# List sections

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some stuff about `list.sections` (definition in `data.list.defs`). A section of a
list of lists `[l₁, ..., lₙ]` is a list whose `i`-th element comes from the `i`-th list.
-/


open Nat Function

namespace List

variable {α β : Type _}

#print List.mem_sections /-
theorem mem_sections {L : List (List α)} {f} : f ∈ sections L ↔ Forall₂ (· ∈ ·) f L :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · induction L generalizing f
    · cases mem_singleton.1 h
      exact forall₂.nil
    simp only [sections, bind_eq_bind, mem_bind, mem_map] at h
    rcases h with ⟨_, _, _, _, rfl⟩
    simp only [*, forall₂_cons, true_and_iff]
  · induction' h with a l f L al fL fs
    · exact Or.inl rfl
    simp only [sections, bind_eq_bind, mem_bind, mem_map]
    exact ⟨_, fs, _, al, rfl, rfl⟩
#align list.mem_sections List.mem_sections
-/

#print List.mem_sections_length /-
theorem mem_sections_length {L : List (List α)} {f} (h : f ∈ sections L) : length f = length L :=
  (mem_sections.1 h).length_eq
#align list.mem_sections_length List.mem_sections_length
-/

/- warning: list.rel_sections -> List.rel_sections is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} (List.{u1} (List.{u1} α)) (List.{u2} (List.{u2} β)) (List.{u1} (List.{u1} α)) (List.{u2} (List.{u2} β)) (List.Forall₂.{u1, u2} (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β r)) (List.Forall₂.{u1, u2} (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β r)) (List.sections.{u1} α) (List.sections.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop}, Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} (List.{u2} (List.{u2} α)) (List.{u1} (List.{u1} β)) (List.{u2} (List.{u2} α)) (List.{u1} (List.{u1} β)) (List.Forall₂.{u2, u1} (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β r)) (List.Forall₂.{u2, u1} (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β r)) (List.sections.{u2} α) (List.sections.{u1} β)
Case conversion may be inaccurate. Consider using '#align list.rel_sections List.rel_sectionsₓ'. -/
theorem rel_sections {r : α → β → Prop} :
    (Forall₂ (Forall₂ r) ⇒ Forall₂ (Forall₂ r)) sections sections
  | _, _, forall₂.nil => Forall₂.cons Forall₂.nil Forall₂.nil
  | _, _, forall₂.cons h₀ h₁ =>
    rel_bind (rel_sections h₁) fun _ _ hl => rel_map (fun _ _ ha => Forall₂.cons ha hl) h₀
#align list.rel_sections List.rel_sections

end List

