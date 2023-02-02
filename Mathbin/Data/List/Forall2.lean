/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module data.list.forall2
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Infix

/-!
# Double universal quantification on a list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides an API for `list.forall₂` (definition in `data.list.defs`).
`forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length, and whenever `a` is the nth element
of `l₁`, and `b` is the nth element of `l₂`, then `R a b` is satisfied.
-/


open Nat Function

namespace List

variable {α β γ δ : Type _} {R S : α → β → Prop} {P : γ → δ → Prop} {Rₐ : α → α → Prop}

open Relator

mk_iff_of_inductive_prop List.Forall₂ List.forall₂_iff

/- warning: list.forall₂_cons -> List.forall₂_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {a : α} {b : β} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, Iff (List.Forall₂.{u1, u2} α β R (List.cons.{u1} α a l₁) (List.cons.{u2} β b l₂)) (And (R a b) (List.Forall₂.{u1, u2} α β R l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {a : α} {b : β} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, Iff (List.Forall₂.{u2, u1} α β R (List.cons.{u2} α a l₁) (List.cons.{u1} β b l₂)) (And (R a b) (List.Forall₂.{u2, u1} α β R l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.forall₂_cons List.forall₂_consₓ'. -/
@[simp]
theorem forall₂_cons {a b l₁ l₂} : Forall₂ R (a :: l₁) (b :: l₂) ↔ R a b ∧ Forall₂ R l₁ l₂ :=
  ⟨fun h => by cases' h with h₁ h₂ <;> constructor <;> assumption, fun ⟨h₁, h₂⟩ =>
    Forall₂.cons h₁ h₂⟩
#align list.forall₂_cons List.forall₂_cons

/- warning: list.forall₂.imp -> List.Forall₂.imp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {S : α -> β -> Prop}, (forall (a : α) (b : β), (R a b) -> (S a b)) -> (forall {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (List.Forall₂.{u1, u2} α β R l₁ l₂) -> (List.Forall₂.{u1, u2} α β S l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {S : α -> β -> Prop}, (forall (a : α) (b : β), (R a b) -> (S a b)) -> (forall {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (List.Forall₂.{u2, u1} α β R l₁ l₂) -> (List.Forall₂.{u2, u1} α β S l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.forall₂.imp List.Forall₂.impₓ'. -/
theorem Forall₂.imp (H : ∀ a b, R a b → S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> solve_by_elim
#align list.forall₂.imp List.Forall₂.imp

/- warning: list.forall₂.mp -> List.Forall₂.mp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {S : α -> β -> Prop} {Q : α -> β -> Prop}, (forall (a : α) (b : β), (Q a b) -> (R a b) -> (S a b)) -> (forall {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (List.Forall₂.{u1, u2} α β Q l₁ l₂) -> (List.Forall₂.{u1, u2} α β R l₁ l₂) -> (List.Forall₂.{u1, u2} α β S l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {S : α -> β -> Prop} {Q : α -> β -> Prop}, (forall (a : α) (b : β), (Q a b) -> (R a b) -> (S a b)) -> (forall {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (List.Forall₂.{u2, u1} α β Q l₁ l₂) -> (List.Forall₂.{u2, u1} α β R l₁ l₂) -> (List.Forall₂.{u2, u1} α β S l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.forall₂.mp List.Forall₂.mpₓ'. -/
theorem Forall₂.mp {Q : α → β → Prop} (h : ∀ a b, Q a b → R a b → S a b) :
    ∀ {l₁ l₂}, Forall₂ Q l₁ l₂ → Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | [], [], forall₂.nil, forall₂.nil => Forall₂.nil
  | a :: l₁, b :: l₂, forall₂.cons hr hrs, forall₂.cons hq hqs =>
    Forall₂.cons (h a b hr hq) (forall₂.mp hrs hqs)
#align list.forall₂.mp List.Forall₂.mp

/- warning: list.forall₂.flip -> List.Forall₂.flip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {a : List.{u1} α} {b : List.{u2} β}, (List.Forall₂.{u2, u1} β α (flip.{succ u1, succ u2, 1} α β Prop R) b a) -> (List.Forall₂.{u1, u2} α β R a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {a : List.{u2} α} {b : List.{u1} β}, (List.Forall₂.{u1, u2} β α (flip.{succ u2, succ u1, 1} α β Prop R) b a) -> (List.Forall₂.{u2, u1} α β R a b)
Case conversion may be inaccurate. Consider using '#align list.forall₂.flip List.Forall₂.flipₓ'. -/
theorem Forall₂.flip : ∀ {a b}, Forall₂ (flip R) b a → Forall₂ R a b
  | _, _, forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => Forall₂.cons h₁ h₂.flip
#align list.forall₂.flip List.Forall₂.flip

#print List.forall₂_same /-
@[simp]
theorem forall₂_same : ∀ {l : List α}, Forall₂ Rₐ l l ↔ ∀ x ∈ l, Rₐ x x
  | [] => by simp
  | a :: l => by simp [@forall₂_same l]
#align list.forall₂_same List.forall₂_same
-/

#print List.forall₂_refl /-
theorem forall₂_refl [IsRefl α Rₐ] (l : List α) : Forall₂ Rₐ l l :=
  forall₂_same.2 fun a h => refl _
#align list.forall₂_refl List.forall₂_refl
-/

#print List.forall₂_eq_eq_eq /-
@[simp]
theorem forall₂_eq_eq_eq : Forall₂ ((· = ·) : α → α → Prop) = (· = ·) :=
  by
  funext a b; apply propext
  constructor
  · intro h
    induction h
    · rfl
    simp only [*] <;> constructor <;> rfl
  · rintro rfl
    exact forall₂_refl _
#align list.forall₂_eq_eq_eq List.forall₂_eq_eq_eq
-/

#print List.forall₂_nil_left_iff /-
@[simp]
theorem forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ l = nil :=
  ⟨fun H => by cases H <;> rfl, by rintro rfl <;> exact forall₂.nil⟩
#align list.forall₂_nil_left_iff List.forall₂_nil_left_iff
-/

/- warning: list.forall₂_nil_right_iff -> List.forall₂_nil_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {l : List.{u1} α}, Iff (List.Forall₂.{u1, u2} α β R l (List.nil.{u2} β)) (Eq.{succ u1} (List.{u1} α) l (List.nil.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {l : List.{u2} α}, Iff (List.Forall₂.{u2, u1} α β R l (List.nil.{u1} β)) (Eq.{succ u2} (List.{u2} α) l (List.nil.{u2} α))
Case conversion may be inaccurate. Consider using '#align list.forall₂_nil_right_iff List.forall₂_nil_right_iffₓ'. -/
@[simp]
theorem forall₂_nil_right_iff {l} : Forall₂ R l nil ↔ l = nil :=
  ⟨fun H => by cases H <;> rfl, by rintro rfl <;> exact forall₂.nil⟩
#align list.forall₂_nil_right_iff List.forall₂_nil_right_iff

/- warning: list.forall₂_cons_left_iff -> List.forall₂_cons_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {a : α} {l : List.{u1} α} {u : List.{u2} β}, Iff (List.Forall₂.{u1, u2} α β R (List.cons.{u1} α a l) u) (Exists.{succ u2} β (fun (b : β) => Exists.{succ u2} (List.{u2} β) (fun (u' : List.{u2} β) => And (R a b) (And (List.Forall₂.{u1, u2} α β R l u') (Eq.{succ u2} (List.{u2} β) u (List.cons.{u2} β b u'))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {a : α} {l : List.{u2} α} {u : List.{u1} β}, Iff (List.Forall₂.{u2, u1} α β R (List.cons.{u2} α a l) u) (Exists.{succ u1} β (fun (b : β) => Exists.{succ u1} (List.{u1} β) (fun (u' : List.{u1} β) => And (R a b) (And (List.Forall₂.{u2, u1} α β R l u') (Eq.{succ u1} (List.{u1} β) u (List.cons.{u1} β b u'))))))
Case conversion may be inaccurate. Consider using '#align list.forall₂_cons_left_iff List.forall₂_cons_left_iffₓ'. -/
theorem forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨b, u', h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂
#align list.forall₂_cons_left_iff List.forall₂_cons_left_iff

#print List.forall₂_cons_right_iff /-
theorem forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h =>
      match u, h with
      | b :: u', forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    fun h =>
    match u, h with
    | _, ⟨b, u', h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂
#align list.forall₂_cons_right_iff List.forall₂_cons_right_iff
-/

/- warning: list.forall₂_and_left -> List.forall₂_and_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {p : α -> Prop} (l : List.{u1} α) (u : List.{u2} β), Iff (List.Forall₂.{u1, u2} α β (fun (a : α) (b : β) => And (p a) (R a b)) l u) (And (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (p a)) (List.Forall₂.{u1, u2} α β R l u))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {p : α -> Prop} (l : List.{u2} α) (u : List.{u1} β), Iff (List.Forall₂.{u2, u1} α β (fun (a : α) (b : β) => And (p a) (R a b)) l u) (And (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (p a)) (List.Forall₂.{u2, u1} α β R l u))
Case conversion may be inaccurate. Consider using '#align list.forall₂_and_left List.forall₂_and_leftₓ'. -/
theorem forall₂_and_left {p : α → Prop} :
    ∀ l u, Forall₂ (fun a b => p a ∧ R a b) l u ↔ (∀ a ∈ l, p a) ∧ Forall₂ R l u
  | [], u => by
    simp only [forall₂_nil_left_iff, forall_prop_of_false (not_mem_nil _), imp_true_iff,
      true_and_iff]
  | a :: l, u => by
    simp only [forall₂_and_left l, forall₂_cons_left_iff, forall_mem_cons, and_assoc', and_comm',
      and_left_comm, exists_and_distrib_left.symm]
#align list.forall₂_and_left List.forall₂_and_left

#print List.forall₂_map_left_iff /-
@[simp]
theorem forall₂_map_left_iff {f : γ → α} :
    ∀ {l u}, Forall₂ R (map f l) u ↔ Forall₂ (fun c b => R (f c) b) l u
  | [], _ => by simp only [map, forall₂_nil_left_iff]
  | a :: l, _ => by simp only [map, forall₂_cons_left_iff, forall₂_map_left_iff]
#align list.forall₂_map_left_iff List.forall₂_map_left_iff
-/

/- warning: list.forall₂_map_right_iff -> List.forall₂_map_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {R : α -> β -> Prop} {f : γ -> β} {l : List.{u1} α} {u : List.{u3} γ}, Iff (List.Forall₂.{u1, u2} α β R l (List.map.{u3, u2} γ β f u)) (List.Forall₂.{u1, u3} α γ (fun (a : α) (c : γ) => R a (f c)) l u)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {R : α -> β -> Prop} {f : γ -> β} {l : List.{u3} α} {u : List.{u2} γ}, Iff (List.Forall₂.{u3, u1} α β R l (List.map.{u2, u1} γ β f u)) (List.Forall₂.{u3, u2} α γ (fun (a : α) (c : γ) => R a (f c)) l u)
Case conversion may be inaccurate. Consider using '#align list.forall₂_map_right_iff List.forall₂_map_right_iffₓ'. -/
@[simp]
theorem forall₂_map_right_iff {f : γ → β} :
    ∀ {l u}, Forall₂ R l (map f u) ↔ Forall₂ (fun a c => R a (f c)) l u
  | _, [] => by simp only [map, forall₂_nil_right_iff]
  | _, b :: u => by simp only [map, forall₂_cons_right_iff, forall₂_map_right_iff]
#align list.forall₂_map_right_iff List.forall₂_map_right_iff

/- warning: list.left_unique_forall₂' -> List.left_unique_forall₂' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, (Relator.LeftUnique.{u1, u2} α β R) -> (forall {a : List.{u1} α} {b : List.{u1} α} {c : List.{u2} β}, (List.Forall₂.{u1, u2} α β R a c) -> (List.Forall₂.{u1, u2} α β R b c) -> (Eq.{succ u1} (List.{u1} α) a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, (Relator.LeftUnique.{u2, u1} α β R) -> (forall {a : List.{u2} α} {b : List.{u2} α} {c : List.{u1} β}, (List.Forall₂.{u2, u1} α β R a c) -> (List.Forall₂.{u2, u1} α β R b c) -> (Eq.{succ u2} (List.{u2} α) a b))
Case conversion may be inaccurate. Consider using '#align list.left_unique_forall₂' List.left_unique_forall₂'ₓ'. -/
theorem left_unique_forall₂' (hr : LeftUnique R) : ∀ {a b c}, Forall₂ R a c → Forall₂ R b c → a = b
  | a₀, nil, a₁, forall₂.nil, forall₂.nil => rfl
  | a₀ :: l₀, b :: l, a₁ :: l₁, forall₂.cons ha₀ h₀, forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ left_unique_forall₂' h₀ h₁ ▸ rfl
#align list.left_unique_forall₂' List.left_unique_forall₂'

/- warning: relator.left_unique.forall₂ -> Relator.LeftUnique.forall₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, (Relator.LeftUnique.{u1, u2} α β R) -> (Relator.LeftUnique.{u1, u2} (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β R))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, (Relator.LeftUnique.{u2, u1} α β R) -> (Relator.LeftUnique.{u2, u1} (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β R))
Case conversion may be inaccurate. Consider using '#align relator.left_unique.forall₂ Relator.LeftUnique.forall₂ₓ'. -/
theorem Relator.LeftUnique.forall₂ (hr : LeftUnique R) : LeftUnique (Forall₂ R) :=
  @left_unique_forall₂' _ _ _ hr
#align relator.left_unique.forall₂ Relator.LeftUnique.forall₂

/- warning: list.right_unique_forall₂' -> List.right_unique_forall₂' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, (Relator.RightUnique.{u1, u2} α β R) -> (forall {a : List.{u1} α} {b : List.{u2} β} {c : List.{u2} β}, (List.Forall₂.{u1, u2} α β R a b) -> (List.Forall₂.{u1, u2} α β R a c) -> (Eq.{succ u2} (List.{u2} β) b c))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, (Relator.RightUnique.{u2, u1} α β R) -> (forall {a : List.{u2} α} {b : List.{u1} β} {c : List.{u1} β}, (List.Forall₂.{u2, u1} α β R a b) -> (List.Forall₂.{u2, u1} α β R a c) -> (Eq.{succ u1} (List.{u1} β) b c))
Case conversion may be inaccurate. Consider using '#align list.right_unique_forall₂' List.right_unique_forall₂'ₓ'. -/
theorem right_unique_forall₂' (hr : RightUnique R) :
    ∀ {a b c}, Forall₂ R a b → Forall₂ R a c → b = c
  | nil, a₀, a₁, forall₂.nil, forall₂.nil => rfl
  | b :: l, a₀ :: l₀, a₁ :: l₁, forall₂.cons ha₀ h₀, forall₂.cons ha₁ h₁ =>
    hr ha₀ ha₁ ▸ right_unique_forall₂' h₀ h₁ ▸ rfl
#align list.right_unique_forall₂' List.right_unique_forall₂'

/- warning: relator.right_unique.forall₂ -> Relator.RightUnique.forall₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, (Relator.RightUnique.{u1, u2} α β R) -> (Relator.RightUnique.{u1, u2} (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β R))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, (Relator.RightUnique.{u2, u1} α β R) -> (Relator.RightUnique.{u2, u1} (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β R))
Case conversion may be inaccurate. Consider using '#align relator.right_unique.forall₂ Relator.RightUnique.forall₂ₓ'. -/
theorem Relator.RightUnique.forall₂ (hr : RightUnique R) : RightUnique (Forall₂ R) :=
  @right_unique_forall₂' _ _ _ hr
#align relator.right_unique.forall₂ Relator.RightUnique.forall₂

/- warning: relator.bi_unique.forall₂ -> Relator.BiUnique.forall₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, (Relator.BiUnique.{u1, u2} α β R) -> (Relator.BiUnique.{u1, u2} (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β R))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, (Relator.BiUnique.{u2, u1} α β R) -> (Relator.BiUnique.{u2, u1} (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β R))
Case conversion may be inaccurate. Consider using '#align relator.bi_unique.forall₂ Relator.BiUnique.forall₂ₓ'. -/
theorem Relator.BiUnique.forall₂ (hr : BiUnique R) : BiUnique (Forall₂ R) :=
  ⟨hr.left.forall₂, hr.right.forall₂⟩
#align relator.bi_unique.forall₂ Relator.BiUnique.forall₂

/- warning: list.forall₂.length_eq -> List.Forall₂.length_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (List.Forall₂.{u1, u2} α β R l₁ l₂) -> (Eq.{1} Nat (List.length.{u1} α l₁) (List.length.{u2} β l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (List.Forall₂.{u2, u1} α β R l₁ l₂) -> (Eq.{1} Nat (List.length.{u2} α l₁) (List.length.{u1} β l₂))
Case conversion may be inaccurate. Consider using '#align list.forall₂.length_eq List.Forall₂.length_eqₓ'. -/
theorem Forall₂.length_eq : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → length l₁ = length l₂
  | _, _, forall₂.nil => rfl
  | _, _, forall₂.cons h₁ h₂ => congr_arg succ (forall₂.length_eq h₂)
#align list.forall₂.length_eq List.Forall₂.length_eq

/- warning: list.forall₂.nth_le -> List.Forall₂.nthLe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {x : List.{u1} α} {y : List.{u2} β}, (List.Forall₂.{u1, u2} α β R x y) -> (forall {{i : Nat}} (hx : LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} α x)) (hy : LT.lt.{0} Nat Nat.hasLt i (List.length.{u2} β y)), R (List.nthLe.{u1} α x i hx) (List.nthLe.{u2} β y i hy))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {x : List.{u2} α} {y : List.{u1} β}, (List.Forall₂.{u2, u1} α β R x y) -> (forall {{i : Nat}} (hx : LT.lt.{0} Nat instLTNat i (List.length.{u2} α x)) (hy : LT.lt.{0} Nat instLTNat i (List.length.{u1} β y)), R (List.nthLe.{u2} α x i hx) (List.nthLe.{u1} β y i hy))
Case conversion may be inaccurate. Consider using '#align list.forall₂.nth_le List.Forall₂.nthLeₓ'. -/
theorem Forall₂.nthLe :
    ∀ {x : List α} {y : List β} (h : Forall₂ R x y) ⦃i : ℕ⦄ (hx : i < x.length) (hy : i < y.length),
      R (x.nthLe i hx) (y.nthLe i hy)
  | a₁ :: l₁, a₂ :: l₂, forall₂.cons ha hl, 0, hx, hy => ha
  | a₁ :: l₁, a₂ :: l₂, forall₂.cons ha hl, succ i, hx, hy => hl.nthLe _ _
#align list.forall₂.nth_le List.Forall₂.nthLe

/- warning: list.forall₂_of_length_eq_of_nth_le -> List.forall₂_of_length_eq_of_nthLe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {x : List.{u1} α} {y : List.{u2} β}, (Eq.{1} Nat (List.length.{u1} α x) (List.length.{u2} β y)) -> (forall (i : Nat) (h₁ : LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} α x)) (h₂ : LT.lt.{0} Nat Nat.hasLt i (List.length.{u2} β y)), R (List.nthLe.{u1} α x i h₁) (List.nthLe.{u2} β y i h₂)) -> (List.Forall₂.{u1, u2} α β R x y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {x : List.{u2} α} {y : List.{u1} β}, (Eq.{1} Nat (List.length.{u2} α x) (List.length.{u1} β y)) -> (forall (i : Nat) (h₁ : LT.lt.{0} Nat instLTNat i (List.length.{u2} α x)) (h₂ : LT.lt.{0} Nat instLTNat i (List.length.{u1} β y)), R (List.nthLe.{u2} α x i h₁) (List.nthLe.{u1} β y i h₂)) -> (List.Forall₂.{u2, u1} α β R x y)
Case conversion may be inaccurate. Consider using '#align list.forall₂_of_length_eq_of_nth_le List.forall₂_of_length_eq_of_nthLeₓ'. -/
theorem forall₂_of_length_eq_of_nthLe :
    ∀ {x : List α} {y : List β},
      x.length = y.length → (∀ i h₁ h₂, R (x.nthLe i h₁) (y.nthLe i h₂)) → Forall₂ R x y
  | [], [], hl, h => Forall₂.nil
  | a₁ :: l₁, a₂ :: l₂, hl, h =>
    Forall₂.cons (h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
      (forall₂_of_length_eq_of_nth_le (succ.inj hl) fun i h₁ h₂ =>
        h i.succ (succ_lt_succ h₁) (succ_lt_succ h₂))
#align list.forall₂_of_length_eq_of_nth_le List.forall₂_of_length_eq_of_nthLe

/- warning: list.forall₂_iff_nth_le -> List.forall₂_iff_nthLe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, Iff (List.Forall₂.{u1, u2} α β R l₁ l₂) (And (Eq.{1} Nat (List.length.{u1} α l₁) (List.length.{u2} β l₂)) (forall (i : Nat) (h₁ : LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} α l₁)) (h₂ : LT.lt.{0} Nat Nat.hasLt i (List.length.{u2} β l₂)), R (List.nthLe.{u1} α l₁ i h₁) (List.nthLe.{u2} β l₂ i h₂)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, Iff (List.Forall₂.{u2, u1} α β R l₁ l₂) (And (Eq.{1} Nat (List.length.{u2} α l₁) (List.length.{u1} β l₂)) (forall (i : Nat) (h₁ : LT.lt.{0} Nat instLTNat i (List.length.{u2} α l₁)) (h₂ : LT.lt.{0} Nat instLTNat i (List.length.{u1} β l₂)), R (List.nthLe.{u2} α l₁ i h₁) (List.nthLe.{u1} β l₂ i h₂)))
Case conversion may be inaccurate. Consider using '#align list.forall₂_iff_nth_le List.forall₂_iff_nthLeₓ'. -/
theorem forall₂_iff_nthLe {l₁ : List α} {l₂ : List β} :
    Forall₂ R l₁ l₂ ↔ l₁.length = l₂.length ∧ ∀ i h₁ h₂, R (l₁.nthLe i h₁) (l₂.nthLe i h₂) :=
  ⟨fun h => ⟨h.length_eq, h.nthLe⟩, And.ndrec forall₂_of_length_eq_of_nthLe⟩
#align list.forall₂_iff_nth_le List.forall₂_iff_nthLe

/- warning: list.forall₂_zip -> List.forall₂_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (List.Forall₂.{u1, u2} α β R l₁ l₂) -> (forall {a : α} {b : β}, (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (List.zip.{u1, u2} α β l₁ l₂)) -> (R a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (List.Forall₂.{u2, u1} α β R l₁ l₂) -> (forall {a : α} {b : β}, (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.instMembershipList.{max u1 u2} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b) (List.zip.{u2, u1} α β l₁ l₂)) -> (R a b))
Case conversion may be inaccurate. Consider using '#align list.forall₂_zip List.forall₂_zipₓ'. -/
theorem forall₂_zip : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b
  | _, _, forall₂.cons h₁ h₂, x, y, Or.inl rfl => h₁
  | _, _, forall₂.cons h₁ h₂, x, y, Or.inr h₃ => forall₂_zip h₂ h₃
#align list.forall₂_zip List.forall₂_zip

/- warning: list.forall₂_iff_zip -> List.forall₂_iff_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, Iff (List.Forall₂.{u1, u2} α β R l₁ l₂) (And (Eq.{1} Nat (List.length.{u1} α l₁) (List.length.{u2} β l₂)) (forall {a : α} {b : β}, (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (List.zip.{u1, u2} α β l₁ l₂)) -> (R a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, Iff (List.Forall₂.{u2, u1} α β R l₁ l₂) (And (Eq.{1} Nat (List.length.{u2} α l₁) (List.length.{u1} β l₂)) (forall {a : α} {b : β}, (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.instMembershipList.{max u1 u2} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b) (List.zip.{u2, u1} α β l₁ l₂)) -> (R a b)))
Case conversion may be inaccurate. Consider using '#align list.forall₂_iff_zip List.forall₂_iff_zipₓ'. -/
theorem forall₂_iff_zip {l₁ l₂} :
    Forall₂ R l₁ l₂ ↔ length l₁ = length l₂ ∧ ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b :=
  ⟨fun h => ⟨Forall₂.length_eq h, @forall₂_zip _ _ _ _ _ h⟩, fun h =>
    by
    cases' h with h₁ h₂
    induction' l₁ with a l₁ IH generalizing l₂
    · cases length_eq_zero.1 h₁.symm
      constructor
    · cases' l₂ with b l₂ <;> injection h₁ with h₁
      exact forall₂.cons (h₂ <| Or.inl rfl) (IH h₁ fun a b h => h₂ <| Or.inr h)⟩
#align list.forall₂_iff_zip List.forall₂_iff_zip

/- warning: list.forall₂_take -> List.forall₂_take is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} (n : Nat) {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (List.Forall₂.{u1, u2} α β R l₁ l₂) -> (List.Forall₂.{u1, u2} α β R (List.take.{u1} α n l₁) (List.take.{u2} β n l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} (n : Nat) {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (List.Forall₂.{u2, u1} α β R l₁ l₂) -> (List.Forall₂.{u2, u1} α β R (List.take.{u2} α n l₁) (List.take.{u1} β n l₂))
Case conversion may be inaccurate. Consider using '#align list.forall₂_take List.forall₂_takeₓ'. -/
theorem forall₂_take : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (take n l₁) (take n l₂)
  | 0, _, _, _ => by simp only [forall₂.nil, take]
  | n + 1, _, _, forall₂.nil => by simp only [forall₂.nil, take]
  | n + 1, _, _, forall₂.cons h₁ h₂ => by simp [And.intro h₁ h₂, forall₂_take n]
#align list.forall₂_take List.forall₂_take

/- warning: list.forall₂_drop -> List.forall₂_drop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} (n : Nat) {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (List.Forall₂.{u1, u2} α β R l₁ l₂) -> (List.Forall₂.{u1, u2} α β R (List.drop.{u1} α n l₁) (List.drop.{u2} β n l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} (n : Nat) {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (List.Forall₂.{u2, u1} α β R l₁ l₂) -> (List.Forall₂.{u2, u1} α β R (List.drop.{u2} α n l₁) (List.drop.{u1} β n l₂))
Case conversion may be inaccurate. Consider using '#align list.forall₂_drop List.forall₂_dropₓ'. -/
theorem forall₂_drop : ∀ (n) {l₁ l₂}, Forall₂ R l₁ l₂ → Forall₂ R (drop n l₁) (drop n l₂)
  | 0, _, _, h => by simp only [drop, h]
  | n + 1, _, _, forall₂.nil => by simp only [forall₂.nil, drop]
  | n + 1, _, _, forall₂.cons h₁ h₂ => by simp [And.intro h₁ h₂, forall₂_drop n]
#align list.forall₂_drop List.forall₂_drop

/- warning: list.forall₂_take_append -> List.forall₂_take_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} (l : List.{u1} α) (l₁ : List.{u2} β) (l₂ : List.{u2} β), (List.Forall₂.{u1, u2} α β R l (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) l₁ l₂)) -> (List.Forall₂.{u1, u2} α β R (List.take.{u1} α (List.length.{u2} β l₁) l) l₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} (l : List.{u2} α) (l₁ : List.{u1} β) (l₂ : List.{u1} β), (List.Forall₂.{u2, u1} α β R l (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) l₁ l₂)) -> (List.Forall₂.{u2, u1} α β R (List.take.{u2} α (List.length.{u1} β l₁) l) l₁)
Case conversion may be inaccurate. Consider using '#align list.forall₂_take_append List.forall₂_take_appendₓ'. -/
theorem forall₂_take_append (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.take (length l₁) l) l₁ :=
  by
  have h' : Forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)) :=
    forall₂_take (length l₁) h
  rwa [take_left] at h'
#align list.forall₂_take_append List.forall₂_take_append

/- warning: list.forall₂_drop_append -> List.forall₂_drop_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} (l : List.{u1} α) (l₁ : List.{u2} β) (l₂ : List.{u2} β), (List.Forall₂.{u1, u2} α β R l (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) l₁ l₂)) -> (List.Forall₂.{u1, u2} α β R (List.drop.{u1} α (List.length.{u2} β l₁) l) l₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} (l : List.{u2} α) (l₁ : List.{u1} β) (l₂ : List.{u1} β), (List.Forall₂.{u2, u1} α β R l (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) l₁ l₂)) -> (List.Forall₂.{u2, u1} α β R (List.drop.{u2} α (List.length.{u1} β l₁) l) l₂)
Case conversion may be inaccurate. Consider using '#align list.forall₂_drop_append List.forall₂_drop_appendₓ'. -/
theorem forall₂_drop_append (l : List α) (l₁ : List β) (l₂ : List β) (h : Forall₂ R l (l₁ ++ l₂)) :
    Forall₂ R (List.drop (length l₁) l) l₂ :=
  by
  have h' : Forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)) :=
    forall₂_drop (length l₁) h
  rwa [drop_left] at h'
#align list.forall₂_drop_append List.forall₂_drop_append

/- warning: list.rel_mem -> List.rel_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, (Relator.BiUnique.{u1, u2} α β R) -> (Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} α β ((List.{u1} α) -> Prop) ((List.{u2} β) -> Prop) R (Relator.LiftFun.{succ u1, succ u2, 1, 1} (List.{u1} α) (List.{u2} β) Prop Prop (List.Forall₂.{u1, u2} α β R) Iff) (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α)) (Membership.Mem.{u2, u2} β (List.{u2} β) (List.hasMem.{u2} β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, (Relator.BiUnique.{u2, u1} α β R) -> (Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} α β ((List.{u2} α) -> Prop) ((List.{u1} β) -> Prop) R (Relator.LiftFun.{succ u2, succ u1, 1, 1} (List.{u2} α) (List.{u1} β) Prop Prop (List.Forall₂.{u2, u1} α β R) Iff) (fun (x._@.Mathlib.Data.List.Forall2._hyg.4975 : α) (x._@.Mathlib.Data.List.Forall2._hyg.4977 : List.{u2} α) => Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) x._@.Mathlib.Data.List.Forall2._hyg.4975 x._@.Mathlib.Data.List.Forall2._hyg.4977) (fun (x._@.Mathlib.Data.List.Forall2._hyg.4990 : β) (x._@.Mathlib.Data.List.Forall2._hyg.4992 : List.{u1} β) => Membership.mem.{u1, u1} β (List.{u1} β) (List.instMembershipList.{u1} β) x._@.Mathlib.Data.List.Forall2._hyg.4990 x._@.Mathlib.Data.List.Forall2._hyg.4992))
Case conversion may be inaccurate. Consider using '#align list.rel_mem List.rel_memₓ'. -/
theorem rel_mem (hr : BiUnique R) : (R ⇒ Forall₂ R ⇒ Iff) (· ∈ ·) (· ∈ ·)
  | a, b, h, [], [], forall₂.nil => by simp only [not_mem_nil]
  | a, b, h, a' :: as, b' :: bs, forall₂.cons h₁ h₂ => rel_or (rel_eq hr h h₁) (rel_mem h h₂)
#align list.rel_mem List.rel_mem

/- warning: list.rel_map -> List.rel_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{max (succ u1) (succ u3), max (succ u2) (succ u4), max (succ u1) (succ u3), max (succ u2) (succ u4)} (α -> γ) (β -> δ) ((List.{u1} α) -> (List.{u3} γ)) ((List.{u2} β) -> (List.{u4} δ)) (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} α β γ δ R P) (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} (List.{u1} α) (List.{u2} β) (List.{u3} γ) (List.{u4} δ) (List.Forall₂.{u1, u2} α β R) (List.Forall₂.{u3, u4} γ δ P)) (List.map.{u1, u3} α γ) (List.map.{u2, u4} β δ)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{max (succ u4) (succ u3), max (succ u2) (succ u1), max (succ u4) (succ u3), max (succ u2) (succ u1)} (α -> γ) (β -> δ) ((List.{u4} α) -> (List.{u3} γ)) ((List.{u2} β) -> (List.{u1} δ)) (Relator.LiftFun.{succ u4, succ u2, succ u3, succ u1} α β γ δ R P) (Relator.LiftFun.{succ u4, succ u2, succ u3, succ u1} (List.{u4} α) (List.{u2} β) (List.{u3} γ) (List.{u1} δ) (List.Forall₂.{u4, u2} α β R) (List.Forall₂.{u3, u1} γ δ P)) (List.map.{u4, u3} α γ) (List.map.{u2, u1} β δ)
Case conversion may be inaccurate. Consider using '#align list.rel_map List.rel_mapₓ'. -/
theorem rel_map : ((R ⇒ P) ⇒ Forall₂ R ⇒ Forall₂ P) map map
  | f, g, h, [], [], forall₂.nil => Forall₂.nil
  | f, g, h, a :: as, b :: bs, forall₂.cons h₁ h₂ => Forall₂.cons (h h₁) (rel_map (@h) h₂)
#align list.rel_map List.rel_map

/- warning: list.rel_append -> List.rel_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} (List.{u1} α) (List.{u2} β) ((List.{u1} α) -> (List.{u1} α)) ((List.{u2} β) -> (List.{u2} β)) (List.Forall₂.{u1, u2} α β R) (Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} (List.{u1} α) (List.{u2} β) (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β R) (List.Forall₂.{u1, u2} α β R)) (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α)) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} (List.{u2} α) (List.{u1} β) ((List.{u2} α) -> (List.{u2} α)) ((List.{u1} β) -> (List.{u1} β)) (List.Forall₂.{u2, u1} α β R) (Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} (List.{u2} α) (List.{u1} β) (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β R) (List.Forall₂.{u2, u1} α β R)) (fun (x._@.Mathlib.Data.List.Forall2._hyg.5676 : List.{u2} α) (x._@.Mathlib.Data.List.Forall2._hyg.5678 : List.{u2} α) => HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) x._@.Mathlib.Data.List.Forall2._hyg.5676 x._@.Mathlib.Data.List.Forall2._hyg.5678) (fun (x._@.Mathlib.Data.List.Forall2._hyg.5691 : List.{u1} β) (x._@.Mathlib.Data.List.Forall2._hyg.5693 : List.{u1} β) => HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) x._@.Mathlib.Data.List.Forall2._hyg.5691 x._@.Mathlib.Data.List.Forall2._hyg.5693)
Case conversion may be inaccurate. Consider using '#align list.rel_append List.rel_appendₓ'. -/
theorem rel_append : (Forall₂ R ⇒ Forall₂ R ⇒ Forall₂ R) append append
  | [], [], h, l₁, l₂, hl => hl
  | a :: as, b :: bs, forall₂.cons h₁ h₂, l₁, l₂, hl => Forall₂.cons h₁ (rel_append h₂ hl)
#align list.rel_append List.rel_append

/- warning: list.rel_reverse -> List.rel_reverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} (List.{u1} α) (List.{u2} β) (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β R) (List.Forall₂.{u1, u2} α β R) (List.reverse.{u1} α) (List.reverse.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} (List.{u2} α) (List.{u1} β) (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β R) (List.Forall₂.{u2, u1} α β R) (List.reverse.{u2} α) (List.reverse.{u1} β)
Case conversion may be inaccurate. Consider using '#align list.rel_reverse List.rel_reverseₓ'. -/
theorem rel_reverse : (Forall₂ R ⇒ Forall₂ R) reverse reverse
  | [], [], forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ =>
    by
    simp only [reverse_cons]
    exact rel_append (rel_reverse h₂) (forall₂.cons h₁ forall₂.nil)
#align list.rel_reverse List.rel_reverse

/- warning: list.forall₂_reverse_iff -> List.forall₂_reverse_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, Iff (List.Forall₂.{u1, u2} α β R (List.reverse.{u1} α l₁) (List.reverse.{u2} β l₂)) (List.Forall₂.{u1, u2} α β R l₁ l₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, Iff (List.Forall₂.{u2, u1} α β R (List.reverse.{u2} α l₁) (List.reverse.{u1} β l₂)) (List.Forall₂.{u2, u1} α β R l₁ l₂)
Case conversion may be inaccurate. Consider using '#align list.forall₂_reverse_iff List.forall₂_reverse_iffₓ'. -/
@[simp]
theorem forall₂_reverse_iff {l₁ l₂} : Forall₂ R (reverse l₁) (reverse l₂) ↔ Forall₂ R l₁ l₂ :=
  Iff.intro
    (fun h => by
      rw [← reverse_reverse l₁, ← reverse_reverse l₂]
      exact rel_reverse h)
    fun h => rel_reverse h
#align list.forall₂_reverse_iff List.forall₂_reverse_iff

/- warning: list.rel_join -> List.rel_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop}, Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} (List.{u1} (List.{u1} α)) (List.{u2} (List.{u2} β)) (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β R)) (List.Forall₂.{u1, u2} α β R) (List.join.{u1} α) (List.join.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop}, Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} (List.{u2} (List.{u2} α)) (List.{u1} (List.{u1} β)) (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β R)) (List.Forall₂.{u2, u1} α β R) (List.join.{u2} α) (List.join.{u1} β)
Case conversion may be inaccurate. Consider using '#align list.rel_join List.rel_joinₓ'. -/
theorem rel_join : (Forall₂ (Forall₂ R) ⇒ Forall₂ R) join join
  | [], [], forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => rel_append h₁ (rel_join h₂)
#align list.rel_join List.rel_join

/- warning: list.rel_bind -> List.rel_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{succ u1, succ u2, max (succ u1) (succ u3), max (succ u2) (succ u4)} (List.{u1} α) (List.{u2} β) ((α -> (List.{u3} γ)) -> (List.{u3} γ)) ((β -> (List.{u4} δ)) -> (List.{u4} δ)) (List.Forall₂.{u1, u2} α β R) (Relator.LiftFun.{max (succ u1) (succ u3), max (succ u2) (succ u4), succ u3, succ u4} (α -> (List.{u3} γ)) (β -> (List.{u4} δ)) (List.{u3} γ) (List.{u4} δ) (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} α β (List.{u3} γ) (List.{u4} δ) R (List.Forall₂.{u3, u4} γ δ P)) (List.Forall₂.{u3, u4} γ δ P)) (List.bind.{u1, u3} α γ) (List.bind.{u2, u4} β δ)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{succ u4, succ u3, max (succ u4) (succ u2), max (succ u3) (succ u1)} (List.{u4} α) (List.{u3} β) ((α -> (List.{u2} γ)) -> (List.{u2} γ)) ((β -> (List.{u1} δ)) -> (List.{u1} δ)) (List.Forall₂.{u4, u3} α β R) (Relator.LiftFun.{max (succ u4) (succ u2), max (succ u3) (succ u1), succ u2, succ u1} (α -> (List.{u2} γ)) (β -> (List.{u1} δ)) (List.{u2} γ) (List.{u1} δ) (Relator.LiftFun.{succ u4, succ u3, succ u2, succ u1} α β (List.{u2} γ) (List.{u1} δ) R (List.Forall₂.{u2, u1} γ δ P)) (List.Forall₂.{u2, u1} γ δ P)) (List.bind.{u4, u2} α γ) (List.bind.{u3, u1} β δ)
Case conversion may be inaccurate. Consider using '#align list.rel_bind List.rel_bindₓ'. -/
theorem rel_bind : (Forall₂ R ⇒ (R ⇒ Forall₂ P) ⇒ Forall₂ P) List.bind List.bind :=
  fun a b h₁ f g h₂ => rel_join (rel_map (@h₂) h₁)
#align list.rel_bind List.rel_bind

/- warning: list.rel_foldl -> List.rel_foldl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{max (succ u1) (succ u3), max (succ u2) (succ u4), max (succ u1) (succ u3), max (succ u2) (succ u4)} (γ -> α -> γ) (δ -> β -> δ) (γ -> (List.{u1} α) -> γ) (δ -> (List.{u2} β) -> δ) (Relator.LiftFun.{succ u3, succ u4, max (succ u1) (succ u3), max (succ u2) (succ u4)} γ δ (α -> γ) (β -> δ) P (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} α β γ δ R P)) (Relator.LiftFun.{succ u3, succ u4, max (succ u1) (succ u3), max (succ u2) (succ u4)} γ δ ((List.{u1} α) -> γ) ((List.{u2} β) -> δ) P (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} (List.{u1} α) (List.{u2} β) γ δ (List.Forall₂.{u1, u2} α β R) P)) (List.foldl.{u3, u1} γ α) (List.foldl.{u4, u2} δ β)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{max (succ u4) (succ u3), max (succ u2) (succ u1), max (succ u4) (succ u3), max (succ u2) (succ u1)} (γ -> α -> γ) (δ -> β -> δ) (γ -> (List.{u4} α) -> γ) (δ -> (List.{u2} β) -> δ) (Relator.LiftFun.{succ u3, succ u1, max (succ u4) (succ u3), max (succ u2) (succ u1)} γ δ (α -> γ) (β -> δ) P (Relator.LiftFun.{succ u4, succ u2, succ u3, succ u1} α β γ δ R P)) (Relator.LiftFun.{succ u3, succ u1, max (succ u4) (succ u3), max (succ u2) (succ u1)} γ δ ((List.{u4} α) -> γ) ((List.{u2} β) -> δ) P (Relator.LiftFun.{succ u4, succ u2, succ u3, succ u1} (List.{u4} α) (List.{u2} β) γ δ (List.Forall₂.{u4, u2} α β R) P)) (List.foldl.{u3, u4} γ α) (List.foldl.{u1, u2} δ β)
Case conversion may be inaccurate. Consider using '#align list.rel_foldl List.rel_foldlₓ'. -/
theorem rel_foldl : ((P ⇒ R ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldl foldl
  | f, g, hfg, _, _, h, _, _, forall₂.nil => h
  | f, g, hfg, x, y, hxy, _, _, forall₂.cons hab hs => rel_foldl (@hfg) (hfg hxy hab) hs
#align list.rel_foldl List.rel_foldl

/- warning: list.rel_foldr -> List.rel_foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{max (succ u1) (succ u3), max (succ u2) (succ u4), max (succ u1) (succ u3), max (succ u2) (succ u4)} (α -> γ -> γ) (β -> δ -> δ) (γ -> (List.{u1} α) -> γ) (δ -> (List.{u2} β) -> δ) (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} α β (γ -> γ) (δ -> δ) R (Relator.LiftFun.{succ u3, succ u4, succ u3, succ u4} γ δ γ δ P P)) (Relator.LiftFun.{succ u3, succ u4, max (succ u1) (succ u3), max (succ u2) (succ u4)} γ δ ((List.{u1} α) -> γ) ((List.{u2} β) -> δ) P (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} (List.{u1} α) (List.{u2} β) γ δ (List.Forall₂.{u1, u2} α β R) P)) (List.foldr.{u1, u3} α γ) (List.foldr.{u2, u4} β δ)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{max (succ u4) (succ u3), max (succ u2) (succ u1), max (succ u4) (succ u3), max (succ u2) (succ u1)} (α -> γ -> γ) (β -> δ -> δ) (γ -> (List.{u4} α) -> γ) (δ -> (List.{u2} β) -> δ) (Relator.LiftFun.{succ u4, succ u2, succ u3, succ u1} α β (γ -> γ) (δ -> δ) R (Relator.LiftFun.{succ u3, succ u1, succ u3, succ u1} γ δ γ δ P P)) (Relator.LiftFun.{succ u3, succ u1, max (succ u4) (succ u3), max (succ u2) (succ u1)} γ δ ((List.{u4} α) -> γ) ((List.{u2} β) -> δ) P (Relator.LiftFun.{succ u4, succ u2, succ u3, succ u1} (List.{u4} α) (List.{u2} β) γ δ (List.Forall₂.{u4, u2} α β R) P)) (List.foldr.{u4, u3} α γ) (List.foldr.{u2, u1} β δ)
Case conversion may be inaccurate. Consider using '#align list.rel_foldr List.rel_foldrₓ'. -/
theorem rel_foldr : ((R ⇒ P ⇒ P) ⇒ P ⇒ Forall₂ R ⇒ P) foldr foldr
  | f, g, hfg, _, _, h, _, _, forall₂.nil => h
  | f, g, hfg, x, y, hxy, _, _, forall₂.cons hab hs => hfg hab (rel_foldr (@hfg) hxy hs)
#align list.rel_foldr List.rel_foldr

/- warning: list.rel_filter -> List.rel_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {p : α -> Prop} {q : β -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u2} β q], (Relator.LiftFun.{succ u1, succ u2, 1, 1} α β Prop Prop R Iff p q) -> (Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} (List.{u1} α) (List.{u2} β) (List.{u1} α) (List.{u2} β) (List.Forall₂.{u1, u2} α β R) (List.Forall₂.{u1, u2} α β R) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a)) (List.filterₓ.{u2} β q (fun (a : β) => _inst_2 a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {p : α -> Bool} {q : β -> Bool}, (Relator.LiftFun.{succ u2, succ u1, 1, 1} α β Prop Prop R (fun (x._@.Mathlib.Data.List.Forall2._hyg.7204 : Prop) (x._@.Mathlib.Data.List.Forall2._hyg.7206 : Prop) => Iff x._@.Mathlib.Data.List.Forall2._hyg.7204 x._@.Mathlib.Data.List.Forall2._hyg.7206) (fun (x : α) => Eq.{1} Bool (p x) Bool.true) (fun (x : β) => Eq.{1} Bool (q x) Bool.true)) -> (Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} (List.{u2} α) (List.{u1} β) (List.{u2} α) (List.{u1} β) (List.Forall₂.{u2, u1} α β R) (List.Forall₂.{u2, u1} α β R) (List.filter.{u2} α p) (List.filter.{u1} β q))
Case conversion may be inaccurate. Consider using '#align list.rel_filter List.rel_filterₓ'. -/
theorem rel_filter {p : α → Prop} {q : β → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : (R ⇒ (· ↔ ·)) p q) : (Forall₂ R ⇒ Forall₂ R) (filter p) (filter q)
  | _, _, forall₂.nil => Forall₂.nil
  | a :: as, b :: bs, forall₂.cons h₁ h₂ => by
    by_cases p a
    · have : q b := by rwa [← hpq h₁]
      simp only [filter_cons_of_pos _ h, filter_cons_of_pos _ this, forall₂_cons, h₁, rel_filter h₂,
        and_true_iff]
    · have : ¬q b := by rwa [← hpq h₁]
      simp only [filter_cons_of_neg _ h, filter_cons_of_neg _ this, rel_filter h₂]
#align list.rel_filter List.rel_filter

/- warning: list.rel_filter_map -> List.rel_filterMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{max (succ u1) (succ u3), max (succ u2) (succ u4), max (succ u1) (succ u3), max (succ u2) (succ u4)} (α -> (Option.{u3} γ)) (β -> (Option.{u4} δ)) ((List.{u1} α) -> (List.{u3} γ)) ((List.{u2} β) -> (List.{u4} δ)) (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} α β (Option.{u3} γ) (Option.{u4} δ) R (Option.Rel.{u3, u4} γ δ P)) (Relator.LiftFun.{succ u1, succ u2, succ u3, succ u4} (List.{u1} α) (List.{u2} β) (List.{u3} γ) (List.{u4} δ) (List.Forall₂.{u1, u2} α β R) (List.Forall₂.{u3, u4} γ δ P)) (List.filterMap.{u1, u3} α γ) (List.filterMap.{u2, u4} β δ)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u1}} {R : α -> β -> Prop} {P : γ -> δ -> Prop}, Relator.LiftFun.{max (succ u4) (succ u3), max (succ u2) (succ u1), max (succ u4) (succ u3), max (succ u2) (succ u1)} (α -> (Option.{u3} γ)) (β -> (Option.{u1} δ)) ((List.{u4} α) -> (List.{u3} γ)) ((List.{u2} β) -> (List.{u1} δ)) (Relator.LiftFun.{succ u4, succ u2, succ u3, succ u1} α β (Option.{u3} γ) (Option.{u1} δ) R (Option.Rel.{u3, u1} γ δ P)) (Relator.LiftFun.{succ u4, succ u2, succ u3, succ u1} (List.{u4} α) (List.{u2} β) (List.{u3} γ) (List.{u1} δ) (List.Forall₂.{u4, u2} α β R) (List.Forall₂.{u3, u1} γ δ P)) (List.filterMap.{u4, u3} α γ) (List.filterMap.{u2, u1} β δ)
Case conversion may be inaccurate. Consider using '#align list.rel_filter_map List.rel_filterMapₓ'. -/
theorem rel_filterMap : ((R ⇒ Option.Rel P) ⇒ Forall₂ R ⇒ Forall₂ P) filterMap filterMap
  | f, g, hfg, _, _, forall₂.nil => Forall₂.nil
  | f, g, hfg, a :: as, b :: bs, forall₂.cons h₁ h₂ => by
    rw [filter_map_cons, filter_map_cons] <;>
      exact
        match f a, g b, hfg h₁ with
        | _, _, Option.Rel.none => rel_filter_map (@hfg) h₂
        | _, _, Option.Rel.some h => forall₂.cons h (rel_filter_map (@hfg) h₂)
#align list.rel_filter_map List.rel_filterMap

/- warning: list.rel_prod -> List.rel_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β], (R (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)))))) -> (Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} α β (α -> α) (β -> β) R (Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} α β α β R R) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))))) -> (Relator.LiftFun.{succ u1, succ u2, succ u1, succ u2} (List.{u1} α) (List.{u2} β) α β (List.Forall₂.{u1, u2} α β R) R (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (List.prod.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} [_inst_1 : Monoid.{u2} α] [_inst_2 : Monoid.{u1} β], (R (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α _inst_1))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β _inst_2)))) -> (Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} α β (α -> α) (β -> β) R (Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} α β α β R R) (fun (x._@.Mathlib.Data.List.Forall2._hyg.8067 : α) (x._@.Mathlib.Data.List.Forall2._hyg.8069 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1))) x._@.Mathlib.Data.List.Forall2._hyg.8067 x._@.Mathlib.Data.List.Forall2._hyg.8069) (fun (x._@.Mathlib.Data.List.Forall2._hyg.8082 : β) (x._@.Mathlib.Data.List.Forall2._hyg.8084 : β) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_2))) x._@.Mathlib.Data.List.Forall2._hyg.8082 x._@.Mathlib.Data.List.Forall2._hyg.8084)) -> (Relator.LiftFun.{succ u2, succ u1, succ u2, succ u1} (List.{u2} α) (List.{u1} β) α β (List.Forall₂.{u2, u1} α β R) R (List.prod.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)) (Monoid.toOne.{u2} α _inst_1)) (List.prod.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_2)) (Monoid.toOne.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align list.rel_prod List.rel_prodₓ'. -/
@[to_additive]
theorem rel_prod [Monoid α] [Monoid β] (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·)) :
    (Forall₂ R ⇒ R) prod prod :=
  rel_foldl hf h
#align list.rel_prod List.rel_prod
#align list.rel_sum List.rel_sum

#print List.SublistForall₂ /-
/-- Given a relation `R`, `sublist_forall₂ r l₁ l₂` indicates that there is a sublist of `l₂` such
  that `forall₂ r l₁ l₂`. -/
inductive SublistForall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil {l} : sublist_forall₂ [] l
  | cons {a₁ a₂ l₁ l₂} : R a₁ a₂ → sublist_forall₂ l₁ l₂ → sublist_forall₂ (a₁ :: l₁) (a₂ :: l₂)
  | cons_right {a l₁ l₂} : sublist_forall₂ l₁ l₂ → sublist_forall₂ l₁ (a :: l₂)
#align list.sublist_forall₂ List.SublistForall₂
-/

/- warning: list.sublist_forall₂_iff -> List.sublistForall₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {R : α -> β -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, Iff (List.SublistForall₂.{u1, u2} α β R l₁ l₂) (Exists.{succ u2} (List.{u2} β) (fun (l : List.{u2} β) => And (List.Forall₂.{u1, u2} α β R l₁ l) (List.Sublist.{u2} β l l₂)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {R : α -> β -> Prop} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, Iff (List.SublistForall₂.{u2, u1} α β R l₁ l₂) (Exists.{succ u1} (List.{u1} β) (fun (l : List.{u1} β) => And (List.Forall₂.{u2, u1} α β R l₁ l) (List.Sublist.{u1} β l l₂)))
Case conversion may be inaccurate. Consider using '#align list.sublist_forall₂_iff List.sublistForall₂_iffₓ'. -/
theorem sublistForall₂_iff {l₁ : List α} {l₂ : List β} :
    SublistForall₂ R l₁ l₂ ↔ ∃ l, Forall₂ R l₁ l ∧ l <+ l₂ :=
  by
  constructor <;> intro h
  · induction' h with _ a b l1 l2 rab rll ih b l1 l2 hl ih
    · exact ⟨nil, forall₂.nil, nil_sublist _⟩
    · obtain ⟨l, hl1, hl2⟩ := ih
      refine' ⟨b :: l, forall₂.cons rab hl1, hl2.cons_cons b⟩
    · obtain ⟨l, hl1, hl2⟩ := ih
      exact ⟨l, hl1, hl2.trans (sublist.cons _ _ _ (sublist.refl _))⟩
  · obtain ⟨l, hl1, hl2⟩ := h
    revert l₁
    induction' hl2 with _ _ _ _ ih _ _ _ _ ih <;> intro l₁ hl1
    · rw [forall₂_nil_right_iff.1 hl1]
      exact sublist_forall₂.nil
    · exact sublist_forall₂.cons_right (ih hl1)
    · cases' hl1 with _ _ _ _ hr hl _
      exact sublist_forall₂.cons hr (ih hl)
#align list.sublist_forall₂_iff List.sublistForall₂_iff

#print List.SublistForall₂.is_refl /-
instance SublistForall₂.is_refl [IsRefl α Rₐ] : IsRefl (List α) (SublistForall₂ Rₐ) :=
  ⟨fun l => sublistForall₂_iff.2 ⟨l, forall₂_refl l, Sublist.refl l⟩⟩
#align list.sublist_forall₂.is_refl List.SublistForall₂.is_refl
-/

#print List.SublistForall₂.is_trans /-
instance SublistForall₂.is_trans [IsTrans α Rₐ] : IsTrans (List α) (SublistForall₂ Rₐ) :=
  ⟨fun a b c => by
    revert a b
    induction' c with _ _ ih
    · rintro _ _ h1 (_ | _ | _)
      exact h1
    · rintro a b h1 h2
      cases' h2 with _ _ _ _ _ hbc tbc _ _ y1 btc
      · cases h1
        exact sublist_forall₂.nil
      · cases' h1 with _ _ _ _ _ hab tab _ _ _ atb
        · exact sublist_forall₂.nil
        · exact sublist_forall₂.cons (trans hab hbc) (ih _ _ tab tbc)
        · exact sublist_forall₂.cons_right (ih _ _ atb tbc)
      · exact sublist_forall₂.cons_right (ih _ _ h1 btc)⟩
#align list.sublist_forall₂.is_trans List.SublistForall₂.is_trans
-/

#print List.Sublist.sublistForall₂ /-
theorem Sublist.sublistForall₂ {l₁ l₂ : List α} (h : l₁ <+ l₂) [IsRefl α Rₐ] :
    SublistForall₂ Rₐ l₁ l₂ :=
  sublistForall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩
#align list.sublist.sublist_forall₂ List.Sublist.sublistForall₂
-/

#print List.tail_sublistForall₂_self /-
theorem tail_sublistForall₂_self [IsRefl α Rₐ] (l : List α) : SublistForall₂ Rₐ l.tail l :=
  l.tail_sublist.SublistForall₂
#align list.tail_sublist_forall₂_self List.tail_sublistForall₂_self
-/

end List

