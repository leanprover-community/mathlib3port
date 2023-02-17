/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau

! This file was ported from Lean 3 source module data.list.zip
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic
import Mathbin.Algebra.Order.Monoid.MinMax

/-!
# zip & unzip

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides results about `list.zip_with`, `list.zip` and `list.unzip` (definitions are in
core Lean).
`zip_with f l₁ l₂` applies `f : α → β → γ` pointwise to a list `l₁ : list α` and `l₂ : list β`. It
applies, until one of the lists is exhausted. For example,
`zip_with f [0, 1, 2] [6.28, 31] = [f 0 6.28, f 1 31]`.
`zip` is `zip_with` applied to `prod.mk`. For example,
`zip [a₁, a₂] [b₁, b₂, b₃] = [(a₁, b₁), (a₂, b₂)]`.
`unzip` undoes `zip`. For example, `unzip [(a₁, b₁), (a₂, b₂)] = ([a₁, a₂], [b₁, b₂])`.
-/


universe u

open Nat

namespace List

variable {α : Type u} {β γ δ ε : Type _}

/- warning: list.zip_with_cons_cons -> List.zipWith_cons_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (a : α) (b : β) (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f (List.cons.{u1} α a l₁) (List.cons.{u2} β b l₂)) (List.cons.{u3} γ (f a b) (List.zipWith.{u1, u2, u3} α β γ f l₁ l₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (a : α) (b : β) (l₁ : List.{u3} α) (l₂ : List.{u2} β), Eq.{succ u1} (List.{u1} γ) (List.zipWith.{u3, u2, u1} α β γ f (List.cons.{u3} α a l₁) (List.cons.{u2} β b l₂)) (List.cons.{u1} γ (f a b) (List.zipWith.{u3, u2, u1} α β γ f l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.zip_with_cons_cons List.zipWith_cons_consₓ'. -/
@[simp]
theorem zipWith_cons_cons (f : α → β → γ) (a : α) (b : β) (l₁ : List α) (l₂ : List β) :
    zipWith f (a :: l₁) (b :: l₂) = f a b :: zipWith f l₁ l₂ :=
  rfl
#align list.zip_with_cons_cons List.zipWith_cons_cons

/- warning: list.zip_cons_cons -> List.zip_cons_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (b : β) (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.zip.{u1, u2} α β (List.cons.{u1} α a l₁) (List.cons.{u2} β b l₂)) (List.cons.{max u1 u2} (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a b) (List.zip.{u1, u2} α β l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (b : β) (l₁ : List.{u2} α) (l₂ : List.{u1} β), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.zip.{u2, u1} α β (List.cons.{u2} α a l₁) (List.cons.{u1} β b l₂)) (List.cons.{max u1 u2} (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a b) (List.zip.{u2, u1} α β l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.zip_cons_cons List.zip_cons_consₓ'. -/
@[simp]
theorem zip_cons_cons (a : α) (b : β) (l₁ : List α) (l₂ : List β) :
    zip (a :: l₁) (b :: l₂) = (a, b) :: zip l₁ l₂ :=
  rfl
#align list.zip_cons_cons List.zip_cons_cons

/- warning: list.zip_with_nil_left -> List.zipWith_nil_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f (List.nil.{u1} α) l) (List.nil.{u3} γ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (l : List.{u2} β), Eq.{succ u1} (List.{u1} γ) (List.zipWith.{u3, u2, u1} α β γ f (List.nil.{u3} α) l) (List.nil.{u1} γ)
Case conversion may be inaccurate. Consider using '#align list.zip_with_nil_left List.zipWith_nil_leftₓ'. -/
@[simp]
theorem zipWith_nil_left (f : α → β → γ) (l) : zipWith f [] l = [] :=
  rfl
#align list.zip_with_nil_left List.zipWith_nil_left

/- warning: list.zip_with_nil_right -> List.zipWith_nil_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l : List.{u1} α), Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f l (List.nil.{u2} β)) (List.nil.{u3} γ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (f : α -> β -> γ) (l : List.{u3} α), Eq.{succ u2} (List.{u2} γ) (List.zipWith.{u3, u1, u2} α β γ f l (List.nil.{u1} β)) (List.nil.{u2} γ)
Case conversion may be inaccurate. Consider using '#align list.zip_with_nil_right List.zipWith_nil_rightₓ'. -/
@[simp]
theorem zipWith_nil_right (f : α → β → γ) (l) : zipWith f l [] = [] := by cases l <;> rfl
#align list.zip_with_nil_right List.zipWith_nil_right

/- warning: list.zip_with_eq_nil_iff -> List.zipWith_eq_nil_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {l : List.{u1} α} {l' : List.{u2} β}, Iff (Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f l l') (List.nil.{u3} γ)) (Or (Eq.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) (Eq.{succ u2} (List.{u2} β) l' (List.nil.{u2} β)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {l : List.{u3} α} {l' : List.{u2} β}, Iff (Eq.{succ u1} (List.{u1} γ) (List.zipWith.{u3, u2, u1} α β γ f l l') (List.nil.{u1} γ)) (Or (Eq.{succ u3} (List.{u3} α) l (List.nil.{u3} α)) (Eq.{succ u2} (List.{u2} β) l' (List.nil.{u2} β)))
Case conversion may be inaccurate. Consider using '#align list.zip_with_eq_nil_iff List.zipWith_eq_nil_iffₓ'. -/
@[simp]
theorem zipWith_eq_nil_iff {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp
#align list.zip_with_eq_nil_iff List.zipWith_eq_nil_iff

/- warning: list.zip_nil_left -> List.zip_nil_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α), Eq.{succ (max u2 u1)} (List.{max u2 u1} (Prod.{u2, u1} β α)) (List.zip.{u2, u1} β α (List.nil.{u2} β) l) (List.nil.{max u2 u1} (Prod.{u2, u1} β α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α), Eq.{max (succ u2) (succ u1)} (List.{max u2 u1} (Prod.{u1, u2} β α)) (List.zip.{u1, u2} β α (List.nil.{u1} β) l) (List.nil.{max u2 u1} (Prod.{u1, u2} β α))
Case conversion may be inaccurate. Consider using '#align list.zip_nil_left List.zip_nil_leftₓ'. -/
@[simp]
theorem zip_nil_left (l : List α) : zip ([] : List β) l = [] :=
  rfl
#align list.zip_nil_left List.zip_nil_left

/- warning: list.zip_nil_right -> List.zip_nil_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α), Eq.{succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.zip.{u1, u2} α β l (List.nil.{u2} β)) (List.nil.{max u1 u2} (Prod.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.zip.{u2, u1} α β l (List.nil.{u1} β)) (List.nil.{max u2 u1} (Prod.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align list.zip_nil_right List.zip_nil_rightₓ'. -/
@[simp]
theorem zip_nil_right (l : List α) : zip l ([] : List β) = [] :=
  zipWith_nil_right _ l
#align list.zip_nil_right List.zip_nil_right

/- warning: list.zip_swap -> List.zip_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{succ (max u2 u1)} (List.{max u2 u1} (Prod.{u2, u1} β α)) (List.map.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β) (List.zip.{u1, u2} α β l₁ l₂)) (List.zip.{u2, u1} β α l₂ l₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l₁ : List.{u2} α) (l₂ : List.{u1} β), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u1, u2} β α)) (List.map.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β) (List.zip.{u2, u1} α β l₁ l₂)) (List.zip.{u1, u2} β α l₂ l₁)
Case conversion may be inaccurate. Consider using '#align list.zip_swap List.zip_swapₓ'. -/
@[simp]
theorem zip_swap : ∀ (l₁ : List α) (l₂ : List β), (zip l₁ l₂).map Prod.swap = zip l₂ l₁
  | [], l₂ => (zip_nil_right _).symm
  | l₁, [] => by rw [zip_nil_right] <;> rfl
  | a :: l₁, b :: l₂ => by
    simp only [zip_cons_cons, map_cons, zip_swap l₁ l₂, Prod.swap_prod_mk] <;> constructor <;> rfl
#align list.zip_swap List.zip_swap

/- warning: list.length_zip_with clashes with list.length_map₂ -> List.length_zipWith
warning: list.length_zip_with -> List.length_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{1} Nat (List.length.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l₁ l₂)) (LinearOrder.min.{0} Nat Nat.linearOrder (List.length.{u1} α l₁) (List.length.{u2} β l₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (l₁ : List.{u3} α) (l₂ : List.{u2} β), Eq.{1} Nat (List.length.{u1} γ (List.zipWith.{u3, u2, u1} α β γ f l₁ l₂)) (Min.min.{0} Nat instMinNat (List.length.{u3} α l₁) (List.length.{u2} β l₂))
Case conversion may be inaccurate. Consider using '#align list.length_zip_with List.length_zipWithₓ'. -/
@[simp]
theorem length_zipWith (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), length (zipWith f l₁ l₂) = min (length l₁) (length l₂)
  | [], l₂ => rfl
  | l₁, [] => by simp only [length, min_zero, zip_with_nil_right]
  | a :: l₁, b :: l₂ => by simp [length, zip_cons_cons, length_zip_with l₁ l₂, min_add_add_right]
#align list.length_zip_with List.length_zipWith

/- warning: list.length_zip -> List.length_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{1} Nat (List.length.{max u1 u2} (Prod.{u1, u2} α β) (List.zip.{u1, u2} α β l₁ l₂)) (LinearOrder.min.{0} Nat Nat.linearOrder (List.length.{u1} α l₁) (List.length.{u2} β l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l₁ : List.{u2} α) (l₂ : List.{u1} β), Eq.{1} Nat (List.length.{max u1 u2} (Prod.{u2, u1} α β) (List.zip.{u2, u1} α β l₁ l₂)) (Min.min.{0} Nat instMinNat (List.length.{u2} α l₁) (List.length.{u1} β l₂))
Case conversion may be inaccurate. Consider using '#align list.length_zip List.length_zipₓ'. -/
@[simp]
theorem length_zip :
    ∀ (l₁ : List α) (l₂ : List β), length (zip l₁ l₂) = min (length l₁) (length l₂) :=
  length_zipWith _
#align list.length_zip List.length_zip

/- warning: list.all₂_zip_with -> List.all₂_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {p : γ -> Prop} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (Eq.{1} Nat (List.length.{u1} α l₁) (List.length.{u2} β l₂)) -> (Iff (List.All₂.{u3} γ p (List.zipWith.{u1, u2, u3} α β γ f l₁ l₂)) (List.Forall₂.{u1, u2} α β (fun (x : α) (y : β) => p (f x y)) l₁ l₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {p : γ -> Prop} {l₁ : List.{u3} α} {l₂ : List.{u2} β}, (Eq.{1} Nat (List.length.{u3} α l₁) (List.length.{u2} β l₂)) -> (Iff (List.All₂.{u1} γ p (List.zipWith.{u3, u2, u1} α β γ f l₁ l₂)) (List.Forall₂.{u3, u2} α β (fun (x : α) (y : β) => p (f x y)) l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.all₂_zip_with List.all₂_zipWithₓ'. -/
theorem all₂_zipWith {f : α → β → γ} {p : γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂),
      All₂ p (zipWith f l₁ l₂) ↔ Forall₂ (fun x y => p (f x y)) l₁ l₂
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    simp only [length_cons, add_left_inj] at h
    simp [all₂_zip_with h]
#align list.all₂_zip_with List.all₂_zipWith

/- warning: list.lt_length_left_of_zip_with -> List.lt_length_left_of_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {i : Nat} {l : List.{u1} α} {l' : List.{u2} β}, (LT.lt.{0} Nat Nat.hasLt i (List.length.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l l'))) -> (LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} α l))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {i : Nat} {l : List.{u3} α} {l' : List.{u2} β}, (LT.lt.{0} Nat instLTNat i (List.length.{u1} γ (List.zipWith.{u3, u2, u1} α β γ f l l'))) -> (LT.lt.{0} Nat instLTNat i (List.length.{u3} α l))
Case conversion may be inaccurate. Consider using '#align list.lt_length_left_of_zip_with List.lt_length_left_of_zipWithₓ'. -/
theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l.length :=
  by
  rw [length_zip_with, lt_min_iff] at h
  exact h.left
#align list.lt_length_left_of_zip_with List.lt_length_left_of_zipWith

/- warning: list.lt_length_right_of_zip_with -> List.lt_length_right_of_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {i : Nat} {l : List.{u1} α} {l' : List.{u2} β}, (LT.lt.{0} Nat Nat.hasLt i (List.length.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l l'))) -> (LT.lt.{0} Nat Nat.hasLt i (List.length.{u2} β l'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {i : Nat} {l : List.{u3} α} {l' : List.{u2} β}, (LT.lt.{0} Nat instLTNat i (List.length.{u1} γ (List.zipWith.{u3, u2, u1} α β γ f l l'))) -> (LT.lt.{0} Nat instLTNat i (List.length.{u2} β l'))
Case conversion may be inaccurate. Consider using '#align list.lt_length_right_of_zip_with List.lt_length_right_of_zipWithₓ'. -/
theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {l : List α} {l' : List β}
    (h : i < (zipWith f l l').length) : i < l'.length :=
  by
  rw [length_zip_with, lt_min_iff] at h
  exact h.right
#align list.lt_length_right_of_zip_with List.lt_length_right_of_zipWith

/- warning: list.lt_length_left_of_zip -> List.lt_length_left_of_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {i : Nat} {l : List.{u1} α} {l' : List.{u2} β}, (LT.lt.{0} Nat Nat.hasLt i (List.length.{max u1 u2} (Prod.{u1, u2} α β) (List.zip.{u1, u2} α β l l'))) -> (LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} α l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {i : Nat} {l : List.{u2} α} {l' : List.{u1} β}, (LT.lt.{0} Nat instLTNat i (List.length.{max u2 u1} (Prod.{u2, u1} α β) (List.zip.{u2, u1} α β l l'))) -> (LT.lt.{0} Nat instLTNat i (List.length.{u2} α l))
Case conversion may be inaccurate. Consider using '#align list.lt_length_left_of_zip List.lt_length_left_of_zipₓ'. -/
theorem lt_length_left_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l.length :=
  lt_length_left_of_zipWith h
#align list.lt_length_left_of_zip List.lt_length_left_of_zip

/- warning: list.lt_length_right_of_zip -> List.lt_length_right_of_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {i : Nat} {l : List.{u1} α} {l' : List.{u2} β}, (LT.lt.{0} Nat Nat.hasLt i (List.length.{max u1 u2} (Prod.{u1, u2} α β) (List.zip.{u1, u2} α β l l'))) -> (LT.lt.{0} Nat Nat.hasLt i (List.length.{u2} β l'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {i : Nat} {l : List.{u2} α} {l' : List.{u1} β}, (LT.lt.{0} Nat instLTNat i (List.length.{max u2 u1} (Prod.{u2, u1} α β) (List.zip.{u2, u1} α β l l'))) -> (LT.lt.{0} Nat instLTNat i (List.length.{u1} β l'))
Case conversion may be inaccurate. Consider using '#align list.lt_length_right_of_zip List.lt_length_right_of_zipₓ'. -/
theorem lt_length_right_of_zip {i : ℕ} {l : List α} {l' : List β} (h : i < (zip l l').length) :
    i < l'.length :=
  lt_length_right_of_zipWith h
#align list.lt_length_right_of_zip List.lt_length_right_of_zip

/- warning: list.zip_append -> List.zip_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : List.{u1} α} {r₁ : List.{u1} α} {l₂ : List.{u2} β} {r₂ : List.{u2} β}, (Eq.{1} Nat (List.length.{u1} α l₁) (List.length.{u2} β l₂)) -> (Eq.{succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.zip.{u1, u2} α β (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ r₁) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) l₂ r₂)) (Append.append.{max u1 u2} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.hasAppend.{max u1 u2} (Prod.{u1, u2} α β)) (List.zip.{u1, u2} α β l₁ l₂) (List.zip.{u1, u2} α β r₁ r₂)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l₁ : List.{u2} α} {r₁ : List.{u2} α} {l₂ : List.{u1} β} {r₂ : List.{u1} β}, (Eq.{1} Nat (List.length.{u2} α l₁) (List.length.{u1} β l₂)) -> (Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.zip.{u2, u1} α β (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l₁ r₁) (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) l₂ r₂)) (HAppend.hAppend.{max u2 u1, max u2 u1, max u2 u1} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.{max u1 u2} (Prod.{u2, u1} α β)) (instHAppend.{max u2 u1} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.instAppendList.{max u2 u1} (Prod.{u2, u1} α β))) (List.zip.{u2, u1} α β l₁ l₂) (List.zip.{u2, u1} α β r₁ r₂)))
Case conversion may be inaccurate. Consider using '#align list.zip_append List.zip_appendₓ'. -/
theorem zip_append :
    ∀ {l₁ r₁ : List α} {l₂ r₂ : List β} (h : length l₁ = length l₂),
      zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂
  | [], r₁, l₂, r₂, h => by simp only [eq_nil_of_length_eq_zero h.symm] <;> rfl
  | l₁, r₁, [], r₂, h => by simp only [eq_nil_of_length_eq_zero h] <;> rfl
  | a :: l₁, r₁, b :: l₂, r₂, h => by
    simp only [cons_append, zip_cons_cons, zip_append (succ.inj h)] <;> constructor <;> rfl
#align list.zip_append List.zip_append

/- warning: list.zip_map -> List.zip_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> γ) (g : β -> δ) (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{succ (max u3 u4)} (List.{max u3 u4} (Prod.{u3, u4} γ δ)) (List.zip.{u3, u4} γ δ (List.map.{u1, u3} α γ f l₁) (List.map.{u2, u4} β δ g l₂)) (List.map.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (Prod.map.{u1, u3, u2, u4} α γ β δ f g) (List.zip.{u1, u2} α β l₁ l₂))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} (f : α -> γ) (g : β -> δ) (l₁ : List.{u4} α) (l₂ : List.{u3} β), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} γ δ)) (List.zip.{u2, u1} γ δ (List.map.{u4, u2} α γ f l₁) (List.map.{u3, u1} β δ g l₂)) (List.map.{max u3 u4, max u1 u2} (Prod.{u4, u3} α β) (Prod.{u2, u1} γ δ) (Prod.map.{u4, u2, u3, u1} α γ β δ f g) (List.zip.{u4, u3} α β l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.zip_map List.zip_mapₓ'. -/
theorem zip_map (f : α → γ) (g : β → δ) :
    ∀ (l₁ : List α) (l₂ : List β), zip (l₁.map f) (l₂.map g) = (zip l₁ l₂).map (Prod.map f g)
  | [], l₂ => rfl
  | l₁, [] => by simp only [map, zip_nil_right]
  | a :: l₁, b :: l₂ => by
    simp only [map, zip_cons_cons, zip_map l₁ l₂, Prod.map] <;> constructor <;> rfl
#align list.zip_map List.zip_map

/- warning: list.zip_map_left -> List.zip_map_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> γ) (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{succ (max u3 u2)} (List.{max u3 u2} (Prod.{u3, u2} γ β)) (List.zip.{u3, u2} γ β (List.map.{u1, u3} α γ f l₁) l₂) (List.map.{max u1 u2, max u3 u2} (Prod.{u1, u2} α β) (Prod.{u3, u2} γ β) (Prod.map.{u1, u3, u2, u2} α γ β β f (id.{succ u2} β)) (List.zip.{u1, u2} α β l₁ l₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> γ) (l₁ : List.{u3} α) (l₂ : List.{u2} β), Eq.{max (succ u2) (succ u1)} (List.{max u2 u1} (Prod.{u1, u2} γ β)) (List.zip.{u1, u2} γ β (List.map.{u3, u1} α γ f l₁) l₂) (List.map.{max u2 u3, max u2 u1} (Prod.{u3, u2} α β) (Prod.{u1, u2} γ β) (Prod.map.{u3, u1, u2, u2} α γ β β f (id.{succ u2} β)) (List.zip.{u3, u2} α β l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.zip_map_left List.zip_map_leftₓ'. -/
theorem zip_map_left (f : α → γ) (l₁ : List α) (l₂ : List β) :
    zip (l₁.map f) l₂ = (zip l₁ l₂).map (Prod.map f id) := by rw [← zip_map, map_id]
#align list.zip_map_left List.zip_map_left

/- warning: list.zip_map_right -> List.zip_map_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : β -> γ) (l₁ : List.{u1} α) (l₂ : List.{u2} β), Eq.{succ (max u1 u3)} (List.{max u1 u3} (Prod.{u1, u3} α γ)) (List.zip.{u1, u3} α γ l₁ (List.map.{u2, u3} β γ f l₂)) (List.map.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ) (Prod.map.{u1, u1, u2, u3} α α β γ (id.{succ u1} α) f) (List.zip.{u1, u2} α β l₁ l₂))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : β -> γ) (l₁ : List.{u3} α) (l₂ : List.{u2} β), Eq.{max (succ u3) (succ u1)} (List.{max u1 u3} (Prod.{u3, u1} α γ)) (List.zip.{u3, u1} α γ l₁ (List.map.{u2, u1} β γ f l₂)) (List.map.{max u2 u3, max u1 u3} (Prod.{u3, u2} α β) (Prod.{u3, u1} α γ) (Prod.map.{u3, u3, u2, u1} α α β γ (id.{succ u3} α) f) (List.zip.{u3, u2} α β l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.zip_map_right List.zip_map_rightₓ'. -/
theorem zip_map_right (f : β → γ) (l₁ : List α) (l₂ : List β) :
    zip l₁ (l₂.map f) = (zip l₁ l₂).map (Prod.map id f) := by rw [← zip_map, map_id]
#align list.zip_map_right List.zip_map_right

/- warning: list.zip_with_map -> List.zipWith_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {μ : Type.{u5}} (f : γ -> δ -> μ) (g : α -> γ) (h : β -> δ) (as : List.{u1} α) (bs : List.{u2} β), Eq.{succ u5} (List.{u5} μ) (List.zipWith.{u3, u4, u5} γ δ μ f (List.map.{u1, u3} α γ g as) (List.map.{u2, u4} β δ h bs)) (List.zipWith.{u1, u2, u5} α β μ (fun (a : α) (b : β) => f (g a) (h b)) as bs)
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} {μ : Type.{u4}} (f : γ -> δ -> μ) (g : α -> γ) (h : β -> δ) (as : List.{u5} α) (bs : List.{u3} β), Eq.{succ u4} (List.{u4} μ) (List.zipWith.{u2, u1, u4} γ δ μ f (List.map.{u5, u2} α γ g as) (List.map.{u3, u1} β δ h bs)) (List.zipWith.{u5, u3, u4} α β μ (fun (a : α) (b : β) => f (g a) (h b)) as bs)
Case conversion may be inaccurate. Consider using '#align list.zip_with_map List.zipWith_mapₓ'. -/
@[simp]
theorem zipWith_map {μ} (f : γ → δ → μ) (g : α → γ) (h : β → δ) (as : List α) (bs : List β) :
    zipWith f (as.map g) (bs.map h) = zipWith (fun a b => f (g a) (h b)) as bs :=
  by
  induction as generalizing bs
  · simp
  · cases bs <;> simp [*]
#align list.zip_with_map List.zipWith_map

/- warning: list.zip_with_map_left -> List.zipWith_map_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> β -> γ) (g : δ -> α) (l : List.{u4} δ) (l' : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f (List.map.{u4, u1} δ α g l) l') (List.zipWith.{u4, u2, u3} δ β γ (Function.comp.{succ u4, succ u1, max (succ u2) (succ u3)} δ α (β -> γ) f g) l l')
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u3}} (f : α -> β -> γ) (g : δ -> α) (l : List.{u3} δ) (l' : List.{u2} β), Eq.{succ u1} (List.{u1} γ) (List.zipWith.{u4, u2, u1} α β γ f (List.map.{u3, u4} δ α g l) l') (List.zipWith.{u3, u2, u1} δ β γ (Function.comp.{succ u3, succ u4, max (succ u1) (succ u2)} δ α (β -> γ) f g) l l')
Case conversion may be inaccurate. Consider using '#align list.zip_with_map_left List.zipWith_map_leftₓ'. -/
theorem zipWith_map_left (f : α → β → γ) (g : δ → α) (l : List δ) (l' : List β) :
    zipWith f (l.map g) l' = zipWith (f ∘ g) l l' :=
  by
  convert zip_with_map f g id l l'
  exact Eq.symm (List.map_id _)
#align list.zip_with_map_left List.zipWith_map_left

/- warning: list.zip_with_map_right -> List.zipWith_map_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> β -> γ) (l : List.{u1} α) (g : δ -> β) (l' : List.{u4} δ), Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f l (List.map.{u4, u2} δ β g l')) (List.zipWith.{u1, u4, u3} α δ γ (fun (x : α) => Function.comp.{succ u4, succ u2, succ u3} δ β γ (f x) g) l l')
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u1}} {γ : Type.{u2}} {δ : Type.{u3}} (f : α -> β -> γ) (l : List.{u4} α) (g : δ -> β) (l' : List.{u3} δ), Eq.{succ u2} (List.{u2} γ) (List.zipWith.{u4, u1, u2} α β γ f l (List.map.{u3, u1} δ β g l')) (List.zipWith.{u4, u3, u2} α δ γ (fun (x : α) => Function.comp.{succ u3, succ u1, succ u2} δ β γ (f x) g) l l')
Case conversion may be inaccurate. Consider using '#align list.zip_with_map_right List.zipWith_map_rightₓ'. -/
theorem zipWith_map_right (f : α → β → γ) (l : List α) (g : δ → β) (l' : List δ) :
    zipWith f l (l'.map g) = zipWith (fun x => f x ∘ g) l l' :=
  by
  convert List.zipWith_map f id g l l'
  exact Eq.symm (List.map_id _)
#align list.zip_with_map_right List.zipWith_map_right

/- warning: list.zip_map' -> List.zip_map' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : α -> γ) (l : List.{u1} α), Eq.{succ (max u2 u3)} (List.{max u2 u3} (Prod.{u2, u3} β γ)) (List.zip.{u2, u3} β γ (List.map.{u1, u2} α β f l) (List.map.{u1, u3} α γ g l)) (List.map.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (fun (a : α) => Prod.mk.{u2, u3} β γ (f a) (g a)) l)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β) (g : α -> γ) (l : List.{u3} α), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} β γ)) (List.zip.{u2, u1} β γ (List.map.{u3, u2} α β f l) (List.map.{u3, u1} α γ g l)) (List.map.{u3, max u1 u2} α (Prod.{u2, u1} β γ) (fun (a : α) => Prod.mk.{u2, u1} β γ (f a) (g a)) l)
Case conversion may be inaccurate. Consider using '#align list.zip_map' List.zip_map'ₓ'. -/
theorem zip_map' (f : α → β) (g : α → γ) :
    ∀ l : List α, zip (l.map f) (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by simp only [map, zip_cons_cons, zip_map' l] <;> constructor <;> rfl
#align list.zip_map' List.zip_map'

/- warning: list.map_zip_with -> List.map_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> β) (g : γ -> δ -> α) (l : List.{u3} γ) (l' : List.{u4} δ), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.zipWith.{u3, u4, u1} γ δ α g l l')) (List.zipWith.{u3, u4, u2} γ δ β (fun (x : γ) (y : δ) => f (g x y)) l l')
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u1}} {γ : Type.{u2}} {δ : Type.{u3}} (f : α -> β) (g : γ -> δ -> α) (l : List.{u2} γ) (l' : List.{u3} δ), Eq.{succ u1} (List.{u1} β) (List.map.{u4, u1} α β f (List.zipWith.{u2, u3, u4} γ δ α g l l')) (List.zipWith.{u2, u3, u1} γ δ β (fun (x : γ) (y : δ) => f (g x y)) l l')
Case conversion may be inaccurate. Consider using '#align list.map_zip_with List.map_zipWithₓ'. -/
theorem map_zipWith {δ : Type _} (f : α → β) (g : γ → δ → α) (l : List γ) (l' : List δ) :
    map f (zipWith g l l') = zipWith (fun x y => f (g x y)) l l' :=
  by
  induction' l with hd tl hl generalizing l'
  · simp
  · cases l'
    · simp
    · simp [hl]
#align list.map_zip_with List.map_zipWith

/- warning: list.mem_zip -> List.mem_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {a : α} {b : β} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (List.zip.{u1, u2} α β l₁ l₂)) -> (And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₁) (Membership.Mem.{u2, u2} β (List.{u2} β) (List.hasMem.{u2} β) b l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {a : α} {b : β} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.instMembershipList.{max u1 u2} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b) (List.zip.{u2, u1} α β l₁ l₂)) -> (And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₁) (Membership.mem.{u1, u1} β (List.{u1} β) (List.instMembershipList.{u1} β) b l₂))
Case conversion may be inaccurate. Consider using '#align list.mem_zip List.mem_zipₓ'. -/
theorem mem_zip {a b} : ∀ {l₁ : List α} {l₂ : List β}, (a, b) ∈ zip l₁ l₂ → a ∈ l₁ ∧ b ∈ l₂
  | _ :: l₁, _ :: l₂, Or.inl rfl => ⟨Or.inl rfl, Or.inl rfl⟩
  | a' :: l₁, b' :: l₂, Or.inr h => by
    constructor <;> simp only [mem_cons_iff, or_true_iff, mem_zip h]
#align list.mem_zip List.mem_zip

/- warning: list.map_fst_zip -> List.map_fst_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l₁ : List.{u1} α) (l₂ : List.{u2} β), (LE.le.{0} Nat Nat.hasLe (List.length.{u1} α l₁) (List.length.{u2} β l₂)) -> (Eq.{succ u1} (List.{u1} α) (List.map.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (List.zip.{u1, u2} α β l₁ l₂)) l₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l₁ : List.{u2} α) (l₂ : List.{u1} β), (LE.le.{0} Nat instLENat (List.length.{u2} α l₁) (List.length.{u1} β l₂)) -> (Eq.{succ u2} (List.{u2} α) (List.map.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) (List.zip.{u2, u1} α β l₁ l₂)) l₁)
Case conversion may be inaccurate. Consider using '#align list.map_fst_zip List.map_fst_zipₓ'. -/
theorem map_fst_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length ≤ l₂.length → map Prod.fst (zip l₁ l₂) = l₁
  | [], bs, _ => rfl
  | a :: as, b :: bs, h => by
    simp at h
    simp! [*]
  | a :: as, [], h => by
    simp at h
    contradiction
#align list.map_fst_zip List.map_fst_zip

/- warning: list.map_snd_zip -> List.map_snd_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l₁ : List.{u1} α) (l₂ : List.{u2} β), (LE.le.{0} Nat Nat.hasLe (List.length.{u2} β l₂) (List.length.{u1} α l₁)) -> (Eq.{succ u2} (List.{u2} β) (List.map.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (List.zip.{u1, u2} α β l₁ l₂)) l₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l₁ : List.{u2} α) (l₂ : List.{u1} β), (LE.le.{0} Nat instLENat (List.length.{u1} β l₂) (List.length.{u2} α l₁)) -> (Eq.{succ u1} (List.{u1} β) (List.map.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) (List.zip.{u2, u1} α β l₁ l₂)) l₂)
Case conversion may be inaccurate. Consider using '#align list.map_snd_zip List.map_snd_zipₓ'. -/
theorem map_snd_zip :
    ∀ (l₁ : List α) (l₂ : List β), l₂.length ≤ l₁.length → map Prod.snd (zip l₁ l₂) = l₂
  | _, [], _ => by
    rw [zip_nil_right]
    rfl
  | [], b :: bs, h => by
    simp at h
    contradiction
  | a :: as, b :: bs, h => by
    simp at h
    simp! [*]
#align list.map_snd_zip List.map_snd_zip

/- warning: list.unzip_nil -> List.unzip_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} (List.{u1} α) (List.{u2} β)) (List.unzip.{u1, u2} α β (List.nil.{max u1 u2} (Prod.{u1, u2} α β))) (Prod.mk.{u1, u2} (List.{u1} α) (List.{u2} β) (List.nil.{u1} α) (List.nil.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} (List.{u2} α) (List.{u1} β)) (List.unzip.{u2, u1} α β (List.nil.{max u1 u2} (Prod.{u2, u1} α β))) (Prod.mk.{u2, u1} (List.{u2} α) (List.{u1} β) (List.nil.{u2} α) (List.nil.{u1} β))
Case conversion may be inaccurate. Consider using '#align list.unzip_nil List.unzip_nilₓ'. -/
@[simp]
theorem unzip_nil : unzip (@nil (α × β)) = ([], []) :=
  rfl
#align list.unzip_nil List.unzip_nil

/- warning: list.unzip_cons -> List.unzip_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (b : β) (l : List.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} (List.{u1} α) (List.{u2} β)) (List.unzip.{u1, u2} α β (List.cons.{max u1 u2} (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a b) l)) (Prod.mk.{u1, u2} (List.{u1} α) (List.{u2} β) (List.cons.{u1} α a (Prod.fst.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β l))) (List.cons.{u2} β b (Prod.snd.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β l))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (b : β) (l : List.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} (List.{u2} α) (List.{u1} β)) (List.unzip.{u2, u1} α β (List.cons.{max u1 u2} (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a b) l)) (Prod.mk.{u2, u1} (List.{u2} α) (List.{u1} β) (List.cons.{u2} α a (Prod.fst.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β l))) (List.cons.{u1} β b (Prod.snd.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β l))))
Case conversion may be inaccurate. Consider using '#align list.unzip_cons List.unzip_consₓ'. -/
@[simp]
theorem unzip_cons (a : α) (b : β) (l : List (α × β)) :
    unzip ((a, b) :: l) = (a :: (unzip l).1, b :: (unzip l).2) := by
  rw [unzip] <;> cases unzip l <;> rfl
#align list.unzip_cons List.unzip_cons

/- warning: list.unzip_eq_map -> List.unzip_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} (List.{u1} α) (List.{u2} β)) (List.unzip.{u1, u2} α β l) (Prod.mk.{u1, u2} (List.{u1} α) (List.{u2} β) (List.map.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) l) (List.map.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} (List.{u2} α) (List.{u1} β)) (List.unzip.{u2, u1} α β l) (Prod.mk.{u2, u1} (List.{u2} α) (List.{u1} β) (List.map.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) l) (List.map.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) l))
Case conversion may be inaccurate. Consider using '#align list.unzip_eq_map List.unzip_eq_mapₓ'. -/
theorem unzip_eq_map : ∀ l : List (α × β), unzip l = (l.map Prod.fst, l.map Prod.snd)
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, map_cons, unzip_eq_map l]
#align list.unzip_eq_map List.unzip_eq_map

/- warning: list.unzip_left -> List.unzip_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u1} (List.{u1} α) (Prod.fst.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β l)) (List.map.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u2} (List.{u2} α) (Prod.fst.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β l)) (List.map.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) l)
Case conversion may be inaccurate. Consider using '#align list.unzip_left List.unzip_leftₓ'. -/
theorem unzip_left (l : List (α × β)) : (unzip l).1 = l.map Prod.fst := by simp only [unzip_eq_map]
#align list.unzip_left List.unzip_left

/- warning: list.unzip_right -> List.unzip_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u2} (List.{u2} β) (Prod.snd.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β l)) (List.map.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u1} (List.{u1} β) (Prod.snd.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β l)) (List.map.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) l)
Case conversion may be inaccurate. Consider using '#align list.unzip_right List.unzip_rightₓ'. -/
theorem unzip_right (l : List (α × β)) : (unzip l).2 = l.map Prod.snd := by simp only [unzip_eq_map]
#align list.unzip_right List.unzip_right

/- warning: list.unzip_swap -> List.unzip_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} (List.{u2} β) (List.{u1} α)) (List.unzip.{u2, u1} β α (List.map.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β) l)) (Prod.swap.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} (List.{u1} β) (List.{u2} α)) (List.unzip.{u1, u2} β α (List.map.{max u1 u2, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β) l)) (Prod.swap.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β l))
Case conversion may be inaccurate. Consider using '#align list.unzip_swap List.unzip_swapₓ'. -/
theorem unzip_swap (l : List (α × β)) : unzip (l.map Prod.swap) = (unzip l).symm := by
  simp only [unzip_eq_map, map_map] <;> constructor <;> rfl
#align list.unzip_swap List.unzip_swap

/- warning: list.zip_unzip -> List.zip_unzip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.zip.{u1, u2} α β (Prod.fst.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β l)) (Prod.snd.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β l))) l
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.zip.{u2, u1} α β (Prod.fst.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β l)) (Prod.snd.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β l))) l
Case conversion may be inaccurate. Consider using '#align list.zip_unzip List.zip_unzipₓ'. -/
theorem zip_unzip : ∀ l : List (α × β), zip (unzip l).1 (unzip l).2 = l
  | [] => rfl
  | (a, b) :: l => by simp only [unzip_cons, zip_cons_cons, zip_unzip l] <;> constructor <;> rfl
#align list.zip_unzip List.zip_unzip

/- warning: list.unzip_zip_left -> List.unzip_zip_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (LE.le.{0} Nat Nat.hasLe (List.length.{u1} α l₁) (List.length.{u2} β l₂)) -> (Eq.{succ u1} (List.{u1} α) (Prod.fst.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β (List.zip.{u1, u2} α β l₁ l₂))) l₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (LE.le.{0} Nat instLENat (List.length.{u2} α l₁) (List.length.{u1} β l₂)) -> (Eq.{succ u2} (List.{u2} α) (Prod.fst.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β (List.zip.{u2, u1} α β l₁ l₂))) l₁)
Case conversion may be inaccurate. Consider using '#align list.unzip_zip_left List.unzip_zip_leftₓ'. -/
theorem unzip_zip_left :
    ∀ {l₁ : List α} {l₂ : List β}, length l₁ ≤ length l₂ → (unzip (zip l₁ l₂)).1 = l₁
  | [], l₂, h => rfl
  | l₁, [], h => by rw [eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)] <;> rfl
  | a :: l₁, b :: l₂, h => by
    simp only [zip_cons_cons, unzip_cons, unzip_zip_left (le_of_succ_le_succ h)] <;> constructor <;>
      rfl
#align list.unzip_zip_left List.unzip_zip_left

/- warning: list.unzip_zip_right -> List.unzip_zip_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (LE.le.{0} Nat Nat.hasLe (List.length.{u2} β l₂) (List.length.{u1} α l₁)) -> (Eq.{succ u2} (List.{u2} β) (Prod.snd.{u1, u2} (List.{u1} α) (List.{u2} β) (List.unzip.{u1, u2} α β (List.zip.{u1, u2} α β l₁ l₂))) l₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (LE.le.{0} Nat instLENat (List.length.{u1} β l₂) (List.length.{u2} α l₁)) -> (Eq.{succ u1} (List.{u1} β) (Prod.snd.{u2, u1} (List.{u2} α) (List.{u1} β) (List.unzip.{u2, u1} α β (List.zip.{u2, u1} α β l₁ l₂))) l₂)
Case conversion may be inaccurate. Consider using '#align list.unzip_zip_right List.unzip_zip_rightₓ'. -/
theorem unzip_zip_right {l₁ : List α} {l₂ : List β} (h : length l₂ ≤ length l₁) :
    (unzip (zip l₁ l₂)).2 = l₂ := by rw [← zip_swap, unzip_swap] <;> exact unzip_zip_left h
#align list.unzip_zip_right List.unzip_zip_right

/- warning: list.unzip_zip -> List.unzip_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : List.{u1} α} {l₂ : List.{u2} β}, (Eq.{1} Nat (List.length.{u1} α l₁) (List.length.{u2} β l₂)) -> (Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} (List.{u1} α) (List.{u2} β)) (List.unzip.{u1, u2} α β (List.zip.{u1, u2} α β l₁ l₂)) (Prod.mk.{u1, u2} (List.{u1} α) (List.{u2} β) l₁ l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l₁ : List.{u2} α} {l₂ : List.{u1} β}, (Eq.{1} Nat (List.length.{u2} α l₁) (List.length.{u1} β l₂)) -> (Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} (List.{u2} α) (List.{u1} β)) (List.unzip.{u2, u1} α β (List.zip.{u2, u1} α β l₁ l₂)) (Prod.mk.{u2, u1} (List.{u2} α) (List.{u1} β) l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.unzip_zip List.unzip_zipₓ'. -/
theorem unzip_zip {l₁ : List α} {l₂ : List β} (h : length l₁ = length l₂) :
    unzip (zip l₁ l₂) = (l₁, l₂) := by
  rw [← @Prod.mk.eta _ _ (unzip (zip l₁ l₂)), unzip_zip_left (le_of_eq h),
    unzip_zip_right (ge_of_eq h)]
#align list.unzip_zip List.unzip_zip

/- warning: list.zip_of_prod -> List.zip_of_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : List.{u1} α} {l' : List.{u2} β} {lp : List.{max u1 u2} (Prod.{u1, u2} α β)}, (Eq.{succ u1} (List.{u1} α) (List.map.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) lp) l) -> (Eq.{succ u2} (List.{u2} β) (List.map.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) lp) l') -> (Eq.{succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) lp (List.zip.{u1, u2} α β l l'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : List.{u2} α} {l' : List.{u1} β} {lp : List.{max u1 u2} (Prod.{u2, u1} α β)}, (Eq.{succ u2} (List.{u2} α) (List.map.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) lp) l) -> (Eq.{succ u1} (List.{u1} β) (List.map.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) lp) l') -> (Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} α β)) lp (List.zip.{u2, u1} α β l l'))
Case conversion may be inaccurate. Consider using '#align list.zip_of_prod List.zip_of_prodₓ'. -/
theorem zip_of_prod {l : List α} {l' : List β} {lp : List (α × β)} (hl : lp.map Prod.fst = l)
    (hr : lp.map Prod.snd = l') : lp = l.zip l' := by
  rw [← hl, ← hr, ← zip_unzip lp, ← unzip_left, ← unzip_right, zip_unzip, zip_unzip]
#align list.zip_of_prod List.zip_of_prod

/- warning: list.map_prod_left_eq_zip -> List.map_prod_left_eq_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : List.{u1} α} (f : α -> β), Eq.{succ (max u1 u2)} (List.{max u1 u2} (Prod.{u1, u2} α β)) (List.map.{u1, max u1 u2} α (Prod.{u1, u2} α β) (fun (x : α) => Prod.mk.{u1, u2} α β x (f x)) l) (List.zip.{u1, u2} α β l (List.map.{u1, u2} α β f l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : List.{u2} α} (f : α -> β), Eq.{max (succ u2) (succ u1)} (List.{max u1 u2} (Prod.{u2, u1} α β)) (List.map.{u2, max u1 u2} α (Prod.{u2, u1} α β) (fun (x : α) => Prod.mk.{u2, u1} α β x (f x)) l) (List.zip.{u2, u1} α β l (List.map.{u2, u1} α β f l))
Case conversion may be inaccurate. Consider using '#align list.map_prod_left_eq_zip List.map_prod_left_eq_zipₓ'. -/
theorem map_prod_left_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (x, f x)) = l.zip (l.map f) :=
  by
  rw [← zip_map']
  congr
  exact map_id _
#align list.map_prod_left_eq_zip List.map_prod_left_eq_zip

/- warning: list.map_prod_right_eq_zip -> List.map_prod_right_eq_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : List.{u1} α} (f : α -> β), Eq.{succ (max u2 u1)} (List.{max u2 u1} (Prod.{u2, u1} β α)) (List.map.{u1, max u2 u1} α (Prod.{u2, u1} β α) (fun (x : α) => Prod.mk.{u2, u1} β α (f x) x) l) (List.zip.{u2, u1} β α (List.map.{u1, u2} α β f l) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : List.{u2} α} (f : α -> β), Eq.{max (succ u2) (succ u1)} (List.{max u2 u1} (Prod.{u1, u2} β α)) (List.map.{u2, max u2 u1} α (Prod.{u1, u2} β α) (fun (x : α) => Prod.mk.{u1, u2} β α (f x) x) l) (List.zip.{u1, u2} β α (List.map.{u2, u1} α β f l) l)
Case conversion may be inaccurate. Consider using '#align list.map_prod_right_eq_zip List.map_prod_right_eq_zipₓ'. -/
theorem map_prod_right_eq_zip {l : List α} (f : α → β) :
    (l.map fun x => (f x, x)) = (l.map f).zip l :=
  by
  rw [← zip_map']
  congr
  exact map_id _
#align list.map_prod_right_eq_zip List.map_prod_right_eq_zip

/- warning: list.zip_with_comm -> List.zipWith_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (la : List.{u1} α) (lb : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f la lb) (List.zipWith.{u2, u1, u3} β α γ (fun (b : β) (a : α) => f a b) lb la)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (la : List.{u3} α) (lb : List.{u2} β), Eq.{succ u1} (List.{u1} γ) (List.zipWith.{u3, u2, u1} α β γ f la lb) (List.zipWith.{u2, u3, u1} β α γ (fun (b : β) (a : α) => f a b) lb la)
Case conversion may be inaccurate. Consider using '#align list.zip_with_comm List.zipWith_commₓ'. -/
theorem zipWith_comm (f : α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith f la lb = zipWith (fun b a => f a b) lb la
  | [], _ => (List.zipWith_nil_right _ _).symm
  | a :: as, [] => rfl
  | a :: as, b :: bs => congr_arg _ (zip_with_comm as bs)
#align list.zip_with_comm List.zipWith_comm

/- warning: list.zip_with_congr -> List.zipWith_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (g : α -> β -> γ) (la : List.{u1} α) (lb : List.{u2} β), (List.Forall₂.{u1, u2} α β (fun (a : α) (b : β) => Eq.{succ u3} γ (f a b) (g a b)) la lb) -> (Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f la lb) (List.zipWith.{u1, u2, u3} α β γ g la lb))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (g : α -> β -> γ) (la : List.{u3} α) (lb : List.{u2} β), (List.Forall₂.{u3, u2} α β (fun (a : α) (b : β) => Eq.{succ u1} γ (f a b) (g a b)) la lb) -> (Eq.{succ u1} (List.{u1} γ) (List.zipWith.{u3, u2, u1} α β γ f la lb) (List.zipWith.{u3, u2, u1} α β γ g la lb))
Case conversion may be inaccurate. Consider using '#align list.zip_with_congr List.zipWith_congrₓ'. -/
@[congr]
theorem zipWith_congr (f g : α → β → γ) (la : List α) (lb : List β)
    (h : List.Forall₂ (fun a b => f a b = g a b) la lb) : zipWith f la lb = zipWith g la lb :=
  by
  induction' h with a b as bs hfg habs ih
  · rfl
  · exact congr_arg₂ _ hfg ih
#align list.zip_with_congr List.zipWith_congr

/- warning: list.zip_with_comm_of_comm -> List.zipWith_comm_of_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> α -> β), (forall (x : α) (y : α), Eq.{succ u2} β (f x y) (f y x)) -> (forall (l : List.{u1} α) (l' : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.zipWith.{u1, u1, u2} α α β f l l') (List.zipWith.{u1, u1, u2} α α β f l' l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> α -> β), (forall (x : α) (y : α), Eq.{succ u1} β (f x y) (f y x)) -> (forall (l : List.{u2} α) (l' : List.{u2} α), Eq.{succ u1} (List.{u1} β) (List.zipWith.{u2, u2, u1} α α β f l l') (List.zipWith.{u2, u2, u1} α α β f l' l))
Case conversion may be inaccurate. Consider using '#align list.zip_with_comm_of_comm List.zipWith_comm_of_commₓ'. -/
theorem zipWith_comm_of_comm (f : α → α → β) (comm : ∀ x y : α, f x y = f y x) (l l' : List α) :
    zipWith f l l' = zipWith f l' l := by
  rw [zip_with_comm]
  simp only [comm]
#align list.zip_with_comm_of_comm List.zipWith_comm_of_comm

/- warning: list.zip_with_same -> List.zipWith_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : Type.{u2}} (f : α -> α -> δ) (l : List.{u1} α), Eq.{succ u2} (List.{u2} δ) (List.zipWith.{u1, u1, u2} α α δ f l l) (List.map.{u1, u2} α δ (fun (a : α) => f a a) l)
but is expected to have type
  forall {α : Type.{u2}} {δ : Type.{u1}} (f : α -> α -> δ) (l : List.{u2} α), Eq.{succ u1} (List.{u1} δ) (List.zipWith.{u2, u2, u1} α α δ f l l) (List.map.{u2, u1} α δ (fun (a : α) => f a a) l)
Case conversion may be inaccurate. Consider using '#align list.zip_with_same List.zipWith_sameₓ'. -/
@[simp]
theorem zipWith_same (f : α → α → δ) : ∀ l : List α, zipWith f l l = l.map fun a => f a a
  | [] => rfl
  | x :: xs => congr_arg _ (zip_with_same xs)
#align list.zip_with_same List.zipWith_same

/- warning: list.zip_with_zip_with_left -> List.zipWith_zipWith_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} (f : δ -> γ -> ε) (g : α -> β -> δ) (la : List.{u1} α) (lb : List.{u2} β) (lc : List.{u3} γ), Eq.{succ u5} (List.{u5} ε) (List.zipWith.{u4, u3, u5} δ γ ε f (List.zipWith.{u1, u2, u4} α β δ g la lb) lc) (List.zipWith3.{u1, u2, u3, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => f (g a b) c) la lb lc)
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u4}} {γ : Type.{u3}} {δ : Type.{u1}} {ε : Type.{u2}} (f : δ -> γ -> ε) (g : α -> β -> δ) (la : List.{u5} α) (lb : List.{u4} β) (lc : List.{u3} γ), Eq.{succ u2} (List.{u2} ε) (List.zipWith.{u1, u3, u2} δ γ ε f (List.zipWith.{u5, u4, u1} α β δ g la lb) lc) (List.zipWith3.{u5, u4, u3, u2} α β γ ε (fun (a : α) (b : β) (c : γ) => f (g a b) c) la lb lc)
Case conversion may be inaccurate. Consider using '#align list.zip_with_zip_with_left List.zipWith_zipWith_leftₓ'. -/
theorem zipWith_zipWith_left (f : δ → γ → ε) (g : α → β → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f (zipWith g la lb) lc = zipWith3 (fun a b c => f (g a b) c) la lb lc
  | [], _, _ => rfl
  | a :: as, [], _ => rfl
  | a :: as, b :: bs, [] => rfl
  | a :: as, b :: bs, c :: cs => congr_arg (cons _) <| zip_with_zip_with_left as bs cs
#align list.zip_with_zip_with_left List.zipWith_zipWith_left

/- warning: list.zip_with_zip_with_right -> List.zipWith_zipWith_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} (f : α -> δ -> ε) (g : β -> γ -> δ) (la : List.{u1} α) (lb : List.{u2} β) (lc : List.{u3} γ), Eq.{succ u5} (List.{u5} ε) (List.zipWith.{u1, u4, u5} α δ ε f la (List.zipWith.{u2, u3, u4} β γ δ g lb lc)) (List.zipWith3.{u1, u2, u3, u5} α β γ ε (fun (a : α) (b : β) (c : γ) => f a (g b c)) la lb lc)
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u4}} {γ : Type.{u3}} {δ : Type.{u1}} {ε : Type.{u2}} (f : α -> δ -> ε) (g : β -> γ -> δ) (la : List.{u5} α) (lb : List.{u4} β) (lc : List.{u3} γ), Eq.{succ u2} (List.{u2} ε) (List.zipWith.{u5, u1, u2} α δ ε f la (List.zipWith.{u4, u3, u1} β γ δ g lb lc)) (List.zipWith3.{u5, u4, u3, u2} α β γ ε (fun (a : α) (b : β) (c : γ) => f a (g b c)) la lb lc)
Case conversion may be inaccurate. Consider using '#align list.zip_with_zip_with_right List.zipWith_zipWith_rightₓ'. -/
theorem zipWith_zipWith_right (f : α → δ → ε) (g : β → γ → δ) :
    ∀ (la : List α) (lb : List β) (lc : List γ),
      zipWith f la (zipWith g lb lc) = zipWith3 (fun a b c => f a (g b c)) la lb lc
  | [], _, _ => rfl
  | a :: as, [], _ => rfl
  | a :: as, b :: bs, [] => rfl
  | a :: as, b :: bs, c :: cs => congr_arg (cons _) <| zip_with_zip_with_right as bs cs
#align list.zip_with_zip_with_right List.zipWith_zipWith_right

/- warning: list.zip_with3_same_left -> List.zipWith3_same_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> α -> β -> γ) (la : List.{u1} α) (lb : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.zipWith3.{u1, u1, u2, u3} α α β γ f la la lb) (List.zipWith.{u1, u2, u3} α β γ (fun (a : α) (b : β) => f a a b) la lb)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> α -> β -> γ) (la : List.{u3} α) (lb : List.{u2} β), Eq.{succ u1} (List.{u1} γ) (List.zipWith3.{u3, u3, u2, u1} α α β γ f la la lb) (List.zipWith.{u3, u2, u1} α β γ (fun (a : α) (b : β) => f a a b) la lb)
Case conversion may be inaccurate. Consider using '#align list.zip_with3_same_left List.zipWith3_same_leftₓ'. -/
@[simp]
theorem zipWith3_same_left (f : α → α → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la la lb = zipWith (fun a b => f a a b) la lb
  | [], _ => rfl
  | a :: as, [] => rfl
  | a :: as, b :: bs => congr_arg (cons _) <| zip_with3_same_left as bs
#align list.zip_with3_same_left List.zipWith3_same_left

/- warning: list.zip_with3_same_mid -> List.zipWith3_same_mid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> α -> γ) (la : List.{u1} α) (lb : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.zipWith3.{u1, u2, u1, u3} α β α γ f la lb la) (List.zipWith.{u1, u2, u3} α β γ (fun (a : α) (b : β) => f a b a) la lb)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> α -> γ) (la : List.{u3} α) (lb : List.{u2} β), Eq.{succ u1} (List.{u1} γ) (List.zipWith3.{u3, u2, u3, u1} α β α γ f la lb la) (List.zipWith.{u3, u2, u1} α β γ (fun (a : α) (b : β) => f a b a) la lb)
Case conversion may be inaccurate. Consider using '#align list.zip_with3_same_mid List.zipWith3_same_midₓ'. -/
@[simp]
theorem zipWith3_same_mid (f : α → β → α → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb la = zipWith (fun a b => f a b a) la lb
  | [], _ => rfl
  | a :: as, [] => rfl
  | a :: as, b :: bs => congr_arg (cons _) <| zip_with3_same_mid as bs
#align list.zip_with3_same_mid List.zipWith3_same_mid

/- warning: list.zip_with3_same_right -> List.zipWith3_same_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> β -> γ) (la : List.{u1} α) (lb : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.zipWith3.{u1, u2, u2, u3} α β β γ f la lb lb) (List.zipWith.{u1, u2, u3} α β γ (fun (a : α) (b : β) => f a b b) la lb)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> β -> γ) (la : List.{u3} α) (lb : List.{u2} β), Eq.{succ u1} (List.{u1} γ) (List.zipWith3.{u3, u2, u2, u1} α β β γ f la lb lb) (List.zipWith.{u3, u2, u1} α β γ (fun (a : α) (b : β) => f a b b) la lb)
Case conversion may be inaccurate. Consider using '#align list.zip_with3_same_right List.zipWith3_same_rightₓ'. -/
@[simp]
theorem zipWith3_same_right (f : α → β → β → γ) :
    ∀ (la : List α) (lb : List β), zipWith3 f la lb lb = zipWith (fun a b => f a b b) la lb
  | [], _ => rfl
  | a :: as, [] => rfl
  | a :: as, b :: bs => congr_arg (cons _) <| zip_with3_same_right as bs
#align list.zip_with3_same_right List.zipWith3_same_right

instance (f : α → α → β) [IsSymmOp α β f] : IsSymmOp (List α) (List β) (zipWith f) :=
  ⟨zipWith_comm_of_comm f IsSymmOp.symm_op⟩

#print List.length_revzip /-
@[simp]
theorem length_revzip (l : List α) : length (revzip l) = length l := by
  simp only [revzip, length_zip, length_reverse, min_self]
#align list.length_revzip List.length_revzip
-/

#print List.unzip_revzip /-
@[simp]
theorem unzip_revzip (l : List α) : (revzip l).unzip = (l, l.reverse) :=
  unzip_zip (length_reverse l).symm
#align list.unzip_revzip List.unzip_revzip
-/

#print List.revzip_map_fst /-
@[simp]
theorem revzip_map_fst (l : List α) : (revzip l).map Prod.fst = l := by
  rw [← unzip_left, unzip_revzip]
#align list.revzip_map_fst List.revzip_map_fst
-/

#print List.revzip_map_snd /-
@[simp]
theorem revzip_map_snd (l : List α) : (revzip l).map Prod.snd = l.reverse := by
  rw [← unzip_right, unzip_revzip]
#align list.revzip_map_snd List.revzip_map_snd
-/

#print List.reverse_revzip /-
theorem reverse_revzip (l : List α) : reverse l.revzip = revzip l.reverse := by
  rw [← zip_unzip.{u, u} (revzip l).reverse, unzip_eq_map] <;> simp <;> simp [revzip]
#align list.reverse_revzip List.reverse_revzip
-/

#print List.revzip_swap /-
theorem revzip_swap (l : List α) : (revzip l).map Prod.swap = revzip l.reverse := by simp [revzip]
#align list.revzip_swap List.revzip_swap
-/

/- warning: list.nth_zip_with -> List.get?_zip_with is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l₁ : List.{u1} α) (l₂ : List.{u2} β) (i : Nat), Eq.{succ u3} (Option.{u3} γ) (List.get?.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l₁ l₂) i) (Option.bind.{max u2 u3, u3} (β -> γ) γ (Option.map.{u1, max u2 u3} α (β -> γ) f (List.get?.{u1} α l₁ i)) (fun (g : β -> γ) => Option.map.{u2, u3} β γ g (List.get?.{u2} β l₂ i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (l₁ : List.{u3} α) (l₂ : List.{u2} β) (i : Nat), Eq.{succ u1} (Option.{u1} γ) (List.get?.{u1} γ (List.zipWith.{u3, u2, u1} α β γ f l₁ l₂) i) (Option.bind.{max u2 u1, u1} (β -> γ) γ (Option.map.{u3, max u2 u1} α (β -> γ) f (List.get?.{u3} α l₁ i)) (fun (g : β -> γ) => Option.map.{u2, u1} β γ g (List.get?.{u2} β l₂ i)))
Case conversion may be inaccurate. Consider using '#align list.nth_zip_with List.get?_zip_withₓ'. -/
theorem get?_zip_with (f : α → β → γ) (l₁ : List α) (l₂ : List β) (i : ℕ) :
    (zipWith f l₁ l₂).get? i = ((l₁.get? i).map f).bind fun g => (l₂.get? i).map g :=
  by
  induction l₁ generalizing l₂ i
  · simp [zip_with, (· <*> ·)]
  · cases l₂ <;> simp only [zip_with, Seq.seq, Functor.map, nth, Option.map_none']
    · cases (l₁_hd :: l₁_tl).get? i <;> rfl
    · cases i <;> simp only [Option.map_some', nth, Option.some_bind', *]
#align list.nth_zip_with List.get?_zip_with

/- warning: list.nth_zip_with_eq_some -> List.get?_zip_with_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l₁ : List.{u1} α) (l₂ : List.{u2} β) (z : γ) (i : Nat), Iff (Eq.{succ u3} (Option.{u3} γ) (List.get?.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l₁ l₂) i) (Option.some.{u3} γ z)) (Exists.{succ u1} α (fun (x : α) => Exists.{succ u2} β (fun (y : β) => And (Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α l₁ i) (Option.some.{u1} α x)) (And (Eq.{succ u2} (Option.{u2} β) (List.get?.{u2} β l₂ i) (Option.some.{u2} β y)) (Eq.{succ u3} γ (f x y) z)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (l₁ : List.{u3} α) (l₂ : List.{u2} β) (z : γ) (i : Nat), Iff (Eq.{succ u1} (Option.{u1} γ) (List.get?.{u1} γ (List.zipWith.{u3, u2, u1} α β γ f l₁ l₂) i) (Option.some.{u1} γ z)) (Exists.{succ u3} α (fun (x : α) => Exists.{succ u2} β (fun (y : β) => And (Eq.{succ u3} (Option.{u3} α) (List.get?.{u3} α l₁ i) (Option.some.{u3} α x)) (And (Eq.{succ u2} (Option.{u2} β) (List.get?.{u2} β l₂ i) (Option.some.{u2} β y)) (Eq.{succ u1} γ (f x y) z)))))
Case conversion may be inaccurate. Consider using '#align list.nth_zip_with_eq_some List.get?_zip_with_eq_someₓ'. -/
theorem get?_zip_with_eq_some {α β γ} (f : α → β → γ) (l₁ : List α) (l₂ : List β) (z : γ) (i : ℕ) :
    (zipWith f l₁ l₂).get? i = some z ↔
      ∃ x y, l₁.get? i = some x ∧ l₂.get? i = some y ∧ f x y = z :=
  by
  induction l₁ generalizing l₂ i
  · simp [zip_with]
  · cases l₂ <;> simp only [zip_with, nth, exists_false, and_false_iff, false_and_iff]
    cases i <;> simp [*]
#align list.nth_zip_with_eq_some List.get?_zip_with_eq_some

/- warning: list.nth_zip_eq_some -> List.get?_zip_eq_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l₁ : List.{u1} α) (l₂ : List.{u2} β) (z : Prod.{u1, u2} α β) (i : Nat), Iff (Eq.{succ (max u1 u2)} (Option.{max u1 u2} (Prod.{u1, u2} α β)) (List.get?.{max u1 u2} (Prod.{u1, u2} α β) (List.zip.{u1, u2} α β l₁ l₂) i) (Option.some.{max u1 u2} (Prod.{u1, u2} α β) z)) (And (Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α l₁ i) (Option.some.{u1} α (Prod.fst.{u1, u2} α β z))) (Eq.{succ u2} (Option.{u2} β) (List.get?.{u2} β l₂ i) (Option.some.{u2} β (Prod.snd.{u1, u2} α β z))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l₁ : List.{u2} α) (l₂ : List.{u1} β) (z : Prod.{u2, u1} α β) (i : Nat), Iff (Eq.{max (succ u2) (succ u1)} (Option.{max u2 u1} (Prod.{u2, u1} α β)) (List.get?.{max u2 u1} (Prod.{u2, u1} α β) (List.zip.{u2, u1} α β l₁ l₂) i) (Option.some.{max u2 u1} (Prod.{u2, u1} α β) z)) (And (Eq.{succ u2} (Option.{u2} α) (List.get?.{u2} α l₁ i) (Option.some.{u2} α (Prod.fst.{u2, u1} α β z))) (Eq.{succ u1} (Option.{u1} β) (List.get?.{u1} β l₂ i) (Option.some.{u1} β (Prod.snd.{u2, u1} α β z))))
Case conversion may be inaccurate. Consider using '#align list.nth_zip_eq_some List.get?_zip_eq_someₓ'. -/
theorem get?_zip_eq_some (l₁ : List α) (l₂ : List β) (z : α × β) (i : ℕ) :
    (zip l₁ l₂).get? i = some z ↔ l₁.get? i = some z.1 ∧ l₂.get? i = some z.2 :=
  by
  cases z
  rw [zip, nth_zip_with_eq_some]; constructor
  · rintro ⟨x, y, h₀, h₁, h₂⟩
    cc
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, _, h₀, h₁, rfl⟩
#align list.nth_zip_eq_some List.get?_zip_eq_some

/- warning: list.nth_le_zip_with -> List.nthLe_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {l : List.{u1} α} {l' : List.{u2} β} {i : Nat} {h : LT.lt.{0} Nat Nat.hasLt i (List.length.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l l'))}, Eq.{succ u3} γ (List.nthLe.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l l') i h) (f (List.nthLe.{u1} α l i (List.lt_length_left_of_zipWith.{u1, u2, u3} α β γ f i l l' h)) (List.nthLe.{u2} β l' i (List.lt_length_right_of_zipWith.{u1, u2, u3} α β γ f i l l' h)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {l : List.{u3} α} {l' : List.{u2} β} {i : Nat} {h : LT.lt.{0} Nat instLTNat i (List.length.{u1} γ (List.zipWith.{u3, u2, u1} α β γ f l l'))}, Eq.{succ u1} γ (List.nthLe.{u1} γ (List.zipWith.{u3, u2, u1} α β γ f l l') i h) (f (List.nthLe.{u3} α l i (List.lt_length_left_of_zipWith.{u1, u2, u3} α β γ f i l l' h)) (List.nthLe.{u2} β l' i (List.lt_length_right_of_zipWith.{u1, u2, u3} α β γ f i l l' h)))
Case conversion may be inaccurate. Consider using '#align list.nth_le_zip_with List.nthLe_zipWithₓ'. -/
@[simp]
theorem nthLe_zipWith {f : α → β → γ} {l : List α} {l' : List β} {i : ℕ}
    {h : i < (zipWith f l l').length} :
    (zipWith f l l').nthLe i h =
      f (l.nthLe i (lt_length_left_of_zipWith h)) (l'.nthLe i (lt_length_right_of_zipWith h)) :=
  by
  rw [← Option.some_inj, ← nth_le_nth, nth_zip_with_eq_some]
  refine'
    ⟨l.nth_le i (lt_length_left_of_zip_with h), l'.nth_le i (lt_length_right_of_zip_with h),
      nth_le_nth _, _⟩
  simp only [← nth_le_nth, eq_self_iff_true, and_self_iff]
#align list.nth_le_zip_with List.nthLe_zipWith

/- warning: list.nth_le_zip -> List.nthLe_zip is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : List.{u1} α} {l' : List.{u2} β} {i : Nat} {h : LT.lt.{0} Nat Nat.hasLt i (List.length.{max u1 u2} (Prod.{u1, u2} α β) (List.zip.{u1, u2} α β l l'))}, Eq.{max (succ u1) (succ u2)} (Prod.{u1, u2} α β) (List.nthLe.{max u1 u2} (Prod.{u1, u2} α β) (List.zip.{u1, u2} α β l l') i h) (Prod.mk.{u1, u2} α β (List.nthLe.{u1} α l i (List.lt_length_left_of_zip.{u1, u2} α β i l l' h)) (List.nthLe.{u2} β l' i (List.lt_length_right_of_zip.{u1, u2} α β i l l' h)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : List.{u2} α} {l' : List.{u1} β} {i : Nat} {h : LT.lt.{0} Nat instLTNat i (List.length.{max u2 u1} (Prod.{u2, u1} α β) (List.zip.{u2, u1} α β l l'))}, Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (List.nthLe.{max u2 u1} (Prod.{u2, u1} α β) (List.zip.{u2, u1} α β l l') i h) (Prod.mk.{u2, u1} α β (List.nthLe.{u2} α l i (List.lt_length_left_of_zip.{u1, u2} α β i l l' h)) (List.nthLe.{u1} β l' i (List.lt_length_right_of_zip.{u1, u2} α β i l l' h)))
Case conversion may be inaccurate. Consider using '#align list.nth_le_zip List.nthLe_zipₓ'. -/
@[simp]
theorem nthLe_zip {l : List α} {l' : List β} {i : ℕ} {h : i < (zip l l').length} :
    (zip l l').nthLe i h =
      (l.nthLe i (lt_length_left_of_zip h), l'.nthLe i (lt_length_right_of_zip h)) :=
  nthLe_zipWith
#align list.nth_le_zip List.nthLe_zip

#print List.mem_zip_inits_tails /-
theorem mem_zip_inits_tails {l : List α} {init tail : List α} :
    (init, tail) ∈ zip l.inits l.tails ↔ init ++ tail = l :=
  by
  induction l generalizing init tail <;> simp_rw [tails, inits, zip_cons_cons]
  · simp
  · constructor <;> rw [mem_cons_iff, zip_map_left, mem_map, Prod.exists]
    · rintro (⟨rfl, rfl⟩ | ⟨_, _, h, rfl, rfl⟩)
      · simp
      · simp [l_ih.mp h]
    · cases init
      · simp
      · intro h
        right
        use init_tl, tail
        simp_all
#align list.mem_zip_inits_tails List.mem_zip_inits_tails
-/

/- warning: list.map_uncurry_zip_eq_zip_with -> List.map_uncurry_zip_eq_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l : List.{u1} α) (l' : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.map.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Function.uncurry.{u1, u2, u3} α β γ f) (List.zip.{u1, u2} α β l l')) (List.zipWith.{u1, u2, u3} α β γ f l l')
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (l : List.{u3} α) (l' : List.{u2} β), Eq.{succ u1} (List.{u1} γ) (List.map.{max u2 u3, u1} (Prod.{u3, u2} α β) γ (Function.uncurry.{u3, u2, u1} α β γ f) (List.zip.{u3, u2} α β l l')) (List.zipWith.{u3, u2, u1} α β γ f l l')
Case conversion may be inaccurate. Consider using '#align list.map_uncurry_zip_eq_zip_with List.map_uncurry_zip_eq_zipWithₓ'. -/
theorem map_uncurry_zip_eq_zipWith (f : α → β → γ) (l : List α) (l' : List β) :
    map (Function.uncurry f) (l.zip l') = zipWith f l l' :=
  by
  induction' l with hd tl hl generalizing l'
  · simp
  · cases' l' with hd' tl'
    · simp
    · simp [hl]
#align list.map_uncurry_zip_eq_zip_with List.map_uncurry_zip_eq_zipWith

/- warning: list.sum_zip_with_distrib_left -> List.sum_zipWith_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Semiring.{u3} γ] (f : α -> β -> γ) (n : γ) (l : List.{u1} α) (l' : List.{u2} β), Eq.{succ u3} γ (List.sum.{u3} γ (Distrib.toHasAdd.{u3} γ (NonUnitalNonAssocSemiring.toDistrib.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_1)))) (MulZeroClass.toHasZero.{u3} γ (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_1)))) (List.zipWith.{u1, u2, u3} α β γ (fun (x : α) (y : β) => HMul.hMul.{u3, u3, u3} γ γ γ (instHMul.{u3} γ (Distrib.toHasMul.{u3} γ (NonUnitalNonAssocSemiring.toDistrib.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_1))))) n (f x y)) l l')) (HMul.hMul.{u3, u3, u3} γ γ γ (instHMul.{u3} γ (Distrib.toHasMul.{u3} γ (NonUnitalNonAssocSemiring.toDistrib.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_1))))) n (List.sum.{u3} γ (Distrib.toHasAdd.{u3} γ (NonUnitalNonAssocSemiring.toDistrib.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_1)))) (MulZeroClass.toHasZero.{u3} γ (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_1)))) (List.zipWith.{u1, u2, u3} α β γ f l l')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : Semiring.{u2} γ] (f : α -> β -> γ) (n : γ) (l : List.{u3} α) (l' : List.{u1} β), Eq.{succ u2} γ (List.sum.{u2} γ (Distrib.toAdd.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_1)))) (MonoidWithZero.toZero.{u2} γ (Semiring.toMonoidWithZero.{u2} γ _inst_1)) (List.zipWith.{u3, u1, u2} α β γ (fun (x : α) (y : β) => HMul.hMul.{u2, u2, u2} γ γ γ (instHMul.{u2} γ (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_1)))) n (f x y)) l l')) (HMul.hMul.{u2, u2, u2} γ γ γ (instHMul.{u2} γ (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_1)))) n (List.sum.{u2} γ (Distrib.toAdd.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_1)))) (MonoidWithZero.toZero.{u2} γ (Semiring.toMonoidWithZero.{u2} γ _inst_1)) (List.zipWith.{u3, u1, u2} α β γ f l l')))
Case conversion may be inaccurate. Consider using '#align list.sum_zip_with_distrib_left List.sum_zipWith_distrib_leftₓ'. -/
@[simp]
theorem sum_zipWith_distrib_left {γ : Type _} [Semiring γ] (f : α → β → γ) (n : γ) (l : List α)
    (l' : List β) : (l.zipWith (fun x y => n * f x y) l').Sum = n * (l.zipWith f l').Sum :=
  by
  induction' l with hd tl hl generalizing f n l'
  · simp
  · cases' l' with hd' tl'
    · simp
    · simp [hl, mul_add]
#align list.sum_zip_with_distrib_left List.sum_zipWith_distrib_left

section Distrib

/-! ### Operations that can be applied before or after a `zip_with` -/


variable (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ)

/- warning: list.zip_with_distrib_take -> List.zipWith_distrib_take is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l : List.{u1} α) (l' : List.{u2} β) (n : Nat), Eq.{succ u3} (List.{u3} γ) (List.take.{u3} γ n (List.zipWith.{u1, u2, u3} α β γ f l l')) (List.zipWith.{u1, u2, u3} α β γ f (List.take.{u1} α n l) (List.take.{u2} β n l'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (f : α -> β -> γ) (l : List.{u3} α) (l' : List.{u1} β) (n : Nat), Eq.{succ u2} (List.{u2} γ) (List.take.{u2} γ n (List.zipWith.{u3, u1, u2} α β γ f l l')) (List.zipWith.{u3, u1, u2} α β γ f (List.take.{u3} α n l) (List.take.{u1} β n l'))
Case conversion may be inaccurate. Consider using '#align list.zip_with_distrib_take List.zipWith_distrib_takeₓ'. -/
theorem zipWith_distrib_take : (zipWith f l l').take n = zipWith f (l.take n) (l'.take n) :=
  by
  induction' l with hd tl hl generalizing l' n
  · simp
  · cases l'
    · simp
    · cases n
      · simp
      · simp [hl]
#align list.zip_with_distrib_take List.zipWith_distrib_take

/- warning: list.zip_with_distrib_drop -> List.zipWith_distrib_drop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l : List.{u1} α) (l' : List.{u2} β) (n : Nat), Eq.{succ u3} (List.{u3} γ) (List.drop.{u3} γ n (List.zipWith.{u1, u2, u3} α β γ f l l')) (List.zipWith.{u1, u2, u3} α β γ f (List.drop.{u1} α n l) (List.drop.{u2} β n l'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (f : α -> β -> γ) (l : List.{u3} α) (l' : List.{u1} β) (n : Nat), Eq.{succ u2} (List.{u2} γ) (List.drop.{u2} γ n (List.zipWith.{u3, u1, u2} α β γ f l l')) (List.zipWith.{u3, u1, u2} α β γ f (List.drop.{u3} α n l) (List.drop.{u1} β n l'))
Case conversion may be inaccurate. Consider using '#align list.zip_with_distrib_drop List.zipWith_distrib_dropₓ'. -/
theorem zipWith_distrib_drop : (zipWith f l l').drop n = zipWith f (l.drop n) (l'.drop n) :=
  by
  induction' l with hd tl hl generalizing l' n
  · simp
  · cases l'
    · simp
    · cases n
      · simp
      · simp [hl]
#align list.zip_with_distrib_drop List.zipWith_distrib_drop

/- warning: list.zip_with_distrib_tail -> List.zipWith_distrib_tail is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l : List.{u1} α) (l' : List.{u2} β), Eq.{succ u3} (List.{u3} γ) (List.tail.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l l')) (List.zipWith.{u1, u2, u3} α β γ f (List.tail.{u1} α l) (List.tail.{u2} β l'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (f : α -> β -> γ) (l : List.{u3} α) (l' : List.{u1} β), Eq.{succ u2} (List.{u2} γ) (List.tail.{u2} γ (List.zipWith.{u3, u1, u2} α β γ f l l')) (List.zipWith.{u3, u1, u2} α β γ f (List.tail.{u3} α l) (List.tail.{u1} β l'))
Case conversion may be inaccurate. Consider using '#align list.zip_with_distrib_tail List.zipWith_distrib_tailₓ'. -/
theorem zipWith_distrib_tail : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  simp_rw [← drop_one, zip_with_distrib_drop]
#align list.zip_with_distrib_tail List.zipWith_distrib_tail

/- warning: list.zip_with_append -> List.zipWith_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l : List.{u1} α) (la : List.{u1} α) (l' : List.{u2} β) (lb : List.{u2} β), (Eq.{1} Nat (List.length.{u1} α l) (List.length.{u2} β l')) -> (Eq.{succ u3} (List.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l la) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) l' lb)) (Append.append.{u3} (List.{u3} γ) (List.hasAppend.{u3} γ) (List.zipWith.{u1, u2, u3} α β γ f l l') (List.zipWith.{u1, u2, u3} α β γ f la lb)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (l : List.{u3} α) (la : List.{u3} α) (l' : List.{u2} β) (lb : List.{u2} β), (Eq.{1} Nat (List.length.{u3} α l) (List.length.{u2} β l')) -> (Eq.{succ u1} (List.{u1} γ) (List.zipWith.{u3, u2, u1} α β γ f (HAppend.hAppend.{u3, u3, u3} (List.{u3} α) (List.{u3} α) (List.{u3} α) (instHAppend.{u3} (List.{u3} α) (List.instAppendList.{u3} α)) l la) (HAppend.hAppend.{u2, u2, u2} (List.{u2} β) (List.{u2} β) (List.{u2} β) (instHAppend.{u2} (List.{u2} β) (List.instAppendList.{u2} β)) l' lb)) (HAppend.hAppend.{u1, u1, u1} (List.{u1} γ) (List.{u1} γ) (List.{u1} γ) (instHAppend.{u1} (List.{u1} γ) (List.instAppendList.{u1} γ)) (List.zipWith.{u3, u2, u1} α β γ f l l') (List.zipWith.{u3, u2, u1} α β γ f la lb)))
Case conversion may be inaccurate. Consider using '#align list.zip_with_append List.zipWith_appendₓ'. -/
theorem zipWith_append (f : α → β → γ) (l la : List α) (l' lb : List β) (h : l.length = l'.length) :
    zipWith f (l ++ la) (l' ++ lb) = zipWith f l l' ++ zipWith f la lb :=
  by
  induction' l with hd tl hl generalizing l'
  · have : l' = [] := eq_nil_of_length_eq_zero (by simpa using h.symm)
    simp [this]
  · cases l'
    · simpa using h
    · simp only [add_left_inj, length] at h
      simp [hl _ h]
#align list.zip_with_append List.zipWith_append

/- warning: list.zip_with_distrib_reverse -> List.zipWith_distrib_reverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β -> γ) (l : List.{u1} α) (l' : List.{u2} β), (Eq.{1} Nat (List.length.{u1} α l) (List.length.{u2} β l')) -> (Eq.{succ u3} (List.{u3} γ) (List.reverse.{u3} γ (List.zipWith.{u1, u2, u3} α β γ f l l')) (List.zipWith.{u1, u2, u3} α β γ f (List.reverse.{u1} α l) (List.reverse.{u2} β l')))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : α -> β -> γ) (l : List.{u3} α) (l' : List.{u2} β), (Eq.{1} Nat (List.length.{u3} α l) (List.length.{u2} β l')) -> (Eq.{succ u1} (List.{u1} γ) (List.reverse.{u1} γ (List.zipWith.{u3, u2, u1} α β γ f l l')) (List.zipWith.{u3, u2, u1} α β γ f (List.reverse.{u3} α l) (List.reverse.{u2} β l')))
Case conversion may be inaccurate. Consider using '#align list.zip_with_distrib_reverse List.zipWith_distrib_reverseₓ'. -/
theorem zipWith_distrib_reverse (h : l.length = l'.length) :
    (zipWith f l l').reverse = zipWith f l.reverse l'.reverse :=
  by
  induction' l with hd tl hl generalizing l'
  · simp
  · cases' l' with hd' tl'
    · simp
    · simp only [add_left_inj, length] at h
      have : tl.reverse.length = tl'.reverse.length := by simp [h]
      simp [hl _ h, zip_with_append _ _ _ _ _ this]
#align list.zip_with_distrib_reverse List.zipWith_distrib_reverse

end Distrib

section CommMonoid

variable [CommMonoid α]

/- warning: list.prod_mul_prod_eq_prod_zip_with_mul_prod_drop -> List.prod_mul_prod_eq_prod_zipWith_mul_prod_drop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (L : List.{u1} α) (L' : List.{u1} α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) L) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) L')) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.zipWith.{u1, u1, u1} α α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) L L')) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.drop.{u1} α (List.length.{u1} α L') L))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.drop.{u1} α (List.length.{u1} α L) L')))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (L : List.{u1} α) (L' : List.{u1} α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) L) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) L')) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (List.zipWith.{u1, u1, u1} α α α (fun (x._@.Mathlib.Data.List.Zip._hyg.6649 : α) (x._@.Mathlib.Data.List.Zip._hyg.6651 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x._@.Mathlib.Data.List.Zip._hyg.6649 x._@.Mathlib.Data.List.Zip._hyg.6651) L L')) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (List.drop.{u1} α (List.length.{u1} α L') L))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (List.drop.{u1} α (List.length.{u1} α L) L')))
Case conversion may be inaccurate. Consider using '#align list.prod_mul_prod_eq_prod_zip_with_mul_prod_drop List.prod_mul_prod_eq_prod_zipWith_mul_prod_dropₓ'. -/
@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith_mul_prod_drop :
    ∀ L L' : List α,
      L.Prod * L'.Prod =
        (zipWith (· * ·) L L').Prod * (L.drop L'.length).Prod * (L'.drop L.length).Prod
  | [], ys => by simp [Nat.zero_le]
  | xs, [] => by simp [Nat.zero_le]
  | x :: xs, y :: ys =>
    by
    simp only [drop, length, zip_with_cons_cons, prod_cons]
    rw [mul_assoc x, mul_comm xs.prod, mul_assoc y, mul_comm ys.prod,
      prod_mul_prod_eq_prod_zip_with_mul_prod_drop xs ys, mul_assoc, mul_assoc, mul_assoc,
      mul_assoc]
#align list.prod_mul_prod_eq_prod_zip_with_mul_prod_drop List.prod_mul_prod_eq_prod_zipWith_mul_prod_drop
#align list.sum_add_sum_eq_sum_zip_with_add_sum_drop List.sum_add_sum_eq_sum_zipWith_add_sum_drop

/- warning: list.prod_mul_prod_eq_prod_zip_with_of_length_eq -> List.prod_mul_prod_eq_prod_zipWith_of_length_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (L : List.{u1} α) (L' : List.{u1} α), (Eq.{1} Nat (List.length.{u1} α L) (List.length.{u1} α L')) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) L) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) L')) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.zipWith.{u1, u1, u1} α α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) L L')))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (L : List.{u1} α) (L' : List.{u1} α), (Eq.{1} Nat (List.length.{u1} α L) (List.length.{u1} α L')) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) L) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) L')) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (List.zipWith.{u1, u1, u1} α α α (fun (x._@.Mathlib.Data.List.Zip._hyg.6848 : α) (x._@.Mathlib.Data.List.Zip._hyg.6850 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x._@.Mathlib.Data.List.Zip._hyg.6848 x._@.Mathlib.Data.List.Zip._hyg.6850) L L')))
Case conversion may be inaccurate. Consider using '#align list.prod_mul_prod_eq_prod_zip_with_of_length_eq List.prod_mul_prod_eq_prod_zipWith_of_length_eqₓ'. -/
@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith_of_length_eq (L L' : List α) (h : L.length = L'.length) :
    L.Prod * L'.Prod = (zipWith (· * ·) L L').Prod :=
  (prod_mul_prod_eq_prod_zipWith_mul_prod_drop L L').trans (by simp [h])
#align list.prod_mul_prod_eq_prod_zip_with_of_length_eq List.prod_mul_prod_eq_prod_zipWith_of_length_eq
#align list.sum_add_sum_eq_sum_zip_with_of_length_eq List.sum_add_sum_eq_sum_zipWith_of_length_eq

end CommMonoid

end List

