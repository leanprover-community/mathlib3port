/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module logic.lemmas
! leanprover-community/mathlib commit dcf2250875895376a142faeeac5eabff32c48655
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Congr
import Mathbin.Tactic.Protected
import Mathbin.Tactic.Rcases
import Mathbin.Tactic.SplitIfs
import Mathbin.Logic.Basic

/-!
# More basic logic properties

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/537
> Any changes to this file require a corresponding PR to mathlib4.

A few more logic lemmas. These are in their own file, rather than `logic.basic`, because it is
convenient to be able to use the `split_ifs` tactic.

## Implementation notes

We spell those lemmas out with `dite` and `ite` rather than the `if then else` notation because this
would result in less delta-reduced statements.
-/


alias heq_iff_eq ↔ HEq.eq Eq.heq

attribute [protected] HEq.eq Eq.heq

alias ne_of_eq_of_ne ← Eq.trans_ne

alias ne_of_ne_of_eq ← Ne.trans_eq

variable {α : Sort _} {p q r : Prop} [Decidable p] [Decidable q] {a b c : α}

#print dite_dite_distrib_left /-
theorem dite_dite_distrib_left {a : p → α} {b : ¬p → q → α} {c : ¬p → ¬q → α} :
    (dite p a fun hp => dite q (b hp) (c hp)) =
      dite q (fun hq => (dite p a) fun hp => b hp hq) fun hq => (dite p a) fun hp => c hp hq :=
  by split_ifs <;> rfl
#align dite_dite_distrib_left dite_dite_distrib_left
-/

#print dite_dite_distrib_right /-
theorem dite_dite_distrib_right {a : p → q → α} {b : p → ¬q → α} {c : ¬p → α} :
    dite p (fun hp => dite q (a hp) (b hp)) c =
      dite q (fun hq => dite p (fun hp => a hp hq) c) fun hq => dite p (fun hp => b hp hq) c :=
  by split_ifs <;> rfl
#align dite_dite_distrib_right dite_dite_distrib_right
-/

#print ite_dite_distrib_left /-
theorem ite_dite_distrib_left {a : α} {b : q → α} {c : ¬q → α} :
    ite p a (dite q b c) = dite q (fun hq => ite p a <| b hq) fun hq => ite p a <| c hq :=
  dite_dite_distrib_left
#align ite_dite_distrib_left ite_dite_distrib_left
-/

#print ite_dite_distrib_right /-
theorem ite_dite_distrib_right {a : q → α} {b : ¬q → α} {c : α} :
    ite p (dite q a b) c = dite q (fun hq => ite p (a hq) c) fun hq => ite p (b hq) c :=
  dite_dite_distrib_right
#align ite_dite_distrib_right ite_dite_distrib_right
-/

#print dite_ite_distrib_left /-
theorem dite_ite_distrib_left {a : p → α} {b : ¬p → α} {c : ¬p → α} :
    (dite p a fun hp => ite q (b hp) (c hp)) = ite q (dite p a b) (dite p a c) :=
  dite_dite_distrib_left
#align dite_ite_distrib_left dite_ite_distrib_left
-/

#print dite_ite_distrib_right /-
theorem dite_ite_distrib_right {a : p → α} {b : p → α} {c : ¬p → α} :
    dite p (fun hp => ite q (a hp) (b hp)) c = ite q (dite p a c) (dite p b c) :=
  dite_dite_distrib_right
#align dite_ite_distrib_right dite_ite_distrib_right
-/

#print ite_ite_distrib_left /-
theorem ite_ite_distrib_left : ite p a (ite q b c) = ite q (ite p a b) (ite p a c) :=
  dite_dite_distrib_left
#align ite_ite_distrib_left ite_ite_distrib_left
-/

#print ite_ite_distrib_right /-
theorem ite_ite_distrib_right : ite p (ite q a b) c = ite q (ite p a c) (ite p b c) :=
  dite_dite_distrib_right
#align ite_ite_distrib_right ite_ite_distrib_right
-/

theorem PropCat.forall {f : Prop → Prop} : (∀ p, f p) ↔ f True ∧ f False :=
  ⟨fun h => ⟨h _, h _⟩, by 
    rintro ⟨h₁, h₀⟩ p
    by_cases hp : p <;> simp only [hp] <;> assumption⟩
#align Prop.forall PropCat.forall

theorem PropCat.exists {f : Prop → Prop} : (∃ p, f p) ↔ f True ∨ f False :=
  ⟨fun ⟨p, h⟩ => by refine' (em p).imp _ _ <;> intro H <;> convert h <;> simp [H], by
    rintro (h | h) <;> exact ⟨_, h⟩⟩
#align Prop.exists PropCat.exists

