/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import SetTheory.Game.Ordinal
import SetTheory.Ordinal.NaturalOps

#align_import set_theory.game.birthday from "leanprover-community/mathlib"@"9240e8be927a0955b9a82c6c85ef499ee3a626b8"

/-!
# Birthdays of games

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The birthday of a game is an ordinal that represents at which "step" the game was constructed. We
define it recursively as the least ordinal larger than the birthdays of its left and right games. We
prove the basic properties about these.

# Main declarations

- `pgame.birthday`: The birthday of a pre-game.

# Todo

- Define the birthdays of `game`s and `surreal`s.
- Characterize the birthdays of basic arithmetical operations.
-/


universe u

open Ordinal

open scoped NaturalOps SetTheory.PGame

namespace SetTheory.PGame

#print SetTheory.PGame.birthday /-
/-- The birthday of a pre-game is inductively defined as the least strict upper bound of the
birthdays of its left and right games. It may be thought as the "step" in which a certain game is
constructed. -/
noncomputable def SetTheory.PGame.birthday : SetTheory.PGame.{u} → Ordinal.{u}
  | ⟨xl, xr, xL, xR⟩ =>
    max (lsub.{u, u} fun i => birthday (xL i)) (lsub.{u, u} fun i => birthday (xR i))
#align pgame.birthday SetTheory.PGame.birthday
-/

#print SetTheory.PGame.birthday_def /-
theorem SetTheory.PGame.birthday_def (x : SetTheory.PGame) :
    SetTheory.PGame.birthday x =
      max (lsub.{u, u} fun i => SetTheory.PGame.birthday (x.moveLeft i))
        (lsub.{u, u} fun i => SetTheory.PGame.birthday (x.moveRight i)) :=
  by cases x; rw [birthday]; rfl
#align pgame.birthday_def SetTheory.PGame.birthday_def
-/

#print SetTheory.PGame.birthday_moveLeft_lt /-
theorem SetTheory.PGame.birthday_moveLeft_lt {x : SetTheory.PGame} (i : x.LeftMoves) :
    (x.moveLeft i).birthday < x.birthday := by cases x; rw [birthday];
  exact lt_max_of_lt_left (lt_lsub _ i)
#align pgame.birthday_move_left_lt SetTheory.PGame.birthday_moveLeft_lt
-/

#print SetTheory.PGame.birthday_moveRight_lt /-
theorem SetTheory.PGame.birthday_moveRight_lt {x : SetTheory.PGame} (i : x.RightMoves) :
    (x.moveRight i).birthday < x.birthday := by cases x; rw [birthday];
  exact lt_max_of_lt_right (lt_lsub _ i)
#align pgame.birthday_move_right_lt SetTheory.PGame.birthday_moveRight_lt
-/

#print SetTheory.PGame.lt_birthday_iff /-
theorem SetTheory.PGame.lt_birthday_iff {x : SetTheory.PGame} {o : Ordinal} :
    o < x.birthday ↔
      (∃ i : x.LeftMoves, o ≤ (x.moveLeft i).birthday) ∨
        ∃ i : x.RightMoves, o ≤ (x.moveRight i).birthday :=
  by
  constructor
  · rw [birthday_def]
    intro h
    cases' lt_max_iff.1 h with h' h'
    · left
      rwa [lt_lsub_iff] at h'
    · right
      rwa [lt_lsub_iff] at h'
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hi.trans_lt (birthday_move_left_lt i)
    · exact hi.trans_lt (birthday_move_right_lt i)
#align pgame.lt_birthday_iff SetTheory.PGame.lt_birthday_iff
-/

#print SetTheory.PGame.Relabelling.birthday_congr /-
theorem SetTheory.PGame.Relabelling.birthday_congr :
    ∀ {x y : SetTheory.PGame.{u}}, x ≡r y → SetTheory.PGame.birthday x = SetTheory.PGame.birthday y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, r =>
    by
    unfold birthday
    congr 1
    all_goals
      apply lsub_eq_of_range_eq.{u, u, u}
      ext i; constructor
    all_goals rintro ⟨j, rfl⟩
    · exact ⟨_, (r.move_left j).birthday_congr.symm⟩
    · exact ⟨_, (r.move_left_symm j).birthday_congr⟩
    · exact ⟨_, (r.move_right j).birthday_congr.symm⟩
    · exact ⟨_, (r.move_right_symm j).birthday_congr⟩
decreasing_by pgame_wf_tac
#align pgame.relabelling.birthday_congr SetTheory.PGame.Relabelling.birthday_congr
-/

#print SetTheory.PGame.birthday_eq_zero /-
@[simp]
theorem SetTheory.PGame.birthday_eq_zero {x : SetTheory.PGame} :
    SetTheory.PGame.birthday x = 0 ↔ IsEmpty x.LeftMoves ∧ IsEmpty x.RightMoves := by
  rw [birthday_def, max_eq_zero, lsub_eq_zero_iff, lsub_eq_zero_iff]
#align pgame.birthday_eq_zero SetTheory.PGame.birthday_eq_zero
-/

#print SetTheory.PGame.birthday_zero /-
@[simp]
theorem SetTheory.PGame.birthday_zero : SetTheory.PGame.birthday 0 = 0 := by simp [PEmpty.isEmpty]
#align pgame.birthday_zero SetTheory.PGame.birthday_zero
-/

#print SetTheory.PGame.birthday_one /-
@[simp]
theorem SetTheory.PGame.birthday_one : SetTheory.PGame.birthday 1 = 1 := by rw [birthday_def]; simp
#align pgame.birthday_one SetTheory.PGame.birthday_one
-/

#print SetTheory.PGame.birthday_star /-
@[simp]
theorem SetTheory.PGame.birthday_star : SetTheory.PGame.birthday SetTheory.PGame.star = 1 := by
  rw [birthday_def]; simp
#align pgame.birthday_star SetTheory.PGame.birthday_star
-/

#print SetTheory.PGame.neg_birthday /-
@[simp]
theorem SetTheory.PGame.neg_birthday : ∀ x : SetTheory.PGame, (-x).birthday = x.birthday
  | ⟨xl, xr, xL, xR⟩ => by
    rw [birthday_def, birthday_def, max_comm]
    congr <;> funext <;> apply neg_birthday
#align pgame.neg_birthday SetTheory.PGame.neg_birthday
-/

#print SetTheory.PGame.toPGame_birthday /-
@[simp]
theorem SetTheory.PGame.toPGame_birthday (o : Ordinal) : o.toPGame.birthday = o :=
  by
  induction' o using Ordinal.induction with o IH
  rw [to_pgame_def, SetTheory.PGame.birthday]
  simp only [lsub_empty, max_zero_right]
  nth_rw 1 [← lsub_typein o]
  congr with x
  exact IH _ (typein_lt_self x)
#align pgame.to_pgame_birthday SetTheory.PGame.toPGame_birthday
-/

#print SetTheory.PGame.le_birthday /-
theorem SetTheory.PGame.le_birthday : ∀ x : SetTheory.PGame, x ≤ x.birthday.toPGame
  | ⟨xl, _, xL, _⟩ =>
    SetTheory.PGame.le_def.2
      ⟨fun i =>
        Or.inl
          ⟨toLeftMovesToPGame ⟨_, SetTheory.PGame.birthday_moveLeft_lt i⟩, by
            simp [le_birthday (xL i)]⟩,
        isEmptyElim⟩
#align pgame.le_birthday SetTheory.PGame.le_birthday
-/

variable (a b x : SetTheory.PGame.{u})

#print SetTheory.PGame.neg_birthday_le /-
theorem SetTheory.PGame.neg_birthday_le : -x.birthday.toPGame ≤ x := by
  simpa only [neg_birthday, ← neg_le_iff] using le_birthday (-x)
#align pgame.neg_birthday_le SetTheory.PGame.neg_birthday_le
-/

#print SetTheory.PGame.birthday_add /-
@[simp]
theorem SetTheory.PGame.birthday_add :
    ∀ x y : SetTheory.PGame.{u}, (x + y).birthday = x.birthday ♯ y.birthday
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ =>
    by
    rw [birthday_def, nadd_def]
    simp only [birthday_add, lsub_sum, mk_add_move_left_inl, move_left_mk, mk_add_move_left_inr,
      mk_add_move_right_inl, move_right_mk, mk_add_move_right_inr]
    rw [max_max_max_comm]
    congr <;> apply le_antisymm
    any_goals
      exact
        max_le_iff.2
          ⟨lsub_le_iff.2 fun i => lt_blsub _ _ (birthday_move_left_lt i),
            lsub_le_iff.2 fun i => lt_blsub _ _ (birthday_move_right_lt i)⟩
    all_goals
      apply blsub_le_iff.2 fun i hi => _
      rcases lt_birthday_iff.1 hi with (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact lt_max_of_lt_left ((nadd_le_nadd_right hj _).trans_lt (lt_lsub _ _))
    · exact lt_max_of_lt_right ((nadd_le_nadd_right hj _).trans_lt (lt_lsub _ _))
    · exact lt_max_of_lt_left ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _))
    · exact lt_max_of_lt_right ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _))
decreasing_by pgame_wf_tac
#align pgame.birthday_add SetTheory.PGame.birthday_add
-/

#print SetTheory.PGame.birthday_add_zero /-
theorem SetTheory.PGame.birthday_add_zero : (a + 0).birthday = a.birthday := by simp
#align pgame.birthday_add_zero SetTheory.PGame.birthday_add_zero
-/

#print SetTheory.PGame.birthday_zero_add /-
theorem SetTheory.PGame.birthday_zero_add : (0 + a).birthday = a.birthday := by simp
#align pgame.birthday_zero_add SetTheory.PGame.birthday_zero_add
-/

#print SetTheory.PGame.birthday_add_one /-
theorem SetTheory.PGame.birthday_add_one : (a + 1).birthday = Order.succ a.birthday := by simp
#align pgame.birthday_add_one SetTheory.PGame.birthday_add_one
-/

#print SetTheory.PGame.birthday_one_add /-
theorem SetTheory.PGame.birthday_one_add : (1 + a).birthday = Order.succ a.birthday := by simp
#align pgame.birthday_one_add SetTheory.PGame.birthday_one_add
-/

#print SetTheory.PGame.birthday_nat_cast /-
@[simp]
theorem SetTheory.PGame.birthday_nat_cast : ∀ n : ℕ, SetTheory.PGame.birthday n = n
  | 0 => SetTheory.PGame.birthday_zero
  | n + 1 => by simp [birthday_nat_cast]
#align pgame.birthday_nat_cast SetTheory.PGame.birthday_nat_cast
-/

#print SetTheory.PGame.birthday_add_nat /-
theorem SetTheory.PGame.birthday_add_nat (n : ℕ) : (a + n).birthday = a.birthday + n := by simp
#align pgame.birthday_add_nat SetTheory.PGame.birthday_add_nat
-/

#print SetTheory.PGame.birthday_nat_add /-
theorem SetTheory.PGame.birthday_nat_add (n : ℕ) : (↑n + a).birthday = a.birthday + n := by simp
#align pgame.birthday_nat_add SetTheory.PGame.birthday_nat_add
-/

end SetTheory.PGame

