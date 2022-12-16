/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module set_theory.game.birthday
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Game.Ordinal
import Mathbin.SetTheory.Ordinal.NaturalOps

/-!
# Birthdays of games

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

open NaturalOps Pgame

namespace Pgame

/-- The birthday of a pre-game is inductively defined as the least strict upper bound of the
birthdays of its left and right games. It may be thought as the "step" in which a certain game is
constructed. -/
noncomputable def birthday : Pgame.{u} → Ordinal.{u}
  | ⟨xl, xr, xL, xR⟩ =>
    max (lsub.{u, u} fun i => birthday (xL i)) (lsub.{u, u} fun i => birthday (xR i))
#align pgame.birthday Pgame.birthday

theorem birthday_def (x : Pgame) :
    birthday x =
      max (lsub.{u, u} fun i => birthday (x.moveLeft i))
        (lsub.{u, u} fun i => birthday (x.moveRight i)) :=
  by 
  cases x
  rw [birthday]
  rfl
#align pgame.birthday_def Pgame.birthday_def

theorem birthday_move_left_lt {x : Pgame} (i : x.LeftMoves) :
    (x.moveLeft i).birthday < x.birthday := by 
  cases x
  rw [birthday]
  exact lt_max_of_lt_left (lt_lsub _ i)
#align pgame.birthday_move_left_lt Pgame.birthday_move_left_lt

theorem birthday_move_right_lt {x : Pgame} (i : x.RightMoves) :
    (x.moveRight i).birthday < x.birthday := by 
  cases x
  rw [birthday]
  exact lt_max_of_lt_right (lt_lsub _ i)
#align pgame.birthday_move_right_lt Pgame.birthday_move_right_lt

theorem lt_birthday_iff {x : Pgame} {o : Ordinal} :
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
#align pgame.lt_birthday_iff Pgame.lt_birthday_iff

theorem Relabelling.birthday_congr : ∀ {x y : Pgame.{u}}, x ≡r y → birthday x = birthday y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, r => by
    unfold birthday
    congr 1
    all_goals 
      apply lsub_eq_of_range_eq.{u, u, u}
      ext i; constructor
    all_goals rintro ⟨j, rfl⟩
    · exact ⟨_, (r.move_left j).birthday_congr.symm⟩
    · exact ⟨_, (r.move_left_symm j).birthday_congr⟩
    · exact ⟨_, (r.move_right j).birthday_congr.symm⟩
    · exact ⟨_, (r.move_right_symm j).birthday_congr⟩decreasing_by pgame_wf_tac
#align pgame.relabelling.birthday_congr Pgame.Relabelling.birthday_congr

@[simp]
theorem birthday_eq_zero {x : Pgame} :
    birthday x = 0 ↔ IsEmpty x.LeftMoves ∧ IsEmpty x.RightMoves := by
  rw [birthday_def, max_eq_zero, lsub_eq_zero_iff, lsub_eq_zero_iff]
#align pgame.birthday_eq_zero Pgame.birthday_eq_zero

@[simp]
theorem birthday_zero : birthday 0 = 0 := by simp [PEmpty.is_empty]
#align pgame.birthday_zero Pgame.birthday_zero

@[simp]
theorem birthday_one : birthday 1 = 1 := by
  rw [birthday_def]
  simp
#align pgame.birthday_one Pgame.birthday_one

@[simp]
theorem birthday_star : birthday star = 1 := by
  rw [birthday_def]
  simp
#align pgame.birthday_star Pgame.birthday_star

@[simp]
theorem neg_birthday : ∀ x : Pgame, (-x).birthday = x.birthday
  | ⟨xl, xr, xL, xR⟩ => by 
    rw [birthday_def, birthday_def, max_comm]
    congr <;> funext <;> apply neg_birthday
#align pgame.neg_birthday Pgame.neg_birthday

@[simp]
theorem to_pgame_birthday (o : Ordinal) : o.toPgame.birthday = o := by
  induction' o using Ordinal.induction with o IH
  rw [to_pgame_def, Pgame.birthday]
  simp only [lsub_empty, max_zero_right]
  nth_rw 1 [← lsub_typein o]
  congr with x
  exact IH _ (typein_lt_self x)
#align pgame.to_pgame_birthday Pgame.to_pgame_birthday

theorem le_birthday : ∀ x : Pgame, x ≤ x.birthday.toPgame
  | ⟨xl, _, xL, _⟩ =>
    le_def.2
      ⟨fun i =>
        Or.inl ⟨toLeftMovesToPgame ⟨_, birthday_move_left_lt i⟩, by simp [le_birthday (xL i)]⟩,
        isEmptyElim⟩
#align pgame.le_birthday Pgame.le_birthday

variable (a b x : Pgame.{u})

theorem neg_birthday_le : -x.birthday.toPgame ≤ x := by
  simpa only [neg_birthday, ← neg_le_iff] using le_birthday (-x)
#align pgame.neg_birthday_le Pgame.neg_birthday_le

@[simp]
theorem birthday_add : ∀ x y : Pgame.{u}, (x + y).birthday = x.birthday ♯ y.birthday
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
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
    · exact lt_max_of_lt_right ((nadd_le_nadd_left hj _).trans_lt (lt_lsub _ _))decreasing_by
  pgame_wf_tac
#align pgame.birthday_add Pgame.birthday_add

theorem birthday_add_zero : (a + 0).birthday = a.birthday := by simp
#align pgame.birthday_add_zero Pgame.birthday_add_zero

theorem birthday_zero_add : (0 + a).birthday = a.birthday := by simp
#align pgame.birthday_zero_add Pgame.birthday_zero_add

theorem birthday_add_one : (a + 1).birthday = Order.succ a.birthday := by simp
#align pgame.birthday_add_one Pgame.birthday_add_one

theorem birthday_one_add : (1 + a).birthday = Order.succ a.birthday := by simp
#align pgame.birthday_one_add Pgame.birthday_one_add

@[simp]
theorem birthday_nat_cast : ∀ n : ℕ, birthday n = n
  | 0 => birthday_zero
  | n + 1 => by simp [birthday_nat_cast]
#align pgame.birthday_nat_cast Pgame.birthday_nat_cast

theorem birthday_add_nat (n : ℕ) : (a + n).birthday = a.birthday + n := by simp
#align pgame.birthday_add_nat Pgame.birthday_add_nat

theorem birthday_nat_add (n : ℕ) : (↑n + a).birthday = a.birthday + n := by simp
#align pgame.birthday_nat_add Pgame.birthday_nat_add

end Pgame

