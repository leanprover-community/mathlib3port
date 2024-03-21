/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel
-/
import Data.Nat.Bitwise
import SetTheory.Game.Birthday
import SetTheory.Game.Impartial

#align_import set_theory.game.nim from "leanprover-community/mathlib"@"d0b1936853671209a866fa35b9e54949c81116e2"

/-!
# Nim and the Sprague-Grundy theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition for nim for any ordinal `o`. In the game of `nim o₁` both players
may move to `nim o₂` for any `o₂ < o₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (grundy_value G)`.
Finally, we compute the sum of finite Grundy numbers: if `G` and `H` have Grundy values `n` and `m`,
where `n` and `m` are natural numbers, then `G + H` has the Grundy value `n xor m`.

## Implementation details

The pen-and-paper definition of nim defines the possible moves of `nim o` to be `set.Iio o`.
However, this definition does not work for us because it would make the type of nim
`ordinal.{u} → pgame.{u + 1}`, which would make it impossible for us to state the Sprague-Grundy
theorem, since that requires the type of `nim` to be `ordinal.{u} → pgame.{u}`. For this reason, we
instead use `o.out.α` for the possible moves. You can use `to_left_moves_nim` and
`to_right_moves_nim` to convert an ordinal less than `o` into a left or right move of `nim o`, and
vice versa.
-/


noncomputable section

universe u

open scoped SetTheory.PGame

namespace SetTheory.PGame

#print SetTheory.PGame.nim /-
-- Uses `noncomputable!` to avoid `rec_fn_macro only allowed in meta definitions` VM error
/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
  take a positive number of stones from it on their turn. -/
noncomputable def SetTheory.PGame.nim : Ordinal.{u} → SetTheory.PGame.{u}
  | o₁ =>
    let f o₂ :=
      have : Ordinal.typein o₁.out.R o₂ < o₁ := Ordinal.typein_lt_self o₂
      nim (Ordinal.typein o₁.out.R o₂)
    ⟨o₁.out.α, o₁.out.α, f, f⟩
#align pgame.nim SetTheory.PGame.nim
-/

open Ordinal

#print SetTheory.PGame.nim_def /-
theorem SetTheory.PGame.nim_def (o : Ordinal) :
    SetTheory.PGame.nim o =
      SetTheory.PGame.mk o.out.α o.out.α (fun o₂ => SetTheory.PGame.nim (Ordinal.typein (· < ·) o₂))
        fun o₂ => SetTheory.PGame.nim (Ordinal.typein (· < ·) o₂) :=
  by rw [nim]; rfl
#align pgame.nim_def SetTheory.PGame.nim_def
-/

#print SetTheory.PGame.leftMoves_nim /-
theorem SetTheory.PGame.leftMoves_nim (o : Ordinal) : (SetTheory.PGame.nim o).LeftMoves = o.out.α :=
  by rw [nim_def]; rfl
#align pgame.left_moves_nim SetTheory.PGame.leftMoves_nim
-/

#print SetTheory.PGame.rightMoves_nim /-
theorem SetTheory.PGame.rightMoves_nim (o : Ordinal) :
    (SetTheory.PGame.nim o).RightMoves = o.out.α := by rw [nim_def]; rfl
#align pgame.right_moves_nim SetTheory.PGame.rightMoves_nim
-/

#print SetTheory.PGame.moveLeft_nim_hEq /-
theorem SetTheory.PGame.moveLeft_nim_hEq (o : Ordinal) :
    HEq (SetTheory.PGame.nim o).moveLeft fun i : o.out.α =>
      SetTheory.PGame.nim (typein (· < ·) i) :=
  by rw [nim_def]; rfl
#align pgame.move_left_nim_heq SetTheory.PGame.moveLeft_nim_hEq
-/

#print SetTheory.PGame.moveRight_nim_hEq /-
theorem SetTheory.PGame.moveRight_nim_hEq (o : Ordinal) :
    HEq (SetTheory.PGame.nim o).moveRight fun i : o.out.α =>
      SetTheory.PGame.nim (typein (· < ·) i) :=
  by rw [nim_def]; rfl
#align pgame.move_right_nim_heq SetTheory.PGame.moveRight_nim_hEq
-/

#print SetTheory.PGame.toLeftMovesNim /-
/-- Turns an ordinal less than `o` into a left move for `nim o` and viceversa. -/
noncomputable def SetTheory.PGame.toLeftMovesNim {o : Ordinal} :
    Set.Iio o ≃ (SetTheory.PGame.nim o).LeftMoves :=
  (enumIsoOut o).toEquiv.trans (Equiv.cast (SetTheory.PGame.leftMoves_nim o).symm)
#align pgame.to_left_moves_nim SetTheory.PGame.toLeftMovesNim
-/

#print SetTheory.PGame.toRightMovesNim /-
/-- Turns an ordinal less than `o` into a right move for `nim o` and viceversa. -/
noncomputable def SetTheory.PGame.toRightMovesNim {o : Ordinal} :
    Set.Iio o ≃ (SetTheory.PGame.nim o).RightMoves :=
  (enumIsoOut o).toEquiv.trans (Equiv.cast (SetTheory.PGame.rightMoves_nim o).symm)
#align pgame.to_right_moves_nim SetTheory.PGame.toRightMovesNim
-/

#print SetTheory.PGame.toLeftMovesNim_symm_lt /-
@[simp]
theorem SetTheory.PGame.toLeftMovesNim_symm_lt {o : Ordinal}
    (i : (SetTheory.PGame.nim o).LeftMoves) : ↑(SetTheory.PGame.toLeftMovesNim.symm i) < o :=
  (SetTheory.PGame.toLeftMovesNim.symm i).Prop
#align pgame.to_left_moves_nim_symm_lt SetTheory.PGame.toLeftMovesNim_symm_lt
-/

#print SetTheory.PGame.toRightMovesNim_symm_lt /-
@[simp]
theorem SetTheory.PGame.toRightMovesNim_symm_lt {o : Ordinal}
    (i : (SetTheory.PGame.nim o).RightMoves) : ↑(SetTheory.PGame.toRightMovesNim.symm i) < o :=
  (SetTheory.PGame.toRightMovesNim.symm i).Prop
#align pgame.to_right_moves_nim_symm_lt SetTheory.PGame.toRightMovesNim_symm_lt
-/

#print SetTheory.PGame.moveLeft_nim' /-
@[simp]
theorem SetTheory.PGame.moveLeft_nim' {o : Ordinal.{u}} (i) :
    (SetTheory.PGame.nim o).moveLeft i =
      SetTheory.PGame.nim (SetTheory.PGame.toLeftMovesNim.symm i).val :=
  (congr_heq (SetTheory.PGame.moveLeft_nim_hEq o).symm (cast_hEq _ i)).symm
#align pgame.move_left_nim' SetTheory.PGame.moveLeft_nim'
-/

#print SetTheory.PGame.moveLeft_nim /-
theorem SetTheory.PGame.moveLeft_nim {o : Ordinal} (i) :
    (SetTheory.PGame.nim o).moveLeft (SetTheory.PGame.toLeftMovesNim i) = SetTheory.PGame.nim i :=
  by simp
#align pgame.move_left_nim SetTheory.PGame.moveLeft_nim
-/

#print SetTheory.PGame.moveRight_nim' /-
@[simp]
theorem SetTheory.PGame.moveRight_nim' {o : Ordinal} (i) :
    (SetTheory.PGame.nim o).moveRight i =
      SetTheory.PGame.nim (SetTheory.PGame.toRightMovesNim.symm i).val :=
  (congr_heq (SetTheory.PGame.moveRight_nim_hEq o).symm (cast_hEq _ i)).symm
#align pgame.move_right_nim' SetTheory.PGame.moveRight_nim'
-/

#print SetTheory.PGame.moveRight_nim /-
theorem SetTheory.PGame.moveRight_nim {o : Ordinal} (i) :
    (SetTheory.PGame.nim o).moveRight (SetTheory.PGame.toRightMovesNim i) = SetTheory.PGame.nim i :=
  by simp
#align pgame.move_right_nim SetTheory.PGame.moveRight_nim
-/

#print SetTheory.PGame.leftMovesNimRecOn /-
/-- A recursion principle for left moves of a nim game. -/
@[elab_as_elim]
def SetTheory.PGame.leftMovesNimRecOn {o : Ordinal} {P : (SetTheory.PGame.nim o).LeftMoves → Sort _}
    (i : (SetTheory.PGame.nim o).LeftMoves)
    (H : ∀ a < o, P <| SetTheory.PGame.toLeftMovesNim ⟨a, H⟩) : P i := by
  rw [← to_left_moves_nim.apply_symm_apply i]; apply H
#align pgame.left_moves_nim_rec_on SetTheory.PGame.leftMovesNimRecOn
-/

#print SetTheory.PGame.rightMovesNimRecOn /-
/-- A recursion principle for right moves of a nim game. -/
@[elab_as_elim]
def SetTheory.PGame.rightMovesNimRecOn {o : Ordinal}
    {P : (SetTheory.PGame.nim o).RightMoves → Sort _} (i : (SetTheory.PGame.nim o).RightMoves)
    (H : ∀ a < o, P <| SetTheory.PGame.toRightMovesNim ⟨a, H⟩) : P i := by
  rw [← to_right_moves_nim.apply_symm_apply i]; apply H
#align pgame.right_moves_nim_rec_on SetTheory.PGame.rightMovesNimRecOn
-/

#print SetTheory.PGame.isEmpty_nim_zero_leftMoves /-
instance SetTheory.PGame.isEmpty_nim_zero_leftMoves : IsEmpty (SetTheory.PGame.nim 0).LeftMoves :=
  by rw [nim_def]; exact Ordinal.isEmpty_out_zero
#align pgame.is_empty_nim_zero_left_moves SetTheory.PGame.isEmpty_nim_zero_leftMoves
-/

#print SetTheory.PGame.isEmpty_nim_zero_rightMoves /-
instance SetTheory.PGame.isEmpty_nim_zero_rightMoves : IsEmpty (SetTheory.PGame.nim 0).RightMoves :=
  by rw [nim_def]; exact Ordinal.isEmpty_out_zero
#align pgame.is_empty_nim_zero_right_moves SetTheory.PGame.isEmpty_nim_zero_rightMoves
-/

#print SetTheory.PGame.nimZeroRelabelling /-
/-- `nim 0` has exactly the same moves as `0`. -/
def SetTheory.PGame.nimZeroRelabelling : SetTheory.PGame.nim 0 ≡r 0 :=
  SetTheory.PGame.Relabelling.isEmpty _
#align pgame.nim_zero_relabelling SetTheory.PGame.nimZeroRelabelling
-/

#print SetTheory.PGame.nim_zero_equiv /-
theorem SetTheory.PGame.nim_zero_equiv : SetTheory.PGame.nim 0 ≈ 0 :=
  SetTheory.PGame.Equiv.isEmpty _
#align pgame.nim_zero_equiv SetTheory.PGame.nim_zero_equiv
-/

#print SetTheory.PGame.uniqueNimOneLeftMoves /-
noncomputable instance SetTheory.PGame.uniqueNimOneLeftMoves :
    Unique (SetTheory.PGame.nim 1).LeftMoves :=
  (Equiv.cast <| SetTheory.PGame.leftMoves_nim 1).unique
#align pgame.unique_nim_one_left_moves SetTheory.PGame.uniqueNimOneLeftMoves
-/

#print SetTheory.PGame.uniqueNimOneRightMoves /-
noncomputable instance SetTheory.PGame.uniqueNimOneRightMoves :
    Unique (SetTheory.PGame.nim 1).RightMoves :=
  (Equiv.cast <| SetTheory.PGame.rightMoves_nim 1).unique
#align pgame.unique_nim_one_right_moves SetTheory.PGame.uniqueNimOneRightMoves
-/

#print SetTheory.PGame.default_nim_one_leftMoves_eq /-
@[simp]
theorem SetTheory.PGame.default_nim_one_leftMoves_eq :
    (default : (SetTheory.PGame.nim 1).LeftMoves) =
      @SetTheory.PGame.toLeftMovesNim 1 ⟨0, zero_lt_one⟩ :=
  rfl
#align pgame.default_nim_one_left_moves_eq SetTheory.PGame.default_nim_one_leftMoves_eq
-/

#print SetTheory.PGame.default_nim_one_rightMoves_eq /-
@[simp]
theorem SetTheory.PGame.default_nim_one_rightMoves_eq :
    (default : (SetTheory.PGame.nim 1).RightMoves) =
      @SetTheory.PGame.toRightMovesNim 1 ⟨0, zero_lt_one⟩ :=
  rfl
#align pgame.default_nim_one_right_moves_eq SetTheory.PGame.default_nim_one_rightMoves_eq
-/

#print SetTheory.PGame.toLeftMovesNim_one_symm /-
@[simp]
theorem SetTheory.PGame.toLeftMovesNim_one_symm (i) :
    (@SetTheory.PGame.toLeftMovesNim 1).symm i = ⟨0, zero_lt_one⟩ := by simp
#align pgame.to_left_moves_nim_one_symm SetTheory.PGame.toLeftMovesNim_one_symm
-/

#print SetTheory.PGame.toRightMovesNim_one_symm /-
@[simp]
theorem SetTheory.PGame.toRightMovesNim_one_symm (i) :
    (@SetTheory.PGame.toRightMovesNim 1).symm i = ⟨0, zero_lt_one⟩ := by simp
#align pgame.to_right_moves_nim_one_symm SetTheory.PGame.toRightMovesNim_one_symm
-/

#print SetTheory.PGame.nim_one_moveLeft /-
theorem SetTheory.PGame.nim_one_moveLeft (x) :
    (SetTheory.PGame.nim 1).moveLeft x = SetTheory.PGame.nim 0 := by simp
#align pgame.nim_one_move_left SetTheory.PGame.nim_one_moveLeft
-/

#print SetTheory.PGame.nim_one_moveRight /-
theorem SetTheory.PGame.nim_one_moveRight (x) :
    (SetTheory.PGame.nim 1).moveRight x = SetTheory.PGame.nim 0 := by simp
#align pgame.nim_one_move_right SetTheory.PGame.nim_one_moveRight
-/

#print SetTheory.PGame.nimOneRelabelling /-
/-- `nim 1` has exactly the same moves as `star`. -/
def SetTheory.PGame.nimOneRelabelling : SetTheory.PGame.nim 1 ≡r SetTheory.PGame.star :=
  by
  rw [nim_def]
  refine' ⟨_, _, fun i => _, fun j => _⟩
  any_goals dsimp; apply Equiv.equivOfUnique
  all_goals simp; exact nim_zero_relabelling
#align pgame.nim_one_relabelling SetTheory.PGame.nimOneRelabelling
-/

#print SetTheory.PGame.nim_one_equiv /-
theorem SetTheory.PGame.nim_one_equiv : SetTheory.PGame.nim 1 ≈ SetTheory.PGame.star :=
  SetTheory.PGame.nimOneRelabelling.Equiv
#align pgame.nim_one_equiv SetTheory.PGame.nim_one_equiv
-/

#print SetTheory.PGame.nim_birthday /-
@[simp]
theorem SetTheory.PGame.nim_birthday (o : Ordinal) : (SetTheory.PGame.nim o).birthday = o :=
  by
  induction' o using Ordinal.induction with o IH
  rw [nim_def, birthday_def]
  dsimp
  rw [max_eq_right le_rfl]
  convert lsub_typein o
  exact funext fun i => IH _ (typein_lt_self i)
#align pgame.nim_birthday SetTheory.PGame.nim_birthday
-/

#print SetTheory.PGame.neg_nim /-
@[simp]
theorem SetTheory.PGame.neg_nim (o : Ordinal) : -SetTheory.PGame.nim o = SetTheory.PGame.nim o :=
  by
  induction' o using Ordinal.induction with o IH
  rw [nim_def]; dsimp <;> congr <;> funext i <;> exact IH _ (Ordinal.typein_lt_self i)
#align pgame.neg_nim SetTheory.PGame.neg_nim
-/

#print SetTheory.PGame.nim_impartial /-
instance SetTheory.PGame.nim_impartial (o : Ordinal) :
    SetTheory.PGame.Impartial (SetTheory.PGame.nim o) :=
  by
  induction' o using Ordinal.induction with o IH
  rw [impartial_def, neg_nim]
  refine' ⟨equiv_rfl, fun i => _, fun i => _⟩ <;> simpa using IH _ (typein_lt_self _)
#align pgame.nim_impartial SetTheory.PGame.nim_impartial
-/

#print SetTheory.PGame.nim_fuzzy_zero_of_ne_zero /-
theorem SetTheory.PGame.nim_fuzzy_zero_of_ne_zero {o : Ordinal} (ho : o ≠ 0) :
    SetTheory.PGame.nim o ‖ 0 :=
  by
  rw [impartial.fuzzy_zero_iff_lf, nim_def, lf_zero_le]
  rw [← Ordinal.pos_iff_ne_zero] at ho
  exact ⟨(Ordinal.principalSegOut ho).top, by simp⟩
#align pgame.nim_fuzzy_zero_of_ne_zero SetTheory.PGame.nim_fuzzy_zero_of_ne_zero
-/

#print SetTheory.PGame.nim_add_equiv_zero_iff /-
@[simp]
theorem SetTheory.PGame.nim_add_equiv_zero_iff (o₁ o₂ : Ordinal) :
    (SetTheory.PGame.nim o₁ + SetTheory.PGame.nim o₂ ≈ 0) ↔ o₁ = o₂ :=
  by
  constructor
  · refine' not_imp_not.1 fun hne : _ ≠ _ => (impartial.not_equiv_zero_iff _).2 _
    wlog h : o₁ < o₂
    · exact (fuzzy_congr_left add_comm_equiv).1 (this _ _ hne.symm (hne.lt_or_lt.resolve_left h))
    rw [impartial.fuzzy_zero_iff_gf, zero_lf_le, nim_def o₂]
    refine' ⟨to_left_moves_add (Sum.inr _), _⟩
    · exact (Ordinal.principalSegOut h).top
    · simpa using (impartial.add_self (nim o₁)).2
  · rintro rfl
    exact impartial.add_self (nim o₁)
#align pgame.nim_add_equiv_zero_iff SetTheory.PGame.nim_add_equiv_zero_iff
-/

#print SetTheory.PGame.nim_add_fuzzy_zero_iff /-
@[simp]
theorem SetTheory.PGame.nim_add_fuzzy_zero_iff {o₁ o₂ : Ordinal} :
    SetTheory.PGame.nim o₁ + SetTheory.PGame.nim o₂ ‖ 0 ↔ o₁ ≠ o₂ := by
  rw [iff_not_comm, impartial.not_fuzzy_zero_iff, nim_add_equiv_zero_iff]
#align pgame.nim_add_fuzzy_zero_iff SetTheory.PGame.nim_add_fuzzy_zero_iff
-/

#print SetTheory.PGame.nim_equiv_iff_eq /-
@[simp]
theorem SetTheory.PGame.nim_equiv_iff_eq {o₁ o₂ : Ordinal} :
    (SetTheory.PGame.nim o₁ ≈ SetTheory.PGame.nim o₂) ↔ o₁ = o₂ := by
  rw [impartial.equiv_iff_add_equiv_zero, nim_add_equiv_zero_iff]
#align pgame.nim_equiv_iff_eq SetTheory.PGame.nim_equiv_iff_eq
-/

#print SetTheory.PGame.grundyValue /-
/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def SetTheory.PGame.grundyValue : ∀ G : SetTheory.PGame.{u}, Ordinal.{u}
  | G => Ordinal.mex.{u, u} fun i => grundy_value (G.moveLeft i)
decreasing_by pgame_wf_tac
#align pgame.grundy_value SetTheory.PGame.grundyValue
-/

#print SetTheory.PGame.grundyValue_eq_mex_left /-
theorem SetTheory.PGame.grundyValue_eq_mex_left (G : SetTheory.PGame) :
    SetTheory.PGame.grundyValue G =
      Ordinal.mex.{u, u} fun i => SetTheory.PGame.grundyValue (G.moveLeft i) :=
  by rw [grundy_value]
#align pgame.grundy_value_eq_mex_left SetTheory.PGame.grundyValue_eq_mex_left
-/

#print SetTheory.PGame.equiv_nim_grundyValue /-
/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem SetTheory.PGame.equiv_nim_grundyValue :
    ∀ (G : SetTheory.PGame.{u}) [G.Impartial],
      G ≈ SetTheory.PGame.nim (SetTheory.PGame.grundyValue G)
  | G => by
    intro hG
    rw [impartial.equiv_iff_add_equiv_zero, ← impartial.forall_left_moves_fuzzy_iff_equiv_zero]
    intro i
    apply left_moves_add_cases i
    · intro i₁
      rw [add_move_left_inl]
      apply (fuzzy_congr_left (add_congr_left (equiv_nim_grundy_value (G.move_left i₁)).symm)).1
      rw [nim_add_fuzzy_zero_iff]
      intro heq
      rw [eq_comm, grundy_value_eq_mex_left G] at heq
      have h := Ordinal.ne_mex _
      rw [HEq] at h
      exact (h i₁).irrefl
    · intro i₂
      rw [add_move_left_inr, ← impartial.exists_left_move_equiv_iff_fuzzy_zero]
      revert i₂
      rw [nim_def]
      intro i₂
      have h' :
        ∃ i : G.left_moves,
          grundy_value (G.move_left i) = Ordinal.typein (Quotient.out (grundy_value G)).R i₂ :=
        by
        revert i₂
        rw [grundy_value_eq_mex_left]
        intro i₂
        have hnotin : _ ∉ _ := fun hin =>
          (le_not_le_of_lt (Ordinal.typein_lt_self i₂)).2 (csInf_le' hin)
        simpa using hnotin
      cases' h' with i hi
      use to_left_moves_add (Sum.inl i)
      rw [add_move_left_inl, move_left_mk]
      apply (add_congr_left (equiv_nim_grundy_value (G.move_left i))).trans
      simpa only [hi] using impartial.add_self (nim (grundy_value (G.move_left i)))
decreasing_by pgame_wf_tac
#align pgame.equiv_nim_grundy_value SetTheory.PGame.equiv_nim_grundyValue
-/

#print SetTheory.PGame.grundyValue_eq_iff_equiv_nim /-
theorem SetTheory.PGame.grundyValue_eq_iff_equiv_nim {G : SetTheory.PGame} [G.Impartial]
    {o : Ordinal} : SetTheory.PGame.grundyValue G = o ↔ (G ≈ SetTheory.PGame.nim o) :=
  ⟨by rintro rfl; exact equiv_nim_grundy_value G, by intro h; rw [← nim_equiv_iff_eq];
    exact (equiv_nim_grundy_value G).symm.trans h⟩
#align pgame.grundy_value_eq_iff_equiv_nim SetTheory.PGame.grundyValue_eq_iff_equiv_nim
-/

#print SetTheory.PGame.nim_grundyValue /-
@[simp]
theorem SetTheory.PGame.nim_grundyValue (o : Ordinal.{u}) :
    SetTheory.PGame.grundyValue (SetTheory.PGame.nim o) = o :=
  SetTheory.PGame.grundyValue_eq_iff_equiv_nim.2 SetTheory.PGame.equiv_rfl
#align pgame.nim_grundy_value SetTheory.PGame.nim_grundyValue
-/

#print SetTheory.PGame.grundyValue_eq_iff_equiv /-
theorem SetTheory.PGame.grundyValue_eq_iff_equiv (G H : SetTheory.PGame) [G.Impartial]
    [H.Impartial] : SetTheory.PGame.grundyValue G = SetTheory.PGame.grundyValue H ↔ (G ≈ H) :=
  SetTheory.PGame.grundyValue_eq_iff_equiv_nim.trans
    (SetTheory.PGame.equiv_congr_left.1 (SetTheory.PGame.equiv_nim_grundyValue H) _).symm
#align pgame.grundy_value_eq_iff_equiv SetTheory.PGame.grundyValue_eq_iff_equiv
-/

#print SetTheory.PGame.grundyValue_zero /-
@[simp]
theorem SetTheory.PGame.grundyValue_zero : SetTheory.PGame.grundyValue 0 = 0 :=
  SetTheory.PGame.grundyValue_eq_iff_equiv_nim.2 SetTheory.PGame.nim_zero_equiv.symm
#align pgame.grundy_value_zero SetTheory.PGame.grundyValue_zero
-/

#print SetTheory.PGame.grundyValue_iff_equiv_zero /-
theorem SetTheory.PGame.grundyValue_iff_equiv_zero (G : SetTheory.PGame) [G.Impartial] :
    SetTheory.PGame.grundyValue G = 0 ↔ (G ≈ 0) := by
  rw [← grundy_value_eq_iff_equiv, grundy_value_zero]
#align pgame.grundy_value_iff_equiv_zero SetTheory.PGame.grundyValue_iff_equiv_zero
-/

#print SetTheory.PGame.grundyValue_star /-
@[simp]
theorem SetTheory.PGame.grundyValue_star : SetTheory.PGame.grundyValue SetTheory.PGame.star = 1 :=
  SetTheory.PGame.grundyValue_eq_iff_equiv_nim.2 SetTheory.PGame.nim_one_equiv.symm
#align pgame.grundy_value_star SetTheory.PGame.grundyValue_star
-/

#print SetTheory.PGame.grundyValue_neg /-
@[simp]
theorem SetTheory.PGame.grundyValue_neg (G : SetTheory.PGame) [G.Impartial] :
    SetTheory.PGame.grundyValue (-G) = SetTheory.PGame.grundyValue G := by
  rw [grundy_value_eq_iff_equiv_nim, neg_equiv_iff, neg_nim, ← grundy_value_eq_iff_equiv_nim]
#align pgame.grundy_value_neg SetTheory.PGame.grundyValue_neg
-/

#print SetTheory.PGame.grundyValue_eq_mex_right /-
theorem SetTheory.PGame.grundyValue_eq_mex_right :
    ∀ (G : SetTheory.PGame) [G.Impartial],
      SetTheory.PGame.grundyValue G =
        Ordinal.mex.{u, u} fun i => SetTheory.PGame.grundyValue (G.moveRight i)
  | ⟨l, r, L, R⟩ => by
    intro H
    rw [← grundy_value_neg, grundy_value_eq_mex_left]
    congr
    ext i
    haveI : (R i).Impartial := @impartial.move_right_impartial ⟨l, r, L, R⟩ _ i
    apply grundy_value_neg
#align pgame.grundy_value_eq_mex_right SetTheory.PGame.grundyValue_eq_mex_right
-/

#print SetTheory.PGame.grundyValue_nim_add_nim /-
-- Todo: this actually generalizes to all ordinals, by defining `ordinal.lxor` as the pairwise
-- `nat.lxor` of base `ω` Cantor normal forms.
/-- The Grundy value of the sum of two nim games with natural numbers of piles equals their bitwise
xor. -/
@[simp]
theorem SetTheory.PGame.grundyValue_nim_add_nim (n m : ℕ) :
    SetTheory.PGame.grundyValue (SetTheory.PGame.nim.{u} n + SetTheory.PGame.nim.{u} m) =
      Nat.xor n m :=
  by
  -- We do strong induction on both variables.
  induction' n using Nat.strong_induction_on with n hn generalizing m
  induction' m using Nat.strong_induction_on with m hm
  rw [grundy_value_eq_mex_left]
  apply (Ordinal.mex_le_of_ne.{u, u} fun i => _).antisymm (Ordinal.le_mex_of_forall fun ou hu => _)
  -- The Grundy value `nat.lxor n m` can't be reached by left moves.
  ·
    apply left_moves_add_cases i <;>
      · -- A left move leaves us with a Grundy value of `nat.lxor k m` for `k < n`, or `nat.lxor n k`
        -- for `k < m`.
        refine' fun a => left_moves_nim_rec_on a fun ok hk => _
        obtain ⟨k, rfl⟩ := Ordinal.lt_omega.1 (hk.trans (Ordinal.nat_lt_omega _))
        simp only [add_move_left_inl, add_move_left_inr, move_left_nim', Equiv.symm_apply_apply]
        -- The inequality follows from injectivity.
        rw [nat_cast_lt] at hk
        first
        | rw [hn _ hk]
        | rw [hm _ hk]
        refine' fun h => hk.ne _
        rw [Ordinal.nat_cast_inj] at h
        first
        | rwa [Nat.xor_left_inj] at h
        | rwa [Nat.xor_right_inj] at h
  -- Every other smaller Grundy value can be reached by left moves.
  · -- If `u < nat.lxor m n`, then either `nat.lxor u n < m` or `nat.lxor u m < n`.
    obtain ⟨u, rfl⟩ := Ordinal.lt_omega.1 (hu.trans (Ordinal.nat_lt_omega _))
    replace hu := Ordinal.nat_cast_lt.1 hu
    cases' Nat.lt_xor_cases hu with h h
    -- In the first case, reducing the `m` pile to `nat.lxor u n` gives the desired Grundy value.
    · refine' ⟨to_left_moves_add (Sum.inl <| to_left_moves_nim ⟨_, Ordinal.nat_cast_lt.2 h⟩), _⟩
      simp [Nat.xor_cancel_right, hn _ h]
    -- In the second case, reducing the `n` pile to `nat.lxor u m` gives the desired Grundy value.
    · refine' ⟨to_left_moves_add (Sum.inr <| to_left_moves_nim ⟨_, Ordinal.nat_cast_lt.2 h⟩), _⟩
      have : n.lxor (u.lxor n) = u; rw [Nat.xor_comm u, Nat.xor_cancel_left]
      simpa [hm _ h] using this
#align pgame.grundy_value_nim_add_nim SetTheory.PGame.grundyValue_nim_add_nim
-/

#print SetTheory.PGame.nim_add_nim_equiv /-
theorem SetTheory.PGame.nim_add_nim_equiv {n m : ℕ} :
    SetTheory.PGame.nim n + SetTheory.PGame.nim m ≈ SetTheory.PGame.nim (Nat.xor n m) := by
  rw [← grundy_value_eq_iff_equiv_nim, grundy_value_nim_add_nim]
#align pgame.nim_add_nim_equiv SetTheory.PGame.nim_add_nim_equiv
-/

#print SetTheory.PGame.grundyValue_add /-
theorem SetTheory.PGame.grundyValue_add (G H : SetTheory.PGame) [G.Impartial] [H.Impartial]
    {n m : ℕ} (hG : SetTheory.PGame.grundyValue G = n) (hH : SetTheory.PGame.grundyValue H = m) :
    SetTheory.PGame.grundyValue (G + H) = Nat.xor n m :=
  by
  rw [← nim_grundy_value (Nat.xor n m), grundy_value_eq_iff_equiv]
  refine' Equiv.trans _ nim_add_nim_equiv
  convert add_congr (equiv_nim_grundy_value G) (equiv_nim_grundy_value H) <;> simp only [hG, hH]
#align pgame.grundy_value_add SetTheory.PGame.grundyValue_add
-/

end SetTheory.PGame

