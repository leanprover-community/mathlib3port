/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import SetTheory.Game.Short

#align_import set_theory.game.state from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# Games described via "the state of the board".

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide a simple mechanism for constructing combinatorial (pre-)games, by describing
"the state of the board", and providing an upper bound on the number of turns remaining.


## Implementation notes

We're very careful to produce a computable definition, so small games can be evaluated
using `dec_trivial`. To achieve this, I've had to rely solely on induction on natural numbers:
relying on general well-foundedness seems to be poisonous to computation?

See `set_theory/game/domineering` for an example using this construction.
-/


universe u

namespace SetTheory.PGame

#print SetTheory.PGame.State /-
/-- `pgame_state S` describes how to interpret `s : S` as a state of a combinatorial game.
Use `pgame.of_state s` or `game.of_state s` to construct the game.

`pgame_state.L : S → finset S` and `pgame_state.R : S → finset S` describe the states reachable
by a move by Left or Right. `pgame_state.turn_bound : S → ℕ` gives an upper bound on the number of
possible turns remaining from this state.
-/
class SetTheory.PGame.State (S : Type u) where
  turnBound : S → ℕ
  l : S → Finset S
  r : S → Finset S
  left_bound : ∀ {s t : S} (m : t ∈ L s), turn_bound t < turn_bound s
  right_bound : ∀ {s t : S} (m : t ∈ R s), turn_bound t < turn_bound s
#align pgame.state SetTheory.PGame.State
-/

open StateM

variable {S : Type u} [SetTheory.PGame.State S]

#print SetTheory.PGame.turnBound_ne_zero_of_left_move /-
theorem SetTheory.PGame.turnBound_ne_zero_of_left_move {s t : S}
    (m : t ∈ SetTheory.PGame.State.l s) : SetTheory.PGame.State.turnBound s ≠ 0 :=
  by
  intro h
  have t := state.left_bound m
  rw [h] at t 
  exact Nat.not_succ_le_zero _ t
#align pgame.turn_bound_ne_zero_of_left_move SetTheory.PGame.turnBound_ne_zero_of_left_move
-/

#print SetTheory.PGame.turnBound_ne_zero_of_right_move /-
theorem SetTheory.PGame.turnBound_ne_zero_of_right_move {s t : S}
    (m : t ∈ SetTheory.PGame.State.r s) : SetTheory.PGame.State.turnBound s ≠ 0 :=
  by
  intro h
  have t := state.right_bound m
  rw [h] at t 
  exact Nat.not_succ_le_zero _ t
#align pgame.turn_bound_ne_zero_of_right_move SetTheory.PGame.turnBound_ne_zero_of_right_move
-/

#print SetTheory.PGame.turnBound_of_left /-
theorem SetTheory.PGame.turnBound_of_left {s t : S} (m : t ∈ SetTheory.PGame.State.l s) (n : ℕ)
    (h : SetTheory.PGame.State.turnBound s ≤ n + 1) : SetTheory.PGame.State.turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (SetTheory.PGame.State.left_bound m) h)
#align pgame.turn_bound_of_left SetTheory.PGame.turnBound_of_left
-/

#print SetTheory.PGame.turnBound_of_right /-
theorem SetTheory.PGame.turnBound_of_right {s t : S} (m : t ∈ SetTheory.PGame.State.r s) (n : ℕ)
    (h : SetTheory.PGame.State.turnBound s ≤ n + 1) : SetTheory.PGame.State.turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (SetTheory.PGame.State.right_bound m) h)
#align pgame.turn_bound_of_right SetTheory.PGame.turnBound_of_right
-/

#print SetTheory.PGame.ofStateAux /-
/-- Construct a `pgame` from a state and a (not necessarily optimal) bound on the number of
turns remaining.
-/
def SetTheory.PGame.ofStateAux :
    ∀ (n : ℕ) (s : S) (h : SetTheory.PGame.State.turnBound s ≤ n), SetTheory.PGame
  | 0, s, h =>
    SetTheory.PGame.mk { t // t ∈ SetTheory.PGame.State.l s } { t // t ∈ SetTheory.PGame.State.r s }
      (fun t => by exfalso; exact turn_bound_ne_zero_of_left_move t.2 (nonpos_iff_eq_zero.mp h))
      fun t => by exfalso; exact turn_bound_ne_zero_of_right_move t.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, s, h =>
    SetTheory.PGame.mk { t // t ∈ SetTheory.PGame.State.l s } { t // t ∈ SetTheory.PGame.State.r s }
      (fun t => of_state_aux n t (SetTheory.PGame.turnBound_of_left t.2 n h)) fun t =>
      of_state_aux n t (SetTheory.PGame.turnBound_of_right t.2 n h)
#align pgame.of_state_aux SetTheory.PGame.ofStateAux
-/

#print SetTheory.PGame.ofStateAuxRelabelling /-
/-- Two different (valid) turn bounds give equivalent games. -/
def SetTheory.PGame.ofStateAuxRelabelling :
    ∀ (s : S) (n m : ℕ) (hn : SetTheory.PGame.State.turnBound s ≤ n)
      (hm : SetTheory.PGame.State.turnBound s ≤ m),
      SetTheory.PGame.Relabelling (SetTheory.PGame.ofStateAux n s hn)
        (SetTheory.PGame.ofStateAux m s hm)
  | s, 0, 0, hn, hm => by
    dsimp [SetTheory.PGame.ofStateAux]
    fconstructor; rfl; rfl
    · intro i; dsimp at i ; exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
    · intro j; dsimp at j ; exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
  | s, 0, m + 1, hn, hm => by
    dsimp [SetTheory.PGame.ofStateAux]
    fconstructor; rfl; rfl
    · intro i; dsimp at i ; exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hn)
    · intro j; dsimp at j ; exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hn)
  | s, n + 1, 0, hn, hm => by
    dsimp [SetTheory.PGame.ofStateAux]
    fconstructor; rfl; rfl
    · intro i; dsimp at i ; exfalso
      exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp hm)
    · intro j; dsimp at j ; exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp hm)
  | s, n + 1, m + 1, hn, hm => by
    dsimp [SetTheory.PGame.ofStateAux]
    fconstructor; rfl; rfl
    · intro i
      apply of_state_aux_relabelling
    · intro j
      apply of_state_aux_relabelling
#align pgame.of_state_aux_relabelling SetTheory.PGame.ofStateAuxRelabelling
-/

#print SetTheory.PGame.ofState /-
/-- Construct a combinatorial `pgame` from a state. -/
def SetTheory.PGame.ofState (s : S) : SetTheory.PGame :=
  SetTheory.PGame.ofStateAux (SetTheory.PGame.State.turnBound s) s (refl _)
#align pgame.of_state SetTheory.PGame.ofState
-/

#print SetTheory.PGame.leftMovesOfStateAux /-
/-- The equivalence between `left_moves` for a `pgame` constructed using `of_state_aux _ s _`, and
`L s`. -/
def SetTheory.PGame.leftMovesOfStateAux (n : ℕ) {s : S}
    (h : SetTheory.PGame.State.turnBound s ≤ n) :
    SetTheory.PGame.LeftMoves (SetTheory.PGame.ofStateAux n s h) ≃
      { t // t ∈ SetTheory.PGame.State.l s } :=
  by induction n <;> rfl
#align pgame.left_moves_of_state_aux SetTheory.PGame.leftMovesOfStateAux
-/

#print SetTheory.PGame.leftMovesOfState /-
/-- The equivalence between `left_moves` for a `pgame` constructed using `of_state s`, and `L s`. -/
def SetTheory.PGame.leftMovesOfState (s : S) :
    SetTheory.PGame.LeftMoves (SetTheory.PGame.ofState s) ≃
      { t // t ∈ SetTheory.PGame.State.l s } :=
  SetTheory.PGame.leftMovesOfStateAux _ _
#align pgame.left_moves_of_state SetTheory.PGame.leftMovesOfState
-/

#print SetTheory.PGame.rightMovesOfStateAux /-
/-- The equivalence between `right_moves` for a `pgame` constructed using `of_state_aux _ s _`, and
`R s`. -/
def SetTheory.PGame.rightMovesOfStateAux (n : ℕ) {s : S}
    (h : SetTheory.PGame.State.turnBound s ≤ n) :
    SetTheory.PGame.RightMoves (SetTheory.PGame.ofStateAux n s h) ≃
      { t // t ∈ SetTheory.PGame.State.r s } :=
  by induction n <;> rfl
#align pgame.right_moves_of_state_aux SetTheory.PGame.rightMovesOfStateAux
-/

#print SetTheory.PGame.rightMovesOfState /-
/-- The equivalence between `right_moves` for a `pgame` constructed using `of_state s`, and
`R s`. -/
def SetTheory.PGame.rightMovesOfState (s : S) :
    SetTheory.PGame.RightMoves (SetTheory.PGame.ofState s) ≃
      { t // t ∈ SetTheory.PGame.State.r s } :=
  SetTheory.PGame.rightMovesOfStateAux _ _
#align pgame.right_moves_of_state SetTheory.PGame.rightMovesOfState
-/

#print SetTheory.PGame.relabellingMoveLeftAux /-
/-- The relabelling showing `move_left` applied to a game constructed using `of_state_aux`
has itself been constructed using `of_state_aux`.
-/
def SetTheory.PGame.relabellingMoveLeftAux (n : ℕ) {s : S}
    (h : SetTheory.PGame.State.turnBound s ≤ n)
    (t : SetTheory.PGame.LeftMoves (SetTheory.PGame.ofStateAux n s h)) :
    SetTheory.PGame.Relabelling (SetTheory.PGame.moveLeft (SetTheory.PGame.ofStateAux n s h) t)
      (SetTheory.PGame.ofStateAux (n - 1) ((SetTheory.PGame.leftMovesOfStateAux n h) t : S)
        (SetTheory.PGame.turnBound_of_left ((SetTheory.PGame.leftMovesOfStateAux n h) t).2 (n - 1)
          (Nat.le_trans h le_tsub_add))) :=
  by
  induction n
  · have t' := (left_moves_of_state_aux 0 h) t
    exfalso; exact turn_bound_ne_zero_of_left_move t'.2 (nonpos_iff_eq_zero.mp h)
  · rfl
#align pgame.relabelling_move_left_aux SetTheory.PGame.relabellingMoveLeftAux
-/

#print SetTheory.PGame.relabellingMoveLeft /-
/-- The relabelling showing `move_left` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def SetTheory.PGame.relabellingMoveLeft (s : S)
    (t : SetTheory.PGame.LeftMoves (SetTheory.PGame.ofState s)) :
    SetTheory.PGame.Relabelling (SetTheory.PGame.moveLeft (SetTheory.PGame.ofState s) t)
      (SetTheory.PGame.ofState ((SetTheory.PGame.leftMovesOfState s).toFun t : S)) :=
  by
  trans
  apply relabelling_move_left_aux
  apply of_state_aux_relabelling
#align pgame.relabelling_move_left SetTheory.PGame.relabellingMoveLeft
-/

#print SetTheory.PGame.relabellingMoveRightAux /-
/-- The relabelling showing `move_right` applied to a game constructed using `of_state_aux`
has itself been constructed using `of_state_aux`.
-/
def SetTheory.PGame.relabellingMoveRightAux (n : ℕ) {s : S}
    (h : SetTheory.PGame.State.turnBound s ≤ n)
    (t : SetTheory.PGame.RightMoves (SetTheory.PGame.ofStateAux n s h)) :
    SetTheory.PGame.Relabelling (SetTheory.PGame.moveRight (SetTheory.PGame.ofStateAux n s h) t)
      (SetTheory.PGame.ofStateAux (n - 1) ((SetTheory.PGame.rightMovesOfStateAux n h) t : S)
        (SetTheory.PGame.turnBound_of_right ((SetTheory.PGame.rightMovesOfStateAux n h) t).2 (n - 1)
          (Nat.le_trans h le_tsub_add))) :=
  by
  induction n
  · have t' := (right_moves_of_state_aux 0 h) t
    exfalso; exact turn_bound_ne_zero_of_right_move t'.2 (nonpos_iff_eq_zero.mp h)
  · rfl
#align pgame.relabelling_move_right_aux SetTheory.PGame.relabellingMoveRightAux
-/

#print SetTheory.PGame.relabellingMoveRight /-
/-- The relabelling showing `move_right` applied to a game constructed using `of`
has itself been constructed using `of`.
-/
def SetTheory.PGame.relabellingMoveRight (s : S)
    (t : SetTheory.PGame.RightMoves (SetTheory.PGame.ofState s)) :
    SetTheory.PGame.Relabelling (SetTheory.PGame.moveRight (SetTheory.PGame.ofState s) t)
      (SetTheory.PGame.ofState ((SetTheory.PGame.rightMovesOfState s).toFun t : S)) :=
  by
  trans
  apply relabelling_move_right_aux
  apply of_state_aux_relabelling
#align pgame.relabelling_move_right SetTheory.PGame.relabellingMoveRight
-/

#print SetTheory.PGame.fintypeLeftMovesOfStateAux /-
instance SetTheory.PGame.fintypeLeftMovesOfStateAux (n : ℕ) (s : S)
    (h : SetTheory.PGame.State.turnBound s ≤ n) :
    Fintype (SetTheory.PGame.LeftMoves (SetTheory.PGame.ofStateAux n s h)) :=
  by
  apply Fintype.ofEquiv _ (left_moves_of_state_aux _ _).symm
  infer_instance
#align pgame.fintype_left_moves_of_state_aux SetTheory.PGame.fintypeLeftMovesOfStateAux
-/

#print SetTheory.PGame.fintypeRightMovesOfStateAux /-
instance SetTheory.PGame.fintypeRightMovesOfStateAux (n : ℕ) (s : S)
    (h : SetTheory.PGame.State.turnBound s ≤ n) :
    Fintype (SetTheory.PGame.RightMoves (SetTheory.PGame.ofStateAux n s h)) :=
  by
  apply Fintype.ofEquiv _ (right_moves_of_state_aux _ _).symm
  infer_instance
#align pgame.fintype_right_moves_of_state_aux SetTheory.PGame.fintypeRightMovesOfStateAux
-/

#print SetTheory.PGame.shortOfStateAux /-
instance SetTheory.PGame.shortOfStateAux :
    ∀ (n : ℕ) {s : S} (h : SetTheory.PGame.State.turnBound s ≤ n),
      SetTheory.PGame.Short (SetTheory.PGame.ofStateAux n s h)
  | 0, s, h =>
    SetTheory.PGame.Short.mk'
      (fun i => by
        have i := (left_moves_of_state_aux _ _).toFun i
        exfalso
        exact turn_bound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp h))
      fun j => by
      have j := (right_moves_of_state_aux _ _).toFun j
      exfalso
      exact turn_bound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, s, h =>
    SetTheory.PGame.Short.mk'
      (fun i =>
        SetTheory.PGame.shortOfRelabelling (SetTheory.PGame.relabellingMoveLeftAux (n + 1) h i).symm
          (short_of_state_aux n _))
      fun j =>
      SetTheory.PGame.shortOfRelabelling (SetTheory.PGame.relabellingMoveRightAux (n + 1) h j).symm
        (short_of_state_aux n _)
#align pgame.short_of_state_aux SetTheory.PGame.shortOfStateAux
-/

#print SetTheory.PGame.shortOfState /-
instance SetTheory.PGame.shortOfState (s : S) : SetTheory.PGame.Short (SetTheory.PGame.ofState s) :=
  by
  dsimp [SetTheory.PGame.ofState]
  infer_instance
#align pgame.short_of_state SetTheory.PGame.shortOfState
-/

end SetTheory.PGame

namespace SetTheory.Game

#print SetTheory.Game.ofState /-
/-- Construct a combinatorial `game` from a state. -/
def SetTheory.Game.ofState {S : Type u} [SetTheory.PGame.State S] (s : S) : SetTheory.Game :=
  ⟦SetTheory.PGame.ofState s⟧
#align game.of_state SetTheory.Game.ofState
-/

end SetTheory.Game

