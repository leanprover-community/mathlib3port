/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import SetTheory.Game.State

#align_import set_theory.game.domineering from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# Domineering as a combinatorial game.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the game of Domineering, played on a chessboard of arbitrary shape
(possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development;
in order to successfully analyse positions we would need some more theorems.
Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact that
disjoint parts of the chessboard give sums of games.
-/


namespace SetTheory.PGame

namespace Domineering

open Function

#print SetTheory.PGame.Domineering.shiftUp /-
/-- The equivalence `(x, y) ↦ (x, y+1)`. -/
@[simps]
def SetTheory.PGame.Domineering.shiftUp : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.refl ℤ).prodCongr (Equiv.addRight (1 : ℤ))
#align pgame.domineering.shift_up SetTheory.PGame.Domineering.shiftUp
-/

#print SetTheory.PGame.Domineering.shiftRight /-
/-- The equivalence `(x, y) ↦ (x+1, y)`. -/
@[simps]
def SetTheory.PGame.Domineering.shiftRight : ℤ × ℤ ≃ ℤ × ℤ :=
  (Equiv.addRight (1 : ℤ)).prodCongr (Equiv.refl ℤ)
#align pgame.domineering.shift_right SetTheory.PGame.Domineering.shiftRight
-/

#print SetTheory.PGame.Domineering.Board /-
/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
def SetTheory.PGame.Domineering.Board :=
  Finset (ℤ × ℤ)
deriving Inhabited
#align pgame.domineering.board SetTheory.PGame.Domineering.Board
-/

attribute [local reducible] board

#print SetTheory.PGame.Domineering.left /-
/-- Left can play anywhere that a square and the square below it are open. -/
def SetTheory.PGame.Domineering.left (b : SetTheory.PGame.Domineering.Board) : Finset (ℤ × ℤ) :=
  b ∩ b.map SetTheory.PGame.Domineering.shiftUp
#align pgame.domineering.left SetTheory.PGame.Domineering.left
-/

#print SetTheory.PGame.Domineering.right /-
/-- Right can play anywhere that a square and the square to the left are open. -/
def SetTheory.PGame.Domineering.right (b : SetTheory.PGame.Domineering.Board) : Finset (ℤ × ℤ) :=
  b ∩ b.map SetTheory.PGame.Domineering.shiftRight
#align pgame.domineering.right SetTheory.PGame.Domineering.right
-/

#print SetTheory.PGame.Domineering.mem_left /-
theorem SetTheory.PGame.Domineering.mem_left {b : SetTheory.PGame.Domineering.Board} (x : ℤ × ℤ) :
    x ∈ SetTheory.PGame.Domineering.left b ↔ x ∈ b ∧ (x.1, x.2 - 1) ∈ b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)
#align pgame.domineering.mem_left SetTheory.PGame.Domineering.mem_left
-/

#print SetTheory.PGame.Domineering.mem_right /-
theorem SetTheory.PGame.Domineering.mem_right {b : SetTheory.PGame.Domineering.Board} (x : ℤ × ℤ) :
    x ∈ SetTheory.PGame.Domineering.right b ↔ x ∈ b ∧ (x.1 - 1, x.2) ∈ b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)
#align pgame.domineering.mem_right SetTheory.PGame.Domineering.mem_right
-/

#print SetTheory.PGame.Domineering.moveLeft /-
/-- After Left moves, two vertically adjacent squares are removed from the board. -/
def SetTheory.PGame.Domineering.moveLeft (b : SetTheory.PGame.Domineering.Board) (m : ℤ × ℤ) :
    SetTheory.PGame.Domineering.Board :=
  (b.eraseₓ m).eraseₓ (m.1, m.2 - 1)
#align pgame.domineering.move_left SetTheory.PGame.Domineering.moveLeft
-/

#print SetTheory.PGame.Domineering.moveRight /-
/-- After Left moves, two horizontally adjacent squares are removed from the board. -/
def SetTheory.PGame.Domineering.moveRight (b : SetTheory.PGame.Domineering.Board) (m : ℤ × ℤ) :
    SetTheory.PGame.Domineering.Board :=
  (b.eraseₓ m).eraseₓ (m.1 - 1, m.2)
#align pgame.domineering.move_right SetTheory.PGame.Domineering.moveRight
-/

#print SetTheory.PGame.Domineering.fst_pred_mem_erase_of_mem_right /-
theorem SetTheory.PGame.Domineering.fst_pred_mem_erase_of_mem_right
    {b : SetTheory.PGame.Domineering.Board} {m : ℤ × ℤ}
    (h : m ∈ SetTheory.PGame.Domineering.right b) : (m.1 - 1, m.2) ∈ b.eraseₓ m :=
  by
  rw [mem_right] at h
  apply Finset.mem_erase_of_ne_of_mem _ h.2
  exact ne_of_apply_ne Prod.fst (pred_ne_self m.1)
#align pgame.domineering.fst_pred_mem_erase_of_mem_right SetTheory.PGame.Domineering.fst_pred_mem_erase_of_mem_right
-/

#print SetTheory.PGame.Domineering.snd_pred_mem_erase_of_mem_left /-
theorem SetTheory.PGame.Domineering.snd_pred_mem_erase_of_mem_left
    {b : SetTheory.PGame.Domineering.Board} {m : ℤ × ℤ}
    (h : m ∈ SetTheory.PGame.Domineering.left b) : (m.1, m.2 - 1) ∈ b.eraseₓ m :=
  by
  rw [mem_left] at h
  apply Finset.mem_erase_of_ne_of_mem _ h.2
  exact ne_of_apply_ne Prod.snd (pred_ne_self m.2)
#align pgame.domineering.snd_pred_mem_erase_of_mem_left SetTheory.PGame.Domineering.snd_pred_mem_erase_of_mem_left
-/

#print SetTheory.PGame.Domineering.card_of_mem_left /-
theorem SetTheory.PGame.Domineering.card_of_mem_left {b : SetTheory.PGame.Domineering.Board}
    {m : ℤ × ℤ} (h : m ∈ SetTheory.PGame.Domineering.left b) : 2 ≤ Finset.card b :=
  by
  have w₁ : m ∈ b := (Finset.mem_inter.1 h).1
  have w₂ : (m.1, m.2 - 1) ∈ b.erase m := snd_pred_mem_erase_of_mem_left h
  have i₁ := Finset.card_erase_lt_of_mem w₁
  have i₂ := Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.card_erase_lt_of_mem w₂)
  exact Nat.lt_of_le_of_lt i₂ i₁
#align pgame.domineering.card_of_mem_left SetTheory.PGame.Domineering.card_of_mem_left
-/

#print SetTheory.PGame.Domineering.card_of_mem_right /-
theorem SetTheory.PGame.Domineering.card_of_mem_right {b : SetTheory.PGame.Domineering.Board}
    {m : ℤ × ℤ} (h : m ∈ SetTheory.PGame.Domineering.right b) : 2 ≤ Finset.card b :=
  by
  have w₁ : m ∈ b := (Finset.mem_inter.1 h).1
  have w₂ := fst_pred_mem_erase_of_mem_right h
  have i₁ := Finset.card_erase_lt_of_mem w₁
  have i₂ := Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.card_erase_lt_of_mem w₂)
  exact Nat.lt_of_le_of_lt i₂ i₁
#align pgame.domineering.card_of_mem_right SetTheory.PGame.Domineering.card_of_mem_right
-/

#print SetTheory.PGame.Domineering.moveLeft_card /-
theorem SetTheory.PGame.Domineering.moveLeft_card {b : SetTheory.PGame.Domineering.Board}
    {m : ℤ × ℤ} (h : m ∈ SetTheory.PGame.Domineering.left b) :
    Finset.card (SetTheory.PGame.Domineering.moveLeft b m) + 2 = Finset.card b :=
  by
  dsimp [move_left]
  rw [Finset.card_erase_of_mem (snd_pred_mem_erase_of_mem_left h)]
  rw [Finset.card_erase_of_mem (Finset.mem_of_mem_inter_left h)]
  exact tsub_add_cancel_of_le (card_of_mem_left h)
#align pgame.domineering.move_left_card SetTheory.PGame.Domineering.moveLeft_card
-/

#print SetTheory.PGame.Domineering.moveRight_card /-
theorem SetTheory.PGame.Domineering.moveRight_card {b : SetTheory.PGame.Domineering.Board}
    {m : ℤ × ℤ} (h : m ∈ SetTheory.PGame.Domineering.right b) :
    Finset.card (SetTheory.PGame.Domineering.moveRight b m) + 2 = Finset.card b :=
  by
  dsimp [move_right]
  rw [Finset.card_erase_of_mem (fst_pred_mem_erase_of_mem_right h)]
  rw [Finset.card_erase_of_mem (Finset.mem_of_mem_inter_left h)]
  exact tsub_add_cancel_of_le (card_of_mem_right h)
#align pgame.domineering.move_right_card SetTheory.PGame.Domineering.moveRight_card
-/

#print SetTheory.PGame.Domineering.moveLeft_smaller /-
theorem SetTheory.PGame.Domineering.moveLeft_smaller {b : SetTheory.PGame.Domineering.Board}
    {m : ℤ × ℤ} (h : m ∈ SetTheory.PGame.Domineering.left b) :
    Finset.card (SetTheory.PGame.Domineering.moveLeft b m) / 2 < Finset.card b / 2 := by
  simp [← move_left_card h, lt_add_one]
#align pgame.domineering.move_left_smaller SetTheory.PGame.Domineering.moveLeft_smaller
-/

#print SetTheory.PGame.Domineering.moveRight_smaller /-
theorem SetTheory.PGame.Domineering.moveRight_smaller {b : SetTheory.PGame.Domineering.Board}
    {m : ℤ × ℤ} (h : m ∈ SetTheory.PGame.Domineering.right b) :
    Finset.card (SetTheory.PGame.Domineering.moveRight b m) / 2 < Finset.card b / 2 := by
  simp [← move_right_card h, lt_add_one]
#align pgame.domineering.move_right_smaller SetTheory.PGame.Domineering.moveRight_smaller
-/

#print SetTheory.PGame.Domineering.state /-
/-- The instance describing allowed moves on a Domineering board. -/
instance SetTheory.PGame.Domineering.state : SetTheory.PGame.State SetTheory.PGame.Domineering.Board
    where
  turnBound s := s.card / 2
  l s := (SetTheory.PGame.Domineering.left s).image (SetTheory.PGame.Domineering.moveLeft s)
  r s := (SetTheory.PGame.Domineering.right s).image (SetTheory.PGame.Domineering.moveRight s)
  left_bound s t m := by
    simp only [Finset.mem_image, Prod.exists] at m
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩
    exact move_left_smaller h
  right_bound s t m := by
    simp only [Finset.mem_image, Prod.exists] at m
    rcases m with ⟨_, _, ⟨h, rfl⟩⟩
    exact move_right_smaller h
#align pgame.domineering.state SetTheory.PGame.Domineering.state
-/

end Domineering

#print SetTheory.PGame.domineering /-
/-- Construct a pre-game from a Domineering board. -/
def SetTheory.PGame.domineering (b : SetTheory.PGame.Domineering.Board) : SetTheory.PGame :=
  SetTheory.PGame.ofState b
#align pgame.domineering SetTheory.PGame.domineering
-/

#print SetTheory.PGame.shortDomineering /-
/-- All games of Domineering are short, because each move removes two squares. -/
instance SetTheory.PGame.shortDomineering (b : SetTheory.PGame.Domineering.Board) :
    SetTheory.PGame.Short (SetTheory.PGame.domineering b) := by dsimp [domineering]; infer_instance
#align pgame.short_domineering SetTheory.PGame.shortDomineering
-/

#print SetTheory.PGame.domineering.one /-
/-- The Domineering board with two squares arranged vertically, in which Left has the only move. -/
def SetTheory.PGame.domineering.one :=
  SetTheory.PGame.domineering [(0, 0), (0, 1)].toFinset
#align pgame.domineering.one SetTheory.PGame.domineering.one
-/

#print SetTheory.PGame.domineering.L /-
/-- The `L` shaped Domineering board, in which Left is exactly half a move ahead. -/
def SetTheory.PGame.domineering.L :=
  SetTheory.PGame.domineering [(0, 2), (0, 1), (0, 0), (1, 0)].toFinset
#align pgame.domineering.L SetTheory.PGame.domineering.L
-/

#print SetTheory.PGame.shortOne /-
instance SetTheory.PGame.shortOne : SetTheory.PGame.Short SetTheory.PGame.domineering.one := by
  dsimp [domineering.one]; infer_instance
#align pgame.short_one SetTheory.PGame.shortOne
-/

#print SetTheory.PGame.shortL /-
instance SetTheory.PGame.shortL : SetTheory.PGame.Short SetTheory.PGame.domineering.L := by
  dsimp [domineering.L]; infer_instance
#align pgame.short_L SetTheory.PGame.shortL
-/

-- The VM can play small games successfully:
-- #eval to_bool (domineering.one ≈ 1)
-- #eval to_bool (domineering.L + domineering.L ≈ 1)
-- The following no longer works since Lean 3.29, since definitions by well-founded
-- recursion no longer reduce definitionally.
-- We can check that `decidable` instances reduce as expected,
-- and so our implementation of domineering is computable.
-- run_cmd tactic.whnf `(by apply_instance : decidable (domineering.one ≤ 1)) >>= tactic.trace
-- dec_trivial can handle most of the dictionary of small games described in [conway2001]
-- example : domineering.one ≈ 1 := dec_trivial
-- example : domineering.L + domineering.L ≈ 1 := dec_trivial
-- example : domineering.L ≈ pgame.of_lists [0] [1] := dec_trivial
-- example : (domineering ([(0,0), (0,1), (0,2), (0,3)].to_finset) ≈ 2) := dec_trivial
-- example : (domineering ([(0,0), (0,1), (1,0), (1,1)].to_finset) ≈ pgame.of_lists [1] [-1]) :=
--   dec_trivial.
-- The 3x3 grid is doable, but takes a minute...
-- example :
--   (domineering ([(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)].to_finset) ≈
--     pgame.of_lists [1] [-1]) := dec_trivial
-- The 5x5 grid is actually 0, but brute-forcing this is too challenging even for the VM.
-- #eval to_bool (domineering ([
--   (0,0), (0,1), (0,2), (0,3), (0,4),
--   (1,0), (1,1), (1,2), (1,3), (1,4),
--   (2,0), (2,1), (2,2), (2,3), (2,4),
--   (3,0), (3,1), (3,2), (3,3), (3,4),
--   (4,0), (4,1), (4,2), (4,3), (4,4)
--   ].to_finset) ≈ 0)
end SetTheory.PGame

