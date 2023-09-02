/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.SetTheory.Game.Basic
import Mathbin.Tactic.NthRewrite.Default

#align_import set_theory.game.impartial from "leanprover-community/mathlib"@"9240e8be927a0955b9a82c6c85ef499ee3a626b8"

/-!
# Basic definitions about impartial (pre-)games

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/


universe u

open scoped SetTheory.PGame

namespace SetTheory.PGame

#print SetTheory.PGame.ImpartialAux /-
/-- The definition for a impartial game, defined using Conway induction. -/
def SetTheory.PGame.ImpartialAux : SetTheory.PGame → Prop
  | G => (G ≈ -G) ∧ (∀ i, impartial_aux (G.moveLeft i)) ∧ ∀ j, impartial_aux (G.moveRight j)
decreasing_by pgame_wf_tac
#align pgame.impartial_aux SetTheory.PGame.ImpartialAux
-/

#print SetTheory.PGame.impartialAux_def /-
theorem SetTheory.PGame.impartialAux_def {G : SetTheory.PGame} :
    G.ImpartialAux ↔
      (G ≈ -G) ∧
        (∀ i, SetTheory.PGame.ImpartialAux (G.moveLeft i)) ∧
          ∀ j, SetTheory.PGame.ImpartialAux (G.moveRight j) :=
  by rw [impartial_aux]
#align pgame.impartial_aux_def SetTheory.PGame.impartialAux_def
-/

#print SetTheory.PGame.Impartial /-
/-- A typeclass on impartial games. -/
class SetTheory.PGame.Impartial (G : SetTheory.PGame) : Prop where
  out : SetTheory.PGame.ImpartialAux G
#align pgame.impartial SetTheory.PGame.Impartial
-/

#print SetTheory.PGame.impartial_iff_aux /-
theorem SetTheory.PGame.impartial_iff_aux {G : SetTheory.PGame} : G.Impartial ↔ G.ImpartialAux :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align pgame.impartial_iff_aux SetTheory.PGame.impartial_iff_aux
-/

#print SetTheory.PGame.impartial_def /-
theorem SetTheory.PGame.impartial_def {G : SetTheory.PGame} :
    G.Impartial ↔
      (G ≈ -G) ∧
        (∀ i, SetTheory.PGame.Impartial (G.moveLeft i)) ∧
          ∀ j, SetTheory.PGame.Impartial (G.moveRight j) :=
  by simpa only [impartial_iff_aux] using impartial_aux_def
#align pgame.impartial_def SetTheory.PGame.impartial_def
-/

namespace Impartial

#print SetTheory.PGame.Impartial.impartial_zero /-
instance SetTheory.PGame.Impartial.impartial_zero : SetTheory.PGame.Impartial 0 := by
  rw [impartial_def]; dsimp; simp
#align pgame.impartial.impartial_zero SetTheory.PGame.Impartial.impartial_zero
-/

#print SetTheory.PGame.Impartial.impartial_star /-
instance SetTheory.PGame.Impartial.impartial_star :
    SetTheory.PGame.Impartial SetTheory.PGame.star := by rw [impartial_def];
  simpa using impartial.impartial_zero
#align pgame.impartial.impartial_star SetTheory.PGame.Impartial.impartial_star
-/

#print SetTheory.PGame.Impartial.neg_equiv_self /-
theorem SetTheory.PGame.Impartial.neg_equiv_self (G : SetTheory.PGame) [h : G.Impartial] : G ≈ -G :=
  (SetTheory.PGame.impartial_def.1 h).1
#align pgame.impartial.neg_equiv_self SetTheory.PGame.Impartial.neg_equiv_self
-/

#print SetTheory.PGame.Impartial.mk'_neg_equiv_self /-
@[simp]
theorem SetTheory.PGame.Impartial.mk'_neg_equiv_self (G : SetTheory.PGame) [h : G.Impartial] :
    -⟦G⟧ = ⟦G⟧ :=
  Quot.sound (SetTheory.PGame.Impartial.neg_equiv_self G).symm
#align pgame.impartial.mk_neg_equiv_self SetTheory.PGame.Impartial.mk'_neg_equiv_self
-/

#print SetTheory.PGame.Impartial.moveLeft_impartial /-
instance SetTheory.PGame.Impartial.moveLeft_impartial {G : SetTheory.PGame} [h : G.Impartial]
    (i : G.LeftMoves) : (G.moveLeft i).Impartial :=
  (SetTheory.PGame.impartial_def.1 h).2.1 i
#align pgame.impartial.move_left_impartial SetTheory.PGame.Impartial.moveLeft_impartial
-/

#print SetTheory.PGame.Impartial.moveRight_impartial /-
instance SetTheory.PGame.Impartial.moveRight_impartial {G : SetTheory.PGame} [h : G.Impartial]
    (j : G.RightMoves) : (G.moveRight j).Impartial :=
  (SetTheory.PGame.impartial_def.1 h).2.2 j
#align pgame.impartial.move_right_impartial SetTheory.PGame.Impartial.moveRight_impartial
-/

#print SetTheory.PGame.Impartial.impartial_congr /-
theorem SetTheory.PGame.Impartial.impartial_congr :
    ∀ {G H : SetTheory.PGame} (e : G ≡r H) [G.Impartial], H.Impartial
  | G, H => fun e => by
    intro h
    exact
      impartial_def.2
        ⟨e.symm.equiv.trans ((neg_equiv_self G).trans (neg_equiv_neg_iff.2 e.equiv)), fun i =>
          impartial_congr (e.move_left_symm i), fun j => impartial_congr (e.move_right_symm j)⟩
decreasing_by pgame_wf_tac
#align pgame.impartial.impartial_congr SetTheory.PGame.Impartial.impartial_congr
-/

#print SetTheory.PGame.Impartial.impartial_add /-
instance SetTheory.PGame.Impartial.impartial_add :
    ∀ (G H : SetTheory.PGame) [G.Impartial] [H.Impartial], (G + H).Impartial
  | G, H => by
    intro hG hH
    rw [impartial_def]
    refine'
      ⟨(add_congr (neg_equiv_self _) (neg_equiv_self _)).trans (neg_add_relabelling _ _).Equiv.symm,
        fun k => _, fun k => _⟩
    · apply left_moves_add_cases k
      all_goals
        intro i; simp only [add_move_left_inl, add_move_left_inr]
        apply impartial_add
    · apply right_moves_add_cases k
      all_goals
        intro i; simp only [add_move_right_inl, add_move_right_inr]
        apply impartial_add
decreasing_by pgame_wf_tac
#align pgame.impartial.impartial_add SetTheory.PGame.Impartial.impartial_add
-/

#print SetTheory.PGame.Impartial.impartial_neg /-
instance SetTheory.PGame.Impartial.impartial_neg :
    ∀ (G : SetTheory.PGame) [G.Impartial], (-G).Impartial
  | G => by
    intro hG
    rw [impartial_def]
    refine' ⟨_, fun i => _, fun i => _⟩
    · rw [neg_neg]
      exact (neg_equiv_self G).symm
    · rw [move_left_neg']
      apply impartial_neg
    · rw [move_right_neg']
      apply impartial_neg
decreasing_by pgame_wf_tac
#align pgame.impartial.impartial_neg SetTheory.PGame.Impartial.impartial_neg
-/

variable (G : SetTheory.PGame) [SetTheory.PGame.Impartial G]

#print SetTheory.PGame.Impartial.nonpos /-
theorem SetTheory.PGame.Impartial.nonpos : ¬0 < G := fun h =>
  by
  have h' := neg_lt_neg_iff.2 h
  rw [neg_zero, lt_congr_left (neg_equiv_self G).symm] at h' 
  exact (h.trans h').False
#align pgame.impartial.nonpos SetTheory.PGame.Impartial.nonpos
-/

#print SetTheory.PGame.Impartial.nonneg /-
theorem SetTheory.PGame.Impartial.nonneg : ¬G < 0 := fun h =>
  by
  have h' := neg_lt_neg_iff.2 h
  rw [neg_zero, lt_congr_right (neg_equiv_self G).symm] at h' 
  exact (h.trans h').False
#align pgame.impartial.nonneg SetTheory.PGame.Impartial.nonneg
-/

#print SetTheory.PGame.Impartial.equiv_or_fuzzy_zero /-
/-- In an impartial game, either the first player always wins, or the second player always wins. -/
theorem SetTheory.PGame.Impartial.equiv_or_fuzzy_zero : (G ≈ 0) ∨ G ‖ 0 :=
  by
  rcases lt_or_equiv_or_gt_or_fuzzy G 0 with (h | h | h | h)
  · exact ((nonneg G) h).elim
  · exact Or.inl h
  · exact ((nonpos G) h).elim
  · exact Or.inr h
#align pgame.impartial.equiv_or_fuzzy_zero SetTheory.PGame.Impartial.equiv_or_fuzzy_zero
-/

#print SetTheory.PGame.Impartial.not_equiv_zero_iff /-
@[simp]
theorem SetTheory.PGame.Impartial.not_equiv_zero_iff : ¬(G ≈ 0) ↔ G ‖ 0 :=
  ⟨(SetTheory.PGame.Impartial.equiv_or_fuzzy_zero G).resolve_left, SetTheory.PGame.Fuzzy.not_equiv⟩
#align pgame.impartial.not_equiv_zero_iff SetTheory.PGame.Impartial.not_equiv_zero_iff
-/

#print SetTheory.PGame.Impartial.not_fuzzy_zero_iff /-
@[simp]
theorem SetTheory.PGame.Impartial.not_fuzzy_zero_iff : ¬G ‖ 0 ↔ (G ≈ 0) :=
  ⟨(SetTheory.PGame.Impartial.equiv_or_fuzzy_zero G).resolve_right, SetTheory.PGame.Equiv.not_fuzzy⟩
#align pgame.impartial.not_fuzzy_zero_iff SetTheory.PGame.Impartial.not_fuzzy_zero_iff
-/

#print SetTheory.PGame.Impartial.add_self /-
theorem SetTheory.PGame.Impartial.add_self : G + G ≈ 0 :=
  (SetTheory.PGame.add_congr_left (SetTheory.PGame.Impartial.neg_equiv_self G)).trans
    (SetTheory.PGame.add_left_neg_equiv G)
#align pgame.impartial.add_self SetTheory.PGame.Impartial.add_self
-/

#print SetTheory.PGame.Impartial.mk'_add_self /-
@[simp]
theorem SetTheory.PGame.Impartial.mk'_add_self : ⟦G⟧ + ⟦G⟧ = 0 :=
  Quot.sound (SetTheory.PGame.Impartial.add_self G)
#align pgame.impartial.mk_add_self SetTheory.PGame.Impartial.mk'_add_self
-/

#print SetTheory.PGame.Impartial.equiv_iff_add_equiv_zero /-
/-- This lemma doesn't require `H` to be impartial. -/
theorem SetTheory.PGame.Impartial.equiv_iff_add_equiv_zero (H : SetTheory.PGame) :
    (H ≈ G) ↔ (H + G ≈ 0) := by
  rw [equiv_iff_game_eq, equiv_iff_game_eq, ← @add_right_cancel_iff _ _ _ (-⟦G⟧)]; simpa
#align pgame.impartial.equiv_iff_add_equiv_zero SetTheory.PGame.Impartial.equiv_iff_add_equiv_zero
-/

#print SetTheory.PGame.Impartial.equiv_iff_add_equiv_zero' /-
/-- This lemma doesn't require `H` to be impartial. -/
theorem SetTheory.PGame.Impartial.equiv_iff_add_equiv_zero' (H : SetTheory.PGame) :
    (G ≈ H) ↔ (G + H ≈ 0) := by
  rw [equiv_iff_game_eq, equiv_iff_game_eq, ← @add_left_cancel_iff _ _ _ (-⟦G⟧), eq_comm]; simpa
#align pgame.impartial.equiv_iff_add_equiv_zero' SetTheory.PGame.Impartial.equiv_iff_add_equiv_zero'
-/

#print SetTheory.PGame.Impartial.le_zero_iff /-
theorem SetTheory.PGame.Impartial.le_zero_iff {G : SetTheory.PGame} [G.Impartial] : G ≤ 0 ↔ 0 ≤ G :=
  by rw [← zero_le_neg_iff, le_congr_right (neg_equiv_self G)]
#align pgame.impartial.le_zero_iff SetTheory.PGame.Impartial.le_zero_iff
-/

#print SetTheory.PGame.Impartial.lf_zero_iff /-
theorem SetTheory.PGame.Impartial.lf_zero_iff {G : SetTheory.PGame} [G.Impartial] : G ⧏ 0 ↔ 0 ⧏ G :=
  by rw [← zero_lf_neg_iff, lf_congr_right (neg_equiv_self G)]
#align pgame.impartial.lf_zero_iff SetTheory.PGame.Impartial.lf_zero_iff
-/

#print SetTheory.PGame.Impartial.equiv_zero_iff_le /-
theorem SetTheory.PGame.Impartial.equiv_zero_iff_le : (G ≈ 0) ↔ G ≤ 0 :=
  ⟨And.left, fun h => ⟨h, SetTheory.PGame.Impartial.le_zero_iff.1 h⟩⟩
#align pgame.impartial.equiv_zero_iff_le SetTheory.PGame.Impartial.equiv_zero_iff_le
-/

#print SetTheory.PGame.Impartial.fuzzy_zero_iff_lf /-
theorem SetTheory.PGame.Impartial.fuzzy_zero_iff_lf : G ‖ 0 ↔ G ⧏ 0 :=
  ⟨And.left, fun h => ⟨h, SetTheory.PGame.Impartial.lf_zero_iff.1 h⟩⟩
#align pgame.impartial.fuzzy_zero_iff_lf SetTheory.PGame.Impartial.fuzzy_zero_iff_lf
-/

#print SetTheory.PGame.Impartial.equiv_zero_iff_ge /-
theorem SetTheory.PGame.Impartial.equiv_zero_iff_ge : (G ≈ 0) ↔ 0 ≤ G :=
  ⟨And.right, fun h => ⟨SetTheory.PGame.Impartial.le_zero_iff.2 h, h⟩⟩
#align pgame.impartial.equiv_zero_iff_ge SetTheory.PGame.Impartial.equiv_zero_iff_ge
-/

#print SetTheory.PGame.Impartial.fuzzy_zero_iff_gf /-
theorem SetTheory.PGame.Impartial.fuzzy_zero_iff_gf : G ‖ 0 ↔ 0 ⧏ G :=
  ⟨And.right, fun h => ⟨SetTheory.PGame.Impartial.lf_zero_iff.2 h, h⟩⟩
#align pgame.impartial.fuzzy_zero_iff_gf SetTheory.PGame.Impartial.fuzzy_zero_iff_gf
-/

#print SetTheory.PGame.Impartial.forall_leftMoves_fuzzy_iff_equiv_zero /-
theorem SetTheory.PGame.Impartial.forall_leftMoves_fuzzy_iff_equiv_zero :
    (∀ i, G.moveLeft i ‖ 0) ↔ (G ≈ 0) :=
  by
  refine' ⟨fun hb => _, fun hp i => _⟩
  · rw [equiv_zero_iff_le G, le_zero_lf]
    exact fun i => (hb i).1
  · rw [fuzzy_zero_iff_lf]
    exact hp.1.moveLeft_lf i
#align pgame.impartial.forall_left_moves_fuzzy_iff_equiv_zero SetTheory.PGame.Impartial.forall_leftMoves_fuzzy_iff_equiv_zero
-/

#print SetTheory.PGame.Impartial.forall_rightMoves_fuzzy_iff_equiv_zero /-
theorem SetTheory.PGame.Impartial.forall_rightMoves_fuzzy_iff_equiv_zero :
    (∀ j, G.moveRight j ‖ 0) ↔ (G ≈ 0) :=
  by
  refine' ⟨fun hb => _, fun hp i => _⟩
  · rw [equiv_zero_iff_ge G, zero_le_lf]
    exact fun i => (hb i).2
  · rw [fuzzy_zero_iff_gf]
    exact hp.2.lf_moveRight i
#align pgame.impartial.forall_right_moves_fuzzy_iff_equiv_zero SetTheory.PGame.Impartial.forall_rightMoves_fuzzy_iff_equiv_zero
-/

#print SetTheory.PGame.Impartial.exists_left_move_equiv_iff_fuzzy_zero /-
theorem SetTheory.PGame.Impartial.exists_left_move_equiv_iff_fuzzy_zero :
    (∃ i, G.moveLeft i ≈ 0) ↔ G ‖ 0 :=
  by
  refine' ⟨fun ⟨i, hi⟩ => (fuzzy_zero_iff_gf G).2 (lf_of_le_move_left hi.2), fun hn => _⟩
  rw [fuzzy_zero_iff_gf G, zero_lf_le] at hn 
  cases' hn with i hi
  exact ⟨i, (equiv_zero_iff_ge _).2 hi⟩
#align pgame.impartial.exists_left_move_equiv_iff_fuzzy_zero SetTheory.PGame.Impartial.exists_left_move_equiv_iff_fuzzy_zero
-/

#print SetTheory.PGame.Impartial.exists_right_move_equiv_iff_fuzzy_zero /-
theorem SetTheory.PGame.Impartial.exists_right_move_equiv_iff_fuzzy_zero :
    (∃ j, G.moveRight j ≈ 0) ↔ G ‖ 0 :=
  by
  refine' ⟨fun ⟨i, hi⟩ => (fuzzy_zero_iff_lf G).2 (lf_of_move_right_le hi.1), fun hn => _⟩
  rw [fuzzy_zero_iff_lf G, lf_zero_le] at hn 
  cases' hn with i hi
  exact ⟨i, (equiv_zero_iff_le _).2 hi⟩
#align pgame.impartial.exists_right_move_equiv_iff_fuzzy_zero SetTheory.PGame.Impartial.exists_right_move_equiv_iff_fuzzy_zero
-/

end Impartial

end SetTheory.PGame

