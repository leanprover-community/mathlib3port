/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.SetTheory.Game.Winner
import Mathbin.Tactic.NthRewrite.Default
import Mathbin.Tactic.EquivRw

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/


universe u

namespace Pgame

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Equiv

/-- The definition for a impartial game, defined using Conway induction -/
def ImpartialAux : Pgame → Prop
  | G => (G ≈ -G) ∧ (∀ i, impartial_aux (G.moveLeft i)) ∧ ∀ j, impartial_aux (G.moveRight j)

theorem impartial_aux_def {G : Pgame} :
    G.ImpartialAux ↔ (G ≈ -G) ∧ (∀ i, ImpartialAux (G.moveLeft i)) ∧ ∀ j, ImpartialAux (G.moveRight j) := by
  constructor
  · intro hi
    unfold1 impartial_aux  at hi
    exact hi
    
  · intro hi
    unfold1 impartial_aux
    exact hi
    

/-- A typeclass on impartial games. -/
class Impartial (G : Pgame) : Prop where
  out : ImpartialAux G

theorem impartial_iff_aux {G : Pgame} : G.Impartial ↔ G.ImpartialAux :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem impartial_def {G : Pgame} :
    G.Impartial ↔ (G ≈ -G) ∧ (∀ i, Impartial (G.moveLeft i)) ∧ ∀ j, Impartial (G.moveRight j) := by
  simpa only [impartial_iff_aux] using impartial_aux_def

namespace Impartial

instance impartial_zero : Impartial 0 := by
  rw [impartial_def]
  dsimp
  simp

theorem neg_equiv_self (G : Pgame) [h : G.Impartial] : G ≈ -G :=
  (impartial_def.1 h).1

instance move_left_impartial {G : Pgame} [h : G.Impartial] (i : G.LeftMoves) : (G.moveLeft i).Impartial :=
  (impartial_def.1 h).2.1 i

instance move_right_impartial {G : Pgame} [h : G.Impartial] (j : G.RightMoves) : (G.moveRight j).Impartial :=
  (impartial_def.1 h).2.2 j

instance impartial_add : ∀ G H : Pgame [G.Impartial] [H.Impartial], (G + H).Impartial
  | G, H => by
    intro hG hH
    rw [impartial_def]
    constructor
    · apply equiv_trans _ (neg_add_relabelling G H).Equiv.symm
      exact add_congr (neg_equiv_self _) (neg_equiv_self _)
      
    constructor
    all_goals
      intro i
      first |
        equiv_rw Pgame.leftMovesAdd G H  at i|
        equiv_rw Pgame.rightMovesAdd G H  at i
      cases i
    all_goals
      simp only [add_move_left_inl, add_move_right_inl, add_move_left_inr, add_move_right_inr]
      exact impartial_add _ _

instance impartial_neg : ∀ G : Pgame [G.Impartial], (-G).Impartial
  | G => by
    intro hG
    rw [impartial_def]
    constructor
    · rw [neg_negₓ]
      symm
      exact neg_equiv_self G
      
    constructor
    all_goals
      intro i
      first |
        equiv_rw G.left_moves_neg  at i|
        equiv_rw G.right_moves_neg  at i
      simp only [move_left_left_moves_neg_symm, move_right_right_moves_neg_symm]
      exact impartial_neg _

theorem winner_cases (G : Pgame) [G.Impartial] : G.FirstLoses ∨ G.FirstWins := by
  rcases G.winner_cases with (hl | hr | hp | hn)
  · cases' hl with hpos hnonneg
    rw [← not_ltₓ] at hnonneg
    have hneg := lt_of_lt_of_equiv hpos (neg_equiv_self G)
    rw [lt_iff_neg_gt, neg_negₓ, Pgame.neg_zero] at hneg
    contradiction
    
  · cases' hr with hnonpos hneg
    rw [← not_ltₓ] at hnonpos
    have hpos := lt_of_equiv_of_lt (neg_equiv_self G).symm hneg
    rw [lt_iff_neg_gt, neg_negₓ, Pgame.neg_zero] at hpos
    contradiction
    
  · left
    assumption
    
  · right
    assumption
    

theorem not_first_wins (G : Pgame) [G.Impartial] : ¬G.FirstWins ↔ G.FirstLoses := by
  cases winner_cases G <;>-- `finish using [not_first_loses_of_first_wins]` can close these goals
    simp [not_first_loses_of_first_wins, not_first_wins_of_first_loses, h]

theorem not_first_loses (G : Pgame) [G.Impartial] : ¬G.FirstLoses ↔ G.FirstWins :=
  Iff.symm <| iff_not_comm.1 <| Iff.symm <| not_first_wins G

theorem add_self (G : Pgame) [G.Impartial] : (G + G).FirstLoses :=
  first_loses_is_zero.2 <| equiv_trans (add_congr (neg_equiv_self G) G.equiv_refl) (add_left_neg_equiv G)

theorem equiv_iff_sum_first_loses (G H : Pgame) [G.Impartial] [H.Impartial] : (G ≈ H) ↔ (G + H).FirstLoses := by
  constructor
  · intro heq
    exact first_loses_of_equiv (add_congr (equiv_refl _) HEq) (add_self G)
    
  · intro hGHp
    constructor
    · rw [le_iff_sub_nonneg]
      exact
        le_transₓ hGHp.2
          (le_transₓ add_comm_le <| le_of_le_of_equiv (Pgame.le_refl _) <| add_congr (equiv_refl _) (neg_equiv_self G))
      
    · rw [le_iff_sub_nonneg]
      exact le_transₓ hGHp.2 (le_of_le_of_equiv (Pgame.le_refl _) <| add_congr (equiv_refl _) (neg_equiv_self H))
      
    

theorem le_zero_iff {G : Pgame} [G.Impartial] : G ≤ 0 ↔ 0 ≤ G := by
  rw [le_zero_iff_zero_le_neg, le_congr (equiv_refl 0) (neg_equiv_self G)]

theorem lt_zero_iff {G : Pgame} [G.Impartial] : G < 0 ↔ 0 < G := by
  rw [lt_iff_neg_gt, Pgame.neg_zero, lt_congr (equiv_refl 0) (neg_equiv_self G)]

theorem first_loses_symm (G : Pgame) [G.Impartial] : G.FirstLoses ↔ G ≤ 0 :=
  ⟨And.left, fun h => ⟨h, le_zero_iff.1 h⟩⟩

theorem first_wins_symm (G : Pgame) [G.Impartial] : G.FirstWins ↔ G < 0 :=
  ⟨And.right, fun h => ⟨lt_zero_iff.1 h, h⟩⟩

theorem first_loses_symm' (G : Pgame) [G.Impartial] : G.FirstLoses ↔ 0 ≤ G :=
  ⟨And.right, fun h => ⟨le_zero_iff.2 h, h⟩⟩

theorem first_wins_symm' (G : Pgame) [G.Impartial] : G.FirstWins ↔ 0 < G :=
  ⟨And.left, fun h => ⟨h, lt_zero_iff.2 h⟩⟩

theorem no_good_left_moves_iff_first_loses (G : Pgame) [G.Impartial] :
    (∀ i : G.LeftMoves, (G.moveLeft i).FirstWins) ↔ G.FirstLoses := by
  constructor
  · intro hbad
    rw [first_loses_symm G, le_def_lt]
    constructor
    · intro i
      specialize hbad i
      exact hbad.2
      
    · intro j
      exact Pempty.elimₓ j
      
    
  · intro hp i
    rw [first_wins_symm]
    exact (le_def_lt.1 <| (first_loses_symm G).1 hp).1 i
    

theorem no_good_right_moves_iff_first_loses (G : Pgame) [G.Impartial] :
    (∀ j : G.RightMoves, (G.moveRight j).FirstWins) ↔ G.FirstLoses := by
  rw [first_loses_of_equiv_iff (neg_equiv_self G), ← no_good_left_moves_iff_first_loses]
  refine' ⟨fun h i => _, fun h i => _⟩
  · simpa [first_wins_of_equiv_iff (neg_equiv_self ((-G).moveLeft i))] using h (left_moves_neg _ i)
    
  · simpa [first_wins_of_equiv_iff (neg_equiv_self (G.move_right i))] using h ((left_moves_neg _).symm i)
    

theorem good_left_move_iff_first_wins (G : Pgame) [G.Impartial] :
    (∃ i : G.LeftMoves, (G.moveLeft i).FirstLoses) ↔ G.FirstWins := by
  refine' ⟨fun ⟨i, hi⟩ => (first_wins_symm' G).2 (lt_def_le.2 <| Or.inl ⟨i, hi.2⟩), fun hn => _⟩
  rw [first_wins_symm' G, lt_def_le] at hn
  rcases hn with (⟨i, hi⟩ | ⟨j, _⟩)
  · exact ⟨i, (first_loses_symm' _).2 hi⟩
    
  · exact Pempty.elimₓ j
    

theorem good_right_move_iff_first_wins (G : Pgame) [G.Impartial] :
    (∃ j : G.RightMoves, (G.moveRight j).FirstLoses) ↔ G.FirstWins := by
  refine' ⟨fun ⟨j, hj⟩ => (first_wins_symm G).2 (lt_def_le.2 <| Or.inr ⟨j, hj.1⟩), fun hn => _⟩
  rw [first_wins_symm G, lt_def_le] at hn
  rcases hn with (⟨i, _⟩ | ⟨j, hj⟩)
  · exact Pempty.elimₓ i
    
  · exact ⟨j, (first_loses_symm _).2 hj⟩
    

end Impartial

end Pgame

